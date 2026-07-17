//! DN-126 (M-1077) — the type-strictness axis. Fixtures live here (data-driven where it matters);
//! test bodies stay `assert`-over-a-case (CLAUDE.md test-layout rule).

use crate::checkty::{check_nodule, check_nodule_with_strictness, Env, Ty};
use crate::eval::{Evaluator, L1Value};
use crate::parse;
use crate::type_strictness::*;
use mycelium_core::Payload;

fn strict_env(src: &str) -> Env {
    check_nodule(&parse(src).expect("parses")).expect("strict-checks")
}

fn run(env: &Env) -> L1Value {
    Evaluator::new(env).call("main", vec![]).expect("evaluates")
}

fn bits(v: &L1Value) -> &Payload {
    let L1Value::Repr(r) = v else { panic!("repr") };
    r.payload()
}

// ---- an explicit ascription mismatch (DN-126 §3.1 "Hinted") -----------------------------------

/// `(0b0000_0001 : Ternary{1})` is a cross-paradigm ascription mismatch (Binary literal, Ternary
/// ascription) — `check_ascribe`'s demotable site.
const ASCRIBE_MISMATCH: &str =
    "nodule d;\nfn main() => Binary{8} = let x = (0b0000_0001 : Ternary{1}) in x;";

#[test]
fn strict_mode_refuses_the_ascription_mismatch() {
    let err = check_nodule(&parse(ASCRIBE_MISMATCH).expect("parses"))
        .expect_err("strict must refuse a violated ascription");
    assert!(
        err.message.contains("ascription"),
        "refusal should name the ascription site: {}",
        err.message
    );
}

/// The DoD fixture: loose mode FLAGS (not silently passes) the same type-level error, and the
/// program still runs on the interpreted path.
#[test]
fn loose_mode_flags_the_ascription_mismatch_instead_of_refusing() {
    let (env, flags) = check_nodule_with_strictness(
        &parse(ASCRIBE_MISMATCH).expect("parses"),
        TypeStrictness::Loose,
    )
    .expect("loose mode must not refuse a type-level ascription mismatch");
    assert_eq!(
        flags.len(),
        1,
        "exactly one demotion should fire: {flags:?}"
    );
    assert_eq!(flags[0].kind, TypeFlagKind::Ascription);
    assert_eq!(
        flags[0].declared,
        Ty::Ternary(crate::checkty::Width::Lit(1))
    );
    assert_eq!(
        flags[0].resolution,
        Resolution::Principal(Ty::Binary(crate::checkty::Width::Lit(8)))
    );

    // The program still runs: the evaluator ignores the ascribed type entirely (`Expr::Ascribe`
    // just evaluates `inner`), so `x` is the literal's own Binary{8} runtime value.
    let v = run(&env);
    assert_eq!(
        bits(&v),
        &Payload::Bits(vec![false, false, false, false, false, false, false, true])
    );
}

// ---- a function body vs. its declared return type ----------------------------------------------

/// `main`'s body is a bare `Binary{8}` literal but its declared return is `Ternary{1}` —
/// `check_fn_body`'s demotable "body" edge.
const RETURN_TYPE_MISMATCH: &str = "nodule d;\nfn main() => Ternary{1} = 0b0000_0001;";

#[test]
fn strict_mode_refuses_the_return_type_mismatch() {
    check_nodule(&parse(RETURN_TYPE_MISMATCH).expect("parses"))
        .expect_err("strict must refuse a body that disagrees with its declared return type");
}

#[test]
fn loose_mode_flags_the_return_type_mismatch_and_still_runs() {
    let (env, flags) = check_nodule_with_strictness(
        &parse(RETURN_TYPE_MISMATCH).expect("parses"),
        TypeStrictness::Loose,
    )
    .expect("loose mode must not refuse a type-level return-type mismatch");
    assert_eq!(
        flags.len(),
        1,
        "exactly one demotion should fire: {flags:?}"
    );
    assert_eq!(flags[0].kind, TypeFlagKind::ReturnType);

    let v = run(&env);
    assert_eq!(
        bits(&v),
        &Payload::Bits(vec![false, false, false, false, false, false, false, true])
    );
}

// ---- the runnable floor (DN-126 §3.3) stays HARD in loose mode ---------------------------------

/// An unresolved *name* is un-runnable, not merely untyped — this must refuse in **both** modes
/// (the demotion mechanism never touches this call path).
const UNRESOLVED_NAME: &str = "nodule d;\nfn main() => Binary{8} = no_such_fn();";

#[test]
fn loose_mode_still_refuses_an_unresolved_name() {
    let err = check_nodule_with_strictness(
        &parse(UNRESOLVED_NAME).expect("parses"),
        TypeStrictness::Loose,
    )
    .expect_err("an unresolved name is the runnable floor — it must refuse even in Loose mode");
    // Same refusal `check_nodule` (strict, the default) gives — the runnable floor is untouched by
    // the mode.
    let strict_err = check_nodule(&parse(UNRESOLVED_NAME).expect("parses"))
        .expect_err("strict refuses the same program");
    assert_eq!(err, strict_err);
}

// ---- loose == strict observable runtime, when there is nothing to flag (DN-126 §6.3/§9.2) ------

/// A well-typed program strict-checks cleanly; running it under `Loose` must be **observably
/// identical** (ADR-003 — loose mode changes the checker's gate, never the evaluator) and must
/// record zero flags.
#[test]
fn loose_and_strict_observable_runtime_are_identical_when_nothing_is_flagged() {
    let src = "nodule d;\nfn main() => Binary{8} = let a = 0b1010_1010 in not(a);";
    let strict = run(&strict_env(src));

    let (loose_env, flags) =
        check_nodule_with_strictness(&parse(src).expect("parses"), TypeStrictness::Loose)
            .expect("a well-typed program checks under either mode");
    assert!(flags.is_empty(), "nothing should be flagged: {flags:?}");
    let loose = run(&loose_env);

    assert_eq!(bits(&strict), bits(&loose));
}

/// `TypeStrictness::default()` is `Strict`, and `check_nodule` (the pre-M-1077 public entry
/// point) is unaffected by this axis's introduction — it always checks in `Strict` posture, so it
/// refuses exactly the fixtures above exactly as it always has.
#[test]
fn default_strictness_is_strict_and_check_nodule_is_unaffected() {
    assert_eq!(TypeStrictness::default(), TypeStrictness::Strict);
    assert!(!TypeStrictness::default().is_loose());
    assert!(TypeStrictness::Loose.is_loose());
    check_nodule(&parse(ASCRIBE_MISMATCH).expect("parses")).expect_err("unchanged: still refuses");
    check_nodule(&parse(RETURN_TYPE_MISMATCH).expect("parses"))
        .expect_err("unchanged: still refuses");
}

// ---- mechanical strictification (DN-126 §4) — the principality invariant (§4.1) ----------------
//
// The sharpest test: a `TypeFlag` whose resolution is `NonPrincipal` (⊥ or ambiguous) must NEVER
// be mechanically materialized — only ever surfaced. Constructed directly (no live call site in
// this landing produces `NonPrincipal` — see the `type_strictness` module doc) to prove the
// classifier itself is sound, independent of which sites currently feed it.

fn w(n: u32) -> crate::checkty::Width {
    crate::checkty::Width::Lit(n)
}

#[test]
fn strictify_materializes_only_principal_flags_and_surfaces_non_principal_ones() {
    let principal = TypeFlag {
        site: "f".to_owned(),
        kind: TypeFlagKind::ReturnType,
        declared: Ty::Binary(w(8)),
        resolution: Resolution::Principal(Ty::Binary(w(16))),
        message: "body has type Binary{16}, expected Binary{8}".to_owned(),
    };
    // Bottom: no type satisfies every constraint.
    let bottom = TypeFlag {
        site: "g".to_owned(),
        kind: TypeFlagKind::Ascription,
        declared: Ty::Bytes,
        resolution: Resolution::NonPrincipal { candidates: vec![] },
        message: "g's duck-typed value has no whole-program static type".to_owned(),
    };
    // Ambiguous: more than one observationally-distinct candidate (DN-126 §9.1's adversarial
    // "used at Binary{8} in one branch, Data(\"Foo\") in another" case).
    let ambiguous = TypeFlag {
        site: "h".to_owned(),
        kind: TypeFlagKind::Ascription,
        declared: Ty::Bytes,
        resolution: Resolution::NonPrincipal {
            candidates: vec![Ty::Binary(w(8)), Ty::Data("Foo".to_owned(), vec![])],
        },
        message: "h is used at two incompatible shapes".to_owned(),
    };

    let out = strictify(&[principal.clone(), bottom.clone(), ambiguous.clone()]);

    assert_eq!(out.materialized, vec![("f".to_owned(), Ty::Binary(w(16)))]);
    // Never-silent (G2): both non-principal flags are surfaced, in order, and NEITHER is guessed
    // into `materialized` — the soundness invariant, checked directly.
    assert_eq!(out.residual, vec![bottom, ambiguous]);
    assert!(out
        .materialized
        .iter()
        .all(|(_, ty)| *ty != Ty::Bytes && *ty != Ty::Data("Foo".to_owned(), vec![])));
}

#[test]
fn resolution_principal_accessor_matches_the_variant() {
    let p = Resolution::Principal(Ty::Bytes);
    assert_eq!(p.principal(), Some(&Ty::Bytes));
    let np = Resolution::NonPrincipal {
        candidates: vec![Ty::Bytes, Ty::Float],
    };
    assert_eq!(np.principal(), None);
}

#[test]
fn strictify_over_an_empty_flag_set_is_empty() {
    let out = strictify(&[]);
    assert!(out.materialized.is_empty());
    assert!(out.residual.is_empty());
}

#[test]
fn display_impls_are_non_empty_and_never_panic() {
    assert_eq!(TypeStrictness::Strict.to_string(), "strict");
    assert_eq!(TypeStrictness::Loose.to_string(), "loose");
    assert_eq!(TypeFlagKind::Ascription.to_string(), "ascription");
    assert_eq!(TypeFlagKind::ReturnType.to_string(), "return-type");
    let flag = TypeFlag {
        site: "f".to_owned(),
        kind: TypeFlagKind::ReturnType,
        declared: Ty::Bytes,
        resolution: Resolution::Principal(Ty::Float),
        message: "mismatch".to_owned(),
    };
    let rendered = flag.to_string();
    assert!(rendered.contains("loose:return-type"));
    assert!(rendered.contains('f'));
    assert!(rendered.contains("mismatch"));
}
