//! **M-1054 Stage 3 (OQ-H4) — affine soundness over the substituted expansion** (DN-117). The
//! non-vacuous acceptance/refusal/sabotage corpus DN-117 §5 commissions for the real
//! `Cx::check_sugar_call` mechanism: a check-time-only, shadowing-aware substituted `Expr` (each
//! argument spliced at every unshadowed occurrence of its value param — the `Expr`-level analogue
//! of [`crate::elab::sugar_expand`]'s (B) substitution) walked by the real, landed M-919
//! [`crate::affine::Tracker`], accepting iff no [`crate::affine::UseOutcome::DoubleUse`] is
//! produced.
//!
//! # Layout, mirroring `src/tests/hygiene_affine_expanded.rs`'s (E5) own discipline
//! - `A1`–`A3`: fixtures that must **ACCEPT** — linear top-level use, linear composite use, and the
//!   **drop** case (a corrected verdict — see DN-117 §4.3: the static pass enforces only
//!   use-at-most-once, never a must-consume lower bound, so an unused affine value param is
//!   accepted, not refused).
//! - `R1`–`R5`: fixtures that must **REFUSE** (a genuine duplicated affine move), each asserting the
//!   specific `double-consume` diagnostic, never "failed for some reason."
//! - **Non-vacuity, mandatory (not optional decoration):**
//!   1. **Mutation flips the verdict** — `A1`→`R1` (the same argument, only the RHS's occurrence
//!      count of its value param changes from one to two) flips ACCEPT→REFUSE.
//!   2. **Sabotage control** — [`crate::checkty::infer_type_with_active_affine_sabotaged`] (a
//!      `#[cfg(test)]`-only entry point that walks the **unsubstituted** RHS instead of the real
//!      substituted `Expr` — see that function's doc comment) makes `R2` and `R3` **wrongly
//!      ACCEPT**, proving the substituted-`Expr` splice is load-bearing (not just the trigger, and
//!      not just the per-argument type-check). `R1` and `R4` do **not** flip under this sabotage —
//!      documented per-fixture below, honestly, rather than silently only picking witnesses that
//!      flip (VR-5): those two hazards are already caught by mechanisms *other* than the
//!      substituted-`Expr` walk (the defensive param-scope seeding for `R1`'s top-level case; the
//!      ordinary per-argument affine bookkeeping for `R4`'s cross-argument-aliasing case).
//!
//! # Why every fixture uses [`infer_type_with_active_affine`], not the ordinary `infer_type`
//! Every existing M-1054 Stage 1b/Stage 3 white-box fixture (`src/tests/checkty.rs`,
//! `src/tests/reachability_stage1b.rs`) checks a bare call `Expr` via `crate::checkty::infer_type`
//! — necessary because there is still no surface grammar for `LowerDecl::value_params` (DN-110
//! §8.6), so there is no `check_nodule`/real-`fn`-body route to a `Cx` with an **active** affine
//! tracker. But `infer_type` is deliberately **inert** there (post-check re-inference — see its own
//! doc comment), which makes every `self.affine` interaction inside `Cx::check_sugar_call`'s Stage-3
//! mechanism a no-op: the per-argument tracker-touch trigger never fires and the substituted-`Expr`
//! walk can never detect a `DoubleUse`. **Every REFUSE/sabotage assertion in this module therefore
//! needs the active-tracker entry point** — using the inert one here would silently make every
//! REFUSE fixture pass for the wrong reason (always-accept, an inert tracker can never refuse). This
//! was confirmed empirically while building this module (both pre-existing "Stage 3 gate" tests in
//! `checkty.rs`/`reachability_stage1b.rs` that assert genuine duplication had to move to the active
//! entry point for the same reason — see their own updated doc comments).
//!
//! # A grounded, honestly-flagged residual (not this leaf's regression)
//! Aliasing a **pre-existing** `Handle`-typed local twice and destructuring each reference
//! independently (as opposed to R2's *freshly constructed* `Wrap(consume s)` argument) is **not**
//! caught — by an equivalent ordinary, non-sugar `fn` either (each pattern-match's field capture
//! creates its own independent tracker slot; the landed M-919 tracker does not itself track a
//! composite value's identity across two separate destructurings of it). This is a **pre-existing**
//! M-919 gap, not introduced or regressed by this leaf — verified in
//! `src/tests/checkty.rs::stage3_prior_handle_alias_destructured_twice_is_a_known_pre_existing_gap`
//! (which checks the hand-written, sugar-free equivalent too). DN-117 §4.3's own design goal is
//! "matches hand-written code's own static posture exactly" — this module's R2 is the shape Stage 3
//! *does* newly close (a fresh, argument-carried duplication the old wholesale gate could only
//! refuse by over-approximating every composite type).

use crate::ast::{
    Arm, BaseType, Expr, LowerDecl, LowerRhs, Param, Path, Pattern, TypeRef, WidthRef,
};
use crate::checkty::{
    check_nodule, infer_type_with_active_affine, infer_type_with_active_affine_sabotaged,
    CheckError, CtorInfo, DataInfo, Env, Ty,
};
use crate::parse;

// -------------------------------------------------------------------------------------------
// Builders (self-contained per the house test-layout rule — DRY-by-convention with
// `src/tests/checkty.rs`/`reachability_stage1b.rs`, not by shared code).
// -------------------------------------------------------------------------------------------

fn is_double_consume(err: &CheckError) -> bool {
    err.message.contains("double-consume")
}

fn bin8_ty() -> TypeRef {
    TypeRef {
        base: BaseType::Binary(WidthRef::Lit(8)),
        guarantee: None,
    }
}

fn substrate_ty(tag: &str) -> TypeRef {
    TypeRef {
        base: BaseType::Substrate(tag.to_owned()),
        guarantee: None,
    }
}

fn named_ty(name: &str) -> TypeRef {
    TypeRef {
        base: BaseType::Named(name.to_owned(), vec![]),
        guarantee: None,
    }
}

fn sv(name: &str) -> Expr {
    Expr::Path(Path(vec![name.to_owned()]))
}

fn bin8_lit(bits: &str) -> Expr {
    Expr::Lit(crate::ast::Literal::Bin(bits.to_owned()))
}

fn consume(e: Expr) -> Expr {
    Expr::Consume(Box::new(e))
}

fn call(name: &str, args: Vec<Expr>) -> Expr {
    Expr::App {
        head: Box::new(sv(name)),
        args,
    }
}

/// `let _ = consume <name> in <body>` — a drop-bound affine acquisition (the R3 "affine-hiding
/// non-affine type" shape: the *binding*'s own type is whatever `body` types to, not `Substrate`).
fn let_drop_consume_in(name: &str, body: Expr) -> Expr {
    Expr::Let {
        name: "_".to_owned(),
        ty: None,
        bound: Box::new(consume(sv(name))),
        body: Box::new(body),
    }
}

/// `Wrap(consume <name>)` — a freshly constructed composite argument that consumes `name` inline
/// (DN-117 §2/§5's A2/R2 shape — distinct from splicing a *pre-existing* `Handle`-typed local, see
/// this module's own doc comment).
fn wrap_consume(name: &str) -> Expr {
    call("Wrap", vec![consume(sv(name))])
}

/// `match <scrutinee_name> { Wrap(<bind>) => consume <bind> }`.
fn match_extract_consume(scrutinee_name: &str, bind: &str) -> Expr {
    Expr::Match {
        scrutinee: Box::new(sv(scrutinee_name)),
        arms: vec![Arm {
            pattern: Pattern::Ctor("Wrap".to_owned(), vec![Pattern::Ident(bind.to_owned())]),
            body: consume(sv(bind)),
        }],
    }
}

fn env(src: &str) -> Env {
    check_nodule(&parse::parse(src).expect("parses")).expect("checks")
}

/// The base fixture env every case starts from — one ordinary nullary `lower` rule (so the env's
/// registries are non-trivially populated), mirroring `checkty.rs::stage0_base_env` /
/// `reachability_stage1b.rs::base_env`.
fn base_env() -> Env {
    env("nodule d;\nlower Eight = 0b0000_0001;")
}

/// Register `Handle = Wrap(Substrate{gpu})` — DN-117 §1's composite/nested-affine shape.
fn register_handle(e: &mut Env) {
    e.types.insert(
        "Handle".to_owned(),
        DataInfo {
            home: String::new(), // DN-112/M-1036: test fixture, unqualified/bare identity
            name: "Handle".to_owned(),
            params: vec![],
            ctors: vec![CtorInfo {
                name: "Wrap".to_owned(),
                fields: vec![Ty::Substrate("gpu".to_owned())],
            }],
        },
    );
}

/// Register `Coin = Heads | Tails` (two nullary constructors) — the independent-selector type for
/// R5's match-arm-independence fixture.
fn register_coin(e: &mut Env) {
    e.types.insert(
        "Coin".to_owned(),
        DataInfo {
            home: String::new(), // DN-112/M-1036: test fixture, unqualified/bare identity
            name: "Coin".to_owned(),
            params: vec![],
            ctors: vec![
                CtorInfo {
                    name: "Heads".to_owned(),
                    fields: vec![],
                },
                CtorInfo {
                    name: "Tails".to_owned(),
                    fields: vec![],
                },
            ],
        },
    );
}

fn register_rule(e: &mut Env, name: &str, params: Vec<(&str, TypeRef)>, rhs: Expr) {
    e.lower_rules.insert(
        name.to_owned(),
        LowerDecl {
            name: name.to_owned(),
            params: vec![],
            value_params: params
                .into_iter()
                .map(|(n, ty)| Param {
                    name: n.to_owned(),
                    ty,
                })
                .collect(),
            rhs: LowerRhs::Expr(rhs),
        },
    );
}

fn substrate_scope(name: &str) -> Vec<(String, Ty)> {
    vec![(name.to_owned(), Ty::Substrate("gpu".to_owned()))]
}

// -------------------------------------------------------------------------------------------
// A1 — linear top-level accept: `use1(p: Substrate) = consume p`, invoked with a use-site
// `Substrate` argument.
// -------------------------------------------------------------------------------------------

fn a1_env() -> Env {
    let mut e = base_env();
    register_rule(
        &mut e,
        "Use1",
        vec![("p", substrate_ty("gpu"))],
        consume(sv("p")),
    );
    e
}

fn a1_call() -> Expr {
    call("Use1", vec![sv("some_substrate")])
}

#[test]
fn a1_linear_top_level_accept() {
    let e = a1_env();
    let mut scope = substrate_scope("some_substrate");
    infer_type_with_active_affine(&e, &mut scope, &a1_call())
        .expect("a Substrate value param used exactly once must be ACCEPTED (DN-117 A1)");
}

// -------------------------------------------------------------------------------------------
// A2 — linear composite accept: `once(h: Handle) = match h { Wrap(s) => consume s }`, invoked
// with a `Wrap(consume s)`-shaped argument used once.
// -------------------------------------------------------------------------------------------

fn a2_env() -> Env {
    let mut e = base_env();
    register_handle(&mut e);
    register_rule(
        &mut e,
        "Once",
        vec![("h", named_ty("Handle"))],
        match_extract_consume("h", "s"),
    );
    e
}

fn a2_call() -> Expr {
    call("Once", vec![wrap_consume("some_substrate")])
}

#[test]
fn a2_linear_composite_accept() {
    let e = a2_env();
    let mut scope = substrate_scope("some_substrate");
    infer_type_with_active_affine(&e, &mut scope, &a2_call()).expect(
        "a composite (`Handle`)-typed value param used exactly once, extracting the wrapped \
         affine field once, must be ACCEPTED (DN-117 A2)",
    );
}

// -------------------------------------------------------------------------------------------
// A3 — drop accept (the corrected verdict, DN-117 §4.3): `drop0(p: Substrate) = <literal>`, the
// param never referenced in the RHS.
// -------------------------------------------------------------------------------------------

fn a3_env() -> Env {
    let mut e = base_env();
    register_rule(
        &mut e,
        "Drop0",
        vec![("p", substrate_ty("gpu"))],
        bin8_lit("00000000"),
    );
    e
}

fn a3_call() -> Expr {
    call("Drop0", vec![sv("some_substrate")])
}

#[test]
fn a3_drop_accept_the_corrected_verdict() {
    let e = a3_env();
    let mut scope = substrate_scope("some_substrate");
    let ty = infer_type_with_active_affine(&e, &mut scope, &a3_call()).expect(
        "a Substrate value param never referenced in the RHS (a drop) must be ACCEPTED, not \
         refused — the static pass enforces only use-at-most-once, never a must-consume lower \
         bound (DN-117 §4.3, grounded in \
         tests::affine::a_never_consumed_substrate_binding_checks_the_static_pass_does_not_reject_leaks)",
    );
    assert_eq!(ty, Ty::Binary(crate::checkty::Width::Lit(8)));
}

// -------------------------------------------------------------------------------------------
// R1 — top-level double-consume: `dup(p: Substrate) = (consume p, consume p)`.
// -------------------------------------------------------------------------------------------

fn r1_env() -> Env {
    let mut e = base_env();
    register_rule(
        &mut e,
        "Dup",
        vec![("p", substrate_ty("gpu"))],
        Expr::TupleLit(vec![consume(sv("p")), consume(sv("p"))]),
    );
    e
}

fn r1_call() -> Expr {
    call("Dup", vec![sv("some_substrate")])
}

#[test]
fn r1_top_level_double_consume_refused() {
    let e = r1_env();
    let mut scope = substrate_scope("some_substrate");
    let err = infer_type_with_active_affine(&e, &mut scope, &r1_call())
        .expect_err("a Substrate value param used twice must be REFUSED (DN-117 R1)");
    assert!(is_double_consume(&err), "got: {}", err.message);
}

/// **Non-vacuity #1 — mutation flips the verdict (DN-117 §5 item 1).** `A1` and `R1` share the
/// *same* argument (`some_substrate`, a bare `Substrate` reference); the *only* difference is the
/// RHS's occurrence count of its value param (one vs. two). A checker that always accepted or
/// always rejected could not pass both directions.
#[test]
fn mutation_a1_to_r1_flips_accept_to_refuse() {
    let mut scope1 = substrate_scope("some_substrate");
    infer_type_with_active_affine(&a1_env(), &mut scope1, &a1_call())
        .expect("A1 (single use) must accept");
    let mut scope2 = substrate_scope("some_substrate");
    let err = infer_type_with_active_affine(&r1_env(), &mut scope2, &r1_call())
        .expect_err("R1 (doubled use, everything else held fixed) must refuse");
    assert!(is_double_consume(&err), "got: {}", err.message);
}

// -------------------------------------------------------------------------------------------
// R2 — composite double-consume via two pattern matches: `dup2(h: Handle) = (match h { Wrap(s)
// => consume s }, match h { Wrap(s) => consume s })`, invoked with a single `Wrap(consume s)`
// argument (DN-117's exact R2 shape, the exact case the old structural gate could only refuse by
// over-approximating every composite-typed value param).
// -------------------------------------------------------------------------------------------

fn r2_env() -> Env {
    let mut e = base_env();
    register_handle(&mut e);
    register_rule(
        &mut e,
        "Dup2",
        vec![("h", named_ty("Handle"))],
        Expr::TupleLit(vec![
            match_extract_consume("h", "s"),
            match_extract_consume("h", "s"),
        ]),
    );
    e
}

fn r2_call() -> Expr {
    call("Dup2", vec![wrap_consume("some_substrate")])
}

#[test]
fn r2_composite_double_consume_via_two_matches_refused() {
    let e = r2_env();
    let mut scope = substrate_scope("some_substrate");
    let err = infer_type_with_active_affine(&e, &mut scope, &r2_call()).expect_err(
        "a composite (`Handle`)-typed value param used twice, each occurrence extracting +\
         consuming the wrapped affine field, must be REFUSED (DN-117 R2) — this is exactly the \
         case a type-based gate cannot distinguish from A2 without inspecting the argument",
    );
    assert!(is_double_consume(&err), "got: {}", err.message);
}

/// **Non-vacuity #2a — sabotage control (DN-117 §5 item 2).** Feeding the walk the *unsubstituted*
/// RHS (simulating "the splice never happened," via
/// [`infer_type_with_active_affine_sabotaged`]) makes R2 wrongly **ACCEPT**: each `match h {
/// Wrap(s) => ... }` independently extracts a *fresh* tracker slot for `s` regardless of
/// substitution (field-capture is always a fresh acquisition — `crate::affine` module docs), so
/// without the splice putting `consume some_substrate` literally in both positions, there is
/// nothing shared for the tracker to see as duplicated. This proves the substituted-`Expr` splice
/// — not just the trigger or the per-argument check — is load-bearing for the composite case.
#[test]
fn r2_sabotage_without_substitution_wrongly_accepts() {
    let e = r2_env();
    let mut scope = substrate_scope("some_substrate");
    infer_type_with_active_affine_sabotaged(&e, &mut scope, &r2_call()).expect(
        "SABOTAGE CONTROL: with the substituted-Expr splice disabled, R2 must wrongly ACCEPT — \
         proving the splice (not just the trigger) is load-bearing. If this now fails, the \
         sabotage hook itself is broken (report this — the control is meant to prove a genuine \
         degradation, not silently reproduce the real pass's accept)",
    );
}

// -------------------------------------------------------------------------------------------
// R3 — affine-hiding non-affine type: `dupI(p: Int) = (p, p)`, invoked with `let _ = consume s
// in <lit>` — no structural (type-based) gate could ever catch this; only the substituted-term
// walk sees the duplicated `consume s`.
// -------------------------------------------------------------------------------------------

fn r3_env() -> Env {
    let mut e = base_env();
    register_rule(
        &mut e,
        "DupI",
        vec![("p", bin8_ty())],
        Expr::TupleLit(vec![sv("p"), sv("p")]),
    );
    e
}

fn r3_call() -> Expr {
    call(
        "DupI",
        vec![let_drop_consume_in("some_substrate", bin8_lit("00000000"))],
    )
}

#[test]
fn r3_affine_hiding_non_affine_type_refused() {
    let e = r3_env();
    let mut scope = substrate_scope("some_substrate");
    let err = infer_type_with_active_affine(&e, &mut scope, &r3_call()).expect_err(
        "an Int-typed value param used twice, whose argument hides a `consume` with no bearing \
         on the param's own declared type, must be REFUSED (DN-117 R3) — no type-based gate can \
         catch this; only the substituted-term walk sees the duplicated `consume`",
    );
    assert!(is_double_consume(&err), "got: {}", err.message);
}

/// **Non-vacuity #2b — sabotage control, the second (and sharpest) witness (DN-117 §5 item 2).**
/// Without the splice, `p`'s own declared type (`Binary{8}`) seeds a `Skip` slot — referencing `p`
/// twice touches nothing, and the real hazard (the `consume` buried in the *argument*) never
/// appears in the unsubstituted RHS at all. R3 wrongly **ACCEPTS** under sabotage — the single
/// sharpest proof that a type-based trigger alone (DN-117 §3.2's literal text) is insufficient and
/// the real walk is what does the work.
#[test]
fn r3_sabotage_without_substitution_wrongly_accepts() {
    let e = r3_env();
    let mut scope = substrate_scope("some_substrate");
    infer_type_with_active_affine_sabotaged(&e, &mut scope, &r3_call()).expect(
        "SABOTAGE CONTROL: with the substituted-Expr splice disabled, R3 must wrongly ACCEPT — \
         the sharpest witness that the real walk (not a type-based trigger) does the work",
    );
}

// -------------------------------------------------------------------------------------------
// R4 — cross-argument aliasing: a two-param rule invoked with the *same* affine local consumed as
// both arguments. DN-117 itself flags this may already be caught by the *outer* (per-argument)
// tracker walking the argument list, independent of the substituted-Expr mechanism — asserted and
// documented here, not silently assumed.
// -------------------------------------------------------------------------------------------

fn r4_env() -> Env {
    let mut e = base_env();
    register_rule(
        &mut e,
        "Pair",
        vec![("a", substrate_ty("gpu")), ("b", substrate_ty("gpu"))],
        Expr::TupleLit(vec![sv("a"), sv("b")]),
    );
    e
}

fn r4_call() -> Expr {
    call(
        "Pair",
        vec![consume(sv("some_substrate")), consume(sv("some_substrate"))],
    )
}

#[test]
fn r4_cross_argument_aliasing_refused() {
    let e = r4_env();
    let mut scope = substrate_scope("some_substrate");
    let err = infer_type_with_active_affine(&e, &mut scope, &r4_call()).expect_err(
        "the same affine local consumed as two different arguments of the same call must be \
         REFUSED (DN-117 R4)",
    );
    assert!(is_double_consume(&err), "got: {}", err.message);
}

/// **R4 does NOT flip under the substitution-sabotage control — documented, not silently omitted
/// (VR-5).** Unlike R2/R3, this hazard is caught by the *ordinary per-argument* affine bookkeeping
/// in `Cx::check_sugar_call`'s ordinary argument-checking loop — each argument is checked
/// sequentially against the *same* ambient scope/tracker (exactly as an ordinary ≥2-argument
/// function call would be), so the second `consume some_substrate` argument is already refused
/// *before* the Stage-3 substituted-Expr walk ever runs (that walk is never reached — the call
/// already errored). Confirmed here: sabotage must produce the *identical* refusal R4 does without
/// it, since the mechanism it disables is never on this hazard's path.
#[test]
fn r4_sabotage_does_not_change_the_verdict_different_layer_refuses_it() {
    let e = r4_env();
    let mut scope = substrate_scope("some_substrate");
    let err = infer_type_with_active_affine_sabotaged(&e, &mut scope, &r4_call()).expect_err(
        "R4 must still refuse even with the substituted-Expr splice sabotaged — a different \
         layer (the ordinary per-argument bookkeeping) is what catches this one",
    );
    assert!(is_double_consume(&err), "got: {}", err.message);
}

// -------------------------------------------------------------------------------------------
// R5 — match-arm independence is NOT a false positive: the same affine value consumed in two
// *mutually exclusive* RHS match arms must ACCEPT (guards against a naive occurrence-counter that
// would over-refuse — the branch-merge correctness control).
// -------------------------------------------------------------------------------------------

fn r5_env() -> Env {
    let mut e = base_env();
    register_handle(&mut e);
    register_coin(&mut e);
    let rhs = Expr::Match {
        scrutinee: Box::new(sv("c")),
        arms: vec![
            Arm {
                pattern: Pattern::Ctor("Heads".to_owned(), vec![]),
                body: match_extract_consume("h", "s"),
            },
            Arm {
                pattern: Pattern::Ctor("Tails".to_owned(), vec![]),
                body: match_extract_consume("h", "s2"),
            },
        ],
    };
    register_rule(
        &mut e,
        "Pick",
        vec![("h", named_ty("Handle")), ("c", named_ty("Coin"))],
        rhs,
    );
    e
}

fn r5_call() -> Expr {
    call("Pick", vec![wrap_consume("some_substrate"), sv("Heads")])
}

#[test]
fn r5_match_arm_independence_is_not_a_false_positive() {
    let e = r5_env();
    let mut scope = substrate_scope("some_substrate");
    infer_type_with_active_affine(&e, &mut scope, &r5_call()).expect(
        "the same composite affine value param referenced from two mutually-exclusive RHS match \
         arms (only one of which ever executes) must be ACCEPTED, not refused as a false \
         double-consume — the Tracker's own branch-merge (snapshot/restore) semantics, exercised \
         here over the *substituted* term (DN-117 R5)",
    );
}

// -------------------------------------------------------------------------------------------
// CRITICAL — FLAG-pattern-ctor-collision false-accept, fixed 2026-07-11 by adversarial review
// of facility Stage 3. `Cx::stage3_substitute_pattern` used to leave a match-arm `Pattern::Ident`
// binder UNRENAMED whenever its spelling happened to coincide with some unrelated registered
// nullary constructor (`Cx::is_any_nullary_ctor`), on the theory that this was "sound — never
// corrupts a real ctor reference." That theory was false: when the identifier is genuinely a
// binder (not a ctor reference) in *this* pattern, leaving it unrenamed skips the walk's own
// (A)-style capture-avoidance discipline, so a spliced argument's free variable of the *same*
// spelling (a caller-outer local, purely coincidentally named the same as the colliding ctor) is
// captured by the pattern binder instead of resolving to the caller's value — hiding a genuine
// double-consume from the tracker. Fixed: the ambiguous case now REFUSES the whole sugar call
// (a conservative false-REFUSE is sound; the false-ACCEPT was not) rather than guessing which
// reading is meant.
//
// Shape (mirrors the confirmed repro): `Sentinel = s` (a nullary ctor spelled `s`); `Pick3(h:
// Handle, q: Substrate) = match h { Wrap(s) => consume q }` — the field-pattern binder `s` is
// ambiguous only because it happens to spell `Sentinel`'s ctor, not because of anything about
// `Handle`/`Wrap`. Called as `(Pick3(Wrap(consume h_backing), s), consume s)` with a caller-outer
// local also named `s`: under the pre-fix behavior, the unrenamed pattern binder `s` shadows the
// substituted occurrence of `q` (itself `s`, textually) inside the match arm, so the arm's
// `consume q` consumes the FRESH pattern-bound `s` (from destructuring `Wrap(consume h_backing)`)
// instead of the caller's outer `s` — leaving the outer `s` still "Live" when the tuple's second
// element separately does `consume s`, a genuine double-consume of the caller's outer local that
// the pre-fix tracker never saw.
// -------------------------------------------------------------------------------------------

/// Register `Sentinel = s` — a single nullary constructor spelled `s`, purely to make the
/// spelling `s` ambiguous as a match-arm binder (`Cx::is_any_nullary_ctor("s")` becomes `true`).
/// `Sentinel` is otherwise unrelated to `Handle`/`Pick3` — the collision is a pure spelling
/// coincidence, exactly the class this fix closes.
fn register_sentinel_s(e: &mut Env) {
    e.types.insert(
        "Sentinel".to_owned(),
        DataInfo {
            home: String::new(), // DN-112/M-1036: test fixture, unqualified/bare identity
            name: "Sentinel".to_owned(),
            params: vec![],
            ctors: vec![CtorInfo {
                name: "s".to_owned(),
                fields: vec![],
            }],
        },
    );
}

/// `Pick3(h: Handle, q: Substrate) = match h { Wrap(s) => consume q }` — `s` is a genuine
/// field-pattern binder here (this pattern's scrutinee, `Handle`, has nothing to do with
/// `Sentinel`), but its spelling collides with `Sentinel`'s nullary ctor.
fn pattern_ctor_collision_env() -> Env {
    let mut e = base_env();
    register_handle(&mut e);
    register_sentinel_s(&mut e);
    register_rule(
        &mut e,
        "Pick3",
        vec![("h", named_ty("Handle")), ("q", substrate_ty("gpu"))],
        Expr::Match {
            scrutinee: Box::new(sv("h")),
            arms: vec![Arm {
                pattern: Pattern::Ctor("Wrap".to_owned(), vec![Pattern::Ident("s".to_owned())]),
                body: consume(sv("q")),
            }],
        },
    );
    e
}

fn pattern_ctor_collision_call() -> Expr {
    Expr::TupleLit(vec![
        call("Pick3", vec![wrap_consume("h_backing"), sv("s")]),
        consume(sv("s")),
    ])
}

fn pattern_ctor_collision_scope() -> Vec<(String, Ty)> {
    vec![
        ("h_backing".to_owned(), Ty::Substrate("gpu".to_owned())),
        ("s".to_owned(), Ty::Substrate("gpu".to_owned())),
    ]
}

#[test]
fn stage3_pattern_ctor_collision_false_accept_is_now_refused() {
    let e = pattern_ctor_collision_env();
    let mut scope = pattern_ctor_collision_scope();
    let err = infer_type_with_active_affine(&e, &mut scope, &pattern_ctor_collision_call())
        .expect_err(
            "CRITICAL, fixed 2026-07-11: a match-arm binder `s` that merely spells the same as \
             an unrelated registered nullary ctor `s` must not let a spliced argument's free \
             variable `s` be captured by that binder — this call genuinely double-consumes the \
             caller's outer `s` (once via the substituted `consume q` inside `Pick3`'s match arm \
             had renaming happened correctly, once via the outer `consume s`) and must be \
             REFUSED, not silently accepted",
        );
    assert!(
        err.message.contains("nullary") && err.message.contains("constructor"),
        "expected the FLAG-pattern-ctor-collision ambiguity refusal, got: {}",
        err.message
    );
}

// **Non-vacuity — confirmed by hand during this fix's development, not re-automated as a
// permanent sabotage hook (documented here, not silently omitted — VR-5).** With
// `Cx::stage3_substitute_pattern`'s ambiguous-`Ident` arm reverted to the pre-fix behavior
// (`pat.clone()` — leave unrenamed, no refusal) and every other line unchanged,
// `stage3_pattern_ctor_collision_false_accept_is_now_refused` (above) wrongly returns `Ok`
// instead of `Err` — i.e. `pattern_ctor_collision_call()` is falsely ACCEPTED under the old
// code, over the exact same env/scope/call this module now asserts refuses. This confirms the
// refusal is load-bearing (it catches a real, reproducible hazard) rather than a pre-existing
// refusal for some unrelated reason. Unlike the R2/R3 splice-sabotage controls above (which flip
// a *runtime* `#[cfg(test)]` toggle, `infer_type_with_active_affine_sabotaged`, so both readings
// stay reachable from one build), this fix changes which of two *incompatible* `Pattern` shapes
// `stage3_substitute_pattern` commits to at a single decision point — there is no sound way to
// keep both branches live behind one runtime toggle without duplicating the whole function,
// which is out of proportion to this fix's scope. Recorded here as a manual, documented
// confirmation (reproduced during development by `git stash`-reverting just this fix and
// re-running the test above, which then panics with `Ok(...)` instead of the expected `Err` —
// see this fix's own report) rather than a permanent sabotage hook.

// -------------------------------------------------------------------------------------------
// Control — a match-arm binder whose spelling does NOT collide with any registered nullary
// constructor must still be renamed and ACCEPTED normally (no over-refusal of the ordinary
// case introduced by this fix).
// -------------------------------------------------------------------------------------------

/// `Pick3Control(h: Handle, q: Substrate) = match h { Wrap(t) => consume q }` — no `t`-spelled
/// nullary ctor is registered anywhere in this env, so `t` is unambiguously a fresh binder.
fn pattern_no_collision_env() -> Env {
    let mut e = base_env();
    register_handle(&mut e);
    register_rule(
        &mut e,
        "Pick3Control",
        vec![("h", named_ty("Handle")), ("q", substrate_ty("gpu"))],
        Expr::Match {
            scrutinee: Box::new(sv("h")),
            arms: vec![Arm {
                pattern: Pattern::Ctor("Wrap".to_owned(), vec![Pattern::Ident("t".to_owned())]),
                body: consume(sv("q")),
            }],
        },
    );
    e
}

fn pattern_no_collision_call() -> Expr {
    call(
        "Pick3Control",
        vec![wrap_consume("h_backing"), sv("outer_q")],
    )
}

fn pattern_no_collision_scope() -> Vec<(String, Ty)> {
    vec![
        ("h_backing".to_owned(), Ty::Substrate("gpu".to_owned())),
        ("outer_q".to_owned(), Ty::Substrate("gpu".to_owned())),
    ]
}

#[test]
fn stage3_pattern_no_collision_control_still_accepts() {
    let e = pattern_no_collision_env();
    let mut scope = pattern_no_collision_scope();
    infer_type_with_active_affine(&e, &mut scope, &pattern_no_collision_call()).expect(
        "a match-arm binder whose spelling does NOT collide with any registered nullary \
         constructor must still be fresh-renamed and ACCEPTED normally — this fix must not \
         over-refuse the ordinary, unambiguous case",
    );
}
