//! **E5 — affine soundness on the expanded L0 experiment** (M-1055;
//! DN-110-8.2-hygiene-deepdive §4(D)/§7 E5).
//!
//! Validates hygiene-model clause **(D)**: affine/type soundness is checked on the **expanded**
//! term, never asserted by the sugar itself — a sugar that duplicates or drops an affine
//! `Substrate` binding (DN-71 Model S §4.2) must not be able to *launder* the violation through
//! expansion.
//!
//! # Which checker, and why this experiment runs it differently from E1/E2
//!
//! E1/E2 operate on `mycelium_core::Node` — the interpreter's untyped L0 (confirmed at
//! `mycelium-core/src/node.rs:101`: *"the post-typecheck core is untyped — identity is
//! structural"*). The **landed, `Empirical` M-919 affine tracker** ([`crate::affine::Tracker`]),
//! however, is wired into [`crate::checkty::Cx`] and walks [`crate::ast::Expr`] — the **typed L1**
//! surface AST — *before* elaboration to L0 (`checkty.rs:2657`'s `check_lower_rule_rhs_type`,
//! `checkty.rs:3749`'s `check_fn_body`). There is no affine pass that runs directly over
//! `mycelium_core::Node`, because `Node` carries no type information to tell a `Substrate{Sock}`
//! binder from any other — the affine tracker's `Slot::for_ty` (`affine.rs:82`) is keyed on
//! [`crate::checkty::Ty`], which does not exist at the L0 layer.
//!
//! So this experiment's "expanded L0" is realized as a **fully-expanded SOURCE program** — the
//! sugar's RHS with its formal parameter's every occurrence substituted, verbatim, by the
//! use-site argument's surface spelling — fed through the **real, landed** `check_nodule` /
//! `check_fn_body` / `Tracker` pipeline via [`check`] (mirroring `tests/affine.rs`'s own `check`
//! helper exactly, DRY). This is a deliberate choice over reimplementing a parallel Node-level
//! affine checker: E5's job is to confirm the sugar cannot hide a violation from the checker that
//! actually ships, not to prototype a second one. It is not the E1/E2 `Node`-level prototype
//! `expand`; [`expand_source`] here is a **template substitution over surface text**, standing in
//! for "the sugar's RHS after its parameter is replaced by the use-site argument" at the level the
//! real affine tracker operates on.
//!
//! **A positive finding, not just a workaround.** Because L0 `Node` is genuinely untyped
//! (`node.rs:101`), running the affine tracker on substituted *surface* source isn't merely this
//! experiment's expedient stand-in — it likely **previews how the real M-1054 facility will have to
//! be wired**: `check_lower_rule_rhs_type` (`checkty.rs:2657`) already type/affine-checks a rule's
//! RHS as an L1 surface expression, and any future value-parameter substitution M-1054 adds would
//! most naturally re-run that same L1-level pass on the substituted RHS, exactly the shape this
//! module exercises — not a parallel Node-level pass that does not otherwise exist in the codebase.
//!
//! **Deliberately non-capturing (out of scope here — that is E1's job):** every fixture's
//! substituted argument spelling never collides with any name the sugar's own RHS introduces, so
//! this module says nothing about hygiene/capture — only about affine soundness once the (already
//! capture-safe, per E1) substitution has happened.
//!
//! # Additive, non-gating scope (read before treating a PASS as M-1055 progress)
//!
//! **E2 and E5 are additive exploration, not progress against M-1055's formal Definition of Done.**
//! M-1055's DoD is **E1 + E3** — the Rank-1 go/no-go the deep-dive commissions (§9); E3 (`reveal`
//! round-trip fidelity) needs `reveal` Increment-3 and is **unbuilt**, so the formal DoD is not
//! satisfied by this module or its E2 sibling. What a PASS here actually establishes: hygiene-model
//! clause **(D)** (affine soundness) moves `Declared → Empirical` **for the upper-bound
//! (duplication) property only**, via the real M-919 static pass — the drop lower-bound property is
//! an M-904 **runtime** concern, not validated as a static-rejection claim here (see the
//! scope-honesty section below).
//!
//! # Test-only — NOT the M-1054 facility
//!
//! Same posture as E1/E2: nothing here touches [`crate::elab::elaborate_lower_rule`] or any other
//! elaborator surface; `expand_source` lives only in `src/tests/`.
//!
//! # Non-vacuity discipline
//!
//! 1. Every fixture's expected verdict (accept/reject) is an **independent hand-verdict**,
//!    cross-checked against the *landed* semantics documented in `crate::affine`'s own module docs
//!    and the existing `tests/affine.rs` corpus (cited per-fixture below) — not invented for this
//!    experiment.
//! 2. **A mutation flips the verdict, twice, from two independent sources:** (i) duplicating the
//!    *substituted argument* reference (fixture 1 → 2) flips ACCEPT → REJECT; (ii) duplicating a
//!    binder the sugar's **own RHS** introduces, independent of the argument (fixture 4 → 5), also
//!    flips ACCEPT → REJECT. A checker call that always accepted (or always rejected) could not
//!    pass both directions.
//! 3. Every REJECT fixture's error is asserted to be the specific `double-consume` diagnostic
//!    (`is_double_consume`, reused verbatim from `tests/affine.rs`'s helper) — not merely "checking
//!    failed for some reason."
//!
//! # Scope honesty (VR-5) — a grounded correction to the task's assumed oracle for the drop case
//!
//! The task brief that commissioned this experiment describes case (c) — a sugar that **drops**
//! its parameter unused — as one of two sub-cases (with duplication) expected to be a **rejected**
//! affine violation on the expanded L0. **The landed M-919 static checker does not, in fact, reject
//! an unused `Substrate` binding.** (Citation correction: `crate::affine`'s own module docs only
//! *structurally imply* this — they document the tracker as enforcing use-once, not the absence of
//! a lower-bound check; the explicit statement that the *static* pass enforces only the **upper**
//! bound, with the **lower** bound closed at **runtime** instead, lives in the already-landed
//! `tests/affine.rs:304-312` — the
//! `a_never_consumed_substrate_binding_checks_the_static_pass_does_not_reject_leaks` test's own doc
//! comment — plus **DN-71 §8 FLAG-4**'s v0 posture and M-904's `release_if_abandoned`/
//! `SubstrateHandle::release`.) So [`fixture_dropping_unused`]'s **independent hand-verdict is
//! ACCEPT**, confirmed via that landed test + DN-71 §8 FLAG-4 / M-904 — not the REJECT the task
//! brief assumed. This is not an E5 failure and not a
//! new laundering channel opened by sugar: the sugar's expansion is checked by the exact same
//! static pass an equivalent hand-written function body would be, and that pass's documented v0
//! contract is silent on drops either way (mitigation #14 — verify the claim against the codebase
//! before building the fixture, rather than encode an unverified assumption). The runtime backstop
//! that *does* close the drop gap is out of scope for this static-checker-focused experiment (it
//! would require standing up a full `@std-sys`/`wild` acquire-and-run round trip through
//! `mycelium-interp`, disproportionate to a change-scoped test-only harness) — flagged, not built.
//!
//! # Guarantee tag
//!
//! Over this fixture corpus: the **upper-bound** affine property (a sugar cannot launder a
//! duplicated affine move through expansion) is **`Empirical`** for the static M-919 pass — checked
//! below, not proven, and only for the surface-substitution model of "expanded" this module uses
//! (see the "which checker" note above; not literally `mycelium_core::Node`). The **lower-bound**
//! (drop) property is **NOT** validated as a static-rejection claim here — see the scope-honesty
//! note; it stays whatever the landed runtime backstop already provides, unchanged and unexercised
//! by this module.

use crate::checkty::{check_nodule, CheckError, Env};
use crate::parse::parse;

/// Reused verbatim from `tests/affine.rs`'s own `check` helper (DRY — same real pipeline).
fn check(src: &str) -> Result<Env, CheckError> {
    check_nodule(&parse(src).expect("parses"))
}

/// Reused verbatim from `tests/affine.rs`'s own helper.
fn is_double_consume(err: &CheckError) -> bool {
    err.message.contains("double-consume")
}

/// Literal template substitution standing in for "the sugar's RHS with its formal parameter
/// replaced by the use-site argument's surface spelling" (module docs — the surface-text model of
/// expansion this experiment uses). `__ARG__` is the sugar's one formal-parameter placeholder;
/// real Mycelium surface syntax never produces that token, so there is no risk of an accidental
/// match against real syntax (e.g. the `Substrate{Sock}` braces elsewhere in the wrapping source
/// are untouched — this substitution only ever runs over the RHS-body fragment, never the whole
/// nodule source).
fn expand_source(rhs_template: &str, arg_spelling: &str) -> String {
    rhs_template.replace("__ARG__", arg_spelling)
}

/// One E5 fixture: a sugar RHS template (over one formal parameter, spliced via [`expand_source`])
/// plus any nodule-level prelude declarations it needs (a helper `fn`, for the RHS-own-fresh-binder
/// fixtures), assembled into a full nodule source and run through the **real** `check_nodule`
/// pipeline. `expect_accept` is the fixture's independent hand-verdict (see each fixture's doc
/// comment for its grounding).
struct AffineFixture {
    name: &'static str,
    /// Nodule-level declarations the RHS needs, inserted before the wrapping `fn f(...)`. Empty
    /// for the fixtures that need only the substituted argument itself.
    prelude: &'static str,
    /// Whether the nodule needs the `@std-sys` FFI floor (only the `make()`-acquiring fixtures).
    std_sys: bool,
    /// The sugar RHS template (`__ARG__` marks the formal parameter).
    rhs_template: &'static str,
    /// The wrapping fn's declared return type.
    ret_ty: &'static str,
    /// The wrapping fn's `!{…}` effect annotation (RFC-0014 §4.5 I3: no undeclared effects — a
    /// body that transitively performs `ffi` via calling `make()` must declare it on `f` too, not
    /// just on `make` itself). Empty for the fixtures that perform no effect.
    effects: &'static str,
    expect_accept: bool,
}

fn build_source(f: &AffineFixture, arg_spelling: &str) -> String {
    let body = expand_source(f.rhs_template, arg_spelling);
    let header = if f.std_sys {
        "nodule d @std-sys;\n"
    } else {
        "nodule d;\n"
    };
    format!(
        "{header}{prelude}fn f({arg}: Substrate{{Sock}}) => {ret} {effects}= {body};",
        header = header,
        prelude = f.prelude,
        arg = arg_spelling,
        ret = f.ret_ty,
        effects = f.effects,
        body = body
    )
}

// -------------------------------------------------------------------------------------------
// Fixtures
// -------------------------------------------------------------------------------------------

/// **(a) — linear, single use.** Sugar `use1(p) = consume p`, expanded against a use-site
/// `Substrate` argument. Independent verdict: **ACCEPT** — a single move of a `Substrate` binding
/// is exactly `tests/affine.rs::a_substrate_param_used_once_checks`'s shape.
fn fixture_linear_single_use() -> AffineFixture {
    AffineFixture {
        name: "linear_single_use (case a)",
        prelude: "",
        std_sys: false,
        rhs_template: "consume __ARG__",
        ret_ty: "Substrate{Sock}",
        effects: "",
        expect_accept: true,
    }
}

/// **(b) — duplicating.** Sugar `dup(p) = (consume p, consume p)` — the substituted argument is
/// referenced twice. Independent verdict: **REJECT** (double-consume) — the sugar must not be able
/// to launder a double-move of the use-site's own `Substrate` value; matches
/// `tests/affine.rs::a_substrate_param_used_twice_is_refused_naming_both_sites`'s shape, reached
/// here via substitution rather than direct authorship.
fn fixture_duplicating_double_consume() -> AffineFixture {
    AffineFixture {
        name: "duplicating_double_consume (case b)",
        prelude: "",
        std_sys: false,
        rhs_template: "(consume __ARG__, consume __ARG__)",
        ret_ty: "(Substrate{Sock}, Substrate{Sock})",
        effects: "",
        expect_accept: false,
    }
}

/// **(c) — dropping.** Sugar `drop0(p) = True` — the formal parameter never appears in the RHS, so
/// substitution leaves nothing to insert; the argument is passed in but never referenced.
/// Independent verdict: **ACCEPT** — see the module-level scope-honesty note: the landed static
/// checker's v0 contract does not reject an unused `Substrate` binding (the lower bound is a
/// runtime concern, M-904), grounded directly against
/// `tests/affine.rs::a_never_consumed_substrate_binding_checks_the_static_pass_does_not_reject_leaks`.
fn fixture_dropping_unused() -> AffineFixture {
    AffineFixture {
        name: "dropping_unused (case c)",
        prelude: "",
        std_sys: false,
        rhs_template: "True",
        ret_ty: "Bool",
        effects: "",
        expect_accept: true,
    }
}

/// **Independence — an RHS-own-fresh binder alongside the substituted argument.** Sugar
/// `mix(p) = let q = make() in (consume p, consume q)`: the RHS both consumes the substituted
/// argument **and** acquires + consumes an entirely separate `Substrate` value of its own (`q`,
/// standing in for a `%`-fresh RHS-introduced binder — see the note below on why this uses a
/// distinct rather than colliding spelling). Independent verdict: **ACCEPT** — two independently-
/// tracked single moves, matching `tests/affine.rs::two_distinct_substrate_bindings_each_used_once_checks`'s
/// shape (no false-positive cross-contamination between the two scope slots).
///
/// **Honesty on the spelling.** DN-110-8.2-hygiene-deepdive §4(D) and this task's brief describe
/// this property as holding for an RHS binder *identically spelled* to a use-site one (the
/// worst-case a real `%`-freshened name would never actually produce, per (A)). A literal
/// same-spelling collision in *this* surface-text model would require the RHS binder to shadow the
/// wrapping fn's own parameter name, which changes what "the substituted argument" even refers to
/// mid-body — a capture/shadowing concern (E1's territory), not this fixture's affine-independence
/// point. This fixture demonstrates the load-bearing mechanism instead: [`crate::affine::Tracker`]
/// tracks bindings **by scope index, not by name** (`affine.rs` module docs, `checkty.rs:3883`'s
/// field doc) — so two distinct declarations are independent *regardless* of spelling, which is
/// exactly what makes a same-spelled `%`-fresh binder safe in the real facility too.
fn fixture_independent_rhs_fresh_binder() -> AffineFixture {
    AffineFixture {
        name: "independent_rhs_fresh_binder",
        prelude: "fn make() => Substrate{Sock} !{ffi} = wild { host_call() };\n",
        std_sys: true,
        rhs_template: "let q = make() in (consume __ARG__, consume q)",
        ret_ty: "(Substrate{Sock}, Substrate{Sock})",
        effects: "!{ffi} ",
        expect_accept: true,
    }
}

/// **Mutation of [`fixture_independent_rhs_fresh_binder`] — duplicate only the RHS-own binder.**
/// `mix_bad(p) = let q = make() in (consume q, consume q)` — the substituted argument `p` is now
/// unused (a drop, case (c), independently ACCEPT-only per the scope-honesty note) while the RHS's
/// **own** fresh binder `q` is used twice. Independent verdict: **REJECT** (double-consume of `q`)
/// — demonstrates the checker catches a violation the sugar's **own RHS** introduces, not only one
/// that duplicates a substituted use-site argument (fixture 1→2's dimension). This is the second,
/// independent mutation-flips-the-verdict pairing (module doc point 2(ii)).
fn fixture_independent_rhs_fresh_binder_duplicated() -> AffineFixture {
    AffineFixture {
        name: "independent_rhs_fresh_binder_duplicated (mutation of the above)",
        prelude: "fn make() => Substrate{Sock} !{ffi} = wild { host_call() };\n",
        std_sys: true,
        rhs_template: "let q = make() in (consume q, consume q)",
        ret_ty: "(Substrate{Sock}, Substrate{Sock})",
        effects: "!{ffi} ",
        expect_accept: false,
    }
}

fn e5_fixtures() -> Vec<AffineFixture> {
    vec![
        fixture_linear_single_use(),
        fixture_duplicating_double_consume(),
        fixture_dropping_unused(),
        fixture_independent_rhs_fresh_binder(),
        fixture_independent_rhs_fresh_binder_duplicated(),
    ]
}

// -------------------------------------------------------------------------------------------
// The E5 assertion: the real M-919 checker's verdict on the expanded source, per fixture
// -------------------------------------------------------------------------------------------

/// **E5 — affine soundness on the expanded term, dual-graded against an independent hand-verdict.**
/// For every fixture: `check(build_source(f, "s"))`'s accept/reject outcome must match
/// `f.expect_accept`, and every reject must carry the specific `double-consume` diagnostic (not a
/// different failure). A mismatch here is a genuine soundness gap (house rule #2/VR-5): reported
/// honestly, never patched by adjusting a fixture's expected verdict to force a pass.
#[test]
fn e5_affine_soundness_corpus() {
    for f in e5_fixtures() {
        let src = build_source(&f, "s");
        let result = check(&src);
        match (f.expect_accept, result) {
            (true, Ok(_)) => {}
            (true, Err(e)) => panic!(
                "[{}] expected the expanded term to check cleanly, but it was refused: {}\n\
                 source:\n{}",
                f.name, e.message, src
            ),
            (false, Err(e)) => assert!(
                is_double_consume(&e),
                "[{}] expected a double-consume refusal, got a different refusal: {}",
                f.name,
                e.message
            ),
            (false, Ok(_)) => panic!(
                "[{}] expected the expanded term to be REFUSED (the sugar must not be able to \
                 launder this affine violation), but it checked cleanly.\nsource:\n{}",
                f.name, src
            ),
        }
    }
}

/// **Non-vacuity — mutation 1: duplicating the substituted argument flips ACCEPT → REJECT.**
/// Fixture 1 (single use) vs fixture 2 (double use of the *same* substituted argument, everything
/// else held fixed) — a checker call that always accepted or always rejected could not pass this.
#[test]
fn e5_mutation_flips_verdict_on_argument_duplication() {
    let accept_src = build_source(&fixture_linear_single_use(), "s");
    let reject_src = build_source(&fixture_duplicating_double_consume(), "s");
    check(&accept_src).expect("single use of the substituted argument must check cleanly");
    let err =
        check(&reject_src).expect_err("doubled use of the substituted argument must be refused");
    assert!(is_double_consume(&err), "got: {}", err.message);
}

/// **Non-vacuity — mutation 2: duplicating the RHS's OWN fresh binder flips ACCEPT → REJECT.**
/// Independent of mutation 1's dimension (the substituted argument is untouched between these two
/// fixtures — only the RHS-introduced `q` binder's use count changes) — demonstrates the checker
/// genuinely engages with bindings the sugar's expansion introduces on its own, not only ones that
/// come from the use site.
#[test]
fn e5_mutation_flips_verdict_on_rhs_own_binder_duplication() {
    let accept_src = build_source(&fixture_independent_rhs_fresh_binder(), "s");
    let reject_src = build_source(&fixture_independent_rhs_fresh_binder_duplicated(), "s");
    check(&accept_src).expect("single use of both the argument and the RHS's own binder checks");
    let err =
        check(&reject_src).expect_err("doubled use of the RHS's own fresh binder must be refused");
    assert!(is_double_consume(&err), "got: {}", err.message);
}

/// **Grounding spot-check for the scope-honesty note.** Directly restates
/// `tests/affine.rs::a_never_consumed_substrate_binding_checks_the_static_pass_does_not_reject_leaks`
/// through this module's own `check`/`build_source` path, so the drop fixture's ACCEPT verdict
/// above is not merely asserted but independently re-derived here too.
#[test]
fn e5_drop_case_grounding_matches_the_landed_static_posture() {
    let src = build_source(&fixture_dropping_unused(), "s");
    check(&src).expect(
        "a never-consumed Substrate binding must still check under the landed v0 static posture \
         (DN-71 §8 FLAG-4) — the lower bound is a runtime concern (M-904), not a static refusal",
    );
}
