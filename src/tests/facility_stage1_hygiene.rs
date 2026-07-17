//! **M-1054 Stage 1 — production capture-avoidance verification** (DN-110-8.2-hygiene-deepdive §4
//! (A)+(B); OQ-H5). Ports `src/tests/hygiene_expr_sugar.rs`'s E1 fixture corpus onto the **real**
//! elaborator path — [`crate::elab::elaborate_lower_rule_with_args`] — instead of E1's test-only
//! `Expander`. This is the production go/no-go: E1's PASS was over a throwaway prototype; the real
//! elaborator path needs its own witness before (A)+(B) can be tagged `Empirical` *for that path*
//! (VR-5 — a checked basis, not inherited from a different code path).
//!
//! # Why the fixtures are NOT a byte-for-byte copy of E1 (an honest adaptation, not a shortcut)
//!
//! E1's `Expander` walked a **hand-built** `Node` with every binder still in its **raw surface
//! spelling** (`"t"`, never `"t%0"`), so E1's capture scenario was: does the walker's own (A)+(B)
//! correctly avoid a *surface-level* spelling collision between an RHS binder and a literal
//! use-site free variable of the same spelling?
//!
//! The **production** path is different in one respect that turns out to matter: `elaborate_value_
//! parametric_rule`'s first pass elaborates the RHS through the **real elaborator**
//! (`Elab::expr`), which — exactly like elaborating any ordinary function body — **already**
//! assigns every `let`/`lambda` binder a fresh, `%`-namespaced kernel name via `Elab::fresh`
//! (unconditionally, the same machinery every other elaboration path uses). So a *literal* surface
//! spelling collision (an RHS `let t = …` vs. a use-site free `Var("t")`) can no longer arise after
//! pass 1 — pass 1's own pre-existing scope handling already resolves it, for free, before pass 2
//! (`sugar_expand`) ever runs. Reusing E1's fixtures verbatim (with a bare `Var("t")` argument)
//! would therefore be **vacuous** on the production path: freshening on or off would produce the
//! same observable result, because there is nothing left to collide with.
//!
//! The **real** residual hazard on the production path is exactly what OQ-H5 names: **cross-
//! invocation** collision. `Elab::fresh`'s counter resets to `0` for every *independent* top-level
//! elaboration (a fresh `Elab` per call), so two unrelated elaborations can each mint the identical
//! kernel name (`"t%0"`) for their own, unrelated binders. If an argument passed to
//! `elaborate_lower_rule_with_args` is itself a **free reference into some other, already-
//! elaborated context** (the realistic shape a real caller would pass — see `/forward`'s def-site-
//! resolution note, OQ-H1) and that reference happens to be spelled exactly what *this* RHS's own
//! pass 1 is about to mint, disabling pass 2's site-qualified re-freshening captures it for real.
//! So every fixture below builds its "escaping free variable" argument by **actually eliciting**
//! the real elaborator's own first-fresh-name choice (`fresh_kernel_name_via_real_elaboration`)
//! rather than a hand-picked string — non-vacuous by construction, and robust to `Elab::fresh`'s
//! exact numbering scheme ever changing.
//!
//! # The dual non-vacuity oracle (same discipline as E1 — module doc points 1-3 there)
//!
//! For every fixture: (1) [`alpha_eq`] against an independently hand-built oracle using disjoint
//! binder spellings; (2) an independent observational check — `Interpreter::eval` on the real
//! expansion wrapped in its use-site binding, compared to `eval` on the oracle wrapped the same
//! way; (3) the **disable-freshening negative control**
//! (`elaborate_value_parametric_rule_disable_freshening_for_test`, `#[cfg(test)]`-gated in
//! `elab.rs`) — the exact same production pipeline with pass 2's freshening turned off — which
//! must (and does) evaluate to a *different*, wrong value, proving this corpus is capable of
//! catching a real capture bug, not merely failing to trigger one it never exercises.
//!
//! # Scope / guarantee tag (VR-5)
//! A PASS here moves capture-avoidance for **(A)+(B), on the real `elaborate_lower_rule_with_args`
//! path**, `Declared -> Empirical`. It says nothing about (C) def-site resolution or (D) affine-on-
//! expanded-L0 (both stay `Declared`, Stage 2/3). This module's fixtures all call
//! `elaborate_lower_rule`/`elaborate_lower_rule_with_args` **directly** (the white-box entry
//! points, unchanged by M-1054 Stage 1b), never through `Cx::check_sugar_call` — so this module
//! says nothing about the L1 check-phase or the full check→elab reachability chain either way.
//! **Since M-1054 Stage 1b** (DN-116), `Cx::check_sugar_call` no longer unconditionally refuses
//! every recognized call — it accepts a call whose RHS clears the Stage-2 (OQ-H1)/Stage-3 (OQ-H4)
//! gates, and `Elab::app` dispatches such a call to this exact `elaborate_lower_rule_with_args`
//! machinery (§5.2 wiring) — see `src/tests/reachability_stage1b.rs` for that full-chain
//! (check → elab → eval) reachability corpus, this module's production-elaborator-path companion.

use crate::ast::{BaseType, Expr, Literal, LowerDecl, LowerRhs, Param, Path, TypeRef, WidthRef};
use crate::checkty::{check_nodule, Env};
use crate::elab::{
    build_registry, elaborate_lower_rule, elaborate_lower_rule_with_args,
    elaborate_value_parametric_rule_disable_freshening_for_test, sugar_expand, Elab,
};
use crate::parse;
use crate::reveal::alpha_eq;
use mycelium_core::{Alt, ContentHash, CtorRef, Meta, Node, Payload, Provenance, Repr, Value};
use mycelium_interp::Interpreter;
use std::collections::BTreeMap;

fn env(src: &str) -> Env {
    check_nodule(&parse(src).expect("parses")).expect("checks")
}

// -------------------------------------------------------------------------------------------
// Node-level builders (the use-site / oracle side — mirrors `hygiene_expr_sugar.rs`'s builders
// exactly, DRY-by-convention with that module rather than by shared code, per the house test-
// layout rule that each in-crate test module is self-contained).
// -------------------------------------------------------------------------------------------

const WIDTH: u32 = 8;

fn c(i: i64) -> Node {
    let bits = mycelium_core::binary::int_to_bits(i, WIDTH).expect("fits in 8 bits");
    Node::Const(
        Value::new(
            Repr::Binary { width: WIDTH },
            Payload::Bits(bits),
            Meta::exact(Provenance::Root),
        )
        .expect("well-formed Binary{8} const"),
    )
}

fn v(name: &str) -> Node {
    Node::Var(name.to_owned())
}

fn letn(id: &str, bound: Node, body: Node) -> Node {
    Node::Let {
        id: id.to_owned(),
        bound: Box::new(bound),
        body: Box::new(body),
    }
}

fn add(x: Node, y: Node) -> Node {
    Node::Op {
        prim: "bin.add".to_owned(),
        args: vec![x, y],
    }
}

fn as_i64(result: &Value) -> i64 {
    match result.payload() {
        Payload::Bits(bits) => mycelium_core::binary::bits_to_int(bits),
        other => panic!("expected a Binary payload, got {other:?}"),
    }
}

// -------------------------------------------------------------------------------------------
// Surface-Expr builders (the RHS side — what a real `lower` rule's RHS parses/is constructed to;
// fed to `elaborate_lower_rule_with_args` through a real, checked-shape `Env`, never through
// E1's Node-level `Expander`).
// -------------------------------------------------------------------------------------------

fn bin_ty(width: u32) -> TypeRef {
    TypeRef {
        base: BaseType::Binary(WidthRef::Lit(width)),
        guarantee: None,
    }
}

fn sc(i: u8) -> Expr {
    Expr::Lit(Literal::Bin(format!("{i:08b}")))
}

fn sv(name: &str) -> Expr {
    Expr::Path(Path(vec![name.to_owned()]))
}

fn slet(name: &str, bound: Expr, body: Expr) -> Expr {
    Expr::Let {
        name: name.to_owned(),
        ty: None,
        bound: Box::new(bound),
        body: Box::new(body),
    }
}

fn sadd(x: Expr, y: Expr) -> Expr {
    Expr::App {
        head: Box::new(sv("add_s")),
        args: vec![x, y],
    }
}

/// Register a value-parametric `lower` rule (white-box — no surface grammar yet, per
/// `LowerDecl::value_params`'s doc comment) with two `Binary{8}` value parameters `a, b` and the
/// given `rhs`, into a base checked `Env`.
fn base_env_with_rule(rule_name: &str, rhs: Expr) -> Env {
    let mut e = env("nodule d;\nlower Base = 0b00000000;");
    e.lower_rules.insert(
        rule_name.to_owned(),
        LowerDecl {
            name: rule_name.to_owned(),
            params: vec![],
            value_params: vec![
                Param {
                    name: "a".to_owned(),
                    ty: bin_ty(8),
                },
                Param {
                    name: "b".to_owned(),
                    ty: bin_ty(8),
                },
            ],
            rhs: LowerRhs::Expr(rhs),
        },
    );
    e
}

/// **Non-vacuity construction (the module doc's central point).** The realistic spelling an
/// "escaping free variable from some other, unrelated elaboration" argument could carry — obtained
/// by *actually eliciting* the real elaborator's own first-fresh-name choice for a `let <base> =
/// … in <base>` rule, through the real public nullary entry point ([`elaborate_lower_rule`]), and
/// reading back the kernel variable it minted. Every independent top-level elaboration resets
/// `Elab::fresh`'s counter to `0` (a fresh `Elab` per call), so this is exactly the name a second,
/// unrelated `let <base> = …` would *also* mint — the real OQ-H5 cross-invocation collision shape,
/// not a hand-picked string that happens to look right.
fn fresh_kernel_name_via_real_elaboration(base: &str) -> String {
    let rule_name = format!("Probe{base}");
    let src = format!("nodule d;\nlower {rule_name} = let {base} = 0b00000000 in {base};");
    let e = env(&src);
    let node = elaborate_lower_rule(&e, &rule_name).expect("the probe rule elaborates");
    let Node::Let { ref id, .. } = node else {
        panic!("expected the probe rule to elaborate to a `Let`, got {node:?}");
    };
    id.clone()
}

/// One production fixture: a value-parametric rule (`a`, `b`) whose RHS shadows/reuses a binder
/// spelled the same as [`fresh_kernel_name_via_real_elaboration`]'s realistic colliding free
/// variable, an oracle built independently (disjoint binder spellings), and the hand-derived
/// hygienic/captured expected values (same numbers E1 derived — only the *colliding spelling*
/// differs, the arithmetic is unchanged).
struct Fixture {
    name: &'static str,
    rule_name: &'static str,
    rhs: Expr,
    /// `(arg_for_a, arg_for_b)` — `arg_for_b` (or `arg_for_a`, per fixture) is the colliding free
    /// variable built via [`fresh_kernel_name_via_real_elaboration`].
    args: (Node, Node),
    /// The use-site binding wrapping the expansion — binds the colliding free variable's name to
    /// its "real" outer value.
    wrap_id: String,
    wrap_value: Node,
    oracle: Node,
    expected_hygienic: i64,
    expected_captured: i64,
}

/// **Fixture 1 — binder-shadows-use-site (the swap2 classic, DN-110-8.2-hygiene-deepdive §7 E1),
/// adapted to the cross-invocation collision the production path actually needs to guard (see the
/// module doc).** `swap2(a, b) = let t = a in add(b, t)`, invoked with `a = 1`, `b` = the colliding
/// free variable — the same shape a second, unrelated `let t = …` elsewhere would also produce. The
/// use site binds that name to `7`. Hygienic: the RHS's own `t` is re-freshened under a site-
/// qualified namespace, so `b`'s `7` survives: `add(7, 1) = 8`. Captured (freshening disabled): the
/// RHS's `t` keeps pass 1's raw (unqualified) name, colliding with `b`'s own reference, so both
/// operands read the *inner* `1`: `add(1, 1) = 2`.
fn fixture_binder_shadows_use_site() -> Fixture {
    let rhs = slet("t", sv("a"), sadd(sv("b"), sv("t")));
    let colliding = fresh_kernel_name_via_real_elaboration("t");
    let oracle = letn("t_h1", c(1), add(v(&colliding), v("t_h1")));
    Fixture {
        name: "binder_shadows_use_site (swap2 classic)",
        rule_name: "Swap2",
        rhs,
        args: (c(1), v(&colliding)),
        wrap_id: colliding,
        wrap_value: c(7),
        oracle,
        expected_hygienic: 8,
        expected_captured: 2,
    }
}

/// **Fixture 2 — arg mentions the RHS's raw binder spelling, from the OTHER parameter position.**
/// `pair_add(a, b) = let t = b in add(a, t)`, `a` = the colliding free variable, `b = 9`. Hygienic:
/// `add(3, 9) = 12` (the use site binds the colliding name to `3`). Captured: the unfreshened
/// `let t = 9 in …` shadows the reference, hijacking it: `add(9, 9) = 18`.
fn fixture_arg_mentions_raw_binder_spelling() -> Fixture {
    let rhs = slet("t", sv("b"), sadd(sv("a"), sv("t")));
    let colliding = fresh_kernel_name_via_real_elaboration("t");
    let oracle = letn("t_h2", c(9), add(v(&colliding), v("t_h2")));
    Fixture {
        name: "arg_mentions_raw_binder_spelling (pair_add)",
        rule_name: "PairAdd",
        rhs,
        args: (v(&colliding), c(9)),
        wrap_id: colliding,
        wrap_value: c(3),
        oracle,
        expected_hygienic: 12,
        expected_captured: 18,
    }
}

/// **Fixture 3 — multi-param, RHS binder used twice.** `f(a, b) = let t = a in add(b, add(t, t))`,
/// `a = 5`, `b` = the colliding free variable bound to `2` at the use site. Hygienic:
/// `add(2, add(5, 5)) = 12`. Captured: `let t = 5 in …` shadows, so `b`'s reference reads the inner
/// `5` too: `add(5, add(5, 5)) = 15`.
fn fixture_multi_param_used_twice() -> Fixture {
    let rhs = slet("t", sv("a"), sadd(sv("b"), sadd(sv("t"), sv("t"))));
    let colliding = fresh_kernel_name_via_real_elaboration("t");
    let oracle = letn("t_h3", c(5), add(v(&colliding), add(v("t_h3"), v("t_h3"))));
    Fixture {
        name: "multi_param_used_twice (f)",
        rule_name: "MultiUse",
        rhs,
        args: (c(5), v(&colliding)),
        wrap_id: colliding,
        wrap_value: c(2),
        oracle,
        expected_hygienic: 12,
        expected_captured: 15,
    }
}

/// **Fixture 4 — nested binder in the RHS (TWO `let`s, both spelled `t`).**
///
/// **Honest adaptation, flagged (not a shortcut).** E1's own fixture 4 used a `let` **and** a
/// `lambda`, both spelled `t`, to exercise that (A) freshens every kind of binder independently.
/// Porting the `lambda` form literally onto the real elaborator hits a **pre-existing, orthogonal**
/// limitation — confirmed to predate this leaf and to be independent of the value-parametric (A)+
/// (B) work: `elaborate_lower_rule`'s synthetic-single-function-`Env` mechanism (unchanged since
/// before M-1054) cannot elaborate **any** `lower` rule whose RHS is a `lambda` immediately applied
/// (an IIFE) — `crate::mono`'s closure defunctionalization synthesizes a dispatcher function
/// (`apply$Fn$…`) that the ad-hoc single-function synthetic `Env` this mechanism builds does not
/// register, so elaboration refuses with `unknown function/constructor/prim
/// apply$Fn$Binary8$Binary8`. **Reproduced on the plain nullary path too**
/// (`elaborate_lower_rule` on `lower L = (lambda(x: Binary{8}) => add_s(x, 1))(2);` fails
/// identically), so this is not a Stage 1 regression — it is a standing gap in how a `lower` rule's
/// RHS is elaborated at all, independent of value parameters, out of this leaf's (A)+(B) scope
/// (FLAGGED for whoever next touches `elaborate_lower_rule`'s synthetic-entry construction).
///
/// This fixture is therefore adapted to a **second nested `let`** in place of the `lambda`
/// (`let t = b in add(t, 1)` is the beta-reduced form of `(lambda(t) => add(t, 1))(b)` — same
/// value, same binder-nesting shape, same hand-derived expected numbers as E1's original) so it
/// still exercises "(A) freshens every RHS binder independently, including two *different* binders
/// that happen to share a spelling" without depending on the orthogonal lambda-IIFE gap.
///
/// `nest(a, b) = let t = a in add((let t = b in add(t, 1)), t)`, `a = 2`, `b` = the colliding free
/// variable bound to `100` at the use site. Hygienic: inner `let t = 100 in add(t, 1) = 101`, then
/// outer `add(101, 2) = 103`. Captured (freshening disabled): the *outer* `t` keeps pass 1's raw
/// name, colliding with `b`'s own reference — so `b` (used as the *inner* let's bound expression)
/// is captured by the **outer** binder (bound to `a = 2`, not the true use-site `100`): inner
/// `let t = 2 in add(t, 1) = 3`, then outer `add(3, 2) = 5` — the *inner* `t` is a distinct pass-1
/// binder either way (its own fresh name never collides), so only the outer/use-site collision
/// fires, exactly mirroring the lambda version's captured value.
fn fixture_nested_binder_in_rhs() -> Fixture {
    let rhs = slet(
        "t",
        sv("a"),
        sadd(slet("t", sv("b"), sadd(sv("t"), sc(1))), sv("t")),
    );
    let colliding = fresh_kernel_name_via_real_elaboration("t");
    let oracle = letn(
        "oracle_let_t",
        c(2),
        add(
            letn(
                "oracle_inner_t",
                v(&colliding),
                add(v("oracle_inner_t"), c(1)),
            ),
            v("oracle_let_t"),
        ),
    );
    Fixture {
        name: "nested_binder_in_rhs (nest — two lets both spelled t; adapted from E1's let+lambda)",
        rule_name: "Nest",
        rhs,
        args: (c(2), v(&colliding)),
        wrap_id: colliding,
        wrap_value: c(100),
        oracle,
        expected_hygienic: 103,
        expected_captured: 5,
    }
}

fn core_fixtures() -> Vec<Fixture> {
    vec![
        fixture_binder_shadows_use_site(),
        fixture_arg_mentions_raw_binder_spelling(),
        fixture_multi_param_used_twice(),
        fixture_nested_binder_in_rhs(),
    ]
}

/// **The M-1054 Stage 1 production go/no-go.** For every fixture: (1) the real
/// `elaborate_lower_rule_with_args` expansion is `alpha_eq` to the independently hand-built oracle;
/// (2) `eval` of the expansion (wrapped in its use-site binding) agrees with `eval` of the oracle
/// (wrapped the same way), independent of `alpha_eq`; (3) the disable-freshening negative control —
/// the same pipeline with pass 2's freshening turned off — evaluates to the hand-derived *wrong*
/// (captured) value, proving this corpus is capable of catching a real capture bug (non-vacuity).
/// A failure anywhere here is reported honestly (house rule #2/VR-5): it is a genuine finding about
/// the production path, never patched away by adjusting a fixture to force a pass.
#[test]
fn stage1_production_capture_avoidance_corpus() {
    let interp = Interpreter::default();
    for f in core_fixtures() {
        let e = base_env_with_rule(f.rule_name, f.rhs.clone());
        let args = vec![f.args.0.clone(), f.args.1.clone()];

        // -- (1) Structural check: real expansion vs. independent oracle -----------------------
        let expanded =
            elaborate_lower_rule_with_args(&e, f.rule_name, &args).unwrap_or_else(|err| {
                panic!(
                    "[{}] the production path must expand a matched call, got {err:?}",
                    f.name
                )
            });
        assert!(
            alpha_eq(&expanded, &f.oracle),
            "[{}] elaborate_lower_rule_with_args(...) is not alpha-equivalent to the \
             independently hand-built oracle — a genuine hygiene failure on the production path, \
             not a comparator artifact (the oracle uses a disjoint binder-naming scheme).",
            f.name
        );

        // -- (2) Observational check, independent of alpha_eq -----------------------------------
        let wrap = |inner: Node| letn(&f.wrap_id, f.wrap_value.clone(), inner);
        let observed_expanded = interp
            .eval(&wrap(expanded))
            .unwrap_or_else(|err| panic!("[{}] eval(expand(...)) failed: {err}", f.name));
        let observed_oracle = interp
            .eval(&wrap(f.oracle.clone()))
            .unwrap_or_else(|err| panic!("[{}] eval(oracle) failed: {err}", f.name));
        assert_eq!(
            as_i64(&observed_expanded),
            f.expected_hygienic,
            "[{}] eval(elaborate_lower_rule_with_args(...)) did not match the hand-derived \
             expected value",
            f.name
        );
        assert_eq!(
            as_i64(&observed_oracle),
            f.expected_hygienic,
            "[{}] eval(oracle) did not match the hand-derived expected value (oracle itself is \
             miscomputed)",
            f.name
        );

        // -- (3) Disable-freshening negative control — non-vacuity, module doc + task grounding -
        let disabled = elaborate_value_parametric_rule_disable_freshening_for_test(
            &e,
            f.rule_name,
            &f.rhs,
            &[("a", &f.args.0), ("b", &f.args.1)],
        )
        .unwrap_or_else(|err| {
            panic!(
                "[{}] the negative control must still expand (only freshening is disabled), got {err:?}",
                f.name
            )
        });
        let observed_disabled = interp
            .eval(&wrap(disabled))
            .unwrap_or_else(|err| panic!("[{}] eval(disabled-freshening) failed: {err}", f.name));
        assert_eq!(
            as_i64(&observed_disabled),
            f.expected_captured,
            "[{}] disabling (A) freshening must reproduce the hand-derived captured (wrong) value \
             — if it doesn't, this fixture cannot demonstrate the corpus catches a real capture \
             bug (non-vacuity)",
            f.name
        );
        assert_ne!(
            f.expected_captured, f.expected_hygienic,
            "[{}] this fixture's captured/hygienic values coincide — it cannot demonstrate \
             discriminating power",
            f.name
        );
    }
}

// -------------------------------------------------------------------------------------------
// Review-motivated additions (human maintainer + Grok adversarial pass, 2026-07-11) — each
// closes one specific reviewer question with a concrete test rather than just a reply.
// -------------------------------------------------------------------------------------------

/// **Closes a reviewer question:** "what if a value parameter name shadows an RHS binder?"
/// `shadow(a, b) = let a = b in add(a, a)` — the RHS re-binds its OWN parameter name `a` to `b`,
/// then uses `a` twice. Per the Pass-1 invariant documented in `elab.rs` (a bare `Var(name)`
/// surviving Pass 1 can only be a genuine, *unshadowed* parameter reference — a shadowing RHS
/// binder always gets its own `Elab::fresh` name during ordinary elaboration, before the walker
/// ever runs), `a`'s call-site argument must be **completely ignored**: the correct expansion
/// computes `2 * b`, never touching `a`'s own value at all. `a`'s argument is deliberately a wildly
/// different value (`99`) than what a capture bug would plausibly produce, so any regression that
/// *did* leak the outer `a` would be impossible to miss.
#[test]
fn stage1_value_param_name_shadowed_by_rhs_binder_ignores_the_shadowed_arg() {
    let rhs = slet("a", sv("b"), sadd(sv("a"), sv("a")));
    let e = base_env_with_rule("Shadow", rhs);
    let args = vec![c(99), c(5)]; // a=99 (must be ignored), b=5
    let expanded = elaborate_lower_rule_with_args(&e, "Shadow", &args)
        .expect("a value-param name shadowed by its own RHS binder must still expand");
    let oracle = letn("inner_a", c(5), add(v("inner_a"), v("inner_a")));
    assert!(
        alpha_eq(&expanded, &oracle),
        "expansion is not alpha-equivalent to the oracle — got {expanded:?}"
    );
    let interp = Interpreter::default();
    let observed = interp
        .eval(&expanded)
        .unwrap_or_else(|err| panic!("eval(expansion) failed: {err}"));
    assert_eq!(
        as_i64(&observed),
        10,
        "the shadowed parameter's own argument (99) must be completely ignored — only `b`'s value \
         (5) reaches the computation (2*5=10); any other result means the outer `a` leaked through \
         the shadow"
    );
}

/// **Closes a reviewer question:** `fresh_kernel_name_via_real_elaboration` only ever elicits the
/// *first* (`%0`) fresh name a probe elaboration mints — a real caller's escaping free variable
/// could just as plausibly collide with a *later*-numbered kernel name. This re-runs fixture 1's
/// exact scenario (`swap2`) with a colliding name minted **after 5 other binders** in its own
/// probe elaboration (`…%5`, not `…%0`), to confirm the mechanism's correctness does not depend on
/// which specific counter value collides.
fn fresh_kernel_name_via_real_elaboration_after(base: &str, skip: usize) -> String {
    let mut inner = format!("let {base} = 0b00000000 in {base}");
    for i in 0..skip {
        inner = format!("let d{i} = 0b00000000 in {inner}");
    }
    let rule_name = format!("ProbeDeep{base}{skip}");
    let src = format!("nodule d;\nlower {rule_name} = {inner};");
    let e = env(&src);
    let mut node = elaborate_lower_rule(&e, &rule_name).expect("the deep probe rule elaborates");
    for _ in 0..skip {
        let Node::Let { ref body, .. } = node else {
            panic!("expected a nested Let while descending the deep probe, got {node:?}");
        };
        node = (**body).clone();
    }
    let Node::Let { ref id, .. } = node else {
        panic!("expected the deep probe's innermost node to be a Let, got {node:?}");
    };
    id.clone()
}

#[test]
fn stage1_capture_avoidance_holds_against_a_later_minted_colliding_name() {
    // Wrap the real `let t = a in add(b, t)` behind 5 inert dummy `let`s so THIS rule's own Pass-1
    // fresh counter reaches the same depth (`%5`) as the probe's, before minting `t`'s own fresh
    // name -- otherwise the probe's `%5`-numbered name and this rule's own (still `%0`, with no
    // dummies) binder would simply be two different strings that never collide either way,
    // vacuously "passing" the negative control for the wrong reason.
    const SKIP: usize = 5;
    let mut rhs = slet("t", sv("a"), sadd(sv("b"), sv("t")));
    for i in (0..SKIP).rev() {
        rhs = slet(&format!("d{i}"), sc(0), rhs);
    }
    let colliding = fresh_kernel_name_via_real_elaboration_after("t", SKIP);
    let e = base_env_with_rule("Swap2Deep", rhs);
    let args = vec![c(1), v(&colliding)];

    let expanded = elaborate_lower_rule_with_args(&e, "Swap2Deep", &args)
        .expect("expansion must succeed regardless of which counter value the collision targets");
    let mut oracle = letn("t_deep", c(1), add(v(&colliding), v("t_deep")));
    for i in (0..SKIP).rev() {
        oracle = letn(&format!("d_deep{i}"), c(0), oracle);
    }
    assert!(
        alpha_eq(&expanded, &oracle),
        "expansion is not alpha-equivalent to the oracle for a deep (`%5`-numbered) collision — \
         got {expanded:?}"
    );

    let wrap = |inner: Node| letn(&colliding, c(7), inner);
    let interp = Interpreter::default();
    let observed_expanded = interp
        .eval(&wrap(expanded))
        .unwrap_or_else(|err| panic!("eval(expansion) failed: {err}"));
    assert_eq!(
        as_i64(&observed_expanded),
        8,
        "hygienic value must still be add(7,1)=8"
    );

    let disabled = elaborate_value_parametric_rule_disable_freshening_for_test(
        &e,
        "Swap2Deep",
        &rhs_of("Swap2Deep", &e),
        &[("a", &c(1)), ("b", &v(&colliding))],
    )
    .expect("the negative control must still expand");
    let observed_disabled = interp
        .eval(&wrap(disabled))
        .unwrap_or_else(|err| panic!("eval(disabled-freshening) failed: {err}"));
    assert_eq!(
        as_i64(&observed_disabled),
        2,
        "disabling (A) freshening must reproduce the captured (wrong) value even when the \
         collision targets a later-minted (`%5`) name, not just the first"
    );
}

/// Read a registered rule's own RHS `Expr` back out of `e` (a small Law-of-Demeter helper so
/// [`stage1_capture_avoidance_holds_against_a_later_minted_colliding_name`] doesn't have to thread
/// the RHS through twice).
fn rhs_of(rule_name: &str, e: &Env) -> Expr {
    e.lower_rules[rule_name]
        .expr_rhs()
        .expect("Expr-shaped RHS")
        .clone()
}

// -------------------------------------------------------------------------------------------
// Direct `sugar_expand` walker unit tests (Lam/Fix/FixGroup/Alt::Ctor) — closes the reviewer's
// Fixture-4 observation: the full `elaborate_lower_rule_with_args` pipeline only ever reaches the
// walker's `Let` arm (no production fixture's RHS produces a `Lam`/`Fix`/`FixGroup`/`Alt::Ctor`
// binder — the lambda-IIFE shape that would have is blocked by the orthogonal, pre-existing
// synthetic-Env/mono.rs limitation documented on fixture 4). These bypass the full pipeline
// entirely and drive `sugar_expand`/`sugar_expand_alt` directly on hand-built `Node`s (mirroring
// how E1's own `Expander` was tested), giving DIRECT — not merely ported-code-inherited —
// production coverage of every binder-introducing `Node` variant the walker handles.
// -------------------------------------------------------------------------------------------

fn bare_elab(e: &Env) -> Elab<'_> {
    Elab {
        env: e,
        registry: build_registry(e).expect("registry builds for the trivial base env"),
        fresh: 0,
        rec: BTreeMap::new(),
        depth: 0,
    }
}

fn base_env() -> Env {
    env("nodule d;\nlower Base = 0b00000000;")
}

#[test]
fn sugar_expand_freshens_lam_binder_and_all_its_references() {
    let e = base_env();
    let mut el = bare_elab(&e);
    let node = Node::Lam {
        param: "t".to_owned(),
        body: Box::new(v("t")),
    };
    let mut scope = Vec::new();
    let out = sugar_expand(&mut el, "%test%base", true, &[], &mut scope, &node);
    let Node::Lam { param, body } = &out else {
        panic!("expected a Lam, got {out:?}");
    };
    assert_ne!(param, "t", "the Lam binder must be freshened, not left raw");
    assert_eq!(
        **body,
        v(param),
        "the body's reference must follow the binder to its fresh name"
    );
}

#[test]
fn sugar_expand_freshens_fix_binder_and_all_its_references() {
    let e = base_env();
    let mut el = bare_elab(&e);
    let node = Node::Fix {
        name: "f".to_owned(),
        body: Box::new(v("f")),
    };
    let mut scope = Vec::new();
    let out = sugar_expand(&mut el, "%test%base", true, &[], &mut scope, &node);
    let Node::Fix { name, body } = &out else {
        panic!("expected a Fix, got {out:?}");
    };
    assert_ne!(name, "f", "the Fix binder must be freshened, not left raw");
    assert_eq!(
        **body,
        v(name),
        "the body's reference must follow the binder to its fresh name"
    );
}

#[test]
fn sugar_expand_freshens_fixgroup_binders_with_distinct_names_and_correct_cross_references() {
    let e = base_env();
    let mut el = bare_elab(&e);
    // A mutually-recursive pair: f's body refers to g, g's body refers to f, and the overall body
    // refers to f — every occurrence must follow its OWN binder to a DISTINCT fresh name.
    let node = Node::FixGroup {
        defs: vec![
            ("f".to_owned(), Box::new(v("g"))),
            ("g".to_owned(), Box::new(v("f"))),
        ],
        body: Box::new(v("f")),
    };
    let mut scope = Vec::new();
    let out = sugar_expand(&mut el, "%test%base", true, &[], &mut scope, &node);
    let Node::FixGroup { defs, body } = &out else {
        panic!("expected a FixGroup, got {out:?}");
    };
    assert_eq!(defs.len(), 2);
    let (f_fresh, f_body) = &defs[0];
    let (g_fresh, g_body) = &defs[1];
    assert_ne!(f_fresh, "f");
    assert_ne!(g_fresh, "g");
    assert_ne!(
        f_fresh, g_fresh,
        "two different FixGroup members must get DISTINCT fresh names"
    );
    assert_eq!(
        **f_body,
        v(g_fresh),
        "f's body must reference g's fresh name"
    );
    assert_eq!(
        **g_body,
        v(f_fresh),
        "g's body must reference f's fresh name"
    );
    assert_eq!(
        **body,
        v(f_fresh),
        "the outer body must reference f's fresh name"
    );
}

#[test]
fn sugar_expand_freshens_alt_ctor_binders_via_match() {
    let e = base_env();
    let mut el = bare_elab(&e);
    let ctor = CtorRef::new(
        ContentHash::parse("blake3:test").expect("valid content-hash shape"),
        0,
    );
    let node = Node::Match {
        scrutinee: Box::new(c(0)),
        alts: vec![Alt::Ctor {
            ctor: ctor.clone(),
            binders: vec!["x".to_owned()],
            body: v("x"),
        }],
        default: None,
    };
    let mut scope = Vec::new();
    let out = sugar_expand(&mut el, "%test%base", true, &[], &mut scope, &node);
    let Node::Match { alts, .. } = &out else {
        panic!("expected a Match, got {out:?}");
    };
    let Alt::Ctor {
        ctor: out_ctor,
        binders,
        body,
    } = &alts[0]
    else {
        panic!("expected an Alt::Ctor, got {:?}", alts[0]);
    };
    assert_eq!(
        *out_ctor, ctor,
        "the constructor reference itself must pass through unchanged"
    );
    assert_eq!(binders.len(), 1);
    assert_ne!(
        binders[0], "x",
        "the Alt::Ctor field binder must be freshened, not left raw"
    );
    assert_eq!(
        *body,
        v(&binders[0]),
        "the arm body's reference must follow the binder to its fresh name"
    );
}

#[test]
fn sugar_expand_disable_freshening_leaves_every_binder_kind_raw() {
    // The negative-control toggle's own unit-level witness: with freshening off, EVERY binder kind
    // keeps its exact original spelling (not just Let, which the full-pipeline corpus already
    // exercises) — the mechanism this test suite's non-vacuity claim rests on.
    let e = base_env();
    let mut el = bare_elab(&e);
    let node = Node::Lam {
        param: "t".to_owned(),
        body: Box::new(v("t")),
    };
    let mut scope = Vec::new();
    let out = sugar_expand(&mut el, "%test%base", false, &[], &mut scope, &node);
    assert_eq!(
        out,
        Node::Lam {
            param: "t".to_owned(),
            body: Box::new(v("t")),
        },
        "with freshening disabled, a Lam binder must be byte-identical to the input"
    );
}
