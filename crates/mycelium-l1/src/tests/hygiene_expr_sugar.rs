//! **E1 — capture-avoidance experiment** (M-1055; DN-110-8.2-hygiene-deepdive §4/§7).
//!
//! This module is the *go/no-go* prototype the deep-dive's §7 experiment plan calls for — it
//! validates DN-110 §8.2's hygiene model **(A) `%`-freshening of every RHS binder** and
//! **(B) capture-safe verbatim substitution of use-site arguments**, on a real `mycelium_core::Node`
//! corpus, checked two independent ways (structural [`alpha_eq`] + observational [`eval`]).
//!
//! # Test-only — NOT the M-1054 facility
//!
//! [`expand`] below is a **throwaway experiment prototype**, not a candidate implementation for the
//! Accepted-not-Enacted M-1054 sugar-lowering facility. It does not touch
//! [`crate::elab::elaborate_lower_rule`] or any other elaborator surface — extending that function to
//! take value arguments would *be* building M-1054 early, which this experiment must precede, not
//! anticipate (per the task grounding). `expand` lives only in `src/tests/`.
//!
//! # The non-vacuity discipline (the whole point of this module)
//!
//! A prior naive round-trip check (`reveal.rs`'s corpus test, see its own module doc) was
//! **vacuous**: it compared a term to a clone of itself (`reelaborate` returns `shown.clone()` on
//! the success path), so a broken [`alpha_eq`] could not have been caught. **E1 is built to avoid
//! that failure mode by construction:**
//!
//! 1. The **oracle** for every fixture is built by a **different code path** than [`expand`] — direct,
//!    literal [`Node`] tree construction (see the `oracle_*` fixture fields below), using **binder
//!    spellings [`expand`]'s gensym scheme never produces** (`t_h1`/`oracle_lam_t`/… vs `expand`'s
//!    `t%0`/`t%1`/…). [`alpha_eq`] must therefore do genuine alpha-comparison work — a `true`-always or
//!    `false`-always comparator would fail this immediately (never match a *different* spelling, or
//!    never match at all).
//! 2. Every fixture is **also** checked observationally: [`expand`]'s output and the oracle are each
//!    wrapped in the fixture's real use-site `let` and run through [`mycelium_interp::Interpreter`].
//!    This assertion **does not go through [`alpha_eq`] at all** — a broken comparator cannot fake it.
//! 3. Every fixture additionally carries a **hand-built, deliberately unhygienic ("captured") expansion**
//!    — the literal RHS-binder-spelling reuse a naive (non-freshening) elaborator would produce — with
//!    its own independently hand-derived expected value. Asserting `expected_captured != expected_hygienic`
//!    (and that `eval` actually produces `expected_captured` on that node) demonstrates the harness can
//!    *observe* a real capture bug, not merely fail to detect one it never triggers.
//!
//! # Scope honesty (VR-5 — do not read more into a PASS than this)
//!
//! E1 validates deep-dive §4 **(A) freshening + (B) capture-safe substitution ONLY**. A PASS moves
//! capture-avoidance for (A)+(B) `Declared → Empirical`; it says **nothing** about (C) def-site
//! resolution (E2, unbuilt) or (D) affine-on-expanded-L0 (E5, unbuilt), which stay `Declared`. E3
//! (`reveal` round-trip fidelity) is **out of scope here and deliberately not built** — deep-dive §7
//! notes it cannot be non-vacuous at v0 (`reveal_l0` has no lossy step to invert, so
//! `reelaborate(reveal_l0(x))` is definitionally `x.clone()` — see `reveal.rs`'s own "honest scoping"
//! callout). Nesting (E4) is exercised only as an optional, non-gating bonus fixture (see
//! `nested_expansion_bonus_e4`), not part of the E1 go/no-go verdict.
//!
//! # Guarantee tag
//!
//! The [`expand`] prototype's capture-avoidance property, over this fixture corpus: **`Empirical`**
//! (checked by the table below, not proven) — and only for (A)+(B), never upgraded past that (VR-5).

use crate::reveal::alpha_eq;
use mycelium_core::{Meta, Node, Payload, Provenance, Repr, Value};
use mycelium_interp::Interpreter;

// -------------------------------------------------------------------------------------------
// Test-only Node builders (terse constructors — no production surface, this file only)
// -------------------------------------------------------------------------------------------

const WIDTH: u32 = 8;

/// An 8-bit two's-complement `Binary` constant — wide enough for every value this corpus computes
/// (max magnitude 103, well under `i8`'s ±127 range).
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

fn lam(param: &str, body: Node) -> Node {
    Node::Lam {
        param: param.to_owned(),
        body: Box::new(body),
    }
}

fn app(func: Node, arg: Node) -> Node {
    Node::App {
        func: Box::new(func),
        arg: Box::new(arg),
    }
}

/// Decode an evaluated `Binary{8}` result back to `i64` (the corpus's own inverse of [`c`]).
fn as_i64(result: &Value) -> i64 {
    match result.payload() {
        Payload::Bits(bits) => mycelium_core::binary::bits_to_int(bits),
        other => panic!("expected a Binary payload, got {other:?}"),
    }
}

// -------------------------------------------------------------------------------------------
// `expand` — the test-only (A)+(B) hygiene prototype (DN-110-8.2-hygiene-deepdive §4)
// -------------------------------------------------------------------------------------------

/// Expand a sugar RHS `rhs` (parameterized over `params`) against use-site `args`, applying
/// **(A)** `%`-freshening of every binder `rhs` introduces and **(B)** capture-safe verbatim
/// substitution of `args` for `Var(params[i])` — mirroring `Elab::fresh`'s `base%n` discipline
/// (`crates/mycelium-l1/src/elab.rs:1095`) with a standalone monotonic counter local to this
/// expansion call. `%` is surface-illegal (the surface lexer never accepts it inside an
/// identifier — `lexer.rs`), so a `%`-freshened name can never equal (and so never capture) a
/// use-site binder or free variable — the same guarantee `Elab::fresh` already gives the real
/// elaborator, reused here rather than reimplemented (deep-dive §6's "true half").
///
/// Test-only prototype (module doc) — not [`crate::elab::elaborate_lower_rule`], and not extended
/// to take value arguments (that would be M-1054 itself).
fn expand(rhs: &Node, params: &[String], args: &[Node]) -> Node {
    let mut ex = Expander {
        params,
        args,
        scope: Vec::new(),
        counter: 0,
    };
    ex.go(rhs)
}

/// The single-pass walker behind [`expand`]: a scope stack of `(original_spelling, fresh_name)`
/// pairs realizes (A), and a param→arg lookup realizes (B) — both handled in the same walk so a
/// binder that happens to shadow a parameter's name (the `nested_binder_in_rhs` fixture) is
/// resolved with ordinary innermost-shadowing scoping, exactly as a real evaluator would.
struct Expander<'a> {
    params: &'a [String],
    args: &'a [Node],
    /// `(rhs-original spelling, %-freshened spelling)`, innermost-last (shadowing via `rposition`/
    /// reverse search — mirrors [`crate::reveal::alpha_eq`]'s own `binder_index` convention, DRY).
    scope: Vec<(String, String)>,
    /// Monotonic, per-expansion-site — mirrors `Elab::fresh`'s single incrementing counter.
    counter: u32,
}

impl Expander<'_> {
    fn fresh(&mut self, base: &str) -> String {
        let n = self.counter;
        self.counter += 1;
        format!("{base}%{n}")
    }

    fn scoped(&self, name: &str) -> Option<&str> {
        self.scope
            .iter()
            .rev()
            .find(|(orig, _)| orig == name)
            .map(|(_, fresh)| fresh.as_str())
    }

    fn param_arg(&self, name: &str) -> Option<&Node> {
        self.params
            .iter()
            .position(|p| p == name)
            .map(|i| &self.args[i])
    }

    fn go(&mut self, node: &Node) -> Node {
        match node {
            Node::Const(val) => Node::Const(val.clone()),
            Node::Var(id) => {
                if let Some(fresh) = self.scoped(id) {
                    // (A): a reference to an RHS-local binder — follow it to its fresh name.
                    Node::Var(fresh.to_owned())
                } else if let Some(arg) = self.param_arg(id) {
                    // (B): a reference to a sugar parameter — splice the use-site argument
                    // verbatim (capture-safe by (A)'s namespace disjointness — no on-the-fly
                    // renaming needed, deep-dive §4(B)).
                    arg.clone()
                } else {
                    // A genuinely free RHS identifier (out of E1's scope — that's E2/(C)); left
                    // as-is rather than silently guessed at.
                    Node::Var(id.clone())
                }
            }
            Node::Let { id, bound, body } => {
                let bound2 = self.go(bound);
                let fresh = self.fresh(id);
                self.scope.push((id.clone(), fresh.clone()));
                let body2 = self.go(body);
                self.scope.pop();
                Node::Let {
                    id: fresh,
                    bound: Box::new(bound2),
                    body: Box::new(body2),
                }
            }
            Node::Op { prim, args } => Node::Op {
                prim: prim.clone(),
                args: args.iter().map(|a| self.go(a)).collect(),
            },
            Node::Swap {
                src,
                target,
                policy,
            } => Node::Swap {
                src: Box::new(self.go(src)),
                target: target.clone(),
                policy: policy.clone(),
            },
            Node::Construct { ctor, args } => Node::Construct {
                ctor: ctor.clone(),
                args: args.iter().map(|a| self.go(a)).collect(),
            },
            Node::Match {
                scrutinee,
                alts,
                default,
            } => Node::Match {
                scrutinee: Box::new(self.go(scrutinee)),
                alts: alts.iter().map(|a| self.go_alt(a)).collect(),
                default: default.as_ref().map(|d| Box::new(self.go(d))),
            },
            Node::Lam { param, body } => {
                let fresh = self.fresh(param);
                self.scope.push((param.clone(), fresh.clone()));
                let body2 = self.go(body);
                self.scope.pop();
                Node::Lam {
                    param: fresh,
                    body: Box::new(body2),
                }
            }
            Node::App { func, arg } => Node::App {
                func: Box::new(self.go(func)),
                arg: Box::new(self.go(arg)),
            },
            Node::Fix { name, body } => {
                let fresh = self.fresh(name);
                self.scope.push((name.clone(), fresh.clone()));
                let body2 = self.go(body);
                self.scope.pop();
                Node::Fix {
                    name: fresh,
                    body: Box::new(body2),
                }
            }
            Node::FixGroup { defs, body } => {
                let fresh_names: Vec<String> =
                    defs.iter().map(|(name, _)| self.fresh(name)).collect();
                for (orig, fresh) in defs.iter().map(|(n, _)| n).zip(fresh_names.iter()) {
                    self.scope.push((orig.clone(), fresh.clone()));
                }
                let defs2: Vec<(String, Box<Node>)> = defs
                    .iter()
                    .zip(fresh_names.iter())
                    .map(|((_, d), fresh)| (fresh.clone(), Box::new(self.go(d))))
                    .collect();
                let body2 = self.go(body);
                for _ in defs {
                    self.scope.pop();
                }
                Node::FixGroup {
                    defs: defs2,
                    body: Box::new(body2),
                }
            }
        }
    }

    fn go_alt(&mut self, alt: &mycelium_core::Alt) -> mycelium_core::Alt {
        use mycelium_core::Alt;
        match alt {
            Alt::Ctor {
                ctor,
                binders,
                body,
            } => {
                let fresh_names: Vec<String> = binders.iter().map(|b| self.fresh(b)).collect();
                for (orig, fresh) in binders.iter().zip(fresh_names.iter()) {
                    self.scope.push((orig.clone(), fresh.clone()));
                }
                let body2 = self.go(body);
                for _ in binders {
                    self.scope.pop();
                }
                Alt::Ctor {
                    ctor: ctor.clone(),
                    binders: fresh_names,
                    body: body2,
                }
            }
            Alt::Lit { value, body } => Alt::Lit {
                value: value.clone(),
                body: self.go(body),
            },
        }
    }
}

// -------------------------------------------------------------------------------------------
// The E1 fixture corpus (core-E1, capture-relevant; table-driven per the repo convention)
// -------------------------------------------------------------------------------------------

/// One E1 fixture: a sugar `rhs` over `params`, a use-site `args` + `wrap` (the enclosing use-site
/// `let`), an independently hand-built `oracle` (different binder spellings than [`expand`] would
/// ever produce — the non-vacuity discipline, module doc point 1), and a hand-built `captured`
/// (deliberately unhygienic) expansion demonstrating the harness's discriminating power (module doc
/// point 3). `expected_hygienic`/`expected_captured` are hand-derived from the interpreter's own
/// substitution semantics (`mycelium-interp/src/lib.rs`'s `subst`/`step`) — not guessed, and
/// cross-checked by `eval` at test time.
struct Fixture {
    name: &'static str,
    rhs: Node,
    params: Vec<String>,
    args: Vec<Node>,
    /// Wraps an inner (expanded/oracle/captured) node in the fixture's real use-site `let`.
    wrap: fn(Node) -> Node,
    oracle: Node,
    captured: Node,
    expected_hygienic: i64,
    expected_captured: i64,
}

/// **Fixture 1 — binder-shadows-use-site (the swap2 classic, DN-110-8.2-hygiene-deepdive §7 E1).**
/// `swap2(a, b) = let t = a in add(b, t)`, invoked at `let t = 7 in swap2(1, t)` — `b` is literally
/// the use-site `Var("t")`. Hygienic: the RHS `t` is freshened, so `b`'s `7` survives:
/// `add(7, 1) = 8`. Captured (bug): reusing the RHS's raw `t` shadows the use-site `t`, so both
/// operands read the *inner* `1`: `add(1, 1) = 2`.
fn fixture_binder_shadows_use_site() -> Fixture {
    let rhs = letn("t", v("a"), add(v("b"), v("t")));
    let oracle = letn("t_h1", c(1), add(v("t"), v("t_h1")));
    let captured = letn("t", c(1), add(v("t"), v("t")));
    Fixture {
        name: "binder_shadows_use_site (swap2 classic)",
        rhs,
        params: vec!["a".to_owned(), "b".to_owned()],
        args: vec![c(1), v("t")],
        wrap: |inner| letn("t", c(7), inner),
        oracle,
        captured,
        expected_hygienic: 8,
        expected_captured: 2,
    }
}

/// **Fixture 2 — arg mentions the RHS's raw binder spelling, from the OTHER parameter position.**
/// `pair_add(a, b) = let t = b in add(a, t)`, invoked at `let t = 3 in pair_add(t, 9)` — this time
/// it's `a` (not `b`) that is the use-site `Var("t")`, and it sits in the `add`'s first operand
/// while the RHS's own `t` binds `b`. Hygienic: `add(3, 9) = 12`. Captured (bug): the unfreshened
/// `let t = 9 in …` shadows the use-site `t`, so `a`'s reference is hijacked: `add(9, 9) = 18`.
fn fixture_arg_mentions_raw_binder_spelling() -> Fixture {
    let rhs = letn("t", v("b"), add(v("a"), v("t")));
    let oracle = letn("t_h2", c(9), add(v("t"), v("t_h2")));
    let captured = letn("t", c(9), add(v("t"), v("t")));
    Fixture {
        name: "arg_mentions_raw_binder_spelling (pair_add)",
        rhs,
        params: vec!["a".to_owned(), "b".to_owned()],
        args: vec![v("t"), c(9)],
        wrap: |inner| letn("t", c(3), inner),
        oracle,
        captured,
        expected_hygienic: 12,
        expected_captured: 18,
    }
}

/// **Fixture 3 — multi-param, RHS binder used twice.** `f(a, b) = let t = a in add(b, add(t, t))`,
/// invoked at `let t = 2 in f(5, t)`. Exercises that a single fresh name is threaded consistently
/// to *every* occurrence of the RHS binder it replaces, while `b`'s use-site `t` stays free.
/// Hygienic: `add(2, add(5, 5)) = 12`. Captured (bug): `let t = 5 in …` shadows, so `b`'s reference
/// reads the inner `5` too: `add(5, add(5, 5)) = 15`.
fn fixture_multi_param_used_twice() -> Fixture {
    let rhs = letn("t", v("a"), add(v("b"), add(v("t"), v("t"))));
    let oracle = letn("t_h3", c(5), add(v("t"), add(v("t_h3"), v("t_h3"))));
    let captured = letn("t", c(5), add(v("t"), add(v("t"), v("t"))));
    Fixture {
        name: "multi_param_used_twice (f)",
        rhs,
        params: vec!["a".to_owned(), "b".to_owned()],
        args: vec![c(5), v("t")],
        wrap: |inner| letn("t", c(2), inner),
        oracle,
        captured,
        expected_hygienic: 12,
        expected_captured: 15,
    }
}

/// **Fixture 4 — nested binder in the RHS (a `let` *and* a `lambda` both spelled `t`).**
/// `nest(a, b) = let t = a in add((lambda(t) => add(t, 1))(b), t)`, invoked at
/// `let t = 100 in nest(2, t)`. Exercises that (A) freshens **every** binder independently — the
/// outer `let`'s `t` and the inner `lambda`'s `t` get *distinct* fresh names — and that ordinary
/// innermost-shadowing scoping still resolves each `Var("t")` occurrence to the right one.
/// Hygienic: `(lambda(x) => x+1)(100) = 101`, then `add(101, 2) = 103`. Captured (bug): both
/// binders keep the raw spelling `t`; the use-site `t` argument gets hijacked by the *inner*
/// `let t = 2`, so the lambda is applied to `2` (not the true use-site `100`): `(t=>t+1)(2) = 3`,
/// then `add(3, 2) = 5` — a dramatically different, wrong result.
fn fixture_nested_binder_in_rhs() -> Fixture {
    let rhs = letn(
        "t",
        v("a"),
        add(app(lam("t", add(v("t"), c(1))), v("b")), v("t")),
    );
    let oracle = letn(
        "oracle_let_t",
        c(2),
        add(
            app(lam("oracle_lam_t", add(v("oracle_lam_t"), c(1))), v("t")),
            v("oracle_let_t"),
        ),
    );
    let captured = letn(
        "t",
        c(2),
        add(app(lam("t", add(v("t"), c(1))), v("t")), v("t")),
    );
    Fixture {
        name: "nested_binder_in_rhs (nest — let + lambda both spelled t)",
        rhs,
        params: vec!["a".to_owned(), "b".to_owned()],
        args: vec![c(2), v("t")],
        wrap: |inner| letn("t", c(100), inner),
        oracle,
        captured,
        expected_hygienic: 103,
        expected_captured: 5,
    }
}

fn core_e1_fixtures() -> Vec<Fixture> {
    vec![
        fixture_binder_shadows_use_site(),
        fixture_arg_mentions_raw_binder_spelling(),
        fixture_multi_param_used_twice(),
        fixture_nested_binder_in_rhs(),
    ]
}

// -------------------------------------------------------------------------------------------
// The E1 assertion: dual (structural + observational), over the whole corpus
// -------------------------------------------------------------------------------------------

/// **E1 — capture-avoidance, dual-checked (module doc point 1+2).** For every fixture:
/// `alpha_eq(expand(rhs, params, args), oracle)` **and** `eval(wrap(expand(...))) ==
/// eval(wrap(oracle))` — the second check does not depend on [`alpha_eq`] at all. A failure here is
/// a genuine capture bug (house rule #2/VR-5): it must be reported honestly, never patched away by
/// adjusting the fixture to force a pass.
#[test]
fn e1_capture_avoidance_corpus() {
    let interp = Interpreter::default();
    for f in core_e1_fixtures() {
        let expanded = expand(&f.rhs, &f.params, &f.args);

        // -- Structural check --------------------------------------------------------------
        assert!(
            alpha_eq(&expanded, &f.oracle),
            "[{}] expand(...) is not alpha-equivalent to the independently hand-built oracle \
             — this is a genuine hygiene failure, not a comparator artifact (the oracle uses a \
             disjoint binder-naming scheme from expand's %-gensym).",
            f.name
        );

        // -- Observational check (independent of alpha_eq) ----------------------------------
        let full_expanded = (f.wrap)(expanded);
        let full_oracle = (f.wrap)(f.oracle.clone());
        let observed_expanded = interp
            .eval(&full_expanded)
            .unwrap_or_else(|e| panic!("[{}] eval(expand(...)) failed: {e}", f.name));
        let observed_oracle = interp
            .eval(&full_oracle)
            .unwrap_or_else(|e| panic!("[{}] eval(oracle) failed: {e}", f.name));
        assert_eq!(
            as_i64(&observed_expanded),
            f.expected_hygienic,
            "[{}] eval(expand(...)) did not match the hand-derived expected value",
            f.name
        );
        assert_eq!(
            as_i64(&observed_oracle),
            f.expected_hygienic,
            "[{}] eval(oracle) did not match the hand-derived expected value (oracle itself is \
             miscomputed)",
            f.name
        );

        // -- Discriminating-power demonstration (module doc point 3) ------------------------
        let full_captured = (f.wrap)(f.captured.clone());
        let observed_captured = interp
            .eval(&full_captured)
            .unwrap_or_else(|e| panic!("[{}] eval(captured) failed: {e}", f.name));
        assert_eq!(
            as_i64(&observed_captured),
            f.expected_captured,
            "[{}] eval(captured) did not match the hand-derived captured-bug value",
            f.name
        );
        assert_ne!(
            f.expected_captured, f.expected_hygienic,
            "[{}] this fixture's captured/hygienic values coincide — it cannot demonstrate \
             discriminating power (not a capture-bait fixture in practice)",
            f.name
        );
    }
}

// -------------------------------------------------------------------------------------------
// Optional bonus — E4 (nested/recursive expansion), non-gating per the task grounding
// -------------------------------------------------------------------------------------------

/// **Bonus, non-gating (E4 sketch — deep-dive §7).** A two-layer nested expansion: `expand` is run
/// once, and its *output* is fed back through `expand` a second time (standing in for a second sugar
/// rule expanding at a site inside the first's expansion), checking that the two expansions' fresh
/// names never collide (the corpus's own `Expander` uses one counter per `expand` call, so a second
/// call starts back at `%0` — this bonus fixture exists to make that fact explicit and checked, not
/// to validate DN-54 §4.2 acyclicity in full, which is out of scope for a bonus fixture). This does
/// **not** gate the E1 verdict (task grounding: "don't gate on it") — its assertion is a plain
/// alpha_eq/eval check, kept separate from `e1_capture_avoidance_corpus`'s go/no-go loop.
#[test]
fn nested_expansion_bonus_e4() {
    // Outer sugar: outer(x) = let t = x in t  (identity through a freshened let).
    let outer_rhs = letn("t", v("x"), v("t"));
    // Use site: outer(swap2_use), where swap2_use is fixture 1's already-expanded term wrapped in
    // its own use-site let — i.e. we expand fixture 1, then expand *that* as the argument to a
    // second, independent sugar. Two sugar rules ⇒ two independent Expander instances ⇒ each
    // restarts its own %-counter at 0, so this checks the two expansions' fresh names are
    // reconciled correctly when nested (no accidental identity collision breaks alpha_eq).
    let f1 = fixture_binder_shadows_use_site();
    let inner_expanded = expand(&f1.rhs, &f1.params, &f1.args);
    let full_inner = (f1.wrap)(inner_expanded);

    let outer_expanded = expand(
        &outer_rhs,
        &["x".to_owned()],
        std::slice::from_ref(&full_inner),
    );

    // Oracle: a hand-built two's-complement expansion using a disjoint binder name for the outer
    // layer, with the (already independently-verified) inner expansion embedded unchanged.
    let oracle = letn("t_bonus", full_inner.clone(), v("t_bonus"));

    assert!(
        alpha_eq(&outer_expanded, &oracle),
        "nested (two-layer) expansion is not alpha-equivalent to its oracle"
    );

    let interp = Interpreter::default();
    let observed = interp
        .eval(&outer_expanded)
        .expect("nested expansion evaluates");
    // The outer sugar is `let t = x in t` — pure identity — so this must equal fixture 1's own
    // hygienic value (8), unchanged by the extra nesting layer.
    assert_eq!(as_i64(&observed), f1.expected_hygienic);
}
