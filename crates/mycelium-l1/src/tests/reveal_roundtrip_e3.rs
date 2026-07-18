//! **E3 — the reveal round-trip go/no-go** (M-1051 Increment-3; M-1055; DN-110-8.2-hygiene-deepdive
//! §5/§7 E3/§10 OQ-H3). Composes [`crate::reveal::certified_roundtrip`] (and its underlying
//! [`crate::reveal::alpha_eq`]/[`crate::reveal::reelaborate`]/[`crate::reveal::render_surface`])
//! over the E1 non-vacuity recipe (`src/tests/hygiene_expr_sugar.rs`): a test-only `expand`
//! prototype, an **independently-spelled hand-built oracle**, an
//! [`mycelium_interp::Interpreter::eval`] differential that never touches `alpha_eq`, and a
//! deliberately-unhygienic ("captured") variant demonstrating the harness's discriminating power.
//!
//! # What E3 actually proves — the honest scoping (VR-5, do not read more into a PASS than this)
//!
//! **Non-vacuity comes from the independent, disjoint-spelled oracle + `eval` differential, NOT
//! from `reelaborate` inverting a lossy step.** [`crate::reveal::reelaborate`] stays exactly what
//! its own module doc says it is: a validated **clone** on the success path (v0's `reveal_l0` has
//! no lossy rendering step in between to invert). Composing `reelaborate` with `alpha_eq` over a
//! term and *itself* would be vacuous (a broken `alpha_eq` cannot fail a self-comparison either
//! way) — this module never does that. Every hygiene-interesting fixture instead compares
//! `expand`'s (freshened) output against an oracle built by a **different code path, using binder
//! spellings `expand`'s `%`-gensym scheme never produces** — so a `true`-always or `false`-always
//! `alpha_eq` fails immediately (never matches a genuinely different spelling, or never matches at
//! all), and the parallel `eval` differential does not depend on `alpha_eq` at all.
//!
//! **OQ-H3 disposition = option (1)/(a), already pinned in `reveal.rs`.** The identity witness this
//! module certifies is at the **L0-*term* level** — [`crate::reveal::alpha_eq`] over
//! [`crate::reveal::reelaborate`]'s output, composed via [`crate::reveal::certified_roundtrip`]'s
//! [`crate::reveal::L0Witness`]. The **surface** round-trip (`render_surface` → reparse →
//! re-elaborate) is a **secondary, best-effort, `%`-free-only** convenience, **declared
//! out-of-contract for `%`-names** — option (2) (a display-renaming pass that would make `%`-names
//! themselves reparseable) is **deferred**, not built here, per the deep-dive §10 ruling.
//!
//! **The genuinely surface-round-trippable fragment is narrow — independently confirmed here
//! (M-1051 Increment-3 STEP-0, empirical, see `reveal.rs`'s module doc for the full finding).**
//! Every [`mycelium_core::Node::Op`] kernel prim name is `.`/`:`-namespaced
//! (`crate::checkty::prim_kernel_name` — `bin.add`, `bit.not`, …), so [`render_surface`] routes
//! *every* `Op` through the non-reparseable `#op[…]` marker **independent of `%`-freshening** — an
//! **entirely `%`-free** arithmetic sugar expansion is *still* out-of-contract for the surface path
//! (fixture `percent_free_op_based_term_is_honestly_out_of_contract` below demonstrates this
//! directly). The surface path genuinely closes only over the narrow `Const`/`Var`/`Let`(-of-those)
//! fragment (fixture `percent_free_plain_term_surface_roundtrip_closes` below) — **`App` and
//! `Match` do NOT close this even when `%`-free and marker-free**, test-backed by
//! `app_is_honestly_reparse_failed` (`SurfaceOutcome::ReparseFailed` — nothing besides
//! `Lam`/`Fix`/`FixGroup` is callable, and those are already excluded) and
//! `match_is_honestly_alpha_mismatch` (`SurfaceOutcome::AlphaMismatch` — the elaborator injects an
//! extra scrutinee-binding `let` the original never had) below. Not over any realistic
//! hygiene-sugar expansion either, which is why every hygiene-interesting fixture in this module
//! relies on the L0-term witness, never the surface path.
//!
//! # Test-only, not the M-1054 facility
//!
//! [`expand`] below is a fresh, **self-contained** re-implementation of the E1 discipline — not a
//! cross-module import of `hygiene_expr_sugar.rs`'s `expand` (that file's `expand`/`Fixture`/oracle
//! items are module-private, and this task's edit scope is `reveal.rs` +
//! `tests/reveal_roundtrip_e3.rs` + `tests/mod.rs` only; widening `hygiene_expr_sugar.rs`'s
//! visibility is out of scope here). It is, like its E1 sibling, a **throwaway experiment
//! prototype** — not a candidate implementation for the Accepted-not-Enacted M-1054 sugar-lowering
//! facility, and it does not touch [`crate::elab::elaborate_lower_rule`] or any other elaborator
//! surface. It additionally carries a `freshen: bool` toggle E1's version does not need — the
//! **mutation self-check** below flips it to `false` to verify the harness genuinely catches a
//! disabled-freshening regression (non-vacuity at the harness level, not just the fixture level).
//!
//! # Guarantee tags (VR-5 — no upgrade past what is checked here)
//!
//! The round-trip property this module checks — `alpha_eq(reelaborate(expand(rhs, params, args)),
//! independent_oracle)` over the fixture corpus, plus the `eval` differential — is **`Empirical`**
//! (fixture-checked + mutation-self-checked), **never `Proven`**. A PASS here moves the **L0-term-
//! level** round-trip claim, scoped to the reparseable fragment, `Declared → Empirical`
//! (`reveal.rs`'s module doc records the exact scope of this upgrade). It does **not** upgrade the
//! surface `delaborate ∘ lower = id` obligation for `%`-names (stays out-of-contract/unbuilt), and
//! it does **not** by itself Enact DN-110 (M-1054's facility and full reveal-transparency remain
//! open — M-1055's E1+E3 Definition of Done is satisfied by E1 (`hygiene_expr_sugar.rs`) + this E3
//! module both being built and run, not by any single test PASSing in isolation).

use crate::reveal::{alpha_eq, certified_roundtrip, reelaborate, L0Witness, SurfaceOutcome};
use mycelium_core::{Meta, Node, Payload, Provenance, Repr, Value};
use mycelium_interp::Interpreter;

// -------------------------------------------------------------------------------------------
// Test-only Node builders (mirrors hygiene_expr_sugar.rs's own helpers — a fresh, self-contained
// instance per the module doc's edit-scope note, not a cross-module import).
// -------------------------------------------------------------------------------------------

const WIDTH: u32 = 8;

/// An 8-bit two's-complement `Binary` constant — wide enough for every value this corpus computes.
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

/// Decode an evaluated `Binary{8}` result back to `i64` (this corpus's own inverse of [`c`]).
fn as_i64(result: &Value) -> i64 {
    match result.payload() {
        Payload::Bits(bits) => mycelium_core::binary::bits_to_int(bits),
        other => panic!("expected a Binary payload, got {other:?}"),
    }
}

// -------------------------------------------------------------------------------------------
// `expand` — the test-only (A)+(B) hygiene prototype, WITH a `freshen` toggle for the E3 mutation
// self-check (DN-110-8.2-hygiene-deepdive §4; mirrors hygiene_expr_sugar.rs's own Expander).
// -------------------------------------------------------------------------------------------

/// Expand a sugar RHS `rhs` (parameterized over `params`) against use-site `args`. When `freshen`
/// is `true` (the real hygiene discipline), every binder `rhs` introduces is `%`-freshened
/// (capture-avoidance (A)) and every reference to a `params` name is substituted verbatim with its
/// `args` value (B) — mirroring `Elab::fresh`'s `base%n` discipline
/// (`crates/mycelium-l1/src/elab.rs:1095`). When `freshen` is `false`, binders keep their **raw**
/// RHS spelling — a deliberately-mutated, unhygienic variant used ONLY by the mutation self-check
/// below to verify this harness would actually catch a disabled-freshening regression (never used
/// to justify a fixture's "hygienic" expected value).
fn expand(rhs: &Node, params: &[String], args: &[Node], freshen: bool) -> Node {
    let mut ex = Expander {
        params,
        args,
        scope: Vec::new(),
        counter: 0,
        freshen,
    };
    ex.go(rhs)
}

struct Expander<'a> {
    params: &'a [String],
    args: &'a [Node],
    /// `(rhs-original spelling, replacement spelling)`, innermost-last (shadowing via `rposition`).
    scope: Vec<(String, String)>,
    counter: u32,
    freshen: bool,
}

impl Expander<'_> {
    fn fresh(&mut self, base: &str) -> String {
        if !self.freshen {
            // Mutation self-check mode: reuse the raw spelling — no gensym at all.
            return base.to_owned();
        }
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
                    Node::Var(fresh.to_owned())
                } else if let Some(arg) = self.param_arg(id) {
                    arg.clone()
                } else {
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
            other => panic!(
                "reveal_roundtrip_e3::expand: this corpus's fixtures never use {other:?} in a \
                 sugar RHS — extend Expander::go if a future fixture needs it (never silently \
                 mis-expand an unhandled form)"
            ),
        }
    }
}

// -------------------------------------------------------------------------------------------
// (a) %-free fixtures — plain (non-sugar-expanded) Node terms, no `expand` involved: do these
// genuinely close the surface round-trip when the fragment supports it, and honestly refuse when
// it doesn't (the Op dotted-prim gap, independent of %-freshening)?
// -------------------------------------------------------------------------------------------

/// The narrow no-op-identity-shuffle fragment (`reveal.rs` module doc): a plain `let`-only term,
/// no `%`, no `#`-triggering construct anywhere. `certified_roundtrip` must genuinely close the
/// surface loop here, not merely report `reparseable = true` without checking (STEP-0's point).
#[test]
fn percent_free_plain_term_surface_roundtrip_closes() {
    let shown = letn("x", c(5), v("x"));
    let verdict = certified_roundtrip(&shown, "Binary{8}");

    assert_eq!(
        verdict.l0,
        L0Witness::Closed,
        "a closed, %-free plain term must pass the L0-term witness"
    );
    match &verdict.surface {
        SurfaceOutcome::Ok { text } => {
            assert_eq!(text, "let x = 0b00000101 in x");
        }
        other => panic!(
            "expected the surface round-trip to CLOSE on the no-op-identity-shuffle fragment, \
             got {other:?} instead — if this regresses, the STEP-0 narrow-fragment claim in \
             reveal.rs's module doc is no longer supportable and must be downgraded, not silently \
             left stale"
        ),
    }
}

/// An entirely `%`-free arithmetic term — no sugar expansion, no hygiene freshening anywhere —
/// still fails the surface round-trip, honestly, because EVERY kernel `Op` prim name is
/// `.`-namespaced (`bin.add`) and so trips `render_surface`'s `#op[…]` marker regardless of `%`.
/// This is the fixture the module doc's "independent of `%`-freshening" claim rests on.
#[test]
fn percent_free_op_based_term_is_honestly_out_of_contract() {
    let shown = add(c(2), c(3));
    let verdict = certified_roundtrip(&shown, "Binary{8}");

    assert_eq!(
        verdict.l0,
        L0Witness::Closed,
        "the L0-term witness holds regardless of the surface outcome"
    );
    match &verdict.surface {
        SurfaceOutcome::OutOfContract { text } => {
            assert!(
                text.contains("#op["),
                "expected the #op[..] marker on a dotted-prim Op rendering, got {text:?}"
            );
        }
        other => panic!(
            "an Op-containing term (even %-free) must be out-of-contract — the dotted-prim gap is \
             independent of %-freshening; got {other:?} instead"
        ),
    }
}

/// **Boundary fixture (adversarially found in PR #1423 review, 2026-07-11) — `App` does NOT close
/// the surface round-trip, even `%`-free and marker-free.** `let f = 5 in f(3)` renders with
/// `reparseable = true` (no `%`, no `#` anywhere in `"let f = 0b00000101 in f(0b00000011)"`), but
/// the real re-check refuses: nothing besides `Lam`/`Fix`/`FixGroup` is callable in the surface
/// grammar (`crate::checkty`'s "unknown function/constructor/prim" refusal), and all three of
/// those are already excluded from the no-op-identity-shuffle fragment (`reveal.rs` module doc).
/// Grounds that doc's claim: the genuinely-closing fragment is `Const`/`Var`/`Let`(-of-those)
/// **only** — `App` is not part of it, structurally, for any closed `App`-term built solely from
/// that fragment (there is no callable to reparse back to).
#[test]
fn app_is_honestly_reparse_failed() {
    let shown = letn(
        "f",
        c(5),
        Node::App {
            func: Box::new(v("f")),
            arg: Box::new(c(3)),
        },
    );
    let verdict = certified_roundtrip(&shown, "Binary{8}");

    assert_eq!(
        verdict.l0,
        L0Witness::Closed,
        "the L0-term witness holds regardless of the surface outcome"
    );
    match &verdict.surface {
        SurfaceOutcome::ReparseFailed { text, reason } => {
            assert_eq!(text, "let f = 0b00000101 in f(0b00000011)");
            assert!(
                reason.contains("unknown function") || reason.contains("f"),
                "expected the real re-check to refuse citing the unresolved callable `f`, got: \
                 {reason:?}"
            );
        }
        other => panic!(
            "an App-containing term (even %-free, marker-free, reparseable=true) must fail real \
             re-check, not close — got {other:?} instead; if this ever starts closing, the \
             no-op-identity-shuffle fragment claim in reveal.rs's module doc must be widened, not \
             left stale (VR-5)"
        ),
    }
}

/// **Boundary fixture (adversarially found in PR #1423 review, 2026-07-11) — `Match` does NOT
/// close the surface round-trip either, even `%`-free and marker-free.** `let x = 5 in match x { 5
/// => x, _ => x }` genuinely reparses AND re-elaborates (no refusal) — but the elaborator injects
/// an extra scrutinee-binding `let` (`let scrut%N = … in match scrut%N { … }`) that is absent from
/// the original hand-built term, so the re-elaborated result is structurally different and NOT
/// `alpha_eq` to it. This is the `AlphaMismatch` case `SurfaceOutcome` exists to report honestly
/// rather than silently treat "it reparsed" as "it round-tripped" (G2).
#[test]
fn match_is_honestly_alpha_mismatch() {
    let five = Value::new(
        Repr::Binary { width: WIDTH },
        Payload::Bits(mycelium_core::binary::int_to_bits(5, WIDTH).expect("fits")),
        Meta::exact(Provenance::Root),
    )
    .expect("well-formed Binary{8} const");
    let shown = letn(
        "x",
        c(5),
        Node::Match {
            scrutinee: Box::new(v("x")),
            alts: vec![mycelium_core::Alt::Lit {
                value: five,
                body: v("x"),
            }],
            default: Some(Box::new(v("x"))),
        },
    );
    let verdict = certified_roundtrip(&shown, "Binary{8}");

    assert_eq!(
        verdict.l0,
        L0Witness::Closed,
        "the L0-term witness holds regardless of the surface outcome"
    );
    match &verdict.surface {
        SurfaceOutcome::AlphaMismatch { text } => {
            assert_eq!(
                text,
                "let x = 0b00000101 in match x { 0b00000101 => x, _ => x }"
            );
        }
        other => panic!(
            "a Match-containing term (even %-free, marker-free, reparseable=true) must reparse but \
             fail the alpha_eq check (the elaborator's own scrutinee-binding let injection), not \
             cleanly close — got {other:?} instead; if this ever starts closing, the \
             no-op-identity-shuffle fragment claim in reveal.rs's module doc must be widened, not \
             left stale (VR-5)"
        ),
    }
}

// -------------------------------------------------------------------------------------------
// (b) %-name (hygiene-interesting) fixtures — via `expand`, freshen=true. Reuses the E1
// "swap2 classic" shape (independently re-derived here, module doc's edit-scope note).
// -------------------------------------------------------------------------------------------

/// One hygiene-interesting E3 fixture, mirroring `hygiene_expr_sugar.rs`'s `Fixture` shape:
/// `rhs`/`params`/`args` define the sugar + use site; `wrap` embeds the (expanded/oracle/captured)
/// term in its real use-site `let`; `oracle` is independently hand-built (disjoint binder
/// spellings from `expand`'s `%`-gensym); `expected_hygienic`/`expected_captured` are hand-derived
/// from substitution semantics, cross-checked by `eval` at test time.
struct HygieneFixture {
    name: &'static str,
    rhs: Node,
    params: Vec<String>,
    args: Vec<Node>,
    wrap: fn(Node) -> Node,
    oracle: Node,
    expected_hygienic: i64,
    expected_captured: i64,
}

/// **swap2 classic** (DN-110-8.2-hygiene-deepdive §7 E1, re-derived here for E3): `swap2(a, b) =
/// let t = a in add(b, t)`, invoked at `let t = 7 in swap2(1, t)`. Hygienic: the RHS `t` is
/// freshened, so the use-site `b = t = 7` survives unshadowed: `add(7, 1) = 8`. Captured (bug):
/// reusing the RHS's raw `t` shadows the use-site `t`, so both operands read the inner `1`:
/// `add(1, 1) = 2`.
fn fixture_swap2_classic() -> HygieneFixture {
    let rhs = letn("t", v("a"), add(v("b"), v("t")));
    let oracle = letn("t_h1", c(1), add(v("t"), v("t_h1")));
    HygieneFixture {
        name: "swap2_classic",
        rhs,
        params: vec!["a".to_owned(), "b".to_owned()],
        args: vec![c(1), v("t")],
        wrap: |inner| letn("t", c(7), inner),
        oracle,
        expected_hygienic: 8,
        expected_captured: 2,
    }
}

/// **pair_add** (mirrors `hygiene_expr_sugar.rs`'s fixture 2): `pair_add(a, b) = let t = b in
/// add(a, t)`, invoked at `let t = 3 in pair_add(t, 9)` — this time it's `a` that is the use-site
/// `Var("t")`. Hygienic: `add(3, 9) = 12`. Captured: the unfreshened `let t = 9 in …` shadows the
/// use-site `t`, hijacking `a`'s reference: `add(9, 9) = 18`.
fn fixture_pair_add() -> HygieneFixture {
    let rhs = letn("t", v("b"), add(v("a"), v("t")));
    let oracle = letn("t_h2", c(9), add(v("t"), v("t_h2")));
    HygieneFixture {
        name: "pair_add",
        rhs,
        params: vec!["a".to_owned(), "b".to_owned()],
        args: vec![v("t"), c(9)],
        wrap: |inner| letn("t", c(3), inner),
        oracle,
        expected_hygienic: 12,
        expected_captured: 18,
    }
}

fn hygiene_fixtures() -> Vec<HygieneFixture> {
    vec![fixture_swap2_classic(), fixture_pair_add()]
}

/// **E3 go/no-go — the hygiene-interesting corpus.** For every fixture: (1) the surface path is
/// honestly out-of-contract (both a `%`-name AND the `#op[bin.add]` marker are present); (2) the
/// L0-term witness holds AND — the non-vacuous check — is `alpha_eq` to an **independently
/// hand-built oracle** (never a self-clone comparison); (3) an `eval` differential that does not
/// touch `alpha_eq` at all confirms the same result observationally; (4) a hand-derived deliberately
/// unhygienic ("captured") term — built via this same `expand` with `freshen=false` — evaluates to
/// a genuinely different value, demonstrating this harness's discriminating power (module doc).
///
/// **Closedness note:** `expand`'s bare output references its splice-in use-site argument nodes
/// verbatim (B) — for a fixture whose argument is itself a use-site `Var` (e.g. `swap2`'s `b`
/// arg), the *bare* expansion is therefore open (it references the enclosing `wrap`'s binder) —
/// exactly the real-world shape (a macro body is only closed once embedded at its use site). So
/// [`certified_roundtrip`]/[`reelaborate`] below run over `(f.wrap)(expanded)` (the whole closed
/// program), matching what a real `reveal_l0` would show for a fully-elaborated entry — never the
/// bare, possibly-open, expansion fragment.
#[test]
fn e3_hygiene_fixtures_l0_witness_and_eval_differential() {
    let interp = Interpreter::default();
    for f in hygiene_fixtures() {
        let expanded = expand(&f.rhs, &f.params, &f.args, true);
        let full_expanded = (f.wrap)(expanded);
        let full_oracle = (f.wrap)(f.oracle.clone());

        // -- Surface path: honestly out-of-contract (module doc's central claim) --------------
        let verdict = certified_roundtrip(&full_expanded, "Binary{8}");
        match &verdict.surface {
            SurfaceOutcome::OutOfContract { text } => {
                assert!(
                    text.contains('%'),
                    "[{}] expected a %-freshened name in the rendering",
                    f.name
                );
                assert!(
                    text.contains("#op["),
                    "[{}] expected the #op[..] marker (dotted bin.add prim)",
                    f.name
                );
            }
            other => panic!(
                "[{}] a %-name + Op-bearing hygiene expansion must be out-of-contract, got {other:?}",
                f.name
            ),
        }

        // -- L0-term witness: NON-VACUOUS (oracle is independently, disjointly spelled) --------
        assert_eq!(
            verdict.l0,
            L0Witness::Closed,
            "[{}] the L0-term witness (reelaborate + alpha_eq to itself) must hold for the closed \
             (wrapped) expansion",
            f.name
        );
        let reelaborated =
            reelaborate(&full_expanded).unwrap_or_else(|e| panic!("[{}] reelaborate: {e}", f.name));
        assert!(
            alpha_eq(&reelaborated, &full_oracle),
            "[{}] expand(...) is not alpha-equivalent to the independently hand-built oracle — a \
             genuine hygiene failure, not a comparator artifact (the oracle uses a disjoint \
             binder-naming scheme from expand's %-gensym, so a true-always/false-always alpha_eq \
             could not pass this)",
            f.name
        );

        // -- Observational differential: independent of alpha_eq -------------------------------
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

        // -- Discriminating-power demonstration: the captured (freshen=false) variant ----------
        let captured = expand(&f.rhs, &f.params, &f.args, false);
        let full_captured = (f.wrap)(captured);
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
             discriminating power",
            f.name
        );
    }
}

// -------------------------------------------------------------------------------------------
// Non-vacuity: the mutation self-check — disabling freshening must be CAUGHT, not silently pass.
// -------------------------------------------------------------------------------------------

/// **Mutation self-check (module doc; the harness-level, not just fixture-level, non-vacuity
/// demonstration).** Runs the *same* assertions the go/no-go loop above relies on, but against
/// `expand(..., freshen = false)` — a real, mechanically-produced unhygienic expansion (not a
/// separately hand-authored "captured" literal) — and asserts they FAIL exactly where hygiene
/// predicts: `alpha_eq` against the (freshened-spelling) oracle is false, and the `eval`
/// differential diverges from the hygienic expected value. If a future change silently disabled
/// `%`-freshening in a real implementation, this is the shape of check that would catch it — this
/// test proves the shape actually works, on this harness, today.
#[test]
fn e3_mutation_self_check_disabling_freshening_is_caught() {
    let interp = Interpreter::default();
    for f in hygiene_fixtures() {
        let mutated = expand(&f.rhs, &f.params, &f.args, false);

        assert!(
            !alpha_eq(&mutated, &f.oracle),
            "[{}] MUTATION SELF-CHECK FAILED: disabling freshening should break alpha-equivalence \
             to the oracle, but it didn't — the harness would NOT catch a disabled-freshening \
             regression (non-vacuity violated)",
            f.name
        );

        let full_mutated = (f.wrap)(mutated);
        let observed = interp
            .eval(&full_mutated)
            .unwrap_or_else(|e| panic!("[{}] eval(mutated) failed: {e}", f.name));
        assert_eq!(
            as_i64(&observed),
            f.expected_captured,
            "[{}] the freshen=false mutation must reproduce the hand-derived captured-bug value",
            f.name
        );
        assert_ne!(
            as_i64(&observed),
            f.expected_hygienic,
            "[{}] MUTATION SELF-CHECK FAILED: disabling freshening should diverge from the \
             hygienic expected value observationally, but it didn't",
            f.name
        );
    }
}
