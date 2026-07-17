//! **E2 — def-site resolution experiment** (M-1055; DN-110-8.2-hygiene-deepdive §4(C)/§7 E2).
//!
//! Validates hygiene-model clause **(C)**: a free identifier in a sugar RHS resolves at the rule's
//! **definition** scope, never wherever the expansion is later spliced (the use site). Sibling to
//! the landed E1 harness ([`crate::tests::hygiene_expr_sugar`]), which validates (A) RHS-binder
//! freshening + (B) capture-safe argument substitution **only** — E1's own `expand` explicitly
//! punts a genuinely free RHS identifier ("out of E1's scope — that's E2/(C); left as-is rather
//! than silently guessed at"). This module is that follow-on.
//!
//! # Scope — narrowed to the same-nodule / in-scope case (task-directed; read before extending)
//!
//! DN-110-8.2-hygiene-deepdive §7's own E2 spec additionally asks for a **cross-phylum** fixture as
//! an OQ-H1 stressor. **This experiment deliberately does not build one.** Def-site resolution
//! across phyla / separate compilation is **OQ-H1** (deep-dive §10), explicitly flagged as
//! unsettled there — "which `helper` (and its content hash) is captured, and how does re-export /
//! version skew interact?" has no answer in the landed codebase to ground a fixture against, and
//! inventing one would be exactly the guess G2/VR-5 forbid ("flag ambiguity, never guess"). So E2
//! here validates **only** the well-defined in-scope case: a sugar RHS's free identifier, and a
//! *different* binding of the same spelling in scope at the use site, both within one nodule. OQ-H1
//! stays open and is carried in this task's report, not dispositioned here.
//!
//! **A further, unexercised composition gap (caveat, not a claim of soundness):** [`DefEnv::get`]
//! splices the resolved def-site [`Node`] **verbatim** — it does *not* route the spliced content
//! back through (A)'s `%`-freshening walk. In the real DN-110 §4(C) design this is a non-issue (a
//! def-site reference is resolved to a **content-addressed reference**, not textually re-spliced —
//! deep-dive §4(C)), but *this prototype* literally re-inlines raw content, so a fixture where the
//! def-site helper's own bound-variable spelling collides with an RHS binder or a use-site binder
//! is **not tested here** — this module's one fixture avoids that composition by construction (the
//! def-site helper's own `x` never collides with anything in scope at the splice point). Flagged as
//! an open gap in this prototype's coverage, not fixed by inventing a fixture for it (G2/VR-5).
//!
//! # Additive, non-gating scope (read before treating a PASS as M-1055 progress)
//!
//! **E2 and E5 are additive exploration, not progress against M-1055's formal Definition of Done.**
//! M-1055's DoD is **E1 + E3** — the Rank-1 go/no-go the deep-dive commissions (§9); E3 (`reveal`
//! round-trip fidelity) needs `reveal` Increment-3 and is **unbuilt**, so the formal DoD is not
//! satisfied by this module or its E5 sibling. What a PASS here actually establishes: hygiene-model
//! clause **(C)** (def-site resolution) moves `Declared → Empirical` **for the in-scope,
//! same-nodule case only** — cross-phylum resolution (**OQ-H1**) stays open and undecided.
//!
//! # Test-only — NOT the M-1054 facility
//!
//! Exactly the same posture as E1 (see its module docs): [`expand`] is a throwaway experiment
//! prototype confined to `src/tests/`, not a step toward implementing the Accepted-not-Enacted
//! M-1054 facility, and it does not touch [`crate::elab::elaborate_lower_rule`].
//!
//! # The non-vacuity discipline (reused from E1, restated for def-site resolution)
//!
//! 1. The **oracle** is built by direct, literal [`Node`] construction on a **different binder
//!    spelling** than the def-site helper's own (`x_h` vs `x`), so [`alpha_eq`] must do genuine
//!    alpha-comparison work exactly as in E1.
//! 2. Every fixture is checked **observationally** through [`mycelium_interp::Interpreter`] as well
//!    — independent of [`alpha_eq`].
//! 3. Every fixture carries a **hand-built "captured" (referentially-*opaque*) expansion** — the
//!    naive behavior E1's own `expand` already exhibits for a free identifier (leave it as a bare
//!    `Var`, so it resolves wherever it is later embedded) — with its own independently-derived
//!    expected value. `expected_captured != expected_resolved` and `eval` actually produces
//!    `expected_captured` on that node demonstrates the harness can *observe* a real
//!    referential-transparency break, not merely fail to trigger one.
//! 4. **Additionally** (new to E2, the sub-question-(i)-specific check): the correctly-resolved
//!    expansion must contain **no bare `Var("helper")` anywhere** ([`contains_var`]) — the free
//!    reference must have been *replaced* by the def-site binding's own content, not merely left
//!    alone and gotten lucky. The captured variant, by construction, **does** still contain the bare
//!    `Var("helper")` — checked as a discriminating-power sanity assertion.
//!
//! # Guarantee tag
//!
//! [`expand`]'s referential-transparency property (def-site resolution), over this fixture corpus,
//! **for the in-scope same-nodule case only**: **`Empirical`** (checked below, not proven).
//! Cross-phylum resolution (OQ-H1) stays **`Declared`**/open — not moved by this module (VR-5: a
//! PASS here says nothing about the cross-phylum question, and this module never claims it does).

use crate::reveal::alpha_eq;
use mycelium_core::{Meta, Node, Payload, Provenance, Repr, Value};
use mycelium_interp::Interpreter;

// -------------------------------------------------------------------------------------------
// Test-only Node builders (duplicated from `hygiene_expr_sugar.rs` rather than shared — each
// experiment module is self-contained, matching this crate's one-submodule-per-concern layout;
// `hygiene_expr_sugar`'s builders are module-private, not `pub(crate)`, so there is nothing to
// import here even if sharing were desired).
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

fn sub(x: Node, y: Node) -> Node {
    Node::Op {
        prim: "bin.sub".to_owned(),
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

fn as_i64(result: &Value) -> i64 {
    match result.payload() {
        Payload::Bits(bits) => mycelium_core::binary::bits_to_int(bits),
        other => panic!("expected a Binary payload, got {other:?}"),
    }
}

/// Does `node` contain a bare `Var(name)` anywhere in its tree? Used to confirm a def-site-resolved
/// expansion has genuinely *replaced* the free reference (not merely left it alone and gotten lucky
/// on evaluation order) — module doc point 4. Small hand tree-walk (these fixtures are shallow; no
/// need for the kernel's own iterative-traversal discipline, which exists for *deep, adversarial*
/// spines — RFC-0041 §4.5 — not a handful of hand-built test fixtures).
fn contains_var(node: &Node, name: &str) -> bool {
    match node {
        Node::Const(_) => false,
        Node::Var(id) => id == name,
        Node::Let { bound, body, .. } => contains_var(bound, name) || contains_var(body, name),
        Node::Op { args, .. } | Node::Construct { args, .. } => {
            args.iter().any(|a| contains_var(a, name))
        }
        Node::Swap { src, .. } => contains_var(src, name),
        Node::Match {
            scrutinee,
            alts,
            default,
        } => {
            contains_var(scrutinee, name)
                || alts.iter().any(|a| match a {
                    mycelium_core::Alt::Ctor { body, .. }
                    | mycelium_core::Alt::Lit { body, .. } => contains_var(body, name),
                })
                || default.as_deref().is_some_and(|d| contains_var(d, name))
        }
        Node::Lam { body, .. } | Node::Fix { body, .. } => contains_var(body, name),
        Node::App { func, arg } => contains_var(func, name) || contains_var(arg, name),
        Node::FixGroup { defs, body } => {
            defs.iter().any(|(_, d)| contains_var(d, name)) || contains_var(body, name)
        }
    }
}

// -------------------------------------------------------------------------------------------
// `DefEnv` + `expand` — the test-only (C) def-site-resolution prototype
// -------------------------------------------------------------------------------------------

/// A minimal stand-in for "the definitions visible at a sugar rule's own definition site" (deep-dive
/// §4(C)). Not content-addressed (ADR-003's hashing is orthogonal machinery this Node-level
/// prototype doesn't model — see the module report's honesty note); what matters for (C) is *early
/// binding*: the lookup happens against a snapshot fixed when [`expand`] is called with this env,
/// never against whatever scope the expansion is later embedded into.
struct DefEnv {
    defs: std::collections::BTreeMap<String, Node>,
}

impl DefEnv {
    fn new() -> Self {
        DefEnv {
            defs: std::collections::BTreeMap::new(),
        }
    }

    fn with(mut self, name: &str, node: Node) -> Self {
        self.defs.insert(name.to_owned(), node);
        self
    }

    fn get(&self, name: &str) -> Option<&Node> {
        self.defs.get(name)
    }
}

/// Expand a sugar RHS `rhs` (parameterized over `params`) against use-site `args`, resolving any
/// genuinely-free RHS identifier against `def_env` — the rule's **definition-site** bindings — at
/// expansion time (C), in addition to (A) `%`-freshening of RHS binders and (B) capture-safe
/// argument substitution (both reused verbatim from E1's `expand`/`Expander`, not reimplemented:
/// this is `hygiene_expr_sugar::expand`'s own walk with one more resolution rule spliced into the
/// `Var` arm — duplicated rather than imported per this file's self-containment note above).
///
/// The def-site lookup happens **before** falling back to "leave the bare `Var` as-is" (E1's own
/// behavior for an unresolved free identifier) — so a name present in `def_env` is *replaced* by
/// its def-site content, never left as a reference for the use site's scope to wrongly resolve
/// later.
fn expand(rhs: &Node, params: &[String], args: &[Node], def_env: &DefEnv) -> Node {
    let mut ex = Expander {
        params,
        args,
        def_env,
        scope: Vec::new(),
        counter: 0,
    };
    ex.go(rhs)
}

struct Expander<'a> {
    params: &'a [String],
    args: &'a [Node],
    def_env: &'a DefEnv,
    scope: Vec<(String, String)>,
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
                    // (A): an RHS-local binder reference — follow it to its fresh name.
                    Node::Var(fresh.to_owned())
                } else if let Some(arg) = self.param_arg(id) {
                    // (B): a sugar-parameter reference — splice the use-site argument verbatim.
                    arg.clone()
                } else if let Some(def_node) = self.def_env.get(id) {
                    // (C): a genuinely free RHS identifier — resolved at the rule's DEFINITION
                    // scope (`def_env`, fixed at `expand`-call time), independent of the use
                    // site's own bindings of the same spelling.
                    def_node.clone()
                } else {
                    // Truly unresolved even at def-site — E1's own fallback, unchanged.
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
            Node::App { func, arg } => Node::App {
                func: Box::new(self.go(func)),
                arg: Box::new(self.go(arg)),
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
            // The remaining node kinds are not exercised by this corpus's fixtures (kept minimal —
            // YAGNI; E1's `expand` handles the full grammar, this E2-focused variant covers exactly
            // what its fixtures need: Const/Var/Let/Op/App/Lam).
            other => other.clone(),
        }
    }
}

// -------------------------------------------------------------------------------------------
// The E2 fixture (core, in-scope-only per this experiment's narrowed scope)
// -------------------------------------------------------------------------------------------

/// **Fixture — def-site `helper` shadowed by a same-spelled use-site local.**
///
/// Def-site (nodule A, conceptually): `fn helper(x) = x + 100`. Sugar: `bump(v) = helper(v)`. Use
/// site (same nodule, a local `helper` in scope with a *different* body): `let helper = (lambda x
/// => x - 100) in bump(5)`.
///
/// - **Resolved (correct, (C)):** `helper` in the RHS binds to the DEF-SITE `helper` regardless of
///   the use-site shadow. `bump(5)` computes `5 + 100 = 105`.
/// - **Captured (bug — referential-transparency break):** if the free `helper` reference is left as
///   a bare `Var` (E1's own fallback for an unresolved free identifier, which is exactly what a
///   naive expander that skips (C) would ship), it resolves at *eval* time to whatever `helper` is
///   in scope at the splice site — the use-site shadow. `bump(5)` then computes `5 - 100 = -95`.
struct Fixture {
    name: &'static str,
    def_site_helper: Node,
    rhs: Node,
    params: Vec<String>,
    args: Vec<Node>,
    /// Wraps an inner (expanded/oracle/captured) node in the fixture's real use-site `let helper =
    /// … in …` shadow.
    wrap: fn(Node) -> Node,
    oracle: Node,
    captured: Node,
    expected_resolved: i64,
    expected_captured: i64,
}

fn fixture_defsite_shadowed_by_use_site_local() -> Fixture {
    // Def-site helper: x + 100.
    let def_site_helper = lam("x", add(v("x"), c(100)));
    // Sugar RHS: bump(v) = helper(v) — `helper` is genuinely free in the RHS.
    let rhs = app(v("helper"), v("v"));
    // Oracle: independently hand-built, using a DIFFERENT lambda-param spelling (`x_h`) than the
    // def-site helper's own (`x`) — non-vacuity point 1 (forces alpha_eq to do real work).
    let oracle = app(lam("x_h", add(v("x_h"), c(100))), c(5));
    // Captured (bug): the naive/E1-fallback expansion — `helper` left as a bare `Var`, which the
    // wrapping use-site `let helper = … in …` then wrongly resolves at eval time.
    let captured = app(v("helper"), c(5));
    Fixture {
        name: "defsite_shadowed_by_use_site_local (bump/helper)",
        def_site_helper,
        rhs,
        params: vec!["v".to_owned()],
        args: vec![c(5)],
        wrap: |inner| letn("helper", lam("x", sub(v("x"), c(100))), inner),
        oracle,
        captured,
        expected_resolved: 105,
        expected_captured: -95,
    }
}

// -------------------------------------------------------------------------------------------
// The E2 assertion: dual (structural + observational) + the def-site-resolved-reference check
// -------------------------------------------------------------------------------------------

/// **E2 — def-site resolution, dual-checked, in-scope case only.** For the fixture:
/// `alpha_eq(expand(rhs, params, args, def_env), oracle)` **and**
/// `eval(wrap(expand(...))) == eval(wrap(oracle))` — the second does not depend on `alpha_eq` at
/// all. Additionally: the resolved expansion contains **no bare `Var("helper")`** (module doc point
/// 4), and the independently-derived captured/resolved values differ (discriminating power).
#[test]
fn e2_defsite_resolution_in_scope() {
    let interp = Interpreter::default();
    let f = fixture_defsite_shadowed_by_use_site_local();
    let def_env = DefEnv::new().with("helper", f.def_site_helper.clone());

    let expanded = expand(&f.rhs, &f.params, &f.args, &def_env);

    // -- Structural check --------------------------------------------------------------
    assert!(
        alpha_eq(&expanded, &f.oracle),
        "[{}] expand(...) is not alpha-equivalent to the independently hand-built def-site-resolved \
         oracle — a genuine referential-transparency failure, not a comparator artifact.",
        f.name
    );

    // -- Def-site-resolved-reference check (module doc point 4, sub-question (i) specific) -----
    assert!(
        !contains_var(&expanded, "helper"),
        "[{}] the resolved expansion still contains a bare Var(\"helper\") — resolution did not \
         actually replace the free reference with the def-site binding's content",
        f.name
    );
    assert!(
        contains_var(&f.captured, "helper"),
        "[{}] the captured (naive) fixture is supposed to still carry the unresolved bare \
         Var(\"helper\") — sanity check on the fixture itself",
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
        f.expected_resolved,
        "[{}] eval(expand(...)) did not resolve to the def-site helper's value",
        f.name
    );
    assert_eq!(
        as_i64(&observed_oracle),
        f.expected_resolved,
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
        f.expected_captured, f.expected_resolved,
        "[{}] this fixture's captured/resolved values coincide — it cannot demonstrate \
         discriminating power",
        f.name
    );
}
