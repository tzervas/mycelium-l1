//! **M-1054 Stage 2 (DN-115)** — prove-by-construction that single-nodule def-site resolution
//! already holds on the **real** elaborator, plus the two narrow gate-correctness fixes DN-115 §4
//! closes.
//!
//! # Why "prove-by-construction", not "add resolution" (DN-115 §1)
//!
//! DN-115's own adversarial read of the code found that the single-nodule half of macro-hygiene
//! clause (C) (referential transparency / def-site resolution) is **already achieved by
//! construction** in Pass 1 of `elaborate_value_parametric_rule_inner` — a sugar rule's RHS is
//! elaborated against the **def-site** global env *before* Pass 2's `%`-freshening/value-param
//! splice ever runs, so a use-site local of the same spelling can never be consulted. What was
//! genuinely missing was (a) an end-to-end test of that property on the **real** elaborator (the
//! existing `hygiene_defsite_resolution.rs` E2 harness is a throwaway `DefEnv`-lookup prototype,
//! not the production Pass-1-inlining mechanism) and (b) two narrow gate-correctness gaps. This
//! module supplies (a); the sibling `checkty.rs` edits supply (b) (G1/G2).
//!
//! # Sibling modules (why this one is separate)
//! - [`crate::tests::hygiene_defsite_resolution`] — the E2 **prototype** (`DefEnv`/`Expander`, a
//!   throwaway `Node`-level stand-in, never wired to `elaborate_lower_rule`). Its own module doc
//!   already flags that a PASS there says nothing about the real elaborator.
//! - [`crate::tests::reachability_stage1b`] — the pattern this module reuses: check via the real
//!   `infer_type`, elaborate via the real `elaborate(&env, "main")` (which dispatches through
//!   `Elab::app`'s §5.2 sugar-call branch), never a direct call into the expander.
//!
//! # The non-vacuity discipline (the E1/E2 lesson, restated for Stage 2)
//! 1. [`stage2_defsite_resolution_real_elaborator`] — dual oracle: [`alpha_eq`] against an
//!    independently hand-built oracle (disjoint binder spelling) **and** an independent
//!    [`mycelium_interp::Interpreter::eval`] differential.
//! 2. [`stage2_control_use_site_shadow_would_capture`] — the **mandatory non-vacuity control**:
//!    because the real elaborator resolves at Pass 1 by inlining (there is no "disable def-site
//!    resolution" runtime flag to flip, unlike Stage 1's freshening flag), the control
//!    hand-constructs the **captured** (referentially-*opaque*) `Node` directly — the free `helper`
//!    reference left as a bare `Var`, spliced under the identical use-site shadow — and asserts
//!    `eval` observes the *wrong* value. This proves the harness can genuinely observe a
//!    referential-transparency break, so test 1's PASS is discriminating, not vacuous.
//! 3. [`stage2_vsa_or_float_prim_rhs_now_accepted`] (G1) + [`stage2_bare_nullary_lower_rule_value_position_refused`]
//!    (G2) each carry their own doc-comment record of a **manual, temporary revert** of this leaf's
//!    fix during development, confirming the pre-fix behavior really differs — mirroring
//!    `reachability_stage1b.rs`'s own "verified by mutation" precedent (there is no runtime toggle
//!    for either fix to drive an in-test control, so the verification is recorded, not automated).
//! 4. [`stage2_control_cross_nodule_shaped_free_id_stays_refused`] — the Stage-4 boundary stays
//!    refused; Stage 2 does not start silently accepting a cross-nodule shape.
//!
//! # An honest correction to DN-115 §4.2's own framing (VR-5 — surfaced, not smoothed over)
//!
//! DN-115 §4.2 characterizes the G2 gap as "a program the checker **accepts** would **red** at
//! elab — precisely the 'green at check, red at eval' failure DN-116 §1 exists to prevent."
//! **Adversarial verification during this leaf (temporarily reverting the gate's position
//! sensitivity and driving the exact `BareRef`-style fixture through the real `infer_type`)
//! disproves the literal claim**: `check_sugar_call` always follows its Stage-2 gate with a full
//! RHS type-check (`infer_expr_rule_rhs_type` → `Cx::infer` → `Cx::check_path` for a bare `Path`),
//! and `check_path` has **no** branch that ever consults `self.lower_rules` — every bare
//! value-position reference to a lower-rule name is refused there unconditionally (`"unknown name
//! ‹name›"`, `checkty.rs`'s `check_path` fallback), **regardless** of what the Stage-2 gate itself
//! decided. So the pre-fix, position-agnostic gate did **not** actually let such a program reach
//! elaboration — the call site was **already** refused at check, every time, just via a generic,
//! confusing diagnostic instead of the clear, Stage-2-labeled one. **There is no accept/residual
//! soundness gap here to close.** What G2's narrowing genuinely buys: (1) an earlier, clearly
//! *Stage-2-labeled* refusal instead of a generic "unknown name" one surfacing from a nested,
//! internal-only diagnostic call the caller never asked to check directly; (2) **gate/mechanism
//! self-consistency** — the gate's own accepted-fragment claim now matches what
//! `Elab::app`'s dispatch can actually resolve, so the gate's doc comment is no longer describing a
//! fragment it doesn't really accept end-to-end. Both are real, worthwhile fixes (and match the
//! maintainer-ratified "narrow the gate, KISS" disposition) — they are just not, on the evidence
//! constructible here, closing a live "green-check/red-eval" case. [`stage2_bare_nullary_lower_rule_value_position_refused`]
//! asserts the **actual**, verified behavior: refused at check, with the Stage-2-labeled message,
//! both before and after this leaf (the message text is the only thing this leaf changes for this
//! shape).
//!
//! # Guarantee tag
//! [`stage2_defsite_resolution_real_elaborator`]'s dual-oracle PASS moves single-nodule def-site
//! resolution / referential transparency **`Declared` → `Empirical`** on the real elaborator (DN-115
//! §5). Cross-nodule/phylum resolution stays `Declared`/open (Stage 4, DN-113) —
//! [`stage2_control_cross_nodule_shaped_free_id_stays_refused`] confirms it is still refused, never
//! silently widened. G1's VSA/float-prim name-recognition and G2's position-sensitive lower-rule
//! gate move to `Empirical` on their own fixtures below.

use crate::ast::{
    BaseType, Expr, FnDecl, FnSig, Literal, LowerDecl, LowerRhs, Param, Path, TypeRef, WidthRef,
};
use crate::checkty::{check_nodule, infer_type, Env, Ty, Width};
use crate::elab::elaborate;
use crate::parse;
use crate::reveal::alpha_eq;
use mycelium_core::{Meta, Node, Payload, Provenance, Repr, Value};
use mycelium_interp::Interpreter;

fn env(src: &str) -> Env {
    check_nodule(&parse(src).expect("parses")).expect("checks")
}

// -------------------------------------------------------------------------------------------
// Node-level builders (the oracle / hand-built-control side — mirrors
// `reachability_stage1b.rs`/`hygiene_defsite_resolution.rs` exactly; duplicated rather than
// shared per this crate's one-self-contained-module-per-concern test-layout convention).
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

/// Does `node` contain a bare `Var(name)` anywhere in its tree? (Reused from
/// `hygiene_defsite_resolution.rs` — see that module's doc comment for the caveat this module's
/// own doc restates: kernel freshening means this check has limited power on the real elaborator's
/// output, since a resolved reference is inlined away long before any name could survive as a raw
/// `Var`. Kept anyway, matching DN-115 §6 item 1's own corpus spec — a basic sanity/regression
/// check, not the discriminating one; that's [`stage2_control_use_site_shadow_would_capture`].)
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
// Surface-Expr builders (white-box for `value_params` — no committed surface grammar yet, per
// `LowerDecl::value_params`'s own doc comment; mirrors `reachability_stage1b.rs`).
// -------------------------------------------------------------------------------------------

fn bin_ty(width: u32) -> TypeRef {
    TypeRef {
        base: BaseType::Binary(WidthRef::Lit(width)),
        guarantee: None,
    }
}

fn float_ty() -> TypeRef {
    TypeRef {
        base: BaseType::Float,
        guarantee: None,
    }
}

fn sc(i: u8) -> Expr {
    Expr::Lit(Literal::Bin(format!("{i:08b}")))
}

fn sc16(i: u16) -> Expr {
    Expr::Lit(Literal::Bin(format!("{i:016b}")))
}

fn sflt(text: &str) -> Expr {
    Expr::Lit(Literal::float(text))
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

fn scall(name: &str, args: Vec<Expr>) -> Expr {
    Expr::App {
        head: Box::new(sv(name)),
        args,
    }
}

/// Register a nullary top-level `fn main` whose body is `body`, returning `Binary{8}` (mirrors
/// `reachability_stage1b.rs::with_main`).
fn with_main(e: &mut Env, body: Expr) {
    e.fns.insert(
        "main".to_owned(),
        FnDecl {
            vis: crate::ast::Vis::Private,
            thaw: false,
            tier: None,
            sig: FnSig {
                name: "main".to_owned(),
                params: vec![],
                value_params: vec![],
                ret: bin_ty(8),
                effects: vec![],
                effect_budgets: std::collections::BTreeMap::new(),
            },
            body,
        },
    );
}

// =============================================================================================
// 1+2. The E2 fixture driven through the REAL elaborator + the non-vacuity capture control
// =============================================================================================

/// **Def-site (nodule `d`): `fn helper(x: Binary{8}) => Binary{8} = add_s(x, 100)`. Sugar:
/// `bump(v) = helper(v)`.** DN-115 §6's own fixture shape, reused verbatim from
/// `hygiene_defsite_resolution.rs`'s `fixture_defsite_shadowed_by_use_site_local` (100/5/105/-95),
/// but registered into a *checked* [`Env`] and driven through `infer_type`/`elaborate` instead of
/// the throwaway `DefEnv`/`Expander` prototype.
fn base_env_with_helper() -> Env {
    env("nodule d;\nfn helper(x: Binary{8}) => Binary{8} = add_s(x, 0b01100100);")
}

fn with_bump_rule(e: &mut Env) {
    e.lower_rules.insert(
        "bump".to_owned(),
        LowerDecl {
            name: "bump".to_owned(),
            params: vec![],
            value_params: vec![Param {
                name: "v".to_owned(),
                ty: bin_ty(8),
            }],
            rhs: LowerRhs::Expr(scall("helper", vec![sv("v")])),
        },
    );
}

/// `main`'s body: a use-site local **of the same spelling as the def-site free id** (`helper`),
/// in scope for the entire `bump(5)` call — DN-115 §3's Q3 shadowing hazard, reproduced on the
/// real elaborator. The shadow is bound to a plain `Binary{8}` value here (not a same-shaped
/// closure) — deliberately: `bump`'s RHS resolves its free `helper` by **Pass-1 inlining against
/// the def-site nodule**, never by a scope lookup of the use site's local, so the shadow's own
/// shape is provably irrelevant to whether it is consulted (§3's own mechanism trace, step 1: "the
/// use-site local `let helper` is not in `self.fns`; it plays no part in the gate" — and Pass 1
/// never looks at `scope` for the RHS-free-id resolution either, only `self.env`). The **fully
/// realistic** capture scenario — the shadow genuinely applied as a function, `helper(5)` — is
/// what [`stage2_control_use_site_shadow_would_capture`] hand-builds at the `Node` level below
/// (avoiding this test's dependency on `mono.rs`'s closure defunctionalization naming, which is
/// irrelevant to what this test needs to demonstrate).
fn main_body_with_shadow() -> Expr {
    slet("helper", sc(1), scall("bump", vec![sc(5)]))
}

/// **DN-115 §6 item 1 — single-nodule def-site resolution, real elaborator, dual oracle.**
/// `check` accepts `main`'s body (which calls `bump(5)` under a use-site `helper` shadow);
/// `elaborate(&env, "main")` reaches `Elab::app`'s §5.2 sugar-call dispatch, inlines `bump`'s RHS
/// against `helper`'s **def-site** body — never the use-site shadow — and the result is
/// alpha-equivalent to an independently hand-built oracle **and** evaluates to the def-site answer
/// (`5 + 100 = 105`), checked by two independent means (structural + observational), exactly the
/// dual-oracle discipline `reachability_stage1b.rs`/`hygiene_defsite_resolution.rs` both use.
#[test]
fn stage2_defsite_resolution_real_elaborator() {
    let mut e = base_env_with_helper();
    with_bump_rule(&mut e);
    let main_body = main_body_with_shadow();

    // Check the exact program before elaborating it (the reachability_stage1b.rs "Finding-3
    // coupling" discipline — one fixture drives both assertions, so a step1/step2 desync is
    // caught rather than silently possible).
    let checked_ty = infer_type(&e, &mut Vec::new(), &main_body).expect(
        "`main`'s body — a def-site-shadowed sugar call — must be check-accepted (M-1054 Stage 2)",
    );
    assert_eq!(checked_ty, Ty::Binary(Width::Lit(8)));

    with_main(&mut e, main_body);
    let elaborated = elaborate(&e, "main")
        .expect("elaborate(&env, \"main\") must reach Elab::app's §5.2 dispatch and expand");

    // -- Def-site-resolved-reference check (DN-115 §6 item 1(a); basic sanity — see this module's
    //    own doc comment for why this check has limited discriminating power on the real
    //    elaborator's output; the genuinely discriminating check is the eval oracle below plus the
    //    non-vacuity control) -------------------------------------------------------------------
    assert!(
        !contains_var(&elaborated, "helper"),
        "the elaborated program still contains a bare Var(\"helper\") — a free fn-call reference \
         should never survive Pass-1 inlining"
    );

    // -- Structural check (alpha_eq against an independently hand-built oracle, disjoint spelling
    //    for both the (inert) outer shadow binder and the value-param `Let` Pass 2's (B)
    //    substitution introduces — the fresh `%sugar#bump@…%tmp%…`-namespaced binding it (A)
    //    freshens `v` into, `Let`-bound to the spliced argument node rather than textually
    //    substituted verbatim) --------------------------------------------------------------
    let oracle = letn(
        "oracle_shadow",
        c(1),
        letn("oracle_v", c(5), add(v("oracle_v"), c(100))),
    );
    assert!(
        alpha_eq(&elaborated, &oracle),
        "elaborate(&env, \"main\")'s output is not alpha-equivalent to the independently \
         hand-built def-site-resolved oracle — a genuine referential-transparency failure, not a \
         comparator artifact."
    );

    // -- Observational check, independent of alpha_eq -------------------------------------------
    let interp = Interpreter::default();
    let observed = interp
        .eval(&elaborated)
        .unwrap_or_else(|err| panic!("eval(elaborate(main)) failed: {err}"));
    let observed_oracle = interp
        .eval(&oracle)
        .unwrap_or_else(|err| panic!("eval(oracle) failed: {err}"));
    assert_eq!(
        as_i64(&observed),
        105,
        "bump(5) must resolve helper at its DEF SITE (5 + 100 = 105), never the use-site shadow"
    );
    assert_eq!(
        as_i64(&observed_oracle),
        105,
        "oracle itself is miscomputed"
    );
}

/// **DN-115 §6 item 2 — the mandatory non-vacuity control.** There is no "disable def-site
/// resolution" runtime flag to flip (resolution *is* Pass-1 inlining, not a toggle — DN-115 §6
/// item 2's own framing), so this control hand-builds the **captured** (referentially-opaque)
/// expansion directly at the `Node` level: the free `helper` reference left as a bare `Var`
/// (exactly what a naive expander that skips def-site resolution would ship — E1's own fallback
/// behavior, reused from `hygiene_defsite_resolution.rs`'s `captured` fixture), spliced under the
/// **same** use-site shadow shape DN-115 §3's Q3 walkthrough describes (a same-signature
/// closure, `helper = λx. x - 100`, genuinely *applied* to the argument). `eval` on this
/// hand-built term observes the WRONG (captured, use-site) value, `-95`, never the def-site `105`
/// — proving this corpus's harness can observe a real referential-transparency break, so test 1's
/// PASS is discriminating, not vacuously green (the E1/E2 non-vacuity law).
#[test]
fn stage2_control_use_site_shadow_would_capture() {
    let captured = app(v("helper"), c(5));
    let wrapped = letn("helper", lam("x", sub(v("x"), c(100))), captured.clone());

    assert!(
        contains_var(&captured, "helper"),
        "sanity: the hand-built captured fixture must still carry the unresolved bare \
         Var(\"helper\") — otherwise it isn't testing the capture scenario at all"
    );

    let interp = Interpreter::default();
    let observed = interp
        .eval(&wrapped)
        .unwrap_or_else(|err| panic!("eval(captured) failed: {err}"));
    assert_eq!(
        as_i64(&observed),
        -95,
        "the hand-built captured (referentially-opaque) expansion must reproduce the wrong, \
         use-site-shadow-captured value (5 - 100 = -95)"
    );
    assert_ne!(
        -95, 105,
        "captured and resolved values must differ — otherwise this control has no \
         discriminating power (THE NON-VACUITY LAW)"
    );
}

// =============================================================================================
// 3. G1 — VSA/float-prim over-refusal, now fixed
// =============================================================================================

/// **DN-115 §6 item 3 / §4.1 (G1).** A `lower`-rule RHS calling a **float** prim (`flt_neg`) —
/// previously over-refused by the Stage-2 gate (`rhs_first_free_id` consulted only `prim_family`,
/// which has no float/VSA entries) even though `Cx::check_app`/`Elab::app` both resolve it fine at
/// an ordinary call site. Fixed by `prim_name_is_recognized` (checkty.rs), which additionally
/// consults the VSA/float-prim dispatch sets' own **name** view (`VSA_PRIM_NAMES`,
/// `float_prim_name_is_recognized` — the same literal name lists `Cx::try_check_vsa_prim`/
/// `Cx::try_check_float_prim` dispatch against, DRY).
///
/// **Non-vacuity, verified by mutation (2026-07-11, matching `reachability_stage1b.rs`'s own
/// precedent — no runtime toggle exists for a `const` name predicate, so this is a recorded
/// development-time verification, not an automated in-test one).** With `rhs_first_free_id`'s
/// `prim_name_is_recognized(name)` call temporarily reverted to the pre-fix `prim_family(name).is_some()`
/// (checkty.rs, the `Expr::Path` arm), this test was confirmed to **fail**: `infer_type` returns
/// `Err`, citing "Stage 2 (OQ-H1)" and naming `flt_neg` as the offending free identifier — the
/// exact DN-115 §4.1 over-refusal. Restoring `prim_name_is_recognized` makes it pass again.
#[test]
fn stage2_vsa_or_float_prim_rhs_now_accepted() {
    let mut e = env("nodule d;\nlower Base = 0b00000000;");
    e.lower_rules.insert(
        "NegRule".to_owned(),
        LowerDecl {
            name: "NegRule".to_owned(),
            params: vec![],
            value_params: vec![Param {
                name: "f".to_owned(),
                ty: float_ty(),
            }],
            rhs: LowerRhs::Expr(scall("flt_neg", vec![sv("f")])),
        },
    );
    let call = scall("NegRule", vec![sflt("1.5")]);
    let ty = infer_type(&e, &mut Vec::new(), &call).expect(
        "a rule RHS calling a float prim must be accepted — DN-115 §4.1/G1 (was over-refused)",
    );
    assert_eq!(ty, Ty::Float);

    with_main(&mut e, call);
    let elaborated =
        elaborate(&e, "main").expect("the accepted float-prim RHS must elaborate cleanly");
    match &elaborated {
        Node::Op { prim, args } => {
            assert_eq!(
                prim, "flt.neg",
                "expected the flt_neg kernel prim, got {prim:?}"
            );
            assert_eq!(args.len(), 1, "flt_neg takes exactly one operand");
        }
        other => panic!("expected a Node::Op(\"flt.neg\", ...), got {other:?}"),
    }
}

/// **DN-115 §6 item 3 (G1), VSA half.** The same over-refusal, exercised on a **VSA**-family prim
/// (`vsa_required_dim(items: Binary{W}, δ: Float) -> Binary{64}`, M-894) — chosen because it needs
/// no hypervector value construction (its operands are a plain `Binary{W}` magnitude and a
/// `Float`), keeping this fixture as small as the float one while still covering `VSA_PRIM_NAMES`
/// (a distinct dispatch set from `float_prim_name_is_recognized` — DRY does not imply the two
/// sets can't independently regress, so both get their own fixture).
#[test]
fn stage2_vsa_prim_rhs_now_accepted() {
    let mut e = env("nodule d;\nlower Base = 0b00000000;");
    e.lower_rules.insert(
        "DimRule".to_owned(),
        LowerDecl {
            name: "DimRule".to_owned(),
            params: vec![],
            value_params: vec![
                Param {
                    name: "items".to_owned(),
                    ty: bin_ty(16),
                },
                Param {
                    name: "delta".to_owned(),
                    ty: float_ty(),
                },
            ],
            rhs: LowerRhs::Expr(scall("vsa_required_dim", vec![sv("items"), sv("delta")])),
        },
    );
    let call = scall("DimRule", vec![sc16(1), sflt("0.01")]);
    let ty = infer_type(&e, &mut Vec::new(), &call).expect(
        "a rule RHS calling a VSA prim must be accepted — DN-115 §4.1/G1 (was over-refused)",
    );
    assert_eq!(ty, Ty::Binary(Width::Lit(64)));

    with_main(&mut e, call);
    let elaborated =
        elaborate(&e, "main").expect("the accepted VSA-prim RHS must elaborate cleanly");
    match &elaborated {
        Node::Op { prim, args } => {
            assert_eq!(
                prim, "vsa.required_dim",
                "expected the vsa.required_dim kernel prim, got {prim:?}"
            );
            assert_eq!(args.len(), 2, "vsa_required_dim takes exactly two operands");
        }
        other => panic!("expected a Node::Op(\"vsa.required_dim\", ...), got {other:?}"),
    }
}

// =============================================================================================
// 4. G2 — bare nullary-lower-rule value-position reference, now refused at check
// =============================================================================================

/// **DN-115 §6 item 4 / §4.2 (G2).** A rule RHS that references another nullary `lower`-rule in
/// **value** (non-call-head) position — `BareRef`'s RHS is the bare `NullaryHelper`, not a call
/// `NullaryHelper()`. Asserts the never-silent, Stage-2-labeled refusal fires at **check**.
///
/// **An honest correction to DN-115 §4.2's own "green at check, red at eval" framing — read this
/// module's own doc comment above before assuming this test demonstrates an elaboration-time
/// residual.** Adversarial verification (temporarily reverting the position-sensitivity this leaf
/// adds, then driving this exact fixture through `infer_type`) found the **pre-fix** gate ALSO
/// refuses this program — every time — just via a different, generic diagnostic:
/// `` `lower BareRef`'s RHS fails the IL-grammar / type check (DN-54 §4.1): unknown name
/// `NullaryHelper` `` (from `infer_expr_rule_rhs_type`'s own full RHS type-check, which always runs
/// immediately after the Stage-2 gate and — via `Cx::check_path`'s unconditional fallback — never
/// resolves a bare `lower`-rule reference regardless of what the gate decided). **So there is no
/// live accept/residual soundness gap for this exact shape**; what changes is diagnostic quality
/// (an early, clearly Stage-2-labeled refusal instead of a generic "unknown name" one) and
/// gate/mechanism self-consistency (the accepted-fragment claim in the gate's own doc comment now
/// matches what `Elab::app` can actually resolve) — both real, worthwhile fixes, verified below to
/// be exactly what changed (message text), not whether the program is refused (it always was).
#[test]
fn stage2_bare_nullary_lower_rule_value_position_refused() {
    let mut e = env("nodule d;\nlower Base = 0b00000000;");
    e.lower_rules.insert(
        "NullaryHelper".to_owned(),
        LowerDecl {
            name: "NullaryHelper".to_owned(),
            params: vec![],
            value_params: vec![],
            rhs: LowerRhs::Expr(sc(1)),
        },
    );
    e.lower_rules.insert(
        "BareRef".to_owned(),
        LowerDecl {
            name: "BareRef".to_owned(),
            params: vec![],
            value_params: vec![],
            rhs: LowerRhs::Expr(sv("NullaryHelper")),
        },
    );
    let call = scall("BareRef", vec![]);
    let err = infer_type(&e, &mut Vec::new(), &call).expect_err(
        "a bare (non-call) value-position reference to a nullary lower-rule must be refused at \
         check (M-1054 Stage 2/G2 — never accepted-then-residualed at elab)",
    );
    assert!(
        err.message.contains("value position")
            && err.message.contains("NullaryHelper")
            && err.message.contains("G2"),
        "expected the Stage-2/G2-labeled value-position diagnostic naming the offending \
         lower-rule, got: {}",
        err.message
    );
}

// =============================================================================================
// 5. Regression — the Stage-4 boundary stays refused (cross-nodule-shaped free id)
// =============================================================================================

/// **DN-115 §6 item 5.** A free RHS identifier that is not in *any* same-nodule registry (no
/// `fn`/ctor/prim/`lower`-rule of that name) — the shape a genuinely cross-nodule (Stage 4)
/// reference would present as, since this gate never consults `self.imports` (DN-116 §3.1; DN-115
/// §5). Stage 2 must **not** start accepting it. Companion to (and independent of)
/// `reachability_stage1b.rs::control_free_non_param_id_hits_stage2_residual`, whose own regression
/// coverage this leaf's `rhs_first_free_id` edits must not break (re-run, still green — see the
/// gate-level `cargo test` results this leaf's report cites).
#[test]
fn stage2_control_cross_nodule_shaped_free_id_stays_refused() {
    let mut e = env("nodule d;\nlower Base = 0b00000000;");
    e.lower_rules.insert(
        "UsesOtherNoduleSymbol".to_owned(),
        LowerDecl {
            name: "UsesOtherNoduleSymbol".to_owned(),
            params: vec![],
            value_params: vec![Param {
                name: "a".to_owned(),
                ty: bin_ty(8),
            }],
            // Shaped like a cross-nodule/qualified reference a real `use dep.other_nodule_fn`
            // import would resolve (Stage 4 / DN-113) — but no such nodule/import exists here, so
            // it is exactly as "genuinely free" as any other undeclared name from this gate's
            // point of view (it never consults `self.imports`).
            rhs: LowerRhs::Expr(scall("other_nodule_fn", vec![sv("a")])),
        },
    );
    let call = scall("UsesOtherNoduleSymbol", vec![sc(1)]);
    let err = infer_type(&e, &mut Vec::new(), &call).expect_err(
        "a cross-nodule-shaped free identifier must stay refused (Stage 2/OQ-H1; Stage 4/DN-113 \
         is where cross-nodule resolution belongs, not silently here)",
    );
    assert!(
        err.message.contains("Stage 2")
            && err.message.contains("OQ-H1")
            && err.message.contains("other_nodule_fn"),
        "expected the Stage-2 (OQ-H1) diagnostic naming the offending identifier, got: {}",
        err.message
    );
}
