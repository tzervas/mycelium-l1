use crate::ast::{
    Arm, BaseType, Expr, Item, Literal, LowerDecl, LowerRhs, Nodule, Param, Path, Pattern, TypeRef,
    WidthRef,
};
use crate::checkty::*;
use crate::parse;
use std::collections::BTreeMap;

fn env(src: &str) -> Env {
    check_nodule(&parse(src).expect("parses")).expect("checks")
}

/// Copilot #397: a function-typed LHS is parenthesized in `Ty::Fn`'s Display, so `(A => B) => C`
/// is unambiguous (not `A => B => C`); a simple `A => B` and the right-associative RHS stay bare.
/// The `Ty::Fn` Display arrow is `=>` (RFC-0037 D4 — the internal pretty-printer matches the surface).
#[test]
fn ty_fn_display_parenthesizes_a_function_typed_lhs() {
    let var = |n: &str| Ty::Var(n.to_owned());
    let simple = Ty::Fn(Box::new(var("A")), Box::new(var("B")));
    assert_eq!(format!("{simple}"), "A => B");
    let higher_order = Ty::Fn(
        Box::new(Ty::Fn(Box::new(var("A")), Box::new(var("B")))),
        Box::new(var("C")),
    );
    assert_eq!(format!("{higher_order}"), "(A => B) => C");
    let right = Ty::Fn(
        Box::new(var("A")),
        Box::new(Ty::Fn(Box::new(var("B")), Box::new(var("C")))),
    );
    assert_eq!(format!("{right}"), "A => B => C");
}

fn check_err(src: &str) -> CheckError {
    check_nodule(&parse(src).expect("parses")).expect_err("must fail to check")
}

// ---- M-662: the orphan-rule **arm** itself fires (non-vacuous), independent of resolution ----
//
// In the phylum-wide model a *resolvable* impl is never an orphan (resolving a name implies an
// in-phylum declaration ⇒ it is in the pub-blind coherence view). To prove the orphan ARM is not
// dead code, drive `register_instances` directly with a coherence view that does/does not contain
// the impl's heads — the mutant witness that the generalized check still fires + still accepts.

/// A one-`impl` nodule `impl Tr<Binary{8}> for Binary{8} { fn m(x: Binary{8}) -> Binary{8} = x }`
/// plus the registered `types`/`traits` for `Tr`, for driving `register_instances` directly.
fn impl_fixture() -> (
    BTreeMap<String, DataInfo>,
    BTreeMap<String, TraitInfo>,
    Nodule,
) {
    // Parse a phylum-of-one so the surface `impl` + `trait` are real AST (then strip the trait so
    // it is NOT in this nodule — the orphan scenario is "trait declared elsewhere / nowhere").
    let n = parse(
        "nodule d;\ntrait Tr[A] { fn m(x: A) => A; };\nimpl Tr[Binary{8}] for Binary{8} { fn m(x: Binary{8}) => Binary{8} = x; };",
    )
    .expect("parses");
    let mut types = BTreeMap::new();
    let p = prelude();
    types.insert(p.name.clone(), p);
    register_types(&mut types, &n).expect("types register");
    let traits = register_traits(&types, &n).expect("traits register");
    // The nodule passed to `register_instances` carries only the `impl` (its locality is decided
    // by the supplied coherence view, not by this nodule's own items — M-662).
    let impl_only = Nodule {
        path: n.path.clone(),
        std_sys: false,
        items: n
            .items
            .iter()
            .filter(|i| matches!(i, Item::Impl(_)))
            .cloned()
            .collect(),
    };
    (types, traits, impl_only)
}

#[test]
fn orphan_arm_rejects_when_neither_head_is_in_the_coherence_view() {
    // Empty coherence view ⇒ `Tr` is not phylum-local and `Binary{8}` is a primitive (always
    // phylum-owned) … so to force the orphan arm we must also deny the primitive. The primitive
    // arm is unconditional, so the genuine orphan case is a `for`-type that is a non-local DATA
    // type. Build that: `for Foreign` where `Foreign` is a registered data type NOT in coherence.
    let n = parse(
        "nodule d;\ntrait Tr[A] { fn m(x: A) => A; };\ntype Foreign = Mk(Binary{8});\nimpl Tr[Foreign] for Foreign { fn m(x: Foreign) => Foreign = x; };",
    )
    .expect("parses");
    let mut types = BTreeMap::new();
    let p = prelude();
    types.insert(p.name.clone(), p);
    register_types(&mut types, &n).expect("types");
    let traits = register_traits(&types, &n).expect("traits");
    let impl_only = Nodule {
        path: n.path.clone(),
        std_sys: false,
        items: n
            .items
            .iter()
            .filter(|i| matches!(i, Item::Impl(_)))
            .cloned()
            .collect(),
    };
    // Empty coherence view: neither `Tr` nor `Foreign` is phylum-local ⇒ orphan refusal (G2).
    let empty = CoherenceView::default();
    let err = register_instances(&types, &traits, &empty, &impl_only)
        .expect_err("an impl with neither head in the phylum must orphan-reject");
    assert!(
        err.message.contains("orphan"),
        "the orphan arm must fire, got: {}",
        err.message
    );
}

#[test]
fn orphan_arm_accepts_once_the_trait_is_in_the_coherence_view() {
    // The non-vacuous control: add `Tr` to the (pub-blind) coherence view ⇒ the SAME impl is now
    // in-phylum and registers. Proves the orphan generalization accepts a cross-nodule impl whose
    // trait is declared elsewhere in the phylum.
    let (types, traits, impl_only) = impl_fixture();
    let mut coh = CoherenceView::default();
    coh.traits.insert("Tr".to_owned());
    let instances = register_instances(&types, &traits, &coh, &impl_only)
        .expect("the impl registers once its trait is phylum-local");
    assert!(
        instances.contains_key(&("Tr".to_owned(), "Binary".to_owned())),
        "the instance is keyed by (trait, type-head)"
    );
}

// ---- M-666: `colony { hypha … }` type rule (RFC-0008 §4.7) ----

#[test]
fn a_colony_types_as_its_last_hypha() {
    // The colony's result type is the LAST hypha's (the RT2 sequentialization's observable). Here
    // the body must match the fn's `Binary{8}` return — the leading hyphae may be any type.
    let e = env(
        "nodule d;\nfn compute(x: Binary{8}) => Binary{8} = not(x);\nfn run() => Binary{8} = colony { hypha compute(0b0000_0001), hypha compute(0b0000_0010) };",
    );
    assert!(e.fn_decl("run").is_some());
}

#[test]
fn a_colony_whose_last_hypha_mistypes_is_an_explicit_error() {
    // The last hypha carries the colony's type, so a `Ternary` last hypha under a `Binary{8}`
    // return is a never-silent body mismatch (the bidirectional check catches it).
    let err = check_err(
        "nodule d;\nfn run() => Binary{8} = colony { hypha not(0b0000_0001), hypha 0t00+0 };",
    );
    assert!(
        err.message.contains("body") || err.message.contains("expected"),
        "a mistyped last hypha must be an explicit edge mismatch, got: {}",
        err.message
    );
}

#[test]
fn a_leading_hypha_that_does_not_type_check_is_still_an_error() {
    // RT4/I1: a leading hypha's refusal is never silently dropped — an ill-typed leading hypha
    // (an unknown name) fails the whole colony check.
    let err = check_err(
        "nodule d;\nfn run() => Binary{8} = colony { hypha nope(0b0), hypha not(0b0000_0001) };",
    );
    assert!(
        err.message.contains("nope") || err.message.contains("unknown"),
        "an ill-typed leading hypha must surface its error, got: {}",
        err.message
    );
}

#[test]
fn check_error_at_is_a_public_alias() {
    // `::at` builds the same value the private `new` does (the canonical site+message struct).
    assert_eq!(
        CheckError::at("main", "boom"),
        CheckError::new("main", "boom"),
    );
}

#[test]
fn env_getters_mirror_the_public_maps() {
    // A program with a data type and two functions, one recursive (so totality is filled).
    let e = env("nodule d;\ntype Nat = Z | S(Nat);\nfn count(n: Nat) => Nat = match n { Z => Z, S(m) => S(count(m)) };\nfn main() => Nat = count(S(Z));");
    // type_info ⇔ types.get
    assert_eq!(e.type_info("Nat"), e.types.get("Nat"));
    assert!(e.type_info("Nat").is_some());
    assert!(e.type_info("Nope").is_none());
    // fn_decl ⇔ fns.get
    assert_eq!(e.fn_decl("count"), e.fns.get("count"));
    assert!(e.fn_decl("count").is_some());
    assert!(e.fn_decl("absent").is_none());
    // fn_totality ⇔ totality.get (copied)
    assert_eq!(e.fn_totality("count"), e.totality.get("count").copied());
    assert!(e.fn_totality("count").is_some());
    assert!(e.fn_totality("absent").is_none());
}

mod depth_budget_tests {
    use crate::ast::{
        BaseType, Expr, FnDecl, FnSig, Item, Literal, Nodule, Path, TypeRef, WidthRef,
    };
    use crate::checkty::*;

    /// A `not(not(… not(0b0) …))` nest `depth` deep — built directly (the parser caps surface nesting
    /// at `MAX_EXPR_DEPTH`, so a direct AST is the way to exercise the *checker's* own budget).
    pub(crate) fn deep_not(depth: usize) -> Expr {
        let mut e = Expr::Lit(Literal::Bin("0".to_string()));
        for _ in 0..depth {
            e = Expr::App {
                head: Box::new(Expr::Path(Path(vec!["not".to_string()]))),
                args: vec![e],
            };
        }
        e
    }

    pub(crate) fn nodule_with_body(body: Expr) -> Nodule {
        Nodule {
            path: Path(vec!["d".to_string()]),
            std_sys: false,
            items: vec![Item::Fn(FnDecl {
                vis: crate::ast::Vis::Private,
                thaw: false,
                tier: None,
                sig: FnSig {
                    name: "main".to_string(),
                    params: vec![],
                    value_params: vec![],
                    ret: TypeRef {
                        base: BaseType::Binary(WidthRef::Lit(1)),
                        guarantee: None,
                    },
                    effects: vec![],
                    effect_budgets: std::collections::BTreeMap::new(),
                },
                body,
            })],
        }
    }

    #[test]
    fn the_depth_budget_trips_cleanly_and_just_under_it_succeeds() {
        // Just under the budget: the checker completes — the deep worker stack ([`mycelium_stack`])
        // absorbs `MAX_CHECK_DEPTH` levels with large margin (measured physical ceiling ≫ budget).
        let ok = check_nodule(&nodule_with_body(deep_not((MAX_CHECK_DEPTH - 5) as usize)));
        assert!(ok.is_ok(), "just under the budget should check ok: {ok:?}");
        // Past the budget: a clean, explicit refusal — never a host-stack overflow (banked guard 4).
        let err = check_nodule(&nodule_with_body(deep_not((MAX_CHECK_DEPTH + 50) as usize)))
            .expect_err("past the budget must refuse");
        assert!(
            err.message.contains("depth budget"),
            "expected the explicit depth-budget refusal, got: {}",
            err.message
        );
    }
}

// ---- DN-54 / M-812-cont: lower / derive validation (check-time) ------------------------------
//
// Note on RHS spelling: a `lower` rule's RHS is a real L1 expression, now **type-checked** (DN-54
// §4.1). The boolean constant is the prelude `Bool` constructor `True`/`False` (capitalised) — the
// lowercase `true`/`false` are *not* L1 names (M-812-cont discovery: the prior structural-only check
// accepted `lower X = true`, but that RHS is ill-typed — it now refuses, as it must).

/// A `lower` rule is registered in `Env::lower_rules` after a successful check.
#[test]
fn lower_rule_is_registered_in_env() {
    let e = env("nodule d;\nlower Trivial = True;");
    assert!(
        e.lower_rules.contains_key("Trivial"),
        "`lower Trivial = True` must register the rule name in Env::lower_rules"
    );
}

/// A parametric `lower` rule with one type param is registered. The RHS (`True`) does not mention
/// the type param, so it type-checks under the param scope (DN-54 §4.1).
#[test]
fn lower_rule_with_param_is_registered() {
    let e = env("nodule d;\nlower Wrap[T] = True;");
    assert!(
        e.lower_rules.contains_key("Wrap"),
        "`lower Wrap[T] = True` must register the rule name in Env::lower_rules"
    );
    assert_eq!(
        e.lower_rules["Wrap"].params,
        vec!["T".to_owned()],
        "params must be `[T]`"
    );
}

/// A `derive` application referencing a declared rule must check successfully.
#[test]
fn derive_referencing_known_rule_checks() {
    // `derive Trivial for Binary{8}` must check when `lower Trivial = True` is declared first.
    let _ = env("nodule d;\nlower Trivial = True;\nderive Trivial for Binary{8};");
}

/// A duplicate `lower` rule name in the same nodule is a never-silent check error (G2).
#[test]
fn lower_duplicate_rule_name_is_refused() {
    let err = check_err("nodule d;\nlower Trivial = True;\nlower Trivial = False;");
    assert!(
        err.message.contains("duplicate"),
        "expected duplicate-rule error, got: {}",
        err.message
    );
    assert!(
        err.message.contains("Trivial"),
        "expected rule name in error, got: {}",
        err.message
    );
}

/// Duplicate parameter names in `lower Name[T, T, …]` is a never-silent check error (G2).
#[test]
fn lower_duplicate_param_is_refused() {
    let err = check_err("nodule d;\nlower Bad[T, T] = True;");
    assert!(
        err.message.contains("duplicate"),
        "expected duplicate-param error, got: {}",
        err.message
    );
}

/// A `derive` referencing an unknown rule name is a never-silent check error (G2).
#[test]
fn derive_unknown_rule_name_is_refused() {
    let err = check_err("nodule d;\nderive UnknownRule for Binary{8};");
    assert!(
        err.message.contains("unknown"),
        "expected unknown-rule error, got: {}",
        err.message
    );
    assert!(
        err.message.contains("UnknownRule"),
        "expected rule name in error, got: {}",
        err.message
    );
}

// ---- DN-54 §4.1 IL-grammar RHS type-check (M-812-cont) ---------------------------------------

/// §4.1: an **ill-typed** `lower` RHS is refused at definition time (G2). `nope` is not a name in
/// scope, so the RHS fails the IL-grammar / type check — no `derive` site can invoke a broken rule.
#[test]
fn lower_rule_with_ill_typed_rhs_is_refused() {
    let err = check_err("nodule d;\nlower Bad = nope;");
    assert!(
        err.message.contains("IL-grammar") || err.message.contains("type check"),
        "expected an IL-grammar/type-check refusal, got: {}",
        err.message
    );
}

/// §4.1: a RHS that uses an in-scope name typed correctly is accepted — here a real L1 literal.
#[test]
fn lower_rule_with_well_typed_literal_rhs_is_accepted() {
    let e = env("nodule d;\nlower Eight = 0b0000_0001;");
    assert!(e.lower_rules.contains_key("Eight"));
}

// ---- DN-54 §4.6 purity: no `wild` in a lowering rule's RHS (M-812-cont) ----------------------

/// §4.6: a `lower` rule's RHS may not contain a `wild { … }` block — a generative-lowering rule is
/// a pure compile-time mechanism (the FFI gate is level-independent — DN-38 §3). The refusal is
/// **structural** and names DN-54 §4.6, so it holds even in an `@std-sys` nodule (G2). We assert
/// the refusal fires; the diagnostic cites §4.6 (it may surface as the explicit `wild`-refusal or,
/// for a non-`@std-sys` nodule, as the §4.1 type-check refusal of the `wild` gate — both are
/// never-silent rejections of the rule, which is the load-bearing property).
#[test]
fn lower_rule_with_wild_rhs_is_refused() {
    let err = check_err("nodule d;\nlower Impure = wild { host_call() };");
    assert!(
        err.message.contains("wild")
            || err.message.contains("§4.6")
            || err.message.contains("IL-grammar"),
        "expected a never-silent refusal of a `wild`-bearing lower rule, got: {}",
        err.message
    );
}

// ---- M-919 / DN-71 Model S: affine `Substrate` use-once checking is ACTIVE in a `lower` rule's
// RHS, not silently exempted (the extension-checker enactment of the ratified consume model) -----
//
// A `lower` rule has no value *parameters* (DN-54 §3.2), but its RHS can still legally introduce a
// `Substrate`-typed local by calling an already-checked helper `fn` (DN-54 §3.3 permits calls to
// other top-level fns). Before M-919 the RHS type-check ran with an **inert** affine tracker
// (reasoned only from "no value parameters ⇒ no Substrate in scope", which ignored this helper-fn
// path), so a double-consume of a derive-site-acquired `Substrate` type-checked silently. These
// tests pin the fix: the same double-consume diagnostic `check_fn_body` gives now fires inside a
// `lower` rule's RHS too (reject), and a single, correctly-affine use still checks (accept — no
// over-rejection regression).

/// A helper `fn` in an `@std-sys` nodule acquires a `Substrate` via `wild`; a `lower` rule's RHS
/// `let`-binds the result and uses it **twice** — this must be refused exactly as it would be
/// inside an ordinary function body (DN-71 Model S §4.2), not silently accepted because the RHS
/// check's tracker used to be permanently inert.
#[test]
fn lower_rule_rhs_double_consume_of_a_helper_acquired_substrate_is_refused() {
    let err = check_err(
        "nodule d @std-sys;\n\
         fn make() => Substrate{Sock} !{ffi} = wild { host_call() };\n\
         fn take(s: Substrate{Sock}) => Bool = True;\n\
         lower Bad = let s = make() in let _ = take(s) in take(s);",
    );
    assert!(
        err.message.contains("double-consume"),
        "expected the DN-71 Model S double-consume diagnostic to fire inside a `lower` rule's RHS, \
         got: {}",
        err.message
    );
    assert!(
        err.message.contains("DN-71"),
        "expected the diagnostic to cite DN-71 Model S, got: {}",
        err.message
    );
}

/// The single-use counterpart: the same helper-acquired `Substrate`, used exactly **once** in a
/// `lower` rule's RHS, checks cleanly — the M-919 fix must not over-reject legitimate single-use
/// derive-site code (no regression on the accept side).
#[test]
fn lower_rule_rhs_single_consume_of_a_helper_acquired_substrate_checks() {
    let e = env("nodule d @std-sys;\n\
         fn make() => Substrate{Sock} !{ffi} = wild { host_call() };\n\
         fn take(s: Substrate{Sock}) => Bool = True;\n\
         lower Good = let s = make() in take(s);");
    assert!(e.lower_rules.contains_key("Good"));
}

// ---- DN-54 §10 Model A attachment enactment (M-973): derive-site sibling-impl injection --------
//
// The DN-81 §10 ratified attachment model: an item-shaped `lower Name[T] = impl Trait for T { … }`
// rule, instantiated at each `derive Name for C` site, injects a concrete sibling `impl` BEFORE the
// instance + method-body passes — so coherence/orphan (`register_instances`) and the M-919 active
// affine tracker (`check_impl_methods`) cover it BY CONSTRUCTION. The DN-81 §10.4 correction makes
// the affine coverage a *deliberate* wiring deliverable (Pass-3e-before-Pass-3b, i.e. inject before
// the method-body pass), proven — not self-attested — by the derive-site double-consume reject test.

/// **Accept + injection:** an item-shaped rule derived for a concrete type injects a real sibling
/// `impl` that is registered as an instance (enters the coherence pass) and carries `derive`
/// provenance (OQ-A / DN-81 §6.5). The whole program checks.
#[test]
fn derive_item_rule_injects_a_checked_sibling_impl() {
    let e = env("nodule d;\n\
         trait Eq2 { fn eq2(x: Binary{8}) => Bool; };\n\
         lower MkEq[T] = impl Eq2 for T { fn eq2(x: Binary{8}) => Bool = True; };\n\
         derive MkEq for Binary{8};");
    // The derived impl is registered as a real trait instance — it went through `register_instances`
    // exactly like a hand-written `impl Eq2 for Binary{8}` (coherence by construction).
    assert!(
        e.instances.keys().any(|(tr, _)| tr == "Eq2"),
        "derived impl must register as an `Eq2` instance; instances = {:?}",
        e.instances.keys().collect::<Vec<_>>()
    );
    // Provenance (OQ-A): the injected impl records the rule it came from — distinguishable from a
    // hand-written impl (`Declared`, carried honestly — DN-81 §6.5).
    assert!(
        e.derived_provenance
            .values()
            .any(|(rule, _)| rule == "MkEq"),
        "derived impl must carry `(rule=MkEq, …)` provenance; got {:?}",
        e.derived_provenance
    );
}

/// **The load-bearing proof (DN-81 §10.4):** a derived impl whose method body double-consumes a
/// `Substrate` is refused, never-silently, citing DN-71 — the derive-site twin of
/// `lower_rule_rhs_double_consume_of_a_helper_acquired_substrate_is_refused`. This is the evidence
/// the affine wiring actually landed (the injected impl's body flows through `check_fn_body`'s active
/// M-919 tracker) and did **not** silently no-op: if the sibling injection ran *after* the method
/// body pass (or bypassed it), this double-consume would type-check silently. It does not.
#[test]
fn derive_site_double_consume_of_a_substrate_is_refused() {
    let err = check_err(
        "nodule d @std-sys;\n\
         fn make() => Substrate{Sock} !{ffi} = wild { host_call() };\n\
         fn take(s: Substrate{Sock}) => Bool = True;\n\
         trait Drain { fn drain(x: Binary{8}) => Bool !{ffi}; };\n\
         lower MkDrain[T] = impl Drain for T { \
         fn drain(x: Binary{8}) => Bool !{ffi} = let s = make() in let _ = take(s) in take(s); };\n\
         derive MkDrain for Binary{8};",
    );
    assert!(
        err.message.contains("double-consume"),
        "the derived impl's method body must be affine-checked (DN-81 §10.4 deliberate wiring), \
         firing the DN-71 double-consume refusal; got: {}",
        err.message
    );
    assert!(
        err.message.contains("DN-71"),
        "the double-consume diagnostic must cite DN-71 by name; got: {}",
        err.message
    );
}

/// **Content-key de-dup (ADR-003 / DN-54 §10.3):** two *identical* `derive`s of the same rule at the
/// same type collapse to a single injected impl — a no-op duplicate, not a coherence conflict. The
/// program checks (no overlapping-instance error), proving the dedup by content key `(trait, head)`.
#[test]
fn identical_derives_dedup_and_do_not_conflict() {
    let e = env("nodule d;\n\
         trait Eq2 { fn eq2(x: Binary{8}) => Bool; };\n\
         lower MkEq[T] = impl Eq2 for T { fn eq2(x: Binary{8}) => Bool = True; };\n\
         derive MkEq for Binary{8};\n\
         derive MkEq for Binary{8};");
    // Exactly one `Eq2` instance survives — the duplicate was de-duped, not double-registered.
    assert_eq!(
        e.instances.keys().filter(|(tr, _)| tr == "Eq2").count(),
        1,
        "identical derives must dedup to one instance; instances = {:?}",
        e.instances.keys().collect::<Vec<_>>()
    );
}

/// **Coherence by construction (DN-54 §10.2 crit. 3–4 / RFC-0019 §4.5):** a derived impl that
/// collides with a **hand-written** impl on the same `(trait, head)` is refused as an
/// overlapping-instance / global-uniqueness violation — never-silently — because the injected impl
/// enters the *same* `register_instances` coherence pass. (The orphan arm of that pass is proven
/// non-vacuous by the `register_instances`-direct orphan tests above; a resolvable derive in a
/// phylum-of-one is, by the M-662 resolvability property, never itself an orphan — so coherence
/// entry is demonstrated here via the overlap arm, the constructible case.)
#[test]
fn derived_impl_colliding_with_a_handwritten_impl_is_refused() {
    let err = check_err(
        "nodule d;\n\
         trait Eq2 { fn eq2(x: Binary{8}) => Bool; };\n\
         impl Eq2 for Binary{8} { fn eq2(x: Binary{8}) => Bool = False; };\n\
         lower MkEq[T] = impl Eq2 for T { fn eq2(x: Binary{8}) => Bool = True; };\n\
         derive MkEq for Binary{8};",
    );
    assert!(
        err.message.contains("overlapping") || err.message.contains("coherence"),
        "a derived impl overlapping a hand-written one must be a never-silent coherence refusal; \
         got: {}",
        err.message
    );
}

/// **OQ-B parser (DN-54 §10.1(b)):** an item-shaped RHS parses as an `impl` template. Confirm the
/// rule registers with an item-shaped RHS (the `impl_rhs()` accessor is `Some`), so the surface
/// really did accept `lower Name[T] = impl … for T`.
#[test]
fn item_shaped_lower_rule_parses_and_registers() {
    let e = env("nodule d;\n\
         trait Eq2 { fn eq2(x: Binary{8}) => Bool; };\n\
         lower MkEq[T] = impl Eq2 for T { fn eq2(x: Binary{8}) => Bool = True; };");
    let rule = e.lower_rules.get("MkEq").expect("rule registered");
    assert!(
        rule.impl_rhs().is_some(),
        "the rule must carry an item-shaped (`impl … for …`) RHS"
    );
}

/// A `derive` of an **item-shaped** rule whose parameter arity is not exactly one is a never-silent
/// refusal (Model-A sibling injection binds the single derive target to one rule param; multi-param
/// is OQ-C future — G2). A nullary item rule cannot bind the `derive` target.
#[test]
fn derive_of_a_nullary_item_rule_is_refused() {
    let err = check_err(
        "nodule d;\n\
         trait Eq2 { fn eq2(x: Binary{8}) => Bool; };\n\
         lower MkEq = impl Eq2 for Binary{8} { fn eq2(x: Binary{8}) => Bool = True; };\n\
         derive MkEq for Binary{8};",
    );
    assert!(
        err.message.contains("type parameter") || err.message.contains("parameter"),
        "a derive of a non-single-param item rule must be refused never-silently; got: {}",
        err.message
    );
}

// ---- DN-54 §4.2 cross-rule acyclicity (M-812-cont) ------------------------------------------

/// §4.2: a `lower` rule whose RHS references **itself** is refused (the trivial cycle) — the
/// lowering-rule graph must be acyclic so `derive` terminates (G2). `Loop`'s RHS is a bare path to
/// `Loop`, which is a registered rule name ⇒ a self-edge.
#[test]
fn lower_rule_self_reference_is_refused() {
    let err = check_err("nodule d;\nlower Loop = Loop;");
    assert!(
        err.message.contains("cycle") || err.message.contains("itself"),
        "expected an acyclicity (self-reference) refusal, got: {}",
        err.message
    );
}

/// §4.2: two `lower` rules that reference each other form a cycle and are refused (G2). `A`'s RHS
/// names `B` and `B`'s RHS names `A` — a 2-cycle in the rule graph.
#[test]
fn lower_rules_mutual_cycle_is_refused() {
    let err = check_err("nodule d;\nlower A = B;\nlower B = A;");
    assert!(
        err.message.contains("cycle"),
        "expected a mutual-cycle refusal, got: {}",
        err.message
    );
}

/// §4.2 regression (M-812-cont review): a single-segment RHS path that *resolves as a constructor*
/// is an ordinary value reference, not a rule expansion — so it must **not** count as a rule-graph
/// edge even when a `lower` rule shares the constructor's name. Here `Mk` is both a registered
/// constructor (of `T`) and a `lower` rule; `lower Mk`'s RHS constructs via the ctor `Mk`. Before the
/// ctor/fn exclusion in `check_lower_rule_acyclicity`, this was a **false-positive** self-cycle
/// ("`lower Mk` references itself"); the edge filter now narrows to true rule-refs, so the valid
/// program is accepted. Safe-direction (the filter only *removes* spurious edges; a genuine rule→rule
/// reference is, by §4.1 RHS type-check, never a ctor/fn of the same spelling).
#[test]
fn a_lower_rule_named_like_a_ctor_does_not_self_cycle() {
    let e = env("nodule d;\ntype T = Mk(Binary{8});\nlower Mk = Mk(0b0000_0001);");
    assert!(
        e.lower_rules.contains_key("Mk"),
        "the `lower Mk` rule registers despite sharing the ctor name `Mk` (no false self-cycle)"
    );
}

// ---- DN-54 §6 KC-3 + RHS elaboration to L0 (M-812-cont) -------------------------------------
//
// `low` (M-812) landed `lower`/`derive` as a structural-check-only **residual** (`crate::elab`
// never read `Env::lower_rules`, so a `derive` emitted no L0). M-812-cont lands the load-bearing
// safety + the elaboration: `elaborate_lower_rule` reads `Env::lower_rules` and lowers a rule's RHS
// to a closed L0 `Node` via the **same** path a hand-written nullary fn takes (so the §7
// differential holds by construction; honest tag `Empirical`). KC-3 is `Proven`-by-construction in
// the narrow checked sense: the elaborator's codomain is the *closed* enum `mycelium_core::Node`, so
// a rule cannot add a kernel node — see the assertion below.

/// **RHS elaboration**: a nullary, monomorphic `lower` rule now elaborates to a closed L0 `Node`
/// (no longer a residual). `elaborate_lower_rule` reads `Env::lower_rules` — the M-812-cont
/// completion. The rule's RHS lowers through the same path a hand-written fn would (DRY).
#[test]
fn lower_rule_elaborates_its_rhs_to_l0() {
    let e = env("nodule d;\nlower Eight = 0b0000_0001;");
    let node = crate::elab::elaborate_lower_rule(&e, "Eight").expect("rule RHS elaborates to L0");
    // The hand-lowered equivalent: a fn whose body is the same RHS.
    let hand = env("nodule d;\nfn eight() => Binary{8} = 0b0000_0001;");
    let hand_node = crate::elab::elaborate(&hand, "eight").expect("hand-lowered fn elaborates");
    assert_eq!(
        format!("{node:?}"),
        format!("{hand_node:?}"),
        "DN-54 §7 differential (structural): `elaborate_lower_rule(Eight)` must equal the \
         hand-lowered `fn eight() = 0b0000_0001` — they go through one code path"
    );
}

/// **KC-3 by construction (DN-54 §6)**: the elaborated L0 of a `lower` rule contains **only** the
/// frozen `mycelium_core::Node` variants — a rule adds no new kernel node. The codomain of the
/// elaborator is the closed `Node` enum (the type system is the checked side-condition), so this is
/// `Proven`-by-construction. We confirm the produced node is one of the frozen variants and that its
/// whole tree is in the AOT-lowerable v0 fragment (a total predicate over the frozen node set) — a
/// non-vacuous, never-silent assertion that no out-of-kernel form was synthesised.
#[test]
fn lower_rule_elaboration_adds_no_kernel_node_kc3() {
    let e = env("nodule d;\nlower Eight = 0b0000_0001;");
    let node = crate::elab::elaborate_lower_rule(&e, "Eight").expect("rule RHS elaborates");
    // The node is one of the frozen L0 variants (closed enum) — KC-3 by construction.
    assert!(
        node.is_aot_lowerable(),
        "the elaborated rule must lie entirely within the frozen v0 L0 node set (DN-54 §6 / KC-3)"
    );
}

/// An **unknown** rule name passed to `elaborate_lower_rule` is a never-silent `UnknownFn`, never a
/// fabricated artifact (G2).
#[test]
fn elaborate_lower_rule_unknown_is_refused() {
    let e = env("nodule d;\nlower Eight = 0b0000_0001;");
    let err = crate::elab::elaborate_lower_rule(&e, "Nope").expect_err("unknown rule must refuse");
    assert!(
        matches!(err, crate::elab::ElabError::UnknownFn(ref n) if n == "Nope"),
        "expected UnknownFn(\"Nope\"), got: {err:?}"
    );
}

/// **KC-3 by absence still holds for an unrelated entry**: a `lower`/`derive` pair adds no L0 to an
/// entry that does not reference it (the rule's L0 is produced *on demand* by
/// `elaborate_lower_rule`, never spliced into an unrelated `main`). This is the descendant of the
/// `low`-era residual guard test — the elaboration is now real, but it stays *out* of any entry
/// that does not derive it.
#[test]
fn lower_derive_items_add_no_l0_to_an_unrelated_entry() {
    let plain = env("nodule d;\nfn main() => Binary{8} = 0b00000001;");
    let with_rules = env(
        "nodule d;\nlower Trivial = True;\nderive Trivial for Binary{8};\nfn main() => Binary{8} = 0b00000001;",
    );
    let node_plain = crate::elab::elaborate(&plain, "main").expect("plain entry elaborates");
    let node_rules =
        crate::elab::elaborate(&with_rules, "main").expect("entry elaborates with rules present");
    assert_eq!(
        format!("{node_plain:?}"),
        format!("{node_rules:?}"),
        "a `lower`/`derive` pair must add NO L0 to an unrelated entry (DN-54 §6, KC-3 by absence; \
         a rule's L0 is produced on demand, not spliced into an unrelated `main`)"
    );
}

// -------------------------------------------------------------------------------------------
// M-1054 Stage 0/1b — expression-position sugar-rule call-site recognition (`Cx::check_sugar_call`,
// DN-110 §5-A / DN-116). Companion to `src/tests/elab.rs`'s `elaborate_lower_rule_with_args`
// matcher/guard tests (the L0 elab-phase half) and `src/tests/reachability_stage1b.rs` (the
// full-chain check→elab→eval reachability corpus). No surface grammar produces a non-empty
// `LowerDecl::value_params` yet (§8.6 is an open naming question), so every fixture here
// hand-constructs the rule and inserts it directly into a checked `Env` (white-box, matching the
// house test-layout convention).
//
// **Stage 0 → Stage 1b note (VR-5 — this banner is a claim too, kept current):** Stage 0 refused
// *every* recognized, arity/type-matched sugar call unconditionally (never returned `Ok`). Stage
// 1b (M-1054, DN-116) lands the accept path: a recognized call whose RHS also clears the Stage-2
// (OQ-H1 free-identifier) and Stage-3 (OQ-H4 affine) gates is now **accepted**, typed by
// `infer_expr_rule_rhs_type`. The arity-mismatch / type-mismatch / item-shaped-rule refusals below
// are unchanged by Stage 1b (those gates fire *before* the RHS is ever consulted); only the
// well-formed, gate-clearing case's outcome changed, from refuse to accept — see
// `stage1b_sugar_call_recognized_and_accepted` below (the direct former-Stage-0-refusal fixture,
// now updated to its Stage 1b outcome).
// -------------------------------------------------------------------------------------------

/// A `Binary{width}` surface `TypeRef` with no guarantee slot (the common fixture shape).
fn bin_ty(width: u32) -> TypeRef {
    TypeRef {
        base: BaseType::Binary(WidthRef::Lit(width)),
        guarantee: None,
    }
}

/// M-1054 Stage 0/1b fixture: register a value-parametric `lower` rule with `n` `Binary{8}` value
/// parameters `p0, p1, …` into `e` under `name`. The RHS (`0b0000_0001`, a bare `Binary{8}`
/// literal — the base nodule's own `Eight` rule's RHS, reused as an inert placeholder) is
/// irrelevant to the arity/type-mismatch/item-shaped-rule refusal tests below (those gates fire
/// *before* the RHS is ever consulted); it **is** read by the well-formed-call accept test
/// (`stage1b_sugar_call_recognized_and_accepted`), which is exactly why an inert literal — no
/// free identifiers, no affine binding — was chosen: it clears both Stage 1b gates trivially,
/// isolating that test to recognition + accept, not the gates (those get their own dedicated
/// fixtures below).
fn register_value_parametric_rule(e: &mut Env, name: &str, n: usize) {
    let rhs = e.lower_rules["Eight"].rhs.clone();
    e.lower_rules.insert(
        name.to_owned(),
        LowerDecl {
            name: name.to_owned(),
            params: vec![],
            value_params: (0..n)
                .map(|i| Param {
                    name: format!("p{i}"),
                    ty: bin_ty(8),
                })
                .collect(),
            rhs,
        },
    );
}

/// `Name(args...)` as an [`Expr::App`] over a single-segment [`Path`] — the exact shape
/// `Cx::check_app` dispatches on.
fn call_expr(name: &str, args: Vec<Expr>) -> Expr {
    Expr::App {
        head: Box::new(Expr::Path(Path(vec![name.to_owned()]))),
        args,
    }
}

/// An 8-bit binary literal argument (`Expr::Lit(Literal::Bin(..))`) — well-typed against
/// [`register_value_parametric_rule`]'s declared `Binary{8}` parameters.
fn bin8_lit(bits: &str) -> Expr {
    Expr::Lit(Literal::Bin(bits.to_owned()))
}

/// The base fixture env every Stage 0 checkty test starts from: one ordinary nullary `lower` rule
/// (`Eight`), checked the normal way, so [`register_value_parametric_rule`] has a real RHS to
/// clone and the env's other registries (types/fns/traits) are non-trivially populated.
fn stage0_base_env() -> Env {
    env("nodule d;\nlower Eight = 0b0000_0001;")
}

/// **Recognition + accept (M-1054 Stage 1b, DN-116).** A value-parametric sugar rule invoked with
/// the right arity and well-typed arguments, whose RHS clears both Stage 1b gates (this fixture's
/// inert `0b0000_0001` RHS trivially does — no free identifiers, no affine binding), is *recognized
/// and accepted* by `check_sugar_call`: `infer_type` now returns `Ok`, typed at the RHS's own
/// (fixed, def-time) result type, not "unknown function" (what this name would have produced
/// before Stage 0's recognition branch existed) and not the old, now-superseded Stage-0-only
/// "recognized but gated" refusal (see the module banner's Stage 0 → Stage 1b note above — this is
/// the direct updated fixture for that former test).
#[test]
fn stage1b_sugar_call_recognized_and_accepted() {
    let mut e = stage0_base_env();
    register_value_parametric_rule(&mut e, "Swap2", 2);
    let call = call_expr("Swap2", vec![bin8_lit("0000_0001"), bin8_lit("0000_0010")]);
    let ty = infer_type(&e, &mut Vec::new(), &call)
        .expect("a recognized, gate-clearing sugar call must be accepted (M-1054 Stage 1b)");
    assert_eq!(
        ty,
        Ty::Binary(Width::Lit(8)),
        "the accepted call's type must be the RHS's own def-time-fixed result type (Option B, DN-116), not the arguments' or anything else"
    );
}

// ---- Adversarial-verify finding 1 (2026-07-11, HIGH — fixed): a composite/nested-Substrate value
// parameter must hit the Stage-3 (OQ-H4) residual, not just a top-level `Substrate` type ----------
//
// `Self::ty_structurally_contains_substrate`'s own doc comment (`checkty.rs`) and DN-116 §3.2 carry
// the full narrative; these fixtures pin the regression + its non-vacuity.

/// A bare named-type `TypeRef` with no type arguments (`Data("Handle", [])` once resolved) —
/// mirrors [`bin_ty`] for a registered `Data` type.
fn named_ty(name: &str) -> TypeRef {
    TypeRef {
        base: BaseType::Named(name.to_owned(), vec![]),
        guarantee: None,
    }
}

/// Register a `Data` type `Handle` whose sole constructor `Wrap` wraps a `Substrate{gpu}` field —
/// the composite/nested-affine shape DN-116 §3.2's adversarial-verify finding names — directly into
/// `e.types` (white-box, matching [`register_value_parametric_rule`]'s own convention of hand-
/// building registry entries rather than routing through a surface grammar that does not yet exist
/// for this shape either).
fn register_handle_wrapping_substrate(e: &mut Env) {
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

/// Register a value-parametric `lower` rule `Dup(h: Handle)` whose RHS pattern-matches `h` **twice**
/// — each occurrence extracting the wrapped affine field via `match h { Wrap(s) => s }` — the exact
/// shape that splices the caller's single `h` argument node at two RHS occurrences (a real
/// double-consume hazard once expanded), and which the pre-fix top-level-only
/// `matches!(pty, Ty::Substrate(_))` check missed entirely (`pty` here is `Data("Handle", [])`, not
/// `Ty::Substrate`).
fn register_dup_handle_rule(e: &mut Env) {
    let extract = |v: &str| Expr::Match {
        scrutinee: Box::new(Expr::Path(Path(vec!["h".to_owned()]))),
        arms: vec![Arm {
            pattern: Pattern::Ctor("Wrap".to_owned(), vec![Pattern::Ident(v.to_owned())]),
            body: Expr::Path(Path(vec![v.to_owned()])),
        }],
    };
    e.lower_rules.insert(
        "Dup".to_owned(),
        LowerDecl {
            name: "Dup".to_owned(),
            params: vec![],
            value_params: vec![Param {
                name: "h".to_owned(),
                ty: named_ty("Handle"),
            }],
            rhs: LowerRhs::Expr(Expr::TupleLit(vec![extract("s1"), extract("s2")])),
        },
    );
}

/// **Superseded by Stage 3's real linear check (DN-117 §2, 2026-07-11) — was
/// `stage3_composite_substrate_field_value_param_is_refused`, asserted wholesale refusal of any
/// `Handle`-typed value parameter.** The composite/nested-affine hazard DN-116 §3.2 first found is
/// now caught *precisely* rather than refused wholesale: a `Handle`-typed value parameter used
/// **twice** in the RHS (`Dup`, extracting the wrapped field via two separate `match`es) is REFUSED
/// only when the caller's argument genuinely carries a duplicatable affine move — here, a freshly
/// constructed `Wrap(consume some_substrate)` whose inner `consume` gets spliced (and so
/// re-evaluated) at both RHS occurrences, exactly DN-117 §2/§5's R2 shape. Uses the
/// `#[cfg(test)]`-only active-tracker entry point ([`infer_type_with_active_affine`]) — the real
/// double-consume detection needs a live [`crate::affine::Tracker`], which the ordinary
/// `infer_type` (deliberately inert — post-check re-inference) cannot exercise; see that function's
/// own doc comment. The sibling case — passing a *pre-existing*, non-consuming `Handle`-typed local
/// and destructuring it twice (this test's OLD fixture) — is honestly documented as a **pre-existing,
/// Stage-3-independent** limitation of the landed M-919 tracker in
/// `stage3_prior_handle_alias_destructured_twice_is_a_known_pre_existing_gap`, below (verified via
/// an equivalent hand-written, non-sugar `fn` fixture: the landed tracker does not catch it either
/// — Stage 3 faithfully inherits, not regresses, hand-written code's own static posture, DN-117
/// §4.3).
#[test]
fn stage3_composite_substrate_field_value_param_refused_on_genuine_duplication() {
    let mut e = stage0_base_env();
    register_handle_wrapping_substrate(&mut e);
    register_dup_handle_rule(&mut e);
    let call = call_expr(
        "Dup",
        vec![Expr::App {
            head: Box::new(Expr::Path(Path(vec!["Wrap".to_owned()]))),
            args: vec![Expr::Consume(Box::new(Expr::Path(Path(vec![
                "some_substrate".to_owned(),
            ]))))],
        }],
    );
    let mut scope = vec![("some_substrate".to_owned(), Ty::Substrate("gpu".to_owned()))];
    let err = infer_type_with_active_affine(&e, &mut scope, &call).expect_err(
        "a composite (`Handle`)-typed value parameter used twice in the RHS, whose argument \
         genuinely carries a duplicated affine move once substituted, must be refused \
         (M-1054 Stage 3/OQ-H4/DN-117)",
    );
    assert!(
        err.message.contains("Stage 3") && err.message.contains("OQ-H4"),
        "expected the Stage-3 (OQ-H4) diagnostic, got: {}",
        err.message
    );
    assert!(
        err.message.contains("double-consume"),
        "expected the underlying double-consume diagnostic to be named, got: {}",
        err.message
    );
}

/// **Honest, Stage-3-independent limitation (DN-117 §4.3's "matches hand-written code's own static
/// posture exactly" — verified, not assumed).** Referencing the *same*, pre-existing `Handle`-typed
/// local twice and destructuring each occurrence independently is accepted — by an equivalent
/// **ordinary, non-sugar** `fn` too (each `match`'s field-capture creates its own fresh, independent
/// tracker slot, DN-71 §4.2; the landed tracker does not itself track a composite value's identity
/// across two separate destructurings of it — a real, pre-existing M-919 gap, not something this
/// leaf introduces or is asked to close). This is *not* the same shape as
/// `stage3_composite_substrate_field_value_param_refused_on_genuine_duplication`'s R2 fixture
/// (a *freshly constructed* `Wrap(consume s)` argument, re-evaluated by the splice) — this fixture
/// aliases a *pre-existing* binding instead, which the tracker only ever tracks by scope index, not
/// by "this Data value's wrapped field came from the same acquisition."
#[test]
fn stage3_prior_handle_alias_destructured_twice_is_a_known_pre_existing_gap() {
    // The ordinary hand-written equivalent, independent of any sugar rule at all — confirms this is
    // not a Stage-3-introduced regression.
    check_nodule(
        &parse(
            "nodule d;\ntype Handle = Wrap(Substrate{gpu});\n\
             fn f(h: Handle) => (Substrate{gpu}, Substrate{gpu}) = \
             (match h { Wrap(s1) => s1 }, match h { Wrap(s2) => s2 });",
        )
        .expect("parses"),
    )
    .expect(
        "the ordinary hand-written fn (no sugar involved) is ALSO accepted by the landed tracker \
         — grounding that this is a pre-existing gap, not a Stage-3 regression",
    );

    // The value-parametric-sugar analogue, over the same real Cx pipeline (the exact assertion this
    // test module makes for the composite case): a bare, pre-existing `Handle`-typed local, passed
    // once, destructured at both RHS occurrences.
    let mut e = stage0_base_env();
    register_handle_wrapping_substrate(&mut e);
    register_dup_handle_rule(&mut e);
    let call = call_expr(
        "Dup",
        vec![Expr::Path(Path(vec!["some_handle".to_owned()]))],
    );
    let mut scope = vec![(
        "some_handle".to_owned(),
        Ty::Data("Handle".to_owned(), vec![]),
    )];
    infer_type_with_active_affine(&e, &mut scope, &call).expect(
        "aliasing a pre-existing Handle-typed local across two independent destructurings is \
         accepted, matching the equivalent hand-written fn's own (pre-existing) posture — DN-117 \
         §4.3: Stage 3 must not be *stricter* than hand-written code, only as precise",
    );
}

/// **Non-vacuity — a plain, non-affine `Data` type must stay accepted (no over-refusal, VR-5).** A
/// `Handle2` type structurally identical to `Handle` but wrapping a `Binary{8}` field instead of
/// `Substrate` must NOT trip the Stage-3 gate — proving the recursive structural walk refuses only
/// what actually reaches a `Substrate`, not every `Data`-typed value parameter.
#[test]
fn stage3_composite_non_affine_data_value_param_still_accepted() {
    let mut e = stage0_base_env();
    e.types.insert(
        "Handle2".to_owned(),
        DataInfo {
            home: String::new(), // DN-112/M-1036: test fixture, unqualified/bare identity
            name: "Handle2".to_owned(),
            params: vec![],
            ctors: vec![CtorInfo {
                name: "Wrap2".to_owned(),
                fields: vec![Ty::Binary(Width::Lit(8))],
            }],
        },
    );
    e.lower_rules.insert(
        "DupOk".to_owned(),
        LowerDecl {
            name: "DupOk".to_owned(),
            params: vec![],
            value_params: vec![Param {
                name: "h".to_owned(),
                ty: named_ty("Handle2"),
            }],
            rhs: LowerRhs::Expr(Expr::Path(Path(vec!["h".to_owned()]))),
        },
    );
    let call = call_expr(
        "DupOk",
        vec![Expr::Path(Path(vec!["some_handle2".to_owned()]))],
    );
    let mut scope = vec![(
        "some_handle2".to_owned(),
        Ty::Data("Handle2".to_owned(), vec![]),
    )];
    let ty = infer_type(&e, &mut scope, &call)
        .expect("a plain, non-affine `Data`-typed value parameter must not be refused");
    assert_eq!(ty, Ty::Data("Handle2".to_owned(), vec![]));
}

/// **Termination — a recursive `Data` type with no affine field must still accept (never a silent
/// infinite loop, G2).** `Ring = Node(Ring)` is self-referential; the structural walk's on-path
/// `visiting` cycle-cut must terminate on it without finding a (nonexistent) `Substrate`.
#[test]
fn stage3_recursive_non_affine_data_terminates_and_accepts() {
    let mut e = stage0_base_env();
    e.types.insert(
        "Ring".to_owned(),
        DataInfo {
            home: String::new(), // DN-112/M-1036: test fixture, unqualified/bare identity
            name: "Ring".to_owned(),
            params: vec![],
            ctors: vec![
                CtorInfo {
                    name: "Node".to_owned(),
                    fields: vec![Ty::Data("Ring".to_owned(), vec![])],
                },
                CtorInfo {
                    name: "Leaf".to_owned(),
                    fields: vec![],
                },
            ],
        },
    );
    e.lower_rules.insert(
        "RingId".to_owned(),
        LowerDecl {
            name: "RingId".to_owned(),
            params: vec![],
            value_params: vec![Param {
                name: "r".to_owned(),
                ty: named_ty("Ring"),
            }],
            rhs: LowerRhs::Expr(Expr::Path(Path(vec!["r".to_owned()]))),
        },
    );
    let call = call_expr(
        "RingId",
        vec![Expr::Path(Path(vec!["some_ring".to_owned()]))],
    );
    let mut scope = vec![("some_ring".to_owned(), Ty::Data("Ring".to_owned(), vec![]))];
    let ty = infer_type(&e, &mut scope, &call)
        .expect("a recursive, non-affine `Data`-typed value parameter must not be refused, and the structural walk must terminate rather than loop");
    assert_eq!(ty, Ty::Data("Ring".to_owned(), vec![]));
}

/// **Arity mismatch is refused, never silently.** `Swap2` declares 2 value parameters; calling it
/// with 1 argument is a distinct, named refusal — not the Stage-0 gate message (which only fires
/// after a *successful* match) and not "unknown function".
#[test]
fn stage0_sugar_call_arity_mismatch_is_refused() {
    let mut e = stage0_base_env();
    register_value_parametric_rule(&mut e, "Swap2", 2);
    let call = call_expr("Swap2", vec![bin8_lit("0000_0001")]); // only 1 of 2 declared params
    let err = infer_type(&e, &mut Vec::new(), &call).expect_err("arity mismatch must be refused");
    assert!(
        err.message.contains("arity mismatch"),
        "expected the arity-mismatch diagnostic, got: {}",
        err.message
    );
}

/// **A mismatched argument type is refused, never silently.** `Swap2`'s parameters are
/// `Binary{8}`; a `Ternary{6}` argument must be a named per-parameter type refusal.
#[test]
fn stage0_sugar_call_type_mismatch_is_refused() {
    let mut e = stage0_base_env();
    register_value_parametric_rule(&mut e, "Swap2", 2);
    let bad_ternary = Expr::Lit(Literal::Trit("+0-+0-".to_owned()));
    let call = call_expr("Swap2", vec![bad_ternary, bin8_lit("0000_0010")]);
    let err = infer_type(&e, &mut Vec::new(), &call).expect_err("a type mismatch must be refused");
    assert!(
        err.message.contains("p0"),
        "expected the mismatch to name the failing parameter (`p0`), got: {}",
        err.message
    );
}

/// **An item-shaped rule has no expression-position form at all.** Calling `derive`-only rule
/// `L2` (RHS `impl Trait for T { … }`) as `L2(…)` is a distinct, clearer refusal — never falls
/// through to arity matching against a nonexistent value-param list.
#[test]
fn stage0_item_shaped_rule_has_no_expression_form() {
    let mut e = stage0_base_env();
    e.lower_rules.insert(
        "ItemRule".to_owned(),
        LowerDecl {
            name: "ItemRule".to_owned(),
            params: vec!["T".to_owned()],
            value_params: vec![],
            rhs: LowerRhs::Impl(crate::ast::ImplDecl {
                trait_name: "Cmp".to_owned(),
                trait_args: vec![],
                for_ty: crate::ast::TypeRef {
                    base: crate::ast::BaseType::Named("T".to_owned(), vec![]),
                    guarantee: None,
                },
                methods: vec![],
            }),
        },
    );
    let call = call_expr("ItemRule", vec![]);
    let err = infer_type(&e, &mut Vec::new(), &call).expect_err("item-shaped rule must refuse");
    assert!(
        err.message.contains("item-shaped") && err.message.contains("derive"),
        "expected the item-shaped-rule refusal naming `derive`, got: {}",
        err.message
    );
}

/// **Regression** (M-1054 Stage 0 DoD): registering M-1054's Stage 0 machinery must not change
/// how an ordinary nodule with a real `lower`/`derive` pair checks — `check_nodule` on the exact
/// fixture `lower_derive_items_add_no_l0_to_an_unrelated_entry` uses above must still succeed and
/// register the rule exactly as before (no new call-site recognition is reachable from the
/// *checker's own* full-nodule pipeline, since the parser never emits a non-empty
/// `value_params`).
#[test]
fn stage0_ordinary_lower_derive_nodule_still_checks_unchanged() {
    let e = env(
        "nodule d;\nlower Trivial = True;\nderive Trivial for Binary{8};\nfn main() => Binary{8} = 0b00000001;",
    );
    assert!(e.lower_rules.contains_key("Trivial"));
    assert!(
        e.lower_rules["Trivial"].value_params.is_empty(),
        "the parser must never populate value_params (no surface grammar yet — DN-110 §8.6)"
    );
}

// ---- M-826: v0 tuple/product type + lift f(x)(y) chained application ----

/// A tuple literal `(a, b)` checks to `Tuple$2<Nat, Nat>` — the synthetic type is pre-registered
/// by `register_types`, and the checked env contains the `Tuple$2` DataInfo (KC-3: no new L0 node).
/// Guarantee: `Empirical` (round-trip tested in `differential.rs`).
#[test]
fn tuple_literal_checks_to_synthetic_tuple_type() {
    let e = env("nodule d;\ntype Nat = Z | S(Nat);\nfn main() => (Nat, Nat) = (Z, S(Z));");
    // The synthetic `Tuple$2` type must be in the env's type registry.
    assert!(
        e.types.contains_key("Tuple$2"),
        "Tuple$2 must be registered in the env after checking a 2-tuple literal (M-826)"
    );
}

/// A tuple type in a function signature is resolved: `(Nat, Nat) => Nat` works as a parameter type.
#[test]
fn tuple_type_in_fn_signature_checks() {
    env(
        "nodule d;\ntype Nat = Z | S(Nat);\nfn fst(t: (Nat, Nat)) => Nat = match t { (a, _) => a };\nfn main() => Nat = fst((S(Z), Z));",
    );
}

/// A tuple pattern `(x, y)` destructures a 2-tuple in a `match` arm (G2: never silent on type mismatch).
#[test]
fn tuple_pattern_destructures_in_match() {
    env(
        "nodule d;\ntype Nat = Z | S(Nat);\nfn snd(t: (Nat, Nat)) => Nat = match t { (_, b) => b };\nfn main() => Nat = snd((Z, S(Z)));",
    );
}

/// A 3-tuple literal and 3-tuple type check (arity ≥ 2 is the surface contract).
#[test]
fn triple_tuple_literal_checks() {
    env(
        "nodule d;\ntype Nat = Z | S(Nat);\nfn mid(t: (Nat, Nat, Nat)) => Nat = match t { (_, b, _) => b };\nfn main() => Nat = mid((Z, S(Z), Z));",
    );
}

/// A type mismatch in a tuple literal is an explicit, never-silent error (G2).
#[test]
fn tuple_element_type_mismatch_is_explicit_error() {
    let err = check_err("nodule d;\ntype Nat = Z | S(Nat);\nfn main() => (Nat, Nat) = (Z, True);");
    assert!(
        !err.message.is_empty(),
        "a tuple element type mismatch must produce an explicit error (G2 — never silent, M-826)"
    );
}

/// `f(x)(y)` — chained (HOF) application where the head `f(x)` has function type `Nat -> Nat`.
/// Part 2 of M-826: lifting the first-order application restriction (RFC-0007 §4.4 narrowing).
#[test]
fn chained_hof_application_f_x_y_checks() {
    // `apply` takes a function `Nat -> Nat` and returns it; `apply(succ)(Z)` chains application.
    env(
        "nodule d;\ntype Nat = Z | S(Nat);\nfn succ(n: Nat) => Nat = S(n);\nfn apply(f: Nat => Nat) => (Nat => Nat) = f;\nfn main() => Nat = apply(succ)(Z);",
    );
}

/// A non-function head in application position is an explicit error (G2 — never silent, M-826).
#[test]
fn non_function_head_in_app_is_explicit_error() {
    let err = check_err("nodule d;\ntype Nat = Z | S(Nat);\nfn main() => Nat = Z(Z);");
    // Z is a nullary constructor; calling it like a function (Z(Z)) should fail.
    assert!(
        !err.message.is_empty(),
        "applying a non-function value must produce an explicit error (G2 — never silent, M-826)"
    );
}

// ---- RFC-0020 §9 / R20-Q3: or-patterns — checker desugar + binding-consistency ----------------

/// A two-alternative or-pattern desugars to two plain arms sharing the same body. The checker
/// expands `A | B => e` into `A => e, B => e` before coverage/exhaustiveness analysis.
/// After desugar the checked program is functionally equivalent to writing the arms separately
/// (KC-3: zero L0 kernel growth — uses the existing Match/Alt machinery).
#[test]
fn or_pattern_two_alts_checks_and_desugars() {
    // `Zero | One => 0b1` is the only arm — exhaustive because both constructors are covered.
    let _ = env(
        "nodule d;\ntype Bit = Zero | One;\nfn classify(b: Bit) => Binary{1} = \
         match b { Zero | One => 0b1 };",
    );
}

/// A three-alternative or-pattern with a wildcard arm checks exhaustively.
#[test]
fn or_pattern_three_alts_checks() {
    let _ = env(
        "nodule d;\ntype Sign = Neg | Zero | Pos;\nfn is_zero(s: Sign) => Binary{1} = \
         match s { Zero => 0b1, Neg | Pos => 0b0 };",
    );
}

/// Or-pattern is equivalent to separate arms: `A | B => e` must type-check to the same result as
/// `A => e, B => e`. Both programs must be accepted by the checker.
#[test]
fn or_pattern_equivalent_to_two_separate_arms() {
    // or-pattern form
    let _ = env(
        "nodule d;\ntype Bit = Zero | One;\nfn f(b: Bit) => Binary{2} = \
         match b { Zero | One => 0b00 };",
    );
    // explicit two-arm form (same semantics)
    let _ = env(
        "nodule d;\ntype Bit = Zero | One;\nfn f(b: Bit) => Binary{2} = \
         match b { Zero => 0b00, One => 0b00 };",
    );
}

/// Binding-consistency check (G2 / never-silent): every alternative of an or-pattern must bind
/// the same set of variable names at the same types. A mismatch is a `CheckError`.
#[test]
fn or_pattern_binding_inconsistency_is_refused() {
    // `Pair` has two fields; `Mk(a, b) | Mk(a, _)` binds `{a, b}` vs `{a}` — mismatch.
    let err = check_err(
        "nodule d;\ntype Pair = Mk(Binary{8}, Binary{8});\nfn f(p: Pair) => Binary{8} = \
         match p { Mk(a, b) | Mk(a, _) => a };",
    );
    // The error must cite or-pattern binding consistency (G2).
    assert!(
        err.message.contains("or-pattern") || err.message.contains("alternative"),
        "expected binding-consistency error, got: {}",
        err.message
    );
}

/// Or-pattern bodies must agree on type. `Zero | One => 0b1` is a single body (correct);
/// separate arms with different body types is an arm-agreement error (different code path).
/// This test pins that the or-pattern desugared arms still produce a check-time type error when
/// the ARM types disagree (no separate body per alternative — the body is shared, so this is
/// actually impossible via or-pattern alone; test the separate-arm disagreement path instead).
#[test]
fn or_pattern_arms_type_disagreement_is_refused() {
    // The two arms have different result types: `Zero => 0b0` (Binary{8}), `One => 0t0` (Ternary{1}).
    let err = check_err(
        "nodule d;\ntype Bit = Zero | One;\nfn f(b: Bit) => Binary{8} = \
         match b { Zero => 0b0000_0000, One => 0t0 };",
    );
    assert!(
        err.message.contains("disagree") || err.message.contains("arm"),
        "expected arm-type-disagreement error, got: {}",
        err.message
    );
}

// ---- RFC-0020 §9 / R20-Q5: list-literal bidirectional inference from context ------------------
//
// R20-Q5 status (RFC-0020 §9 changelog):
// - **Already works**: a list literal `[e1, …]` checked against an expected `Seq{T, N}` type (from
//   a function parameter annotation, a `let` binding annotation, or a return-type context) receives
//   the element type `T` bidirectionally — bare-decimal literals resolve to `T`, heterogeneous
//   elements are refused (never-silent, G2).
// - **Still conservative**: the two-pass feedback from a `for`-body constraining the list-literal
//   spine's element type (the original R20-Q5 circular case) is NOT implemented — a list literal
//   used as the `xs` spine of a `for` loop with only body-derived element-type information still
//   requires an explicit element type (via explicit literals or a typed parameter). The two-pass
//   relaxation remains a tracked improvement (RFC-0020 §9).
//
// These tests pin the already-working cases and the conservative rejection.

/// A list literal checked against a `Seq{Binary{8}, N}` parameter type: the `Binary{8}` element
/// type flows into the literal bidirectionally (element type from context, not bottom-up). Bare
/// explicit bit-literals work; the function return type drives the whole flow.
#[test]
fn list_literal_element_type_from_seq_param_context() {
    // `xs: Seq{Binary{8}, 3}` — the call site `[0b1111_0000, 0b0000_1111, 0b1010_1010]` is typed
    // against `Seq{Binary{8}, 3}`: the element type `Binary{8}` flows into each element
    // bidirectionally (the list literal's `expected` is `Some(Seq{Binary{8}, 3})`).
    let _ = env(
        "nodule d;\nfn id(xs: Seq{Binary{8}, 3}) => Seq{Binary{8}, 3} = xs;\n\
         fn main() => Seq{Binary{8}, 3} = id([0b1111_0000, 0b0000_1111, 0b1010_1010]);",
    );
}

/// A list literal whose length disagrees with the expected `Seq{T, N}` length is a never-silent
/// check error (G2 / RFC-0032 D3 — never a silent truncation or padding).
#[test]
fn list_literal_length_mismatch_against_expected_seq_is_refused() {
    let err = check_err(
        "nodule d;\nfn id(xs: Seq{Binary{8}, 3}) => Seq{Binary{8}, 3} = xs;\n\
         fn main() => Seq{Binary{8}, 3} = id([0b1111_0000, 0b0000_1111]);",
    );
    assert!(
        err.message.contains("length") || err.message.contains("Seq"),
        "expected length-mismatch error, got: {}",
        err.message
    );
}

/// A heterogeneous list literal (mixing `Binary{8}` and `Ternary{1}` elements) is a never-silent
/// check error (G2 / RFC-0032 D3 — list elements must be homogeneous).
#[test]
fn list_literal_heterogeneous_elements_are_refused() {
    let err = check_err(
        "nodule d;\nfn f(xs: Seq{Binary{8}, 2}) => Seq{Binary{8}, 2} = xs;\n\
         fn main() => Seq{Binary{8}, 2} = f([0b0000_0000, 0t0]);",
    );
    assert!(
        err.message.contains("element")
            || err.message.contains("homogeneous")
            || err.message.contains("type"),
        "expected element-heterogeneity error, got: {}",
        err.message
    );
}

/// An empty list literal `[]` with no expected `Seq{T, N}` type and no elements is a never-silent
/// error — the element type is undetermined (G2 / RFC-0032 D3).
#[test]
fn empty_list_literal_without_context_is_refused() {
    let err = check_err("nodule d;\nfn f() => Binary{8} = let _ = [] in 0b0000_0000;");
    assert!(
        err.message.contains("empty")
            || err.message.contains("element type")
            || err.message.contains("Seq"),
        "expected undetermined-element-type error for empty `[]`, got: {}",
        err.message
    );
}

// ---------------------------------------------------------------------------------------------
// DN-112 Rank 1 / M-1036 — the nodule-qualified type-identity helpers themselves (white-box unit
// tests; the end-to-end integration witnesses live in `tests/ctor_seal.rs`, which cannot reach
// these `pub(crate)` helpers directly).
// ---------------------------------------------------------------------------------------------

#[test]
fn qualify_type_name_qualifies_a_real_home_and_stays_bare_for_prelude_or_empty() {
    assert_eq!(qualify_type_name("a", "T"), "a::T");
    assert_eq!(qualify_type_name("a.b", "T"), "a.b::T");
    // The reserved/single-home exemption (DN-112 §9 invariant i): PRELUDE_HOME never qualifies.
    assert_eq!(qualify_type_name(PRELUDE_HOME, "Bool"), "Bool");
    // An empty (path-less/anonymous nodule) home also stays bare (the documented narrow residual —
    // see `nodule_home`'s doc comment).
    assert_eq!(qualify_type_name("", "T"), "T");
}

#[test]
fn ty_local_name_strips_exactly_the_last_qualifier_segment() {
    assert_eq!(ty_local_name("a::T"), "T");
    assert_eq!(ty_local_name("a.b::T"), "T");
    // Unqualified input is returned unchanged (the common, single-nodule case — a pure passthrough).
    assert_eq!(ty_local_name("T"), "T");
    assert_eq!(ty_local_name("Bool"), "Bool");
}

#[test]
fn qualify_then_ty_local_name_round_trips_for_any_real_home() {
    // The pair is a round-trip inverse for any non-reserved, non-empty home — the invariant
    // `resolve_ty`'s stamping site relies on (`ty_local_name(name)` before re-qualifying, so a
    // round-trip through an already-qualified name never double-qualifies).
    for (home, bare) in [("a", "T"), ("a.b.c", "Widget"), ("solo_nodule", "X")] {
        let qualified = qualify_type_name(home, bare);
        assert_eq!(ty_local_name(&qualified), bare);
    }
}

#[test]
fn lookup_data_finds_a_bare_key_directly_and_a_qualified_name_via_local_fallback() {
    let mut types: BTreeMap<String, DataInfo> = BTreeMap::new();
    types.insert(
        "T".to_owned(),
        DataInfo {
            name: "T".to_owned(),
            home: "a".to_owned(),
            params: vec![],
            ctors: vec![],
        },
    );
    // The exact (bare) key — the surface-resolution common case.
    assert!(lookup_data(&types, "T").is_some());
    // A qualified name falls back to its local part (the post-check consumer case —
    // `crate::mono`/`crate::elab`/`crate::decision`/`crate::usefulness`).
    assert!(lookup_data(&types, "a::T").is_some());
    assert_eq!(lookup_data(&types, "a::T").unwrap().home, "a");
    // A genuinely unknown name (exact AND local-fallback both miss) is `None` — never a guess.
    assert!(lookup_data(&types, "b::U").is_none());
    assert!(lookup_data(&types, "U").is_none());
}

#[test]
fn nodule_home_joins_a_dotted_path_and_is_empty_for_a_path_less_nodule() {
    assert_eq!(nodule_home(&crate::ast::Path(vec!["a".to_owned()])), "a");
    assert_eq!(
        nodule_home(&crate::ast::Path(vec!["a".to_owned(), "b".to_owned()])),
        "a.b"
    );
    assert_eq!(nodule_home(&crate::ast::Path(vec![])), "");
}

/// **DN-112 Rank 1 / M-1036 — the seal becomes real.** A minimal, direct check of the exploit
/// program's core shape at the `check_nodule`/`Env` level (the fuller cross-nodule differential
/// lives in `tests/ctor_seal.rs`): two nodules each declaring a same-named `T`, with a value of
/// one home's `T` passed where the other home's `T` is expected, is a type mismatch naming both
/// qualified identities — never a silent same-bare-name pass.
#[test]
fn cross_nodule_same_bare_name_types_are_distinct_in_a_checked_signature() {
    let src = "phylum p\n\
               nodule a;\n\
               pub type T = Mk(Binary{8});\n\
               pub fn take(x: T) => Binary{8} = match x { Mk(v) => v };\n\
               nodule b;\n\
               use a.take;\n\
               type T = Mk(Binary{8});\n\
               fn make() => T = Mk(0b0000_0000);\n\
               pub fn bad() => Binary{8} = take(make());";
    let ph = crate::parse::parse_phylum(src).expect("parses as a phylum");
    let err = check_phylum(&ph).expect_err("a::T and b::T must not unify");
    assert!(
        err.message.contains("a::T") && err.message.contains("b::T"),
        "the mismatch names BOTH qualified identities; got: {}",
        err.message
    );
}
