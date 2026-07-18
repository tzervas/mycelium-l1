//! **Cross-phylum import/resolution subsystem** (DN-113 Rank 1 / M-1060) integration tests — the
//! v1 checked-and-linked (whole-graph, content-pinned, CHECK-TIME) mechanism: the `::`
//! phylum-boundary `use dep::a.b.Item` reference, the additive `Phyla`/`ResolvedPhylum` dependency
//! set, layering over the existing `Exports`/`resolve_imports`/`PhylumEnv::link` machinery (DRY, no
//! second linker), and the acyclicity-enforcing multi-phylum graph builder (`phyla::PhylumNode` /
//! `phyla::build_phyla_graph`).
//!
//! Every "the check fires" test is paired with a **control** proving the check is not vacuous (the
//! same shape, minus the violation, is accepted) — the M-662/DN-104/DN-112 precedent this subsystem
//! extends one level up, across the phylum boundary. Honesty (VR-5): every guarantee here is
//! `Empirical` (checked by these witnesses, never `Proven` — no discharged theorem backs it).

use mycelium_core::ContentHash;
use mycelium_l1::phyla::{build_phyla_graph, PhylumNode};
use mycelium_l1::{
    check_phylum, check_phylum_with_deps, parse_phylum, CheckError, Phyla, Phylum, ResolvedPhylum,
};
use std::collections::BTreeMap;

/// A deterministic, well-formed (but not a real content digest — `Declared`, not `Exact`) hash for
/// fixture use — distinct per fixture via the discriminator byte, so two different fixture phyla
/// never accidentally share a "pin".
fn fixture_hash(discriminator: u8) -> ContentHash {
    let digest = format!("{discriminator:02x}", discriminator = discriminator).repeat(32);
    ContentHash::from_parts("blake3", &digest).expect("well-formed fixture digest")
}

/// Parse `src` as a phylum (panics on a parse error — every fixture here is deliberately
/// well-formed at the surface-syntax level; only the *check* is under test).
fn phy(src: &str) -> Phylum {
    parse_phylum(src).expect("fixture parses as a phylum")
}

/// Resolve `src` into a [`ResolvedPhylum`] (checked + linked), the dependency-fixture helper every
/// cross-phylum test builds its `Phyla` from.
fn resolved(src: &str, discriminator: u8) -> ResolvedPhylum {
    ResolvedPhylum::resolve(fixture_hash(discriminator), &phy(src), &Phyla::default())
        .expect("dependency fixture checks")
}

/// Check `src` against `deps`, returning the per-nodule envs.
fn check_with(src: &str, deps: &Phyla) -> Result<mycelium_l1::PhylumEnv, CheckError> {
    check_phylum_with_deps(&phy(src), deps)
}

/// Check `src` against `deps`, expecting a never-silent `CheckError`; returns its message.
fn check_with_err(src: &str, deps: &Phyla) -> String {
    check_with(src, deps)
        .expect_err("must fail to check")
        .message
}

// ---------------------------------------------------------------------------------------------
// The headline: a cross-phylum `use dep::nod.sym` resolves the correct foreign symbol.
// ---------------------------------------------------------------------------------------------

#[test]
fn cross_phylum_use_of_a_pub_fn_resolves_and_type_checks() {
    let dep = resolved(
        "phylum d\nnodule math;\npub fn add1(x: Binary{8}) => Binary{8} = x;",
        1,
    );
    let mut deps = BTreeMap::new();
    deps.insert("collections".to_owned(), dep);
    let phyla = Phyla::from_deps(deps);

    let penv = check_with(
        "phylum p\nnodule use_it;\nuse collections::math.add1;\n\
         pub fn go(y: Binary{8}) => Binary{8} = add1(y);",
        &phyla,
    )
    .expect("a cross-phylum `use` of a pub fn type-checks");
    let env = penv
        .nodule(&mycelium_l1::ast::Path(vec!["use_it".to_owned()]))
        .expect("nodule present");
    assert!(env.fn_decl("go").is_some(), "the consumer's own fn checked");
    assert!(
        env.fn_decl("add1").is_some(),
        "the imported cross-phylum fn is visible in the consumer's checked env \
         (M-662's cross-nodule pattern, extended one level up — DN-113 §7)"
    );
}

/// Non-vacuity control: the SAME source, minus the `use`, does not spuriously resolve `add1` (the
/// name genuinely comes from the cross-phylum import, not some ambient fallback).
#[test]
fn control_without_the_use_the_foreign_fn_is_genuinely_unresolved() {
    let dep = resolved(
        "phylum d\nnodule math;\npub fn add1(x: Binary{8}) => Binary{8} = x;",
        2,
    );
    let mut deps = BTreeMap::new();
    deps.insert("collections".to_owned(), dep);
    let phyla = Phyla::from_deps(deps);

    let err = check_with_err(
        "phylum p\nnodule use_it;\npub fn go(y: Binary{8}) => Binary{8} = add1(y);",
        &phyla,
    );
    assert!(
        !err.is_empty(),
        "without the `use`, `add1` is not in scope — a real unknown-name refusal"
    );
}

/// Non-vacuity control: an empty `Phyla` (no `[dependencies]` at all) checks a dependency-free
/// phylum identically to the pre-M-1060 [`check_phylum`] — the additive-identity claim (DN-113 §5.1).
#[test]
fn empty_phyla_checks_identically_to_check_phylum() {
    let src = "phylum p\nnodule solo;\npub fn id(x: Binary{8}) => Binary{8} = x;";
    let via_plain = check_phylum(&phy(src)).expect("plain check_phylum succeeds");
    let via_empty_deps =
        check_phylum_with_deps(&phy(src), &Phyla::default()).expect("empty-Phyla check succeeds");
    let plain_env = via_plain
        .nodule(&mycelium_l1::ast::Path(vec!["solo".to_owned()]))
        .unwrap();
    let deps_env = via_empty_deps
        .nodule(&mycelium_l1::ast::Path(vec!["solo".to_owned()]))
        .unwrap();
    assert_eq!(
        plain_env.fns.keys().collect::<Vec<_>>(),
        deps_env.fns.keys().collect::<Vec<_>>()
    );
}

// ---------------------------------------------------------------------------------------------
// Never-silent refusals (DN-113 §7/§8/§9): unknown dependency, unknown/private symbol, v1 glob.
// ---------------------------------------------------------------------------------------------

#[test]
fn use_of_an_undeclared_dependency_is_a_never_silent_refusal() {
    // No dependency named `nosuch` in `deps` at all.
    let err = check_with_err(
        "phylum p\nnodule use_it;\nuse nosuch::math.add1;\n\
         pub fn go() => Binary{8} = add1(0b0000_0000);",
        &Phyla::default(),
    );
    assert!(err.contains("no such dependency"), "got: {err}");
}

#[test]
fn use_of_an_unknown_symbol_in_a_known_dependency_is_a_never_silent_refusal() {
    let dep = resolved(
        "phylum d\nnodule math;\npub fn add1(x: Binary{8}) => Binary{8} = x;",
        3,
    );
    let mut deps = BTreeMap::new();
    deps.insert("collections".to_owned(), dep);
    let phyla = Phyla::from_deps(deps);

    let err = check_with_err(
        "phylum p\nnodule use_it;\nuse collections::math.no_such_fn;",
        &phyla,
    );
    assert!(err.contains("no such name"), "got: {err}");
}

#[test]
fn use_of_a_private_symbol_in_a_dependency_is_a_never_silent_refusal_distinguishing_private() {
    let dep = resolved(
        "phylum d\nnodule math;\nfn helper(x: Binary{8}) => Binary{8} = x;",
        4,
    );
    let mut deps = BTreeMap::new();
    deps.insert("collections".to_owned(), dep);
    let phyla = Phyla::from_deps(deps);

    let err = check_with_err(
        "phylum p\nnodule use_it;\nuse collections::math.helper;",
        &phyla,
    );
    assert!(
        err.contains("not `pub`") || err.contains("private"),
        "got: {err}"
    );
}

#[test]
fn a_cross_phylum_glob_is_refused_in_v1() {
    let dep = resolved(
        "phylum d\nnodule math;\npub fn add1(x: Binary{8}) => Binary{8} = x;",
        5,
    );
    let mut deps = BTreeMap::new();
    deps.insert("collections".to_owned(), dep);
    let phyla = Phyla::from_deps(deps);

    let err = check_with_err("phylum p\nnodule use_it;\nuse collections::math.*;", &phyla);
    assert!(
        err.contains("glob") && err.contains("not supported"),
        "got: {err}"
    );
}

// ---------------------------------------------------------------------------------------------
// DN-112 Rank 1 / M-1036 extension: foreign type identity stays distinct from a same-named local.
// ---------------------------------------------------------------------------------------------

#[test]
fn a_foreign_type_from_a_dependency_is_distinct_from_a_same_named_local_type() {
    // `dep` declares `T`; the consumer ALSO declares its own, differently-shaped, same-named `T`,
    // and imports the dependency's `use_t` (which takes the DEPENDENCY's `T`). Constructing a LOCAL
    // `T` and passing it to the foreign `use_t` must be a genuine type mismatch — the exact
    // cross-phylum extension of the DN-112/M-1036 ctor-seal/identity fix (no bare-name collapse
    // across the phylum boundary).
    let dep = resolved(
        "phylum d\nnodule math;\n\
         pub type T = Mk(Binary{8});\n\
         pub fn use_t(x: T) => Binary{8} = match x { Mk(v) => v };",
        6,
    );
    let mut deps = BTreeMap::new();
    deps.insert("collections".to_owned(), dep);
    let phyla = Phyla::from_deps(deps);

    let err = check_with_err(
        "phylum p\nnodule use_it;\n\
         use collections::math.use_t;\n\
         type T = Mk(Binary{8});\n\
         fn forge() => T = Mk(0b0000_0000);\n\
         pub fn exploit() => Binary{8} = use_t(forge());",
        &phyla,
    );
    // Confirms a genuine, home-qualified type mismatch — not a spurious unrelated failure: the
    // consumer's local `T` and the dependency's `T` carry DISTINCT phylum-qualified identities
    // (`use_it::T` vs `collections::math::T`), exactly the DN-112 Rank 1 mechanism extended across
    // the phylum boundary (never a bare-name collapse — G2).
    assert!(
        err.contains("use_it::T") && err.contains("collections::math::T"),
        "a same-named local `T` must NOT satisfy the foreign dependency's `T` — identity does not \
         collapse across the phylum boundary (DN-112 Rank 1 extended by DN-113/M-1060); got: {err}"
    );
}

/// Non-vacuity control: the SAME shape, but the consumer passes a value obtained from the
/// dependency's OWN factory (never constructing a local shadow) — a legitimate cross-phylum flow
/// that must NOT be over-restricted by the identity fix.
#[test]
fn a_legitimate_cross_phylum_flow_using_the_dependencys_own_factory_still_works() {
    let dep = resolved(
        "phylum d\nnodule math;\n\
         pub type T = Mk(Binary{8});\n\
         pub fn make() => T = Mk(0b0000_0000);\n\
         pub fn use_t(x: T) => Binary{8} = match x { Mk(v) => v };",
        7,
    );
    let mut deps = BTreeMap::new();
    deps.insert("collections".to_owned(), dep);
    let phyla = Phyla::from_deps(deps);

    check_with(
        "phylum p\nnodule use_it;\n\
         use collections::math.make;\nuse collections::math.use_t;\n\
         pub fn go() => Binary{8} = use_t(make());",
        &phyla,
    )
    .expect(
        "a value obtained from the dependency's own factory and passed straight back through \
         still type-checks (the identity fix must not over-restrict a legitimate flow)",
    );
}

/// A same-named type in the dependency and the consumer, used **independently** (never mixed),
/// both still check — the identity fix is about cross-phylum MIXING, not about forbidding a common
/// name (mirrors `unrelated_same_named_types_in_different_nodules_used_independently_still_check`
/// intra-phylum in `tests/ctor_seal.rs`).
#[test]
fn same_named_types_used_independently_across_the_phylum_boundary_both_still_check() {
    let dep = resolved(
        "phylum d\nnodule math;\npub type T = Mk(Binary{8});\npub fn dep_use(x: T) => Binary{8} = match x { Mk(v) => v };",
        8,
    );
    let mut deps = BTreeMap::new();
    deps.insert("collections".to_owned(), dep);
    let phyla = Phyla::from_deps(deps);

    check_with(
        "phylum p\nnodule use_it;\n\
         type T = Mk(Binary{4});\n\
         fn local_use(x: T) => Binary{4} = match x { Mk(v) => v };\n\
         pub fn go() => Binary{4} = local_use(Mk(0b0000));",
        &phyla,
    )
    .expect("the consumer's own unrelated same-named local type checks independently");
}

// ---------------------------------------------------------------------------------------------
// CRITICAL fix (adversarial-verification finding, 2026-07-11): `merge_phyla_exports` re-homes an
// imported type's OWN identity (`DataInfo::home`) but, pre-fix, left every ctor field's baked
// `Ty::Data` identity in the DEPENDENCY's own (un-rehomed) home-space. A ctor field naming a
// dependency-internal nodule (e.g. `Ty::Data("m::Bar", [])`) collided with a same-named nodule in
// the CONSUMER — the M-1036 ctor-seal/type-identity collapse one level up, across the phylum
// boundary. Fixed by re-homing every ctor field through `qualify_ty_cross_phylum` against the
// dependency's own linked `Env::types` (the exact helper + oracle the `resolved_fn_sigs` loop
// already used — DRY, one re-homing path).
// ---------------------------------------------------------------------------------------------

#[test]
fn exploit_ctor_field_width_collapse_is_now_refused() {
    // `dep`'s nodule `m` declares `Bar` (home `m`, `Binary{4}`) and a wrapper `BoxP = MkP(Bar)`
    // whose field is baked as `Ty::Data("m::Bar", [])` at the dependency's OWN registration.
    // The CONSUMER also has its own nodule `m`, with its OWN, differently-shaped `Bar`
    // (`Binary{64}`) — same bare identity string `"m::Bar"` pre-fix, so the un-rehomed field
    // collided with the consumer's local `Bar` (home `m` == home `m`, no mismatch detected).
    let dep = resolved(
        "phylum d\nnodule m;\n\
         pub type Bar = MkBar(Binary{4});\n\
         pub type BoxP = MkP(Bar);",
        10,
    );
    let mut deps = BTreeMap::new();
    deps.insert("pp".to_owned(), dep);
    let phyla = Phyla::from_deps(deps);

    let err = check_with_err(
        "phylum p\nnodule m;\n\
         pub type Bar = MkBar(Binary{64});\n\
         use pp::m.BoxP;\n\
         pub fn exploit(x: BoxP) => Binary{64} = match x { MkP(MkBar(v)) => v };",
        &phyla,
    );
    // Post-fix, the wrapper's field carries the correctly-re-homed identity `pp::m::Bar` — which
    // the consumer's own `m::Bar` does NOT satisfy, so the nested `MkBar(v)` sub-pattern is a
    // genuine, explicit DN-112 home-mismatch refusal (never a silent bare-name collapse — G2).
    // Pre-fix, this same program type-checked (Ok) — a `Binary{4}` dependency value silently
    // accepted as the consumer's own `Binary{64}` `Bar`.
    assert!(
        err.contains("pp::m::Bar"),
        "the foreign ctor field must resolve to the re-homed `pp::m::Bar` identity, not collapse \
         onto the consumer's local `m::Bar` (CRITICAL fix, DN-113/M-1060 extension of DN-112 Rank \
         1 across the phylum boundary); got: {err}"
    );
}

/// Non-vacuity / non-over-restriction control for the CRITICAL fix: a benign single-dep consumer
/// that imports BOTH the wrapper type AND its field type explicitly, and never shadows either name
/// locally, must still type-check — the re-homing fix must not turn a legitimate cross-phylum flow
/// into a false refusal. Pre-fix, this same program actually **failed** — an unrelated internal
/// error (`data type m::Bar is not registered`), because the un-rehomed field identity `m::Bar`
/// never matched anything the consumer had registered under the correctly-rehomed bare key `Bar`
/// (home `pp::m`).
#[test]
fn legit_import_wrapper_and_field_type_checks_after_the_fix() {
    let dep = resolved(
        "phylum d\nnodule m;\n\
         pub type Bar = MkBar(Binary{4});\n\
         pub type BoxP = MkP(Bar);",
        11,
    );
    let mut deps = BTreeMap::new();
    deps.insert("pp".to_owned(), dep);
    let phyla = Phyla::from_deps(deps);

    let penv = check_with(
        "phylum p\nnodule use_it;\n\
         use pp::m.BoxP;\nuse pp::m.Bar;\n\
         pub fn go(x: BoxP) => BoxP = match x { MkP(b) => MkP(b) };",
        &phyla,
    )
    .expect(
        "importing both the wrapper and its field type, with no local shadow, must type-check \
         after the ctor-field re-homing fix (the false-reject twin of the CRITICAL exploit)",
    );
    let env = penv
        .nodule(&mycelium_l1::ast::Path(vec!["use_it".to_owned()]))
        .expect("nodule present");
    assert!(env.fn_decl("go").is_some(), "the consumer's own fn checked");
    // The field is correctly re-homed to the dependency's own qualified identity.
    let box_p = env
        .types
        .get("BoxP")
        .expect("the imported wrapper type is registered");
    assert_eq!(
        box_p.ctors[0].fields[0],
        mycelium_l1::checkty::Ty::Data("pp::m::Bar".to_owned(), vec![]),
        "the wrapper's field must carry the re-homed `pp::m::Bar` identity, not the dependency's \
         un-rehomed bare `m::Bar`"
    );
}

// ---------------------------------------------------------------------------------------------
// MED closure (2026-07-11, adversarial-verification follow-up): a foreign trait's signature naming
// a concrete type beyond its own params is NOT yet re-homed against its declaring phylum (unlike
// ctor fields, now fixed above, and fn sigs, always re-homed) — confirmed reachable via a plain
// `use dep::Trait; impl Trait for LocalType { .. }` (no cross-phylum `instances` merge needed at
// all). Refused explicitly (see `foreign_trait_sig_names_a_concrete_type`'s doc comment) rather
// than silently re-resolved against the wrong phylum's registry.
// ---------------------------------------------------------------------------------------------

#[test]
fn implementing_a_foreign_trait_whose_signature_names_a_concrete_type_is_refused() {
    // `pp::m::Trt`'s `get` returns the DEPENDENCY's own concrete `Bar` (not a trait param). The
    // consumer ALSO has its own, differently-shaped `Bar` and tries to satisfy `Trt` for a local
    // type — pre-fix this silently type-checked (the impl's own `Bar` resolved against the
    // CONSUMER's registry, not the dependency's), exactly the same bare-name collapse class the
    // CRITICAL ctor-field fix closes, one level up for a trait signature.
    let dep = resolved(
        "phylum d\nnodule m;\n\
         pub type Bar = MkBar(Binary{4});\n\
         pub trait Trt[A] { fn get(x: A) => Bar; };",
        200,
    );
    let mut deps = BTreeMap::new();
    deps.insert("pp".to_owned(), dep);
    let phyla = Phyla::from_deps(deps);

    let sixty_four_zero_bits = format!("0b{}", "0".repeat(64));
    let err = check_with_err(
        &format!(
            "phylum p\nnodule m;\n\
             pub type Bar = MkBar(Binary{{64}});\n\
             pub type Local = MkL(Binary{{8}});\n\
             use pp::m.Trt;\n\
             impl Trt[Binary{{8}}] for Local {{ fn get(x: Binary{{8}}) => Bar = \
             MkBar({sixty_four_zero_bits}); }};"
        ),
        &phyla,
    );
    assert!(
        err.contains("Bar") && err.contains("DN-122"),
        "a foreign trait signature naming a concrete type beyond its own params must be refused \
         (MED closure, DN-113 §7 / DN-122 residual) rather than silently re-resolved against the \
         consumer's own (wrong) registry; got: {err}"
    );
}

/// Non-vacuity / non-over-restriction control: a foreign trait whose signature references ONLY its
/// own generic params (no concrete type beyond them — the common, legitimate "impl a foreign trait
/// for your own type" pattern the orphan rule exists to allow) is entirely UNAFFECTED by the MED
/// closure above and still type-checks.
#[test]
fn implementing_a_foreign_generic_only_trait_still_type_checks() {
    let dep = resolved(
        "phylum d\nnodule m;\npub trait Cmp[A] { fn cmp(a: A, b: A) => Binary{2}; };",
        201,
    );
    let mut deps = BTreeMap::new();
    deps.insert("pp".to_owned(), dep);
    let phyla = Phyla::from_deps(deps);

    check_with(
        "phylum p\nnodule use_it;\n\
         pub type Local = MkL(Binary{8});\n\
         use pp::m.Cmp;\n\
         impl Cmp[Local] for Local { fn cmp(a: Local, b: Local) => Binary{2} = 0b00; };",
        &phyla,
    )
    .expect(
        "a foreign trait whose signature references only its own generic params carries no \
         concrete-type reference at all, so the MED closure must not over-restrict it",
    );
}

// ---------------------------------------------------------------------------------------------
// DN-113 §9.3: the acyclic-phyla precondition, enforced by `phyla::build_phyla_graph`.
// ---------------------------------------------------------------------------------------------

#[test]
fn a_cyclic_phyla_graph_is_refused_never_silently() {
    let mut graph = BTreeMap::new();
    graph.insert(
        "a".to_owned(),
        PhylumNode {
            phylum_hash: fixture_hash(0xA),
            phylum: phy("phylum a\nnodule n;\npub fn f() => Binary{8} = 0b0000_0000;"),
            deps: BTreeMap::from([("b".to_owned(), "b".to_owned())]),
        },
    );
    graph.insert(
        "b".to_owned(),
        PhylumNode {
            phylum_hash: fixture_hash(0xB),
            phylum: phy("phylum b\nnodule n;\npub fn g() => Binary{8} = 0b0000_0000;"),
            deps: BTreeMap::from([("a".to_owned(), "a".to_owned())]),
        },
    );

    let err = build_phyla_graph(&graph).expect_err("a two-cycle must be refused");
    assert!(err.message.contains("cyclic"), "got: {}", err.message);
}

/// Non-vacuity control: an ACYCLIC two-level graph (root depends on a leaf) resolves cleanly, and
/// the root's own `use` of the leaf's symbol checks — proves the cycle detector is not vacuously
/// refusing every multi-node graph.
#[test]
fn an_acyclic_two_level_graph_resolves_and_the_roots_cross_phylum_use_checks() {
    let mut graph = BTreeMap::new();
    graph.insert(
        "leaf".to_owned(),
        PhylumNode {
            phylum_hash: fixture_hash(0xC),
            phylum: phy("phylum leaf\nnodule math;\npub fn add1(x: Binary{8}) => Binary{8} = x;"),
            deps: BTreeMap::new(),
        },
    );
    graph.insert(
        "root".to_owned(),
        PhylumNode {
            phylum_hash: fixture_hash(0xD),
            phylum: phy("phylum root\nnodule use_it;\nuse leafdep::math.add1;\n\
                 pub fn go(y: Binary{8}) => Binary{8} = add1(y);"),
            deps: BTreeMap::from([("leafdep".to_owned(), "leaf".to_owned())]),
        },
    );

    let resolved = build_phyla_graph(&graph).expect("an acyclic graph resolves");
    assert_eq!(resolved.len(), 2, "both nodes resolved");
    let (root_env, root_phyla) = &resolved["root"];
    assert!(
        root_phyla.deps().contains_key("leafdep"),
        "the root's `Phyla` retains its resolved dependency"
    );
    let env = root_env
        .nodule(&mycelium_l1::ast::Path(vec!["use_it".to_owned()]))
        .unwrap();
    assert!(env.fn_decl("go").is_some());
}

#[test]
fn build_phyla_graph_refuses_an_edge_to_an_absent_node() {
    let mut graph = BTreeMap::new();
    graph.insert(
        "root".to_owned(),
        PhylumNode {
            phylum_hash: fixture_hash(0xE),
            phylum: phy("phylum root\nnodule n;\npub fn f() => Binary{8} = 0b0000_0000;"),
            deps: BTreeMap::from([("missing".to_owned(), "does-not-exist".to_owned())]),
        },
    );
    let err = build_phyla_graph(&graph).expect_err("an edge to an absent node must be refused");
    assert!(
        err.message.contains("unknown dependency") || err.message.contains("not present"),
        "got: {}",
        err.message
    );
}

// ---------------------------------------------------------------------------------------------
// DN-113 §7 (US-4): layering over the ONE canonical linker — a lightweight differential.
// ---------------------------------------------------------------------------------------------

/// `ResolvedPhylum::resolve`'s linked `Env` for a dependency carries the SAME fn/type names as
/// independently checking + linking that same phylum via the plain (pre-M-1060) `check_phylum` +
/// `PhylumEnv::link` path — i.e. resolving a phylum as a *dependency* does not go through some
/// alternate/parallel linker (DN-113 §7 US-4 / §9.6's own "no second resolver" self-test, as a
/// differential rather than a source-level argument).
#[test]
fn a_resolved_dependencys_linked_env_matches_the_plain_check_and_link_path() {
    let src = "phylum d\nnodule math;\npub fn add1(x: Binary{8}) => Binary{8} = x;\nfn helper() => Binary{8} = 0b0000_0001;";
    let via_resolved_phylum = resolved(src, 9);

    let via_plain = check_phylum(&phy(src)).expect("plain check_phylum succeeds");
    let via_plain_linked = via_plain.link().expect("plain link succeeds");

    let mut resolved_fns: Vec<&String> = via_resolved_phylum.env.fns.keys().collect();
    let mut plain_fns: Vec<&String> = via_plain_linked.fns.keys().collect();
    resolved_fns.sort();
    plain_fns.sort();
    assert_eq!(
        resolved_fns, plain_fns,
        "the SAME linker (`PhylumEnv::link`) produced both — no parallel resolver"
    );
}

// ---------------------------------------------------------------------------------------------
// HOLES A / A2 / B closure (M-1060 fix-cycle-3, 2026-07-11 — a completeness adversarial-sweep
// finding, the 3rd fix cycle on the same root class): the two already-landed fixes above (the
// CRITICAL ctor-field re-homing and the MED `register_instances` `impl`-registration guard) left
// two SIBLING consumption sites of the same un-re-homed foreign surface `TypeRef`s ungated:
//
// - HOLE A/A2: `check_trait_method_call` resolves a foreign trait's method sig via
//   `resolve_ty(self.site, self.types, trait_vars, …)` when the trait is called through a generic
//   **bound** (`fn wrap[T: Trt](x: T) => …`) — `require_instance`'s bound-discharge branch needs no
//   registered instance at all, so the register-time guard (which only runs at `impl`
//   registration) never fires for this path. HOLE A = a concrete type in RETURN position; HOLE A2 =
//   a concrete type in a VALUE-PARAM position.
// - HOLE B: `check_app`/`check_app_generic_fn` prefer the re-homed `resolved_fn_sigs` baked entry,
//   but FALL BACK to `resolve_ty(self.site, self.types, …, &pm.ty)` (the CALLER's own registry) when
//   the baked entry is absent — which happens whenever the callee's OWN declaring nodule imports
//   the referenced type from a sibling nodule (`resolve_fn_sig`'s disclosed best-effort scope).
//
// All three are closed the same narrow, sound way as the MED fix: a **never-silent refusal**, not
// a general re-homing (DN-113 §7 / DN-122 tracks the general fix — re-homing every foreign
// trait/fn signature TypeRef against its OWN declaring phylum, mirroring the ctor-field CRITICAL
// fix). The refusal fires ONLY when the callee is genuinely **cross-phylum**
// (`NoduleImports::cross_phylum_traits`/`cross_phylum_fns` — never intra-phylum, since a same-phylum
// sibling's signature is safe to resolve against `self.types`, M-1036 already giving every
// intra-phylum type a qualified, unambiguous identity there) AND its signature actually names a
// concrete type beyond its own generic parameters (`foreign_trait_sig_names_a_concrete_type` /
// `foreign_fn_sig_names_a_concrete_type` — reused from/sharing the MED fix's helper, not forked).
// ---------------------------------------------------------------------------------------------

#[test]
fn exploit_a_foreign_trait_method_call_through_a_bound_collapsing_the_return_type_is_now_refused() {
    // `pp::m::Trt`'s `get` returns the DEPENDENCY's own concrete `Bar` (Binary{4}), not a trait
    // param. The consumer calls `get` through a generic BOUND (`T: Trt`) — never registering any
    // `impl`, so the MED `register_instances` guard's call site is never reached at all. Pre-fix,
    // `wrap`'s declared return type `Bar` (the CONSUMER's own, Binary{64}) silently satisfied the
    // foreign `get`'s Binary{4} return — a genuine width/identity collapse across the phylum
    // boundary.
    let dep = resolved(
        "phylum d\nnodule m;\n\
         pub type Bar = MkBar(Binary{4});\n\
         pub trait Trt[A] { fn get(x: A) => Bar; };",
        210,
    );
    let mut deps = BTreeMap::new();
    deps.insert("pp".to_owned(), dep);
    let phyla = Phyla::from_deps(deps);

    let err = check_with_err(
        "phylum p\nnodule m;\n\
         pub type Bar = MkBar(Binary{64});\n\
         use pp::m.Trt;\n\
         pub fn wrap[T: Trt](x: T) => Bar = get(x);",
        &phyla,
    );
    assert!(
        err.contains("Bar") && err.contains("DN-122"),
        "a foreign trait method called through a generic bound must be refused when the trait's \
         signature names a concrete type (HOLE A) beyond its own generic params — never-silently \
         re-resolved against the consumer's own (wrong) `Bar`; got: {err}"
    );
}

#[test]
fn exploit_a2_foreign_trait_method_call_through_a_bound_collapsing_a_value_param_is_now_refused() {
    // Same shape as HOLE A, but the concrete foreign type is in a VALUE-PARAMETER position rather
    // than the return type — a distinct call site inside `check_trait_method_call` (the
    // `sig.value_params` loop vs the `sig.ret` resolution), so both must be independently closed.
    let dep = resolved(
        "phylum d\nnodule m;\n\
         pub type Bar = MkBar(Binary{4});\n\
         pub trait Trt[A] { fn put(a: A, b: Bar) => A; };",
        211,
    );
    let mut deps = BTreeMap::new();
    deps.insert("pp".to_owned(), dep);
    let phyla = Phyla::from_deps(deps);

    let err = check_with_err(
        "phylum p\nnodule m;\n\
         pub type Bar = MkBar(Binary{64});\n\
         use pp::m.Trt;\n\
         pub fn wrap[T: Trt](x: T, y: Bar) => T = put(x, y);",
        &phyla,
    );
    assert!(
        err.contains("Bar") && err.contains("DN-122"),
        "a foreign trait method called through a generic bound must be refused when the trait's \
         signature names a concrete type (HOLE A2) in a VALUE-PARAMETER position beyond its own \
         generic params; got: {err}"
    );
}

/// Non-vacuity / non-over-restriction control for HOLE A/A2: a foreign trait called through a bound
/// whose signature references ONLY its own generic param (no concrete type at all — the common,
/// legitimate pattern) is entirely UNAFFECTED.
#[test]
fn foreign_generic_only_trait_method_call_through_a_bound_still_type_checks() {
    let dep = resolved(
        "phylum d\nnodule m;\npub trait Trt[A] { fn f(a: A) => A; };",
        212,
    );
    let mut deps = BTreeMap::new();
    deps.insert("pp".to_owned(), dep);
    let phyla = Phyla::from_deps(deps);

    check_with(
        "phylum p\nnodule use_it;\n\
         use pp::m.Trt;\n\
         pub fn wrap[T: Trt](x: T) => T = f(x);",
        &phyla,
    )
    .expect(
        "a foreign trait method called through a bound, whose signature references only its own \
         generic param, carries no concrete-type reference at all, so the HOLE A/A2 closure must \
         not over-restrict it",
    );
}

/// Non-vacuity / non-over-restriction control: a purely intra-phylum (same-phylum, no `deps` at
/// all) trait, whose signature names a concrete type (co-located in its own declaring nodule — a
/// trait's signature must resolve against its OWN nodule's registered types at declaration time,
/// `register_traits`/`check_sig_resolves`, before any cross-nodule import is even resolved; a trait
/// referencing a *sibling*-nodule-imported type is illegal regardless of this fix), called through
/// a bound from a SIBLING nodule, must be entirely unaffected — the HOLE A/A2 guard only ever fires
/// for `NoduleImports::cross_phylum_traits`, which is always empty absent any dependency (never
/// over-refuses the ordinary M-662 multi-nodule pattern). Same shape as the HOLE A exploit fixture
/// above, minus being imported cross-phylum — the exact "same shape, minus the violation" control
/// this file's own house style uses throughout.
#[test]
fn local_same_phylum_trait_method_call_through_a_bound_is_unaffected_by_the_hole_a_a2_closure() {
    check_with(
        "phylum p\nnodule m;\n\
         pub type Bar = MkBar(Binary{4});\n\
         pub trait Trt[A] { fn get(x: A) => Bar; };\n\
         nodule consumer;\nuse m.Trt;\nuse m.Bar;\n\
         pub fn wrap[T: Trt](x: T) => Bar = get(x);",
        &Phyla::default(),
    )
    .expect(
        "a purely intra-phylum trait-method call through a bound, whose signature names a \
         concrete type declared in the trait's own nodule, must be entirely unaffected by the \
         HOLE A/A2 closure",
    );
}

#[test]
fn exploit_b_unbaked_foreign_monomorphic_fn_signature_falls_back_to_consumer_registry_is_now_refused(
) {
    // `pp::api::use_bar`'s OWN declaring nodule (`api`) imports `Bar` from a SIBLING nodule
    // (`types`) — `resolve_fn_sig` only resolves against `api`'s own registered types, so this
    // signature fails to bake (`resolved_fn_sigs` absent for `use_bar`). Pre-fix, `check_app`'s
    // fallback re-resolved the bare name `Bar` against the CONSUMER's own (differently-shaped)
    // `Bar` — a genuine width collapse across the phylum boundary, for a MONOMORPHIC (non-generic)
    // foreign fn.
    let dep = resolved(
        "phylum d\nnodule types;\npub type Bar = MkBar(Binary{4});\n\
         nodule api;\nuse types.Bar;\n\
         pub fn use_bar(x: Bar) => Binary{4} = match x { MkBar(v) => v };",
        213,
    );
    let mut deps = BTreeMap::new();
    deps.insert("pp".to_owned(), dep);
    let phyla = Phyla::from_deps(deps);

    let sixty_four_zero_bits = format!("0b{}", "0".repeat(64));
    let err = check_with_err(
        &format!(
            "phylum p\nnodule m;\n\
             pub type Bar = MkBar(Binary{{64}});\n\
             use pp::api.use_bar;\n\
             pub fn exploit() => Binary{{4}} = use_bar(MkBar({sixty_four_zero_bits}));"
        ),
        &phyla,
    );
    assert!(
        err.contains("Bar") && err.contains("DN-122"),
        "an un-bakeable cross-phylum fn's signature must be refused, never re-resolved against the \
         consumer's own registry, when it names a concrete type (HOLE B); got: {err}"
    );
}

#[test]
fn exploit_b_variant_unbaked_foreign_generic_fn_signature_is_also_refused() {
    // The generic-callee twin of the exploit above — exercises `check_app_generic_fn`'s own
    // unbaked-signature fallback (a distinct call site from `check_app`'s monomorphic path).
    let dep = resolved(
        "phylum d\nnodule types;\npub type Bar = MkBar(Binary{4});\n\
         nodule api;\nuse types.Bar;\n\
         pub fn use_bar_generic[T](x: T, y: Bar) => T = x;",
        214,
    );
    let mut deps = BTreeMap::new();
    deps.insert("pp".to_owned(), dep);
    let phyla = Phyla::from_deps(deps);

    let sixty_four_zero_bits = format!("0b{}", "0".repeat(64));
    let err = check_with_err(
        &format!(
            "phylum p\nnodule m;\n\
             pub type Bar = MkBar(Binary{{64}});\n\
             use pp::api.use_bar_generic;\n\
             pub fn exploit() => Binary{{8}} = \
             use_bar_generic(0b0000_0000, MkBar({sixty_four_zero_bits}));"
        ),
        &phyla,
    );
    assert!(
        err.contains("Bar") && err.contains("DN-122"),
        "the generic-callee twin of HOLE B (`check_app_generic_fn`'s own unbaked-signature \
         fallback) must also be refused when the foreign fn's signature names a concrete type \
         unrelated to its own generic param; got: {err}"
    );
}

/// Non-vacuity / non-over-restriction control (i): a foreign fn whose signature IS baked
/// (`resolved_fn_sigs` present, since its own declaring nodule declares `Bar` directly with no
/// cross-nodule import needed to bake it) must go through the clean re-homed path — entirely
/// unaffected by the HOLE B closure (the guard only ever fires when `baked` is absent).
#[test]
fn bakeable_foreign_fn_call_still_type_checks_unaffected_by_the_hole_b_closure() {
    let dep = resolved(
        "phylum d\nnodule m;\n\
         pub type Bar = MkBar(Binary{4});\n\
         pub fn use_bar(x: Bar) => Binary{4} = match x { MkBar(v) => v };",
        215,
    );
    let mut deps = BTreeMap::new();
    deps.insert("pp".to_owned(), dep);
    let phyla = Phyla::from_deps(deps);

    check_with(
        "phylum p\nnodule use_it;\n\
         use pp::m.use_bar;\nuse pp::m.Bar;\n\
         pub fn go(x: Bar) => Binary{4} = use_bar(x);",
        &phyla,
    )
    .expect(
        "a foreign fn whose signature is baked at its own declaring nodule must go through the \
         re-homed path unaffected by the HOLE B closure",
    );
}

/// Non-vacuity / non-over-restriction control (ii): a foreign fn whose signature is generic-only /
/// primitive-only (no concrete Data type name to collapse) must still type-check. **Structural
/// guarantee, not just an empirical witness:** `resolve_fn_sig` fails to bake a signature ONLY when
/// it references a concrete named type not found in the declaring nodule's own registry (its
/// `# Errors` doc comment) — a signature built entirely from primitives/generic params never hits
/// that failure, so it is ALWAYS baked and never even reaches the HOLE B guard's `baked.is_none()`
/// gate. This test exercises that (always-baked) path end-to-end as the integration-level
/// confirmation of the structural argument.
#[test]
fn foreign_generic_and_primitive_only_fn_signature_still_type_checks() {
    let dep = resolved(
        "phylum d\nnodule m;\npub fn id_prim[T](x: T, y: Binary{8}) => T = x;",
        216,
    );
    let mut deps = BTreeMap::new();
    deps.insert("pp".to_owned(), dep);
    let phyla = Phyla::from_deps(deps);

    check_with(
        "phylum p\nnodule use_it;\n\
         use pp::m.id_prim;\n\
         pub fn go() => Binary{4} = id_prim(0b0000, 0b0000_0001);",
        &phyla,
    )
    .expect(
        "a foreign fn whose signature is generic/primitive-only carries no concrete-type \
         reference at all, so the HOLE B closure must not over-restrict it",
    );
}

/// Non-vacuity / non-over-restriction control (iii): a purely intra-phylum (same-phylum, no `deps`
/// at all) fn call, genuinely UNBAKED (its declaring nodule imports the referenced type from a
/// sibling nodule — the exact pre-existing DN-112 disclosed-residual shape), must be completely
/// unaffected by the HOLE B closure — the guard only ever fires for
/// `NoduleImports::cross_phylum_fns`, which is always empty absent any dependency.
#[test]
fn local_same_phylum_unbaked_fn_call_is_unaffected_by_the_hole_b_closure() {
    let penv = check_with(
        "phylum p\nnodule types;\npub type Bar = MkBar(Binary{4});\n\
         nodule api;\nuse types.Bar;\n\
         pub fn use_bar(x: Bar) => Binary{4} = match x { MkBar(v) => v };\n\
         nodule consumer;\nuse api.use_bar;\nuse types.Bar;\n\
         pub fn go(x: Bar) => Binary{4} = use_bar(x);",
        &Phyla::default(),
    )
    .expect(
        "a purely intra-phylum (same-phylum, no `deps`) unbaked fn call must be completely \
         unaffected by the HOLE B closure",
    );
    let env = penv
        .nodule(&mycelium_l1::ast::Path(vec!["consumer".to_owned()]))
        .expect("nodule present");
    assert!(env.fn_decl("go").is_some(), "the consumer's own fn checked");
}

// ---------------------------------------------------------------------------------------------
// The 4th (and, per an exhaustive fn-as-value/carrier×position enumeration, FINAL) cross-phylum
// type-identity collapse site: fn-as-first-class-VALUE (M-1060 fix-cycle-4, 2026-07-11,
// adversarial-verification finding). HOLE A/A2 (trait-bound method calls) and HOLE B (the unbaked
// fn CALL-site fallback) closed the collapse at every CALL position; this cycle closes the same
// collapse at a VALUE position (`let f = foreignFn`, a HOF argument) those call-site guards never
// guarded — `check_path`'s fn-as-value branch synthesized `Ty::Fn` from the surface `fd.sig` via a
// fresh `resolve_ty` against the CALLER's own registry, bypassing both the re-homed baked
// `resolved_fn_sigs` entry and the `cross_phylum_fns` marker entirely, even in the bakeable case.
// ---------------------------------------------------------------------------------------------

#[test]
fn fn_as_value_cross_phylum_collapse_is_refused() {
    // `gulp`'s signature IS bakeable (`Bar` is declared directly in `gulp`'s own declaring nodule
    // `m` — no cross-nodule import needed, unlike HOLE B's un-bakeable shape). A direct call
    // `gulp(x)` already refuses correctly (the baked foreign `Bar{4}` identity mismatches the
    // consumer's own `Bar{64}`) — but pre-fix, referencing `gulp` as a first-class VALUE
    // (`let f = gulp in f(x)`) bypassed the baked signature entirely, re-resolving `gulp`'s surface
    // `Bar` fresh against the CONSUMER's own registry and silently collapsing the foreign `Bar{4}`
    // onto the consumer's `Bar{64}`.
    let dep = resolved(
        "phylum d\nnodule m;\npub type Bar = MkBar(Binary{4});\n\
         pub fn gulp(x: Bar) => Binary{4} = match x { MkBar(v) => v };",
        221,
    );
    let mut deps = BTreeMap::new();
    deps.insert("pp".to_owned(), dep);
    let phyla = Phyla::from_deps(deps);

    let sixty_four_zero_bits = format!("0b{}", "0".repeat(64));
    let err = check_with_err(
        &format!(
            "phylum p\nnodule m;\n\
             pub type Bar = MkBar(Binary{{64}});\n\
             use pp::m.gulp;\n\
             pub fn exploit() => Binary{{4}} = \
             let f = gulp in f(MkBar({sixty_four_zero_bits}));"
        ),
        &phyla,
    );
    assert!(
        err.contains("Bar"),
        "a fn referenced as a first-class VALUE across the phylum boundary must go through the \
         same baked, re-homed identity as a direct call — never a bare-name collapse via the \
         value-position synthesis path (M-1060 fix-cycle-4); got: {err}"
    );
}

#[test]
fn foreign_fn_as_hof_arg_is_refused() {
    // The higher-order-argument twin of the exploit above: `gulp` is passed BY NAME as an argument
    // to a local HOF (`apply_gulp`), routing through the identical `check_path` value-position
    // synthesis site via `check_app`'s ordinary bidirectional argument check (`self.check(scope, a,
    // Some(&want))` on a bare `Expr::Path` argument) rather than a `let`-binder.
    let dep = resolved(
        "phylum d\nnodule m;\npub type Bar = MkBar(Binary{4});\n\
         pub fn gulp(x: Bar) => Binary{4} = match x { MkBar(v) => v };",
        222,
    );
    let mut deps = BTreeMap::new();
    deps.insert("pp".to_owned(), dep);
    let phyla = Phyla::from_deps(deps);

    let sixty_four_zero_bits = format!("0b{}", "0".repeat(64));
    let err = check_with_err(
        &format!(
            "phylum p\nnodule m;\n\
             pub type Bar = MkBar(Binary{{64}});\n\
             use pp::m.gulp;\n\
             pub fn apply_gulp(f: Bar => Binary{{4}}, x: Bar) => Binary{{4}} = f(x);\n\
             pub fn exploit() => Binary{{4}} = apply_gulp(gulp, MkBar({sixty_four_zero_bits}));"
        ),
        &phyla,
    );
    assert!(
        err.contains("Bar"),
        "a foreign fn passed BY NAME as a HOF argument must route through the same baked identity \
         as a direct call or a `let`-bound value-position reference — never a bare-name collapse \
         (M-1060 fix-cycle-4); got: {err}"
    );
}

/// Non-vacuity / non-over-restriction control (i): a purely LOCAL fn (never cross-phylum) used as a
/// first-class value must be entirely unaffected — `baked` is always `None` for a local fn (it is
/// never present in this consumer's own `NoduleImports::resolved_fn_sigs`) and `cross_phylum_fns`
/// never contains a local name, so the guard never fires.
#[test]
fn local_fn_as_value_is_unaffected_by_the_fn_value_closure() {
    check_with(
        "phylum p\nnodule m;\n\
         pub type Bar = MkBar(Binary{8});\n\
         fn local_fn(x: Bar) => Binary{8} = match x { MkBar(v) => v };\n\
         pub fn go() => Binary{8} = let f = local_fn in f(MkBar(0b0000_0001));",
        &Phyla::default(),
    )
    .expect("a local fn referenced as a first-class value must be unaffected by the fix");
}

/// Non-vacuity / non-over-restriction control (ii): a cross-phylum fn whose signature IS baked,
/// used as a first-class value with the CORRECT (foreign) type, must still type-check — the
/// re-homed baked path is taken and accepts the legitimate use.
#[test]
fn bakeable_foreign_fn_as_value_still_type_checks() {
    let dep = resolved(
        "phylum d\nnodule m;\npub type Bar = MkBar(Binary{4});\n\
         pub fn gulp(x: Bar) => Binary{4} = match x { MkBar(v) => v };",
        223,
    );
    let mut deps = BTreeMap::new();
    deps.insert("pp".to_owned(), dep);
    let phyla = Phyla::from_deps(deps);

    check_with(
        "phylum p\nnodule m;\n\
         use pp::m.gulp;\nuse pp::m.Bar;\n\
         pub fn go(x: Bar) => Binary{4} = let f = gulp in f(x);",
        &phyla,
    )
    .expect(
        "a cross-phylum fn whose signature is baked, used as a value with the correct foreign \
         type, must type-check unaffected by the fn-as-value closure",
    );
}

/// Non-vacuity / non-over-restriction control (iii): a cross-phylum fn whose signature is
/// generic-only / primitive-only (no concrete Data type to collapse) used as a first-class value
/// must still type-check — the guard's `foreign_fn_sig_names_a_concrete_type` finds nothing
/// concrete, so it never fires.
#[test]
fn generic_only_foreign_fn_as_value_still_type_checks() {
    let dep = resolved(
        "phylum d\nnodule m;\npub fn id_prim[T](x: T) => T = x;",
        224,
    );
    let mut deps = BTreeMap::new();
    deps.insert("pp".to_owned(), dep);
    let phyla = Phyla::from_deps(deps);

    check_with(
        "phylum p\nnodule m;\n\
         use pp::m.id_prim;\n\
         pub fn go() => Binary{8} = \
         let f: Binary{8} => Binary{8} = id_prim in f(0b0000_0001);",
        &phyla,
    )
    .expect(
        "a cross-phylum fn whose signature is generic/primitive-only carries no concrete-type \
         reference at all, so the fn-as-value closure must not over-restrict it",
    );
}
