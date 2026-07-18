//! **Per-constructor visibility seal** (M-1027 / ENB-4; DN-104), now an **enforced** capability
//! boundary via **nodule-qualified type identity** (DN-112 Rank 1; M-1036) integration tests.
//!
//! A `priv`-marked constructor of a `pub type` exports the type **NAME** (usable cross-nodule in
//! signatures, `use`, and pattern position) but **withholds the constructor from cross-nodule
//! CONSTRUCTION** — the FR-N3 capability-gate ("only the home nodule mints one"). These tests are the
//! Rust-oracle **differential witnesses** the `/myc-dogfood` dual pairs with:
//!
//! - **home-construct OK** — a sealed ctor is constructible in its home nodule;
//! - **foreign-construct REFUSED** — constructing it from another nodule is a never-silent `CheckError`;
//! - **cross-nodule type-use OK** — the type NAME crosses (signatures) and pattern-matching is permitted.
//!
//! Every "the seal fires" test is paired with a **control** proving the check is not vacuous (the same
//! shape, minus the seal, is accepted). Honesty (VR-5): the seal is a `Declared` capability-gate whose
//! *never-silent behavior* these tests pin — not a proof.
//!
//! **DN-112 Rank 1 / M-1036 (2026-07-11).** `Ty::Data` identity is now nodule-qualified (`"a::T"`
//! for `T` declared in nodule `a`) and an imported function's signature is baked against its own
//! declaring nodule at export time — closing the same-named-local-shadow bypass the seal's own
//! bare-name resolution previously admitted (the former `known_gap_…` test, now flipped to assert
//! the refusal). The section below adds: the flipped exploit test, non-over-restriction controls
//! (unrelated same-named types used independently, a legitimate cross-nodule factory pattern), the
//! `type_head` coherence twin-fix witness (DN-112 §10 item 3), a mangling collision-freedom witness
//! (§10 item 4), and the builtin/prelude uniform-home-invariant regression test the ratification's
//! DoD item 9 requires (`Bool`/`Tuple$N` must resolve identically under every nodule). Guarantee:
//! `Empirical` for the general fix — earned by these witnesses, not proved (VR-5; DN-112 §8).

use mycelium_l1::{check_nodule, check_phylum, parse as parse_nodule, parse_phylum, CheckError};

/// Parse + check a phylum source, returning the per-nodule envs.
fn check_phy(src: &str) -> Result<mycelium_l1::PhylumEnv, CheckError> {
    let ph = parse_phylum(src).expect("parses as a phylum");
    check_phylum(&ph)
}

/// Parse + check a phylum, expecting a never-silent `CheckError`; returns its message.
fn phy_err(src: &str) -> String {
    let ph = parse_phylum(src).expect("parses as a phylum");
    check_phylum(&ph).expect_err("must fail to check").message
}

// ---------------------------------------------------------------------------------------------
// Surface: `priv` parses + round-trips.
// ---------------------------------------------------------------------------------------------

#[test]
fn a_sealed_ctor_parses_and_the_seal_round_trips_through_expand() {
    // `priv` before a ctor name parses; the AST carries `sealed`; `expand_to_source` re-emits `priv`.
    let src = "nodule a;\npub type T = priv Mk(Binary{8});\npub fn mk(x: Binary{8}) => T = Mk(x);";
    let nod = parse_nodule(src).expect("parses");
    let td = nod
        .items
        .iter()
        .find_map(|i| match i {
            mycelium_l1::ast::Item::Type(td) => Some(td),
            _ => None,
        })
        .expect("has a type decl");
    assert!(td.ctors[0].sealed, "the `priv` marker sets Ctor.sealed");

    let rendered = mycelium_l1::expand_to_source(&nod);
    assert!(
        rendered.contains("priv Mk"),
        "the seal round-trips through expand_to_source; got:\n{rendered}"
    );
    // And the re-parsed form still carries the seal (parse → expand → parse is stable).
    let reparsed = parse_nodule(&rendered).expect("re-parses");
    let td2 = reparsed
        .items
        .iter()
        .find_map(|i| match i {
            mycelium_l1::ast::Item::Type(td) => Some(td),
            _ => None,
        })
        .expect("has a type decl");
    assert!(td2.ctors[0].sealed, "the seal survives the round-trip");
}

// ---------------------------------------------------------------------------------------------
// Home-construct OK (accept).
// ---------------------------------------------------------------------------------------------

#[test]
fn a_sealed_ctor_is_constructible_in_its_home_nodule() {
    // `Mk` is `priv`, but the home nodule `a` mints one freely — the seal only withholds *foreign*
    // construction (own decls are subtracted from the withheld set; DN-104 §4).
    check_phy("phylum p\nnodule a;\npub type T = priv Mk(Binary{8});\npub fn mk(x: Binary{8}) => T = Mk(x);")
        .expect("a home-nodule construction of a sealed ctor type-checks");
}

#[test]
fn a_sealed_ctor_is_constructible_in_its_home_phylum_of_one() {
    // A bare nodule (phylum-of-one) has no imports, so the withheld set is empty — construction OK.
    check_nodule(
        &parse_nodule(
            "nodule solo;\npub type T = priv Mk(Binary{8});\nfn mk(x: Binary{8}) => T = Mk(x);",
        )
        .expect("parses"),
    )
    .expect("a phylum-of-one home construction type-checks");
}

// ---------------------------------------------------------------------------------------------
// Foreign-construct REFUSED (reject) + the unsealed control.
// ---------------------------------------------------------------------------------------------

#[test]
fn a_foreign_nodule_constructing_a_sealed_ctor_is_refused_never_silently() {
    // `b` imports `T` and tries to forge a `Mk` — the never-silent capability-gate refusal (G2).
    let err = phy_err(
        "phylum p\nnodule a;\npub type T = priv Mk(Binary{8});\nnodule b;\nuse a.T;\nfn forge(x: Binary{8}) => T = Mk(x);",
    );
    assert!(
        err.contains("priv") && err.contains("cross-nodule construction"),
        "the seal refusal names the withheld construction; got: {err}"
    );
}

#[test]
fn the_unsealed_control_lets_the_foreign_nodule_construct() {
    // Same shape, minus the seal: an UNSEALED `Mk` IS constructible cross-nodule — proves the seal
    // refusal above is not vacuous (the only difference is the `priv` marker).
    check_phy(
        "phylum p\nnodule a;\npub type T = Mk(Binary{8});\nnodule b;\nuse a.T;\nfn forge(x: Binary{8}) => T = Mk(x);",
    )
    .expect("an unsealed ctor constructs cross-nodule (the control)");
}

// ---------------------------------------------------------------------------------------------
// Cross-nodule type-use + pattern-match OK (the NAME crosses; only construction is withheld).
// ---------------------------------------------------------------------------------------------

#[test]
fn the_sealed_types_name_is_usable_cross_nodule_in_a_signature() {
    // `b` imports `T` and uses it as a parameter + return type — no construction, so it type-checks
    // (the seal withholds construction, never the type NAME; DN-104 §4).
    check_phy("phylum p\nnodule a;\npub type T = priv Mk(Binary{8});\nnodule b;\nuse a.T;\nfn passthrough(x: T) => T = x;")
        .expect("the sealed type's name crosses in a signature");
}

#[test]
fn a_foreign_nodule_may_pattern_match_a_sealed_ctor() {
    // Pattern position is permitted (destructuring reveals the field but cannot forge a new value —
    // the capability property is unforgeability, not opacity; DN-104 §4). `b` receives a `T` and reads
    // its field via `match` without ever constructing one.
    check_phy(
        "phylum p\nnodule a;\npub type T = priv Mk(Binary{8});\nnodule b;\nuse a.T;\nfn peek(x: T) => Binary{8} = match x { Mk(v) => v };",
    )
    .expect("pattern-matching a sealed ctor cross-nodule is permitted");
}

// ---------------------------------------------------------------------------------------------
// Redundant seal on a non-`pub` type → never-silent refusal.
// ---------------------------------------------------------------------------------------------

#[test]
fn priv_on_a_non_pub_type_is_a_redundant_seal_refusal() {
    // A nodule-private type is already unimportable, so a `priv` ctor is redundant — refuse it (G2),
    // rather than accept a silent no-op marker.
    let err = check_nodule(
        &parse_nodule(
            "nodule solo;\ntype T = priv Mk(Binary{8});\nfn mk(x: Binary{8}) => T = Mk(x);",
        )
        .expect("parses"),
    )
    .expect_err("must refuse the redundant seal")
    .message;
    assert!(
        err.contains("redundant") && err.contains("priv"),
        "the redundant-seal refusal is explicit; got: {err}"
    );
}

// ---------------------------------------------------------------------------------------------
// `priv` inside an `object` body → never-silent parse refusal (seal scoped to `type`).
// ---------------------------------------------------------------------------------------------

#[test]
fn priv_in_an_object_body_is_a_parse_refusal() {
    let err = parse_nodule("nodule a;\npub object Cell { priv Cell(Binary{8}); }")
        .expect_err("must refuse `priv` in an object body")
        .message;
    assert!(
        err.contains("priv") && err.contains("object"),
        "the object-body seal refusal is explicit; got: {err}"
    );
}

// ---------------------------------------------------------------------------------------------
// A per-ctor subset seal: one sealed ctor withheld, a sibling unsealed ctor free.
// ---------------------------------------------------------------------------------------------

#[test]
fn a_multi_ctor_type_seals_only_the_marked_ctor() {
    // `Open` is free cross-nodule; `Closed` is withheld — the seal is per-constructor (DN-104 §2).
    check_phy(
        "phylum p\nnodule a;\npub type T = Open(Binary{8}) | priv Closed(Binary{8});\nnodule b;\nuse a.T;\nfn ok(x: Binary{8}) => T = Open(x);",
    )
    .expect("the unsealed sibling ctor constructs cross-nodule");

    let err = phy_err(
        "phylum p\nnodule a;\npub type T = Open(Binary{8}) | priv Closed(Binary{8});\nnodule b;\nuse a.T;\nfn forge(x: Binary{8}) => T = Closed(x);",
    );
    assert!(
        err.contains("priv") && err.contains("Closed"),
        "the sealed sibling ctor is withheld cross-nodule; got: {err}"
    );
}

// ---------------------------------------------------------------------------------------------
// CLOSED (DN-112 Rank 1 / M-1036 — nodule-qualified type identity): a same-named local shadow no
// longer bypasses the seal. Was `known_gap_a_same_named_local_shadow_type_bypasses_the_seal`
// (pinned the unsound `Ok`); flipped here to assert the refusal, per that test's own instructions.
// ---------------------------------------------------------------------------------------------

#[test]
fn a_same_named_local_shadow_type_no_longer_bypasses_the_seal() {
    // Mycelium used to resolve types by BARE NAME, re-resolved in the *calling* nodule's own scope
    // — "local decl shadows import" (RFC-0006 §4.3 / M-662) meant a foreign nodule could declare
    // its OWN unsealed type of the SAME NAME — never importing the real sealed `a.T` — and pass a
    // value of its local decoy `T` where `a.T` was expected, because both resolved to the bare
    // name "T". DN-112 Rank 1 (M-1036) closes this: every `Ty::Data` identity is now nodule-
    // qualified (`a::T` vs `b::T`), and an imported function's signature is baked against its
    // *own* declaring nodule at export time (never re-derived at a foreign call site) — so `b`'s
    // decoy `T` and `a`'s real `T` are structurally distinct types, and passing one where the
    // other is expected is an ordinary, never-silent type mismatch (DN-112 §10 item 2's own
    // framing: "a never-silent type mismatch, not a values-forged pass" — not necessarily the
    // `priv`-seal diagnostic itself, since the mismatch is caught by ordinary type equality before
    // the seal check would even need to fire).
    let result = check_phy(
        "phylum p\nnodule a;\npub type T = priv Mk(Binary{8});\npub fn use_t(x: T) => Binary{8} = match x { Mk(v) => v };\nnodule b;\nuse a.use_t;\ntype T = Mk(Binary{8});\nfn forge() => T = Mk(0b00000000);\npub fn exploit() => Binary{8} = use_t(forge());",
    );
    let err = result.expect_err(
        "the shadow-bypass exploit must now be refused (DN-112 Rank 1 / M-1036) — a same-named \
         local decoy no longer silently forges a sealed foreign type",
    );
    assert!(
        err.message.contains("T") || err.message.to_lowercase().contains("type"),
        "the refusal should be a type-identity mismatch naming the mismatched type; got: {}",
        err.message
    );
}

// ---------------------------------------------------------------------------------------------
// Non-vacuity + no over-restriction (DN-112 §9 invariant i / §10 item 5's backward-compat story):
// two UNRELATED nodules independently declaring a same-named, unsealed type — never mixed at a
// call site — must still type-check exactly as before this fix (no false cross-nodule collision).
// ---------------------------------------------------------------------------------------------

#[test]
fn unrelated_same_named_types_in_different_nodules_used_independently_still_check() {
    // `a` and `b` each declare their OWN `type T`, used only within their own bodies — never
    // mixed. The qualified-identity mechanism must not manufacture a false collision here.
    check_phy(
        "phylum p\n\
         nodule a;\n\
         type T = Mk(Binary{8});\n\
         pub fn make_a() => Binary{8} = match Mk(0b0000_0001) { Mk(v) => v };\n\
         nodule b;\n\
         type T = Mk(Binary{4});\n\
         pub fn make_b() => Binary{4} = match Mk(0b0001) { Mk(v) => v };",
    )
    .expect(
        "two unrelated same-named (different-shape!) types, never mixed, must both check \
         (no false-positive collision across unrelated nodules — DN-112 §9 invariant i)",
    );
}

#[test]
fn cross_nodule_mixing_of_unsealed_same_named_types_is_also_refused() {
    // The general identity fix applies to ANY same-named-different-home mixing, not just the
    // sealed-constructor case — an UNSEALED type from `b` passed where `a`'s same-named type is
    // expected is ALSO now a type mismatch (demonstrating the fix is about identity, not merely
    // ctor-seal bookkeeping).
    let err = phy_err(
        "phylum p\n\
         nodule a;\n\
         pub type T = Mk(Binary{8});\n\
         pub fn use_t(x: T) => Binary{8} = match x { Mk(v) => v };\n\
         nodule b;\n\
         use a.use_t;\n\
         type T = Mk(Binary{8});\n\
         fn forge() => T = Mk(0b0000_0000);\n\
         pub fn exploit() => Binary{8} = use_t(forge());",
    );
    assert!(
        !err.is_empty(),
        "an unsealed cross-nodule same-name mix is still a real type mismatch"
    );
}

#[test]
fn a_legitimate_factory_returning_a_sealed_type_still_works_across_nodules() {
    // Non-regression control (DN-104's own recommended pattern): `b` never constructs the sealed
    // type directly, only receives it from `a`'s `pub fn` factory and passes it straight back to
    // another `a`-owned function — the baked-signature mechanism (DN-112 Rank 1) must not
    // over-restrict this well-behaved, always-legitimate cross-nodule flow.
    check_phy(
        "phylum p\n\
         nodule a;\n\
         pub type T = priv Mk(Binary{8});\n\
         pub fn mint(x: Binary{8}) => T = Mk(x);\n\
         pub fn read(t: T) => Binary{8} = match t { Mk(v) => v };\n\
         nodule b;\n\
         use a.mint;\n\
         use a.read;\n\
         pub fn roundtrip() => Binary{8} = read(mint(0b0000_0001));",
    )
    .expect("a value minted by its home nodule's factory and passed straight back still checks");
}

// ---------------------------------------------------------------------------------------------
// CRITICAL #1 (found reproducing on top of the landed DN-112 Rank 1 fix): `check_app_generic_fn`
// re-resolved every parameter FRESH against the caller's own registry, ignoring the baked
// `imports.resolved_fn_sigs` entry the monomorphic path (`check_app`) already consulted — so a
// callee with ANY (even wholly unrelated) type parameter reopened the same-nodule-shadow bypass.
// Fixed by mirroring the monomorphic path's baked-signature preference in the generic path too.
// ---------------------------------------------------------------------------------------------

#[test]
fn a_generic_callee_no_longer_bypasses_the_seal_via_fresh_reresolution() {
    // `use_t[X](x: T, y: X) => X = y` is generic over `X` (unrelated to the sealed `T`). Pre-fix,
    // `check_app_generic_fn` resolved `x`'s parameter type (`T`) FRESH against `b`'s own registry
    // for EVERY call — including this one — so `b`'s local decoy `T` (never imported, never
    // sealed) silently satisfied `x: T`, forging a value of the sealed `a::T` one level up from
    // the already-fixed monomorphic-callee exploit (DN-112 §10 item 2's own shape, generic-arity
    // variant). Fixed by consulting `imports.resolved_fn_sigs` (the baked, declaring-nodule-
    // resolved signature) here too, exactly as `check_app`'s monomorphic path already does.
    let result = check_phy(
        "phylum p\n\
         nodule a;\n\
         pub type T = priv Mk(Binary{8});\n\
         pub fn use_t[X](x: T, y: X) => X = y;\n\
         nodule b;\n\
         use a.use_t;\n\
         type T = Mk(Binary{8});\n\
         fn forge() => T = Mk(0b0000_0000);\n\
         pub fn exploit() => Binary{1} = use_t(forge(), 0b1);",
    );
    let err = result.expect_err(
        "the generic-callee variant of the shadow-bypass exploit must be refused too (CRITICAL #1 \
         fix) — a same-named local decoy must not forge a sealed foreign type through a generic \
         call path either, even when the callee has an unrelated type parameter",
    );
    assert!(
        err.message.contains('T') || err.message.to_lowercase().contains("type"),
        "the refusal should be a type-identity mismatch naming the mismatched type; got: {}",
        err.message
    );
}

#[test]
fn a_legitimate_generic_cross_nodule_call_referencing_an_imported_type_still_checks() {
    // Non-vacuity / non-over-restriction control for CRITICAL #1: a well-behaved generic call that
    // references a REAL imported (never shadowed) cross-nodule sealed type in a FIXED parameter,
    // alongside its own unrelated type parameter, must still check — the baked-signature
    // preference in the generic path must not over-restrict the legitimate case. `b` never
    // constructs `T` directly; it only receives it from `a`'s factory `mint` and passes it
    // straight into the generic `use_t`.
    check_phy(
        "phylum p\n\
         nodule a;\n\
         pub type T = priv Mk(Binary{8});\n\
         pub fn mint(x: Binary{8}) => T = Mk(x);\n\
         pub fn use_t[X](x: T, y: X) => X = y;\n\
         nodule b;\n\
         use a.mint;\n\
         use a.use_t;\n\
         pub fn ok() => Binary{1} = use_t(mint(0b0000_0001), 0b1);",
    )
    .expect(
        "a legitimate generic call passing a genuinely-imported cross-nodule sealed value through \
         a fixed parameter, alongside an unrelated type parameter, still checks (CRITICAL #1 fix \
         must not over-restrict)",
    );
}

// ---------------------------------------------------------------------------------------------
// CRITICAL #2 (found scrutinizing `lookup_data`'s own documented residual): the same-nodule-
// shadow-plus-legitimate-cross-nodule-reach fallback is used in `normalize_pattern`, called from
// `Cx::check_pattern` — INSIDE the checker, not merely elaboration. The `lookup_data` doc's claim
// "the static check stays sound" was FALSE for this call path: an UNSEALED type still lets the
// checker bind a pattern's field type to the WRONG (locally-shadowed) `DataInfo`. Fixed by a
// home-checked lookup (`lookup_data_home_checked`) at the pattern-normalization call sites,
// refusing explicitly (G2) on a home mismatch — the conservative closure, since a single
// bare-keyed registry cannot hold both the shadow's and the foreign type's `DataInfo` at once.
// ---------------------------------------------------------------------------------------------

#[test]
fn a_shadow_plus_foreign_reach_pattern_match_no_longer_type_confuses() {
    // `T` is UNSEALED — no seal, no capability gate, purely a type-IDENTITY bug. `b` shadows `T`
    // locally (`Binary{4}`) and legitimately reaches the REAL `a::T` (`Binary{8}`) via the
    // imported factory `make()`. Pre-fix, `match make() { Mk(v) => v }` type-checked `v` against
    // `b`'s own (WRONG) shadow `DataInfo` — the checker accepted `v: Binary{4}` while the value
    // actually produced at runtime is `a::T`'s real `Binary{8}` field.
    //
    // The exploit's return type is deliberately `Binary{4}` (the SHADOW's width, not the real
    // `Binary{8}`) — matching the WRONG pre-fix inference exactly, so the bug is not incidentally
    // caught by an unrelated return-type mismatch (as a naive `Binary{8}` return would be, since
    // `v`'s pre-fix WRONG inferred type is `Binary{4}`; the checker-accepted mismatch is between
    // `v`'s *checked* type and the value's *real runtime* shape, not between two checked types).
    // Fixed: the home-checked lookup refuses this pattern explicitly rather than silently
    // resolving against the shadow's shape.
    let err = phy_err(
        "phylum p\n\
         nodule a;\n\
         pub type T = Mk(Binary{8});\n\
         pub fn make() => T = Mk(0b0000_0001);\n\
         nodule b;\n\
         use a.make;\n\
         type T = Mk(Binary{4});\n\
         pub fn exploit() => Binary{4} = match make() { Mk(v) => v };",
    );
    assert!(
        !err.is_empty(),
        "the shadow-plus-foreign-reach pattern match must be refused (CRITICAL #2 fix) rather \
         than silently type-checking the binder against the wrong (shadow) DataInfo"
    );
}

#[test]
fn the_no_shadow_control_pattern_still_checks_correctly() {
    // Non-vacuity / non-over-restriction control for CRITICAL #2: the SAME shape, minus the local
    // shadow in `b` — must still check (and the binder correctly gets `a::T`'s real field type).
    // `b` imports `T` explicitly (`use a.T;`, matching the existing
    // `a_foreign_nodule_may_pattern_match_a_sealed_ctor` convention) so its own registry has a
    // bare-keyed entry to pattern-match against — pattern-matching a cross-nodule type's
    // constructors requires the type's DataInfo be locally registered under some bare key,
    // pre-existing (not introduced by the CRITICAL #2 fix): the previous `lookup_data(...)
    // .expect(...)` would have PANICKED on an unregistered bare name exactly the same way.
    check_phy(
        "phylum p\n\
         nodule a;\n\
         pub type T = Mk(Binary{8});\n\
         pub fn make() => T = Mk(0b0000_0001);\n\
         nodule b;\n\
         use a.T;\n\
         use a.make;\n\
         pub fn ok() => Binary{8} = match make() { Mk(v) => v };",
    )
    .expect(
        "without a local shadow, the cross-nodule pattern match still checks (no \
         over-restriction from the CRITICAL #2 home-check)",
    );
}

// ---------------------------------------------------------------------------------------------
// DN-112 §10 item 3 — impl-coherence twin: two same-named-different-home types each carry a
// distinct impl of the same trait, with NO false-overlap refusal; a genuine same-home overlap
// still refuses (the orphan/global-uniqueness rule is unchanged for the real collision case).
// ---------------------------------------------------------------------------------------------

#[test]
fn same_named_different_home_types_each_get_their_own_coherent_instance() {
    // `a::Dup` and `b::Dup` are unrelated same-named types; each `impl`s the SAME trait `Probe`
    // (an arbitrary fixture trait name — renamed from the original `Show` when DN-127/M-1090
    // seeded a built-in prelude trait of that name; mitigation #14: this per-file ad-hoc fixture
    // name has no bearing on the test's actual subject, so it moves rather than the built-in).
    // Pre-fix, `type_head` was bare-name-keyed (`Data:Dup` for both) — a false overlap. Post-fix,
    // `type_head` embeds the qualified name (`Data:a::Dup` vs `Data:b::Dup`) — both instances
    // register, no coherence violation.
    check_phy(
        "phylum p\n\
         nodule a;\n\
         pub trait Probe[A] { fn probe(x: A) => Binary{1}; };\n\
         type Dup = DA(Binary{8});\n\
         impl Probe[Dup] for Dup { fn probe(x: Dup) => Binary{1} = 0b1; };\n\
         nodule b;\n\
         use a.Probe;\n\
         type Dup = DB(Binary{4});\n\
         impl Probe[Dup] for Dup { fn probe(x: Dup) => Binary{1} = 0b0; };",
    )
    .expect(
        "two same-named-different-home types each impl the same trait without a false-overlap \
         refusal (DN-112 §5 / §10 item 3 — the coherence key is now nodule-qualified)",
    );
}

#[test]
fn a_genuine_same_home_overlap_still_refuses() {
    // Two impls of the SAME trait for the SAME (single) type — a real coherence violation, must
    // stay refused exactly as before this fix (the qualification must not loosen genuine overlap).
    let err = phy_err(
        "nodule a;\n\
         trait Probe[A] { fn probe(x: A) => Binary{1}; };\n\
         type Dup = DA(Binary{8});\n\
         impl Probe[Dup] for Dup { fn probe(x: Dup) => Binary{1} = 0b1; };\n\
         impl Probe[Dup] for Dup { fn probe(x: Dup) => Binary{1} = 0b0; };",
    );
    assert!(
        !err.is_empty(),
        "a genuine same-home double-impl must still be refused as a coherence violation"
    );
}

// ---------------------------------------------------------------------------------------------
// DN-112 §10 item 4 — mangling collision-freedom: two same-named-different-home types (each
// declared alone in its own program, so `PhylumEnv::link`'s pre-existing bare-name-uniqueness
// invariant is never in play) monomorphize to DISTINCT mangled registry keys — never aliased to
// one entry. Witnessed through the public `monomorphize` API (mono.rs's mangling internals are
// crate-private; this is the end-to-end behavioral consequence DN-112 §7 requires).
// ---------------------------------------------------------------------------------------------

#[test]
fn same_bare_named_types_in_different_homes_mangle_to_distinct_registry_keys() {
    // `T` is GENERIC (`T[X]`) so `monomorphize` must actually run the mangling pass (`mangle_decl`)
    // to emit `T[Binary{8}]`'s monomorphic instance — a monomorphic (already-closed) program takes
    // a fast passthrough path that never mangles at all, which would make this witness vacuous.
    let env_a = check_nodule(
        &parse_nodule(
            "nodule a;\ntype T[X] = Mk(X);\npub fn main() => T[Binary{8}] = Mk(0b0000_0001);",
        )
        .expect("parses"),
    )
    .expect("checks");
    let mono_a = mycelium_l1::monomorphize(&env_a, "main").expect("monomorphizes");

    let env_b = check_nodule(
        &parse_nodule(
            "nodule b;\ntype T[X] = Mk(X);\npub fn main() => T[Binary{8}] = Mk(0b0000_0001);",
        )
        .expect("parses"),
    )
    .expect("checks");
    let mono_b = mycelium_l1::monomorphize(&env_b, "main").expect("monomorphizes");

    // Both programs declare a bare-surface `T` with the identical shape; their mangled/registered
    // identities must differ (home `a` vs home `b`) — collision-freedom, not merely non-crashing.
    let keys_a: std::collections::BTreeSet<&String> = mono_a.types.keys().collect();
    let keys_b: std::collections::BTreeSet<&String> = mono_b.types.keys().collect();
    assert_ne!(
        keys_a, keys_b,
        "same-named-different-home types must mangle to DISTINCT registry keys \
         (DN-112 §7 mangling collision-freedom); got the same key sets {keys_a:?}"
    );
    // Neither side's `T[Binary{8}]` mangled to the bare (unqualified) pre-fix form that both would
    // have collided on — confirming this is a real qualification effect, not an unrelated diff.
    assert!(
        !keys_a.iter().any(|k| k.as_str() == "T$Binary8"),
        "post-fix, a NAMED nodule's type must NOT mangle to the bare pre-fix form; got {keys_a:?}"
    );
}

// ---------------------------------------------------------------------------------------------
// DN-112 §10 item 9 (ratification CONDITION — the builtin/prelude uniform-home invariant, §9's
// own sharpest adversarial finding): `Bool` (and, structurally, any `PRELUDE_HOME` type) MUST stay
// resolvable under ONE reserved home across every nodule — a program that computes a `Bool` in one
// nodule and consumes it (via `if`/`match`) in ANOTHER must still type-check. A resolution path
// that over-qualified `Bool` per-current-nodule would make this refuse with a false type mismatch.
// ---------------------------------------------------------------------------------------------

#[test]
fn bool_crosses_nodule_boundaries_without_a_false_mismatch() {
    // `a` computes a `Bool` (via `if`, which desugars to a `Match` on the prelude `Bool`) and
    // returns it from a `pub fn`; `b` imports that fn and immediately `if`s on the result — an
    // over-qualified `Bool` (e.g. stamped `a::Bool`) would make `b`'s own `if`-condition check (a
    // BARE, always-`PRELUDE_HOME` `Bool` on `b`'s side) refuse with a spurious type mismatch.
    check_phy(
        "phylum p\n\
         nodule a;\n\
         pub fn a_is_zero(x: Binary{8}) => Bool = match x { 0b0000_0000 => True, _ => False };\n\
         nodule b;\n\
         use a.a_is_zero;\n\
         pub fn b_consumes(x: Binary{8}) => Binary{1} = \
             if a_is_zero(x) then 0b1 else 0b0;",
    )
    .expect(
        "Bool must resolve under the SAME reserved home in every nodule — a cross-nodule Bool \
         round-trip must not spuriously mismatch (DN-112 §9 invariant i / §10 item 9)",
    );
}

#[test]
fn tuple_types_cross_nodule_boundaries_without_a_false_mismatch() {
    // The synthetic `Tuple$N` family carries the same single-reserved-home invariant as `Bool`
    // (DN-112 §9 invariant i) — a tuple built in one nodule and destructured in another must not
    // spuriously mismatch either.
    check_phy(
        "phylum p\n\
         nodule a;\n\
         pub fn a_pair() => (Binary{8}, Binary{8}) = (0b0000_0001, 0b0000_0010);\n\
         nodule b;\n\
         use a.a_pair;\n\
         pub fn b_consumes() => Binary{8} = match a_pair() { (x, _) => x };",
    )
    .expect(
        "Tuple$N must resolve under the SAME reserved home in every nodule (DN-112 §9 invariant i)",
    );
}

// ---------------------------------------------------------------------------------------------
// Elab-sibling scrutiny (CRITICAL #2's flagged follow-up): `elab::field_spec`/
// `ty_to_field_ty_ref` strip a nullary `Ty::Data`'s possibly-qualified identity to its LOCAL name
// for the L0 `FieldSpec`/`FieldTyRef` bridge — the SAME "collapse qualified → bare" shape as
// `lookup_data`'s own residual, but reachable WITHOUT ever pattern-matching the mismatched field
// (a wildcard sub-pattern `Wrap(_)` never queries the field's identity in `normalize_pattern`, so
// CRITICAL #2's check-time fix never fires for it) — confirmed a REAL, distinct hole and fixed
// the same conservative way (home-checked; stage the field, `build_registry`'s existing
// "skip type; Residual if reachable" mechanism closes it).
// ---------------------------------------------------------------------------------------------

#[test]
fn a_wildcard_shielded_shadow_plus_foreign_field_no_longer_silently_misregisters() {
    // `Something = Wrap(T)` is declared in `a` (`T` home `a`, `Binary{8}`); `b` imports
    // `Something` and `make_something` but never imports `T` itself — `b` locally shadows `T`
    // with an UNRELATED shape (`Binary{4}`). `b`'s `peek` pattern-matches `Something` but uses a
    // WILDCARD for the `T`-typed field (`Wrap(_)`) — never triggering CRITICAL #2's
    // `normalize_pattern` home-check (a wildcard binds nothing, so it never queries the field's
    // `DataInfo`). Pre-fix, `elab::build_registry(b_env)` would resolve `Something`'s `Wrap`
    // field (`FieldSpec::Data("T")`, stripped from qualified `a::T`) against `b`'s own registry
    // entry for bare `"T"` — `b`'s shadow (`Binary{4}`), NOT `a`'s real `T` (`Binary{8}`) — a
    // content-addressed registry entry built with the WRONG field shape, entirely outside any
    // pattern-matching path. Fixed: the same home-checked lookup stages (skips) this field,
    // so `Something` never gets an (incorrectly-shaped) registry entry at all — a `T` value
    // never silently gets `Binary{4}`'s shape baked into `Something`'s content hash.
    let phy = check_phy(
        "phylum p\n\
         nodule a;\n\
         pub type T = Mk(Binary{8});\n\
         pub type Something = Wrap(T);\n\
         pub fn make_something() => Something = Wrap(Mk(0b0000_0001));\n\
         nodule b;\n\
         use a.Something;\n\
         use a.make_something;\n\
         type T = Mk(Binary{4});\n\
         pub fn peek() => Binary{1} = match make_something() { Wrap(_) => 0b1 };",
    )
    .expect(
        "the checker itself accepts this program — the wildcard sub-pattern never triggers \
         CRITICAL #2's pattern-normalization home-check, so this is a genuinely DISTINCT \
         reachable path into the same aliasing shape, not a re-hit of CRITICAL #2",
    );
    let (_, b_env) = phy
        .nodules
        .iter()
        .find(|(p, _)| p.0.len() == 1 && p.0[0] == "b")
        .expect("nodule b is present");

    // `Something`'s field-shape aliasing must never silently reach a built registry entry keyed
    // "Something" whose Wrap field carries `b`'s shadow shape. Fixed: `field_spec` stages
    // (skips) the mismatched field, so `Something` gets NO registry entry — confirmed by asking
    // the registry for its declaration hash: `None` (staged, not "shaped either way").
    let registry = mycelium_l1::elab::build_registry(b_env)
        .expect("build_registry: an unreferenced staged type is not a dangling-ref failure");
    assert!(
        registry.decl_hash("Something").is_none(),
        "post-fix, `Something`'s home-mismatched field must leave it UNREGISTERED (staged) — \
         never silently registered under the wrong (shadow) field shape"
    );

    // Elaborating an entry that actually NEEDS `Something`'s registry entry surfaces the gap
    // never-silently (an explicit `ElabError`), never a wrong-shaped construction.
    let elab_result = mycelium_l1::elaborate(b_env, "peek");
    assert!(
        elab_result.is_err(),
        "elaborating `peek` (which constructs/matches `Something`) must surface the staged \
         field as an explicit residual, never silently elaborate against the wrong field shape; \
         got: {elab_result:?}"
    );
}

// ---------------------------------------------------------------------------------------------
// M-1036 residual close — the FOURTH bare-name-collapse site, found in `crate::mono` by a
// systematic re-verify of every DN-112 Rank 1 consumer. `crate::mono::emit_data` (and its
// siblings `ctor_data_instance`/`ctor_field_tys`/`for_elem_ty`) called the plain
// `checkty::lookup_data` unguarded — reachable purely through `monomorphize`, independent of
// BOTH the checker's own (already home-checked) `normalize_pattern`/`resolve_ty` paths AND
// `elab`'s own CRITICAL #2-sibling `field_spec` fix (the wildcard-shielded-shadow test above).
// The wildcard sub-pattern (`Wrap(_)`) never triggers any pattern-position home-check (a
// wildcard queries no `DataInfo`), so `mono`'s own consultation of the SAME bare-keyed registry
// was the last unguarded consumer of this exact field-type reference.
// ---------------------------------------------------------------------------------------------

#[test]
fn a_wildcard_shielded_shadow_no_longer_silently_monomorphizes_the_wrong_shape() {
    // `b` imports `Something` from `a` but never imports `T` itself — `b` locally shadows `T` with
    // an UNRELATED shape (`Binary{4}` vs `a::T`'s real `Binary{8}`). `exploit` takes its `Something`
    // as a VALUE PARAMETER (never constructs one — this deliberately avoids `monomorphize`'s own
    // separate, unrelated "re-derive a callee's body against the caller's own ctor namespace"
    // requirement, which would otherwise trip on `Mk`'s own bare-name visibility before ever
    // reaching this fn's target — the field-type-driven registry consultation) and its `match` uses
    // a wildcard sub-pattern (`Wrap(_)`), so the CHECKER itself accepts this program (the same
    // shape the checker/elab-level witness above exercises). The exploit surfaces only when
    // `monomorphize` runs DIRECTLY on `b`'s own per-nodule `Env` (the same probe the
    // `same_bare_named_types_in_different_homes_…` witness above uses): to emit `exploit`'s own
    // parameter type `Something`, mono must also emit its `Wrap` field type `a::T` — pre-fix, this
    // silently registered `a::T`'s mangled entry using `b`'s WRONG (locally-shadowed) `Binary{4}`
    // shape instead of `a::T`'s real `Binary{8}` one. `id[X]` is a deliberately-unreachable generic
    // fn, present only to force `monomorphize` off its already-monomorphic fast pass-through (which
    // would never re-consult the registry at all, making the exploit unreachable).
    let phy = check_phy(
        "phylum p\n\
         nodule a;\n\
         pub type T = Mk(Binary{8});\n\
         pub type Something = Wrap(T);\n\
         nodule b;\n\
         use a.Something;\n\
         type T = Shadow(Binary{4});\n\
         pub fn id[X](x: X) => X = x;\n\
         pub fn exploit(s: Something) => Binary{1} = match s { Wrap(_) => 0b1 };",
    )
    .expect(
        "the checker itself accepts this program — the wildcard sub-pattern never triggers a \
         pattern-position home-check (the same shape the elab-sibling witness above exercises)",
    );
    let (_, b_env) = phy
        .nodules
        .iter()
        .find(|(p, _)| p.0.len() == 1 && p.0[0] == "b")
        .expect("nodule b is present");

    let result = mycelium_l1::monomorphize(b_env, "exploit");
    let err = result.expect_err(
        "monomorphizing `b`'s own per-nodule Env directly must now REFUSE (M-1036 residual \
         close) rather than silently emit `a::T`'s registry entry under `b`'s WRONG (shadowed) \
         `Binary{4}` shape instead of the real `Binary{8}` one",
    );
    let msg = err.to_string();
    assert!(
        msg.contains('T')
            || msg.to_lowercase().contains("mismatch")
            || msg.to_lowercase().contains("type"),
        "the refusal should name the mismatched type-identity; got: {msg}"
    );
}

#[test]
fn the_no_shadow_control_still_monomorphizes_the_correct_shape() {
    // Non-vacuity / non-over-restriction control: the SAME shape, minus `b`'s local shadow — `b`
    // instead genuinely imports `T` (`use a.T;`) — must still `monomorphize` successfully, AND the
    // emitted mangled registry entry for `a::T` must carry the REAL `Binary{8}` shape (proving the
    // fix routes to the CORRECT declaration, not merely "refuses whenever ambiguous").
    let phy = check_phy(
        "phylum p\n\
         nodule a;\n\
         pub type T = Mk(Binary{8});\n\
         pub type Something = Wrap(T);\n\
         nodule b;\n\
         use a.T;\n\
         use a.Something;\n\
         pub fn id[X](x: X) => X = x;\n\
         pub fn exploit(s: Something) => Binary{1} = match s { Wrap(_) => 0b1 };",
    )
    .expect("checks");
    let (_, b_env) = phy
        .nodules
        .iter()
        .find(|(p, _)| p.0.len() == 1 && p.0[0] == "b")
        .expect("nodule b is present");

    let mono = mycelium_l1::monomorphize(b_env, "exploit").expect(
        "without the local shadow, monomorphization must still succeed (no over-restriction \
         from the M-1036 home-check)",
    );
    let t_entry = mono
        .types
        .get("a$H$T")
        .expect("the real a::T is registered under its mangled (separator-normalized) name");
    let mk = t_entry
        .ctors
        .iter()
        .find(|c| c.name.starts_with("Mk"))
        .expect("the Mk constructor is present");
    assert_eq!(
        mk.fields,
        vec![mycelium_l1::checkty::Ty::Binary(
            mycelium_l1::checkty::Width::Lit(8)
        )],
        "the emitted shape must be a::T's REAL Binary{{8}} field, never b's shadow Binary{{4}} one"
    );
}
