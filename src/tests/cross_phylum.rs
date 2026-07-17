//! White-box unit tests for the DN-113 Rank 1 / M-1060 cross-phylum internals
//! (`qualify_cross_phylum` / `qualify_ty_cross_phylum` / `merge_phyla_exports`) — the units the
//! public-API integration tests (`crates/mycelium-l1/tests/cross_phylum.rs`) exercise end-to-end.
//! These tests pin the exact re-homing string shape and the merge's key/value transforms in
//! isolation, so a future refactor of `resolve_imports`'s cross-phylum branch has a fast, precise
//! regression signal independent of the slower phylum-check integration path.

use crate::ast::Path;
use crate::checkty::*;
use std::collections::BTreeMap;

// ---- `qualify_cross_phylum` (the identity re-homing predicate) --------------------------------

#[test]
fn qualify_cross_phylum_prepends_the_dep_name_to_an_ordinary_home() {
    assert_eq!(qualify_cross_phylum("nod", "dep"), "dep::nod");
    assert_eq!(qualify_cross_phylum("a.b", "dep"), "dep::a.b");
}

#[test]
fn qualify_cross_phylum_leaves_the_prelude_sentinel_bare() {
    // DN-112 §9 invariant i: a builtin/synthetic type resolves identically everywhere, even across
    // a phylum boundary — never re-qualified further.
    assert_eq!(qualify_cross_phylum(PRELUDE_HOME, "dep"), PRELUDE_HOME);
}

#[test]
fn qualify_cross_phylum_maps_an_empty_home_to_just_the_dep_name() {
    // The anonymous/header-less-nodule residual (`nodule_home`'s doc comment): an empty home
    // becomes just `dep_name`, not the visually-ugly `"dep_name::"`.
    assert_eq!(qualify_cross_phylum("", "dep"), "dep");
}

#[test]
fn qualify_cross_phylum_is_injective_over_distinct_dep_names_for_the_same_home() {
    // Two different dependencies never collapse to the same re-homed identity for the same
    // (possibly-colliding) inner home string — the whole point of the phylum-qualifier dimension.
    assert_ne!(
        qualify_cross_phylum("math", "dep_a"),
        qualify_cross_phylum("math", "dep_b")
    );
}

// ---- `qualify_ty_cross_phylum` (recursive `Ty::Data` re-homing) -------------------------------

fn dep_types_with(home_of_t: &str) -> BTreeMap<String, DataInfo> {
    let mut m = BTreeMap::new();
    m.insert(
        "T".to_owned(),
        DataInfo {
            name: "T".to_owned(),
            home: home_of_t.to_owned(),
            params: vec![],
            ctors: vec![],
        },
    );
    m
}

#[test]
fn qualify_ty_cross_phylum_rewrites_a_non_prelude_data_identity() {
    let dep_types = dep_types_with("math");
    let ty = Ty::Data("math::T".to_owned(), vec![]);
    let got = qualify_ty_cross_phylum(&ty, "dep", &dep_types);
    assert_eq!(got, Ty::Data("dep::math::T".to_owned(), vec![]));
}

#[test]
fn qualify_ty_cross_phylum_leaves_a_prelude_data_identity_bare() {
    // `T`'s OWN home is the prelude sentinel (the oracle this function consults) — even though the
    // bare name alone is indistinguishable from an anonymous-nodule non-prelude type by string
    // shape, the registry lookup disambiguates correctly.
    let dep_types = dep_types_with(PRELUDE_HOME);
    let ty = Ty::Data("T".to_owned(), vec![]);
    let got = qualify_ty_cross_phylum(&ty, "dep", &dep_types);
    assert_eq!(
        got,
        Ty::Data("T".to_owned(), vec![]),
        "prelude identity stays bare"
    );
}

#[test]
fn qualify_ty_cross_phylum_recurses_into_type_arguments_fn_and_seq() {
    let dep_types = dep_types_with("math");
    let inner = Ty::Data("math::T".to_owned(), vec![]);
    let applied = Ty::Data("List".to_owned(), vec![inner.clone()]);
    let got = qualify_ty_cross_phylum(&applied, "dep", &dep_types);
    assert_eq!(
        got,
        Ty::Data(
            "dep::List".to_owned(),
            vec![Ty::Data("dep::math::T".to_owned(), vec![])]
        ),
        "a type argument nested inside `Data` is re-homed too"
    );

    let fn_ty = Ty::Fn(Box::new(inner.clone()), Box::new(inner.clone()));
    let got_fn = qualify_ty_cross_phylum(&fn_ty, "dep", &dep_types);
    assert_eq!(
        got_fn,
        Ty::Fn(
            Box::new(Ty::Data("dep::math::T".to_owned(), vec![])),
            Box::new(Ty::Data("dep::math::T".to_owned(), vec![]))
        )
    );

    let seq_ty = Ty::Seq(Box::new(inner), 4);
    let got_seq = qualify_ty_cross_phylum(&seq_ty, "dep", &dep_types);
    assert_eq!(
        got_seq,
        Ty::Seq(Box::new(Ty::Data("dep::math::T".to_owned(), vec![])), 4)
    );
}

#[test]
fn qualify_ty_cross_phylum_leaves_non_data_scalar_reprs_unchanged() {
    let dep_types = BTreeMap::new();
    let ty = Ty::Binary(Width::Lit(8));
    assert_eq!(qualify_ty_cross_phylum(&ty, "dep", &dep_types), ty);
}

// ---- `merge_phyla_exports` (the qualifier-dimension merge) -------------------------------------

fn dep_data_info(home: &str) -> DataInfo {
    DataInfo {
        name: "T".to_owned(),
        home: home.to_owned(),
        params: vec![],
        ctors: vec![],
    }
}

fn exports_with_one_pub_type(qual: &str, home: &str) -> Exports {
    let mut e = Exports::default();
    e.declared.insert(qual.to_owned(), true);
    e.types.insert(qual.to_owned(), dep_data_info(home));
    e
}

fn resolved_phylum(exports: Exports) -> ResolvedPhylum {
    ResolvedPhylum::resolve(
        mycelium_core::ContentHash::from_parts("blake3", &"a".repeat(64)).unwrap(),
        &crate::ast::Phylum::of_one(crate::ast::Nodule {
            path: Path(vec![]),
            std_sys: false,
            items: vec![],
        }),
        &Phyla::default(),
    )
    .map(|mut rp| {
        rp.exports = exports;
        rp
    })
    .expect("an empty nodule always checks")
}

#[test]
fn merge_phyla_exports_is_a_no_op_on_an_empty_phyla() {
    let mut local = Exports::default();
    local.declared.insert("a.X".to_owned(), true);
    let merged = merge_phyla_exports(local, &Phyla::default());
    assert_eq!(merged.declared.len(), 1);
    assert!(merged.declared.contains_key("a.X"));
}

#[test]
fn merge_phyla_exports_prefixes_every_dep_key_and_rehomes_the_type() {
    let dep_exports = exports_with_one_pub_type("math.T", "math");
    let mut deps = BTreeMap::new();
    deps.insert("collections".to_owned(), resolved_phylum(dep_exports));
    let phyla = Phyla::from_deps(deps);

    let merged = merge_phyla_exports(Exports::default(), &phyla);
    assert_eq!(
        merged.declared.get("collections::math.T"),
        Some(&true),
        "the merged key carries the dep-local-name prefix"
    );
    let info = merged
        .types
        .get("collections::math.T")
        .expect("the type entry is merged under the same prefixed key");
    assert_eq!(
        info.home, "collections::math",
        "the merged DataInfo's home is re-homed at the phylum boundary too"
    );
    assert!(
        !merged.declared.contains_key("math.T"),
        "the UNPREFIXED key must not also appear (no accidental bare-name collapse)"
    );
}

#[test]
fn merge_phyla_exports_never_overwrites_a_local_entry_with_a_dep_one() {
    // A local `a.X` and a dep `collections::a.X` share no key (the `::` boundary makes them
    // structurally distinct strings) — the merge must never let one shadow the other.
    let mut local = Exports::default();
    local.declared.insert("a.X".to_owned(), true);
    let dep_exports = exports_with_one_pub_type("a.X", "a");
    let mut deps = BTreeMap::new();
    deps.insert("collections".to_owned(), resolved_phylum(dep_exports));
    let phyla = Phyla::from_deps(deps);

    let merged = merge_phyla_exports(local, &phyla);
    assert_eq!(merged.declared.get("a.X"), Some(&true));
    assert_eq!(merged.declared.get("collections::a.X"), Some(&true));
    assert_eq!(merged.declared.len(), 2, "both entries coexist distinctly");
}

// ---- `Phyla::has_dep` ---------------------------------------------------------------------------

#[test]
fn phyla_has_dep_reports_declared_dependencies_only() {
    let dep_exports = exports_with_one_pub_type("math.T", "math");
    let mut deps = BTreeMap::new();
    deps.insert("collections".to_owned(), resolved_phylum(dep_exports));
    let phyla = Phyla::from_deps(deps);
    assert!(phyla.has_dep("collections"));
    assert!(!phyla.has_dep("nosuch"));
    assert!(!Phyla::default().has_dep("collections"));
}
