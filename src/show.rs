//! DN-127 (M-1090; WU-2) — the `Show` **prelude trait**: the value-to-text (`Display`/`write!`/
//! `format!` PROBLEM's) generic-dispatch surface, seeded exactly like [`crate::fuse`]'s `Fuse`
//! (M-965 F-A1) and [`crate::ord3`]'s `Ord3` (DN-122 §13 / M-1080 WU-B), now over the shared
//! [`crate::preseed::PreludeTraitSeed`] spine (DN-129 §5).
//!
//! **Why this is cheap (DN-127 §5).** `Show[T] { fn render(x: T) => Bytes; }` is single-parameter
//! and **param-only**: its one signature references only the trait's own param `T` plus the
//! primitive repr `Bytes` (a unit [`crate::ast::BaseType::Bytes`], never a `Named` concrete type) —
//! exactly the DN-122 §13.1 admitted class `foreign_trait_sig_names_a_concrete_type` lets through
//! with **no new checker work**. `impl Show[LocalType] for LocalType { fn render(x) => Bytes = … }`
//! checks clean today.
//!
//! **`render`, not `display`/`fmt`** — DN-127 §5's naming call (final naming DN-02-gated, not
//! re-litigated here).
//!
//! Guarantee: the seeded [`TraitInfo`] itself is `Exact` (a fixed, hand-built structural fact);
//! whether an arbitrary `impl Show[...] for ...` renders *usefully* is entirely up to the
//! implementer and unverified here — the same boundary `Fuse`'s non-enumerable-domain skip and
//! `Ord3`'s unverified-order boundary already draw (VR-5, no black-box claim beyond what is
//! actually checked).

use std::collections::BTreeMap;

use crate::ast::{BaseType, FnSig, Param, TypeRef};
use crate::checkty::TraitInfo;
use crate::preseed::PreludeTraitSeed;

/// This trait's name — the one string every registration/lookup/exclusion site agrees on (Law of
/// Demeter — a single named constant beats a scattered literal `"Show"`; mirrors
/// [`crate::fuse::TRAIT_NAME`] / [`crate::ord3::TRAIT_NAME`]).
pub(crate) const TRAIT_NAME: &str = "Show";

/// DN-127 §5 — the built-in `Show` prelude trait: `trait Show[T] { fn render(x: T) => Bytes; }`.
/// Hand-built in Rust (mirrors [`crate::fuse::prelude`] / [`crate::ord3::prelude`]) rather than
/// parsed from surface syntax, so the parameter name `T` is an ordinary trait type-variable — no
/// new trait-model feature.
#[must_use]
pub(crate) fn prelude() -> TraitInfo {
    TraitInfo {
        name: TRAIT_NAME.to_owned(),
        params: vec!["T".to_owned()],
        sigs: vec![FnSig {
            name: "render".to_owned(),
            params: vec![],
            value_params: vec![Param {
                name: "x".to_owned(),
                ty: TypeRef::unguaranteed(BaseType::Named("T".to_owned(), vec![])),
            }],
            ret: TypeRef::unguaranteed(BaseType::Bytes),
            effects: vec![],
            effect_budgets: BTreeMap::new(),
        }],
    }
}

/// This trait's [`PreludeTraitSeed`] — the DN-129 §5 shared spine [`crate::checkty`]'s
/// registration/link/`OwnDecls`-exclusion sites drive off, one call each instead of a hand-copied
/// conditional.
pub(crate) const SEED: PreludeTraitSeed = PreludeTraitSeed {
    name: TRAIT_NAME,
    impl_hint: "impl Show[T] for T { fn render(x: T) => Bytes = … }",
    prelude,
};
