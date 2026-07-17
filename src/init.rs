//! DN-129 §3 (M-1091) — the `Init` **prelude trait**: Mycelium's native answer to the `Default`
//! PROBLEM (a canonical zero/identity value of a type), seeded exactly like [`crate::fuse`]'s
//! `Fuse` (M-965 F-A1) and [`crate::ord3`]'s `Ord3` (DN-122 §13 / M-1080 WU-B), now over the shared
//! [`crate::preseed::PreludeTraitSeed`] spine (DN-129 §5).
//!
//! **The method is `init`, not `default`** — `default` is a taken lowercase-only lexer keyword
//! (`crate::token`, `"default" => Tok::Default`), so a trait method literally named `default` would
//! collide with the keyword; DN-129 §2 works this out and picks `Init`/`init` (final naming
//! DN-02-gated, not re-litigated here).
//!
//! **Why this is cheap (DN-129 §3).** `Init[T] { fn init() => T; }` is single-parameter and
//! **param-only**: its one signature references only the trait's own param `T` (zero value
//! parameters, a return of exactly `T`) — the same DN-122 §13.1 admitted class `Show`/`Ord3`/`Fuse`
//! already use, so `impl Init[LocalType] for LocalType { fn init() => LocalType = … }` checks clean
//! today with no new checker work.
//!
//! Guarantee: the seeded [`TraitInfo`] itself is `Exact` (a fixed, hand-built structural fact);
//! whether an arbitrary `impl Init[...] for ...` returns a *useful* canonical value is entirely up
//! to the implementer and unverified here (same VR-5 boundary as `Fuse`/`Ord3`/`Show`).

use std::collections::BTreeMap;

use crate::ast::{BaseType, FnSig, TypeRef};
use crate::checkty::TraitInfo;
use crate::preseed::PreludeTraitSeed;

/// This trait's name — the one string every registration/lookup/exclusion site agrees on (Law of
/// Demeter — a single named constant beats a scattered literal `"Init"`; mirrors
/// [`crate::fuse::TRAIT_NAME`] / [`crate::ord3::TRAIT_NAME`] / [`crate::show::TRAIT_NAME`]).
pub(crate) const TRAIT_NAME: &str = "Init";

/// DN-129 §3 — the built-in `Init` prelude trait: `trait Init[T] { fn init() => T; }`. Hand-built
/// in Rust (mirrors [`crate::fuse::prelude`] / [`crate::ord3::prelude`] / [`crate::show::prelude`])
/// rather than parsed from surface syntax, so the parameter name `T` is an ordinary trait
/// type-variable — no new trait-model feature.
#[must_use]
pub(crate) fn prelude() -> TraitInfo {
    TraitInfo {
        name: TRAIT_NAME.to_owned(),
        params: vec!["T".to_owned()],
        sigs: vec![FnSig {
            name: "init".to_owned(),
            params: vec![],
            value_params: vec![],
            ret: TypeRef::unguaranteed(BaseType::Named("T".to_owned(), vec![])),
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
    impl_hint: "impl Init[T] for T { fn init() => T = … }",
    prelude,
};
