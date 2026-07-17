//! DN-129 §4 (M-1091) — the `Fault` **prelude trait**: Mycelium's native answer to the `Error`
//! PROBLEM's *abstraction* (a marker naming "this value is a fault"), seeded exactly like
//! [`crate::fuse`]'s `Fuse` (M-965 F-A1) and [`crate::ord3`]'s `Ord3` (DN-122 §13 / M-1080 WU-B),
//! now over the shared [`crate::preseed::PreludeTraitSeed`] spine (DN-129 §5).
//!
//! **OQ-2 resolved (bare marker, not a `Show`-bounded one — honest degrade, VR-5).** DN-129 §4/§5
//! *proposes* `trait Fault[T]: Show[T] {}` (a `Show`-bounded marker — the renderable obligation a
//! `std::error::Error`-shaped abstraction needs), but flags as an **honest open item (OQ-2)**
//! whether RFC-0019 stage-1's trait model admits a supertrait bound on a single-param trait, with
//! an explicit fallback: "if supertrait bounds are not yet in the trait checker, the MVP `Fault` is
//! a **bare marker** (`trait Fault[T] {}`)". **Re-verified against this tree (mitigation #14):**
//! [`crate::checkty::TraitInfo`] has exactly three fields — `name`, `params`, `sigs` — no
//! supertrait/bound slot at all, and a repo-wide `supertrait`/`superclass` grep is empty. So
//! supertrait bounds are **not yet in the trait checker** — the fallback fires. `Fault` is seeded
//! here as the bare marker `trait Fault[T] {}` (zero required methods; an empty
//! `impl Fault[MyErr] for MyErr {}` checks clean). The `Show` obligation stays a **convention**
//! (documented, not type-checked) until a supertrait mechanism lands — flagged forward, never
//! silently assumed to already hold (G2/VR-5; this module's own doc comment is the never-silent
//! record of the degrade, not a swallowed gap).
//!
//! Guarantee: the seeded [`TraitInfo`] itself is `Exact` (a fixed, hand-built structural fact,
//! trivially — an empty method set); the `Show`-bound obligation the design note wants is
//! `Declared`, not enforced, until supertrait bounds are built (VR-5 — never upgraded past what is
//! actually checked).

use crate::checkty::TraitInfo;
use crate::preseed::PreludeTraitSeed;

/// This trait's name — the one string every registration/lookup/exclusion site agrees on (Law of
/// Demeter — a single named constant beats a scattered literal `"Fault"`; mirrors
/// [`crate::fuse::TRAIT_NAME`] / [`crate::ord3::TRAIT_NAME`] / [`crate::show::TRAIT_NAME`] /
/// [`crate::init::TRAIT_NAME`]).
pub(crate) const TRAIT_NAME: &str = "Fault";

/// DN-129 §4/§5 (OQ-2 degrade path) — the built-in `Fault` prelude trait: a **bare marker**
/// `trait Fault[T] {}` (zero required methods). Hand-built in Rust (mirrors
/// [`crate::fuse::prelude`] / [`crate::ord3::prelude`] / [`crate::show::prelude`] /
/// [`crate::init::prelude`]) rather than parsed from surface syntax.
#[must_use]
pub(crate) fn prelude() -> TraitInfo {
    TraitInfo {
        name: TRAIT_NAME.to_owned(),
        params: vec!["T".to_owned()],
        sigs: vec![],
    }
}

/// This trait's [`PreludeTraitSeed`] — the DN-129 §5 shared spine [`crate::checkty`]'s
/// registration/link/`OwnDecls`-exclusion sites drive off, one call each instead of a hand-copied
/// conditional.
pub(crate) const SEED: PreludeTraitSeed = PreludeTraitSeed {
    name: TRAIT_NAME,
    impl_hint: "impl Fault[T] for T { … }",
    prelude,
};
