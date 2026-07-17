//! DN-122 §13 (M-1080; WU-B) — the `Ord3` **prelude surface**: the MVP's single-param,
//! param-only-sig target trait, seeded exactly like [`crate::fuse`]'s `Fuse` (M-965 F-A1).
//!
//! **Why this exists (OQ-6, resolved at DN-122's ratification 2026-07-12: prelude-seed).** DN-122's
//! build-ready MVP (`docs/notes/DN-122-External-Trait-Impls-Across-The-Home-Boundary.md` §13) closes
//! the "impl a foreign single-param, param-only-sig trait for my own type" gap-class (ledger row 89's
//! `Impl`/external-trait class) for the narrow but real sub-case where the target trait is one of a
//! small, hand-seeded set of **prelude** traits — a uniform reserved home (DN-112 §9), so the
//! coherence closure is exactly `{this phylum, <prelude>}`: **no cross-phylum import, no manifest
//! DAG, no diamond, no separate-compilation tension** (std-phylum-declare, the general cross-phylum
//! case, is deferred to the M-1076/WU-C follow-up — not built here, YAGNI).
//!
//! `Ord3` is the MVP's canonical target-trait witness, taken from DN-122 §13.1's own example —
//! `Ord3[A] { fn cmp(a: A, b: A) => Binary{2}; }` — with **one deliberate, documented deviation**:
//! the return repr is `Binary{8}`, not `Binary{2}`. DN-122's `Binary{2}` was illustrative
//! (a caller-defined strength/ordering encoding, uninterpreted either way); `Binary{8}` is the
//! width [`crate::checkty`]'s DN-122-cited guard is agnostic to (it never inspects a signature's
//! *width*, only whether a referenced type is a param-vs-concrete — `crates/mycelium-transpile`'s
//! `map_type` has no confirmed Rust-source mapping onto a bare `Binary{2}`, so `Binary{8}` — the
//! `u8` mapping — is the width WU-A's T-A1 positive-control fixture can actually reach from real
//! Rust source; DN-122's own soundness argument is verified over the shape class, not the specific
//! width). Single-parameter (`params.len() == 1`), and its one signature references only that
//! parameter plus a primitive repr — the exact shape the landed `foreign_trait_sig_names_a_concrete_type`
//! guard (`crate::checkty`, HOLE A/A2) admits without any new checker work (DN-122 §13.1).
//!
//! **No law checker.** Unlike `Fuse` (a semilattice — DN-58 §A.1 mandates idempotence/commutativity/
//! associativity), `Ord3` carries no algebraic law this module verifies; an instance's `cmp` may
//! encode whatever three-way order (or non-order) the implementer intends. Declaring or enforcing a
//! comparison law is out of DN-122's scope (YAGNI — not requested, not needed for the MVP's soundness
//! argument, which rests entirely on the landed `{carrier}×{position}` coherence surface, §13.1).
//!
//! Guarantee: the seeded [`TraitInfo`] itself is `Exact` (a fixed, hand-built structural fact, not a
//! measurement); whether an arbitrary `impl Ord3[...] for ...` *usefully* orders its domain is entirely
//! up to the implementer and unverified here (`Declared`, same boundary as `Fuse`'s non-enumerable-domain
//! skip — VR-5, no black-box claim beyond what is actually checked).

use std::collections::BTreeMap;

use crate::ast::{BaseType, FnSig, Param, TypeRef, WidthRef};
use crate::checkty::TraitInfo;
use crate::preseed::PreludeTraitSeed;

/// F-B1 (DN-122 §13.2 WU-B) — the built-in `Ord3` prelude trait: `trait Ord3[T] { fn cmp(a: T, b: T)
/// => Binary{8}; }` (the module doc explains the `Binary{8}` vs DN-122's illustrative `Binary{2}`).
/// Hand-built in Rust (mirrors [`crate::fuse::prelude`]/[`crate::checkty::prelude`]) rather than
/// parsed from surface syntax, so the parameter name `T` is an ordinary trait type-variable — no new
/// trait-model feature, matching the same idiom `Fuse` established (`impl Ord3[T] for T`, T standing
/// in for the Rust-side `Self`; RFC-0019's stage-1 trait model has no implicit `Self` slot).
#[must_use]
pub(crate) fn prelude() -> TraitInfo {
    let t = |name: &str| TypeRef::unguaranteed(BaseType::Named(name.to_owned(), vec![]));
    TraitInfo {
        name: "Ord3".to_owned(),
        params: vec!["T".to_owned()],
        sigs: vec![FnSig {
            name: "cmp".to_owned(),
            params: vec![],
            value_params: vec![
                Param {
                    name: "a".to_owned(),
                    ty: t("T"),
                },
                Param {
                    name: "b".to_owned(),
                    ty: t("T"),
                },
            ],
            ret: TypeRef::unguaranteed(BaseType::Binary(WidthRef::Lit(8))),
            effects: vec![],
            effect_budgets: BTreeMap::new(),
        }],
    }
}

/// This trait's name — the one string every registration/lookup site must agree on (Law of
/// Demeter — a single named constant beats a scattered literal `"Ord3"`; mirrors
/// [`crate::fuse::TRAIT_NAME`]).
pub(crate) const TRAIT_NAME: &str = "Ord3";

/// This trait's [`PreludeTraitSeed`] (DN-129 §5) — the shared spine [`crate::checkty`]'s
/// registration/link/`OwnDecls`-exclusion sites drive off, one call each instead of a hand-copied
/// conditional. Behavior-identical to the pre-refactor hand-written `Ord3` conditional (pinned by
/// `tests/ord3.rs`, which asserts only `message.contains("Ord3") && message.contains("built-in")`).
pub(crate) const SEED: PreludeTraitSeed = PreludeTraitSeed {
    name: TRAIT_NAME,
    impl_hint: "impl Ord3[T] for T { fn cmp(a: T, b: T) => Binary{8} = … }",
    prelude,
};
