//! `mycelium-l1` — the **L1 surface prototype** (RFC-0006; **NON-NORMATIVE** until RFC-0006 is
//! ratified). A hand-written lexer + recursive-descent parser for the ratified DN-02 surface
//! vocabulary, validated against the `docs/spec/grammar/` conformance corpus (the
//! WebAssembly-spec pattern, T3.1-B: the corpus is the ground truth, not any single parser).
//!
//! The L1 track so far (RFC-0006 §3; RFC-0007): the lexer + recursive-descent parser prove the
//! grammar is real by parsing every `accept/` program and explicitly rejecting every `reject/`
//! one (`tests/conformance.rs`); the v0 monomorphic typechecker + structural totality checker
//! ([`checkty`], [`totality`]; RFC-0007 §4.4/§4.5) gate `matured` on checked totality; the
//! fuel-guarded big-step evaluator ([`eval`]; §4.6) runs every checked program over the *same*
//! trusted prim/swap engines as the L0 paths; and the elaborator ([`elab`]; §4.6) lowers the
//! evaluation-complete fragment to closed L0 terms — refusing everything else with an explicit
//! `Residual`, never a partial artifact. The three-way differential (L1-eval ↔ elaborate→L0-interp
//! ↔ AOT, validated through the M-210 shared checker) lives in `tests/differential.rs` (NFR-7).
//! `match` covers data types and `Binary`/`Ternary` literal patterns *and* **nested** patterns
//! (M-320): a literal arm fires on `repr + payload` equality, and coverage is decided by the
//! **Maranget usefulness** algorithm (`usefulness`) — exhaustiveness (a `_` must not be useful; its
//! witness names a concrete missing case) and redundancy (an arm covered by earlier rows is
//! unreachable) are both *checked* (W7 — never assumed; a `Binary`/`Ternary` value domain is never
//! enumerated, so a literal match still needs a `_`/binder default). The Maranget *compilation* to the
//! flat kernel `Match` (RFC-0007 §3, the elaborator/L0 path) lands with full L1-in-Core-IR (the
//! RFC-0001 revision).
//!
//! Honesty: every malformed input is an explicit [`ParseError`] with a source position — the
//! parser never panics and never silently accepts (S5/G2). The lexer disambiguates the one tricky
//! token (`<` opening a ternary literal vs a type-argument list) by lookahead, and a malformed
//! ternary literal is an explicit error, not a silent truncation.
//!
//! **Trusted-kernel discipline (ADR-014, KC-3):** this crate is `#![forbid(unsafe_code)]` — the
//! reference interpreter is **machine-proven `unsafe`-free**. Host-stack management for the recursive
//! checker/elaborator (the deep worker stack) is deliberately kept *outside* this kernel, in the
//! `mycelium-stack` crate, which the kernel uses only through its safe API; the explicit depth budgets
//! (`parse::MAX_EXPR_DEPTH`, `checkty::MAX_CHECK_DEPTH`, the evaluator's clock) are the portable
//! primitive that carries to the self-hosted frontend.
#![forbid(unsafe_code)]

/// The static affine **use-once** tracker for `Substrate` bindings (M-903; DN-71 Model S §4.2) —
/// piggybacked on [`checkty::Cx`]'s own scope, not a parallel analysis (KC-3/DRY). Internal to the
/// frontend; not part of the public surface.
mod affine;
pub mod ambient;
/// **`policy: ambient` scoped resolution** (DN-142 §3.2) — the third instance of the RFC-0012
/// ambient/scoped-override mechanism, mirroring `mycelium_proj::cert_scope`'s pure resolution shape.
/// Driven by [`checkty::Cx::check_swap`]; `pub` (like `mycelium_proj::cert_scope`) so its resolution
/// law + EXPLAIN rendering are directly citable/testable, not because an external crate consumes it
/// yet.
pub mod ambient_policy;
pub mod ast;
pub mod checkty;
pub(crate) mod decision;
pub mod elab;
pub mod error;
pub mod eval;
/// DN-129 §4 (M-1091) — the `Fault` prelude trait (a bare marker, the OQ-2 honest-degrade
/// resolution — see the module doc), seeded exactly like [`fuse`]'s `Fuse` (M-965) over the shared
/// [`preseed`] spine. Internal to the frontend, like [`fuse`]; not part of the public surface.
pub(crate) mod fault;
/// DN-58 §A (M-965) — the `Fuse` prelude trait (F-A1) + the semilattice-law checker (F-A2), the
/// [`checkty`] post-pass driven by [`checkty::check_nodule`]/[`checkty::check_phylum`]. Internal
/// to the frontend, like [`grade`]; not part of the public surface.
pub(crate) mod fuse;
/// RFC-0018 stage-1a static guarantee grading (Design A) — the [`checkty`] post-pass that enforces
/// the guarantee lattice `Exact ⊐ Proven ⊐ Empirical ⊐ Declared` statically. Internal to the
/// frontend (driven by [`checkty::check_nodule`]); not part of the public surface.
mod grade;
/// **The structural grade catalog** (DN-141 R3 "matrix mint", W-C X2) — committed data naming the
/// RFC-0018 §4.3 grade rule each structural form [`grade`] implements. `pub` so the catalog
/// (`grade_catalog::STRUCTURAL_GRADE_CATALOG`) is directly citable/EXPLAIN-able, matching
/// [`legal_pair`]'s own materialized-table posture.
pub mod grade_catalog;
/// DN-129 §3 (M-1091) — the `Init` prelude trait (Mycelium's native `Default`), seeded exactly
/// like [`fuse`]'s `Fuse` (M-965) over the shared [`preseed`] spine. Internal to the frontend, like
/// [`fuse`]; not part of the public surface.
pub(crate) mod init;
/// The **A1 legal-pair matrix** (DN-142 §7; DESIGN-01 §4.1 row A1) — a checker materialization of
/// RFC-0002 §5's legal-pair table, consulted by [`checkty::Cx::check_swap`]. `pub` so the matrix
/// (`LEGAL_PAIR_TABLE`) is directly citable/inspectable, matching RFC-0002 §5's own normative status.
pub mod legal_pair;
pub mod lexer;
/// **The meet-boundary table** (DN-141 B3/R4/R5, W-C X4) — committed data naming, per boundary
/// crossing kind (an exported/declared return demand, an argument demand), the allow/refuse rule
/// over the guarantee lattice. `pub` so the table is directly citable/EXPLAIN-able, matching
/// [`legal_pair`]'s own materialized-table posture; see the module doc for scope (v0 has no
/// certified-consumer/mode-firewall crossing yet — ledgered, deferred to wave W-E).
pub mod meet_boundary;
pub mod mono;
pub mod nodule;
/// DN-122 §13 (M-1080) — the `Ord3` prelude trait (WU-B), the MVP single-param/param-only-sig
/// target trait for the external-trait-impl gap-class, seeded exactly like [`fuse`]'s `Fuse`
/// (M-965). Internal to the frontend, like [`fuse`]; not part of the public surface.
pub(crate) mod ord3;
pub mod parse;
/// **DN-113 Rank 1 / M-1060** — the multi-phylum dependency-graph builder: [`phyla::PhylumNode`] +
/// [`phyla::build_phyla_graph`] resolve a named graph of phyla bottom-up into checked, linked
/// [`checkty::ResolvedPhylum`]s, refusing a cyclic graph before checking anything (DN-113 §9.3). The
/// single-phylum resolution mechanism (`Phyla`/`ResolvedPhylum`/`check_phylum_with_deps`) it layers
/// over lives in [`checkty`] itself (crate-internal access to `Exports`/`Env`/`DataInfo` needed).
pub mod phyla;
/// DN-129 §5 — the shared **prelude-trait seeding spine** [`fuse`]/[`ord3`]/[`show`]/[`init`]/
/// [`fault`] all ride (a DRY factoring of the `Fuse`/`Ord3` conditionals `checkty` used to
/// hand-copy). Internal to the frontend; not part of the public surface.
pub(crate) mod preseed;
/// **The regime classification** (DESIGN-01 A5, W-C X3) — committed, direction-aware data
/// distinguishing a **total** swap regime (never fails to produce a value — RFC-0002 §4's `enc`)
/// from a **partial** one (`RFC-0002 §4`'s `dec`, `Option`-typed at the kernel layer). `pub` so the
/// classification is directly citable/testable; see the module doc for the disclosed scope limit
/// (classification + a `regime_type_lie` `Diag` builder land; a hard checker refusal for an
/// existing bare-typed partial swap does **not** — it would break already-shipped, tested behavior
/// — see the module doc's "Deferred" section for the exact citation).
pub mod regime;
/// `reveal` — desugar-on-demand, Increment-1 (M-1051; DN-38 §5/§8.3; DN-110 §3.4/§8.4;
/// DN-110-8.2-hygiene-deepdive §5/§7 E3/§10 OQ-H3). The E3-enabling core: [`reveal::reveal_l0`]
/// (the shown L0 term), [`reveal::render_surface`] (the honestly-labelled surface pretty-printer),
/// [`reveal::alpha_eq`] (structural alpha-equivalence — `Node`'s `PartialEq` is not alpha-aware),
/// and [`reveal::reelaborate`] (the L0-level round-trip witness). See the module doc for the pinned
/// v0-fidelity/OQ-H3 rulings.
pub mod reveal;
/// DN-127 §5 (M-1090; WU-2) — the `Show` prelude trait (generic value-to-text render dispatch),
/// seeded exactly like [`fuse`]'s `Fuse` (M-965) over the shared [`preseed`] spine. Internal to the
/// frontend, like [`fuse`]; not part of the public surface.
pub(crate) mod show;
/// The `Substrate` v0 value form (M-902; DN-71 Model S §4.1) — an interpreter-level opaque affine
/// handle at the L1 evaluator level. No new L0 node / no `Repr` growth (KC-3). The affine use-once
/// **runtime backstop** now lives here too (M-903 — [`substrate::SubstrateHandle::try_consume`]);
/// the primary enforcement is the static pass ([`affine`]) run by [`checkty::check_nodule`]. The
/// `consume` **lowering** (real execution through existing paths) is still M-904.
pub mod substrate;
pub mod token;
pub mod totality;
/// DN-126 (M-1077) — the **type-strictness axis**: loose/duck-typed on the interpreted path vs.
/// strict-gates-compile, plus the type-hint-driven mechanical-strictification classifier
/// ([`type_strictness::strictify`]). Orthogonal to [`checkty`]'s [`checkty::CheckError`]'s hard-vs-
/// demotable posture (which this module's [`type_strictness::TypeStrictness`] switches) — see the
/// module doc for the exact, honestly-narrow set of demotable sites this landing covers.
pub mod type_strictness;
pub(crate) mod usefulness;

#[cfg(test)]
mod tests;

pub use ambient::{
    expand_phylum_to_source, expand_to_source, resolve, resolve_report, AmbientError, Resolved,
};
pub use ast::{Nodule, Phylum, UsePath, Vis};
pub use checkty::{
    check_and_resolve, check_nodule, check_nodule_matured, check_phylum, check_phylum_matured,
    check_phylum_matured_with_deps, check_phylum_with_deps, CheckError, Env, Phyla, PhylumEnv,
    ResolvedPhylum, Ty,
};
pub use elab::{
    elaborate, elaborate_colony, elaborate_direct, elaborate_lower_rule,
    elaborate_lower_rule_with_args, elaborate_reclaim, ElabError,
};
pub use error::ParseError;
pub use eval::{Evaluator, ForageDecision, ForageError, L1Error, L1Value};
pub use mono::{
    monomorphize, monomorphize_with_selections, ClosureSpecialization, InstanceSelection,
    MonoSelections,
};
pub use nodule::{parse_nodule_header, NoduleHeader, NoduleHeaderError};
pub use parse::{parse, parse_phylum};
pub use reveal::{
    alpha_eq, reelaborate, render_surface, reveal_l0, RenderError, Rendered, RevealError,
};
pub use substrate::{ReleaseEvent, SubstrateError, SubstrateHandle, SubstrateProvenance};
pub use totality::Totality;
pub use type_strictness::{
    strictify, Resolution, StrictifyOutcome, TypeFlag, TypeFlagKind, TypeStrictness,
};
