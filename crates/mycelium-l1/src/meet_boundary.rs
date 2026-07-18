//! **The meet-boundary table** (DN-141 §4 R4/R5, §8 B3, §6.4; W-C X4) — committed data naming the
//! allow/refuse rule at a boundary crossing, plus a `regime_type_lie`-style first-fault builder for
//! the [`mycelium_diag::SiteKind::MeetBoundary`] site.
//!
//! # What "boundary" means at v0 (verify-first — mitigation #14; scoped to what's real today)
//!
//! DN-141 §3's mental model names three worlds a value can cross between: a quarantine bag (meet
//! **free**, R4), an Exact-core / `pub` export (a **seal** required, R5), and a `certified`
//! consumer (an **airlock admission**, P2-Q3). Of these, [`crate::grade::Gx::require`] and
//! [`crate::grade::check_fn_grades`]'s own inline check are **already** the enforcement mechanism
//! for the export-return-demand and call-argument-demand crossings today (both, ultimately, call
//! [`crate::ast::Strength::satisfies`] — the same arithmetic [`check_boundary`] below is DRY-built
//! on). A `std.airlock` seal (X6) and the `certified`-mode colony-admission firewall (P2-Q3/X7) do
//! not exist yet in this crate — both are explicitly held to wave **W-E** (`PROGRAM-HANDOFF-DESIGN-
//! STEER-2026-07-17.md` §5). [`BoundaryKind::CertifiedConsumer`] is therefore included in the
//! *kind* enumeration (so the table's shape matches DN-141's own three-crossing model and is ready
//! to grow) but has **no rows** and no query path yet — ledgered, not fabricated (G2).
//!
//! **Disclosed residual — not yet live-wired into `grade.rs`.** [`check_boundary`] and
//! [`meet_boundary_refuse_diag`] are correct, tested (`src/tests/meet_boundary.rs`) reifications of
//! the export/argument-demand rule as committed data + an EXPLAIN-able first-fault builder — but
//! `grade.rs` itself (`Gx::require`/`check_fn_grades`) still computes `have.satisfies(demand)`
//! inline rather than calling through this module. `grade.rs` is the DN-80 reject-ledger-pinned
//! file (`crates/mycelium-std-conformance/tests/reject_ledger.rs` pins its exact
//! `CheckError::at`/`::new` call-site count), and `require`'s three call sites are not all the same
//! DN-141 site_kind (a `let`/value ascription is `grade_annotation`, DESIGN-03's own table — a
//! *different* first-fault site from `meet_boundary`'s export/argument-demand crossings) — so
//! threading a `BoundaryKind` through `require` correctly needs a small, focused follow-on change of
//! its own, deliberately not folded into this already-large leaf (scope discipline, "smallest
//! auditable step" — KC-3). Flagged, not silently left unmentioned (G2/VR-5).
//!
//! # R4 — meet is free *inside* a crossing (nodule-scoped, DN-141 §6.4)
//! This table governs **only** the two named boundary crossings above (once wired). Every other
//! composition [`crate::grade::Gx::grade`] performs (`Let`, `If`, `Match`, `Fuse`, `meet_all`, …)
//! calls [`crate::ast::Strength::meet`] **directly**, never through `require` at all — see
//! `src/tests/meet_boundary.rs`'s `internal_composition_never_calls_require` for a grep-level
//! regression guard confirming that invariant holds in `grade.rs`'s actual source today.

use mycelium_diag::{
    CertMode, Decision, Diag, EventId, FirstFaultEnvelope, Phase, Severity, SiteKind,
};

use crate::ast::Strength;

/// `crate::ast::Strength` (the static checker's grade-annotation lattice) and
/// `mycelium_core::GuaranteeStrength` (the value/kernel-level guarantee tag `mycelium_diag::Grades`
/// carries) are the **same 4-point lattice** (`Exact ⊐ Proven ⊐ Empirical ⊐ Declared`) at two
/// different crate layers — no cross-crate `From`/`Into` exists between them (a static-checker
/// concept vs. a kernel `Value::Meta` concept), so this is a small, total, structural mapping
/// (never approximated — a 1:1 name match), not a lossy conversion.
fn to_guarantee_strength(s: Strength) -> mycelium_diag::GuaranteeStrength {
    match s {
        Strength::Exact => mycelium_diag::GuaranteeStrength::Exact,
        Strength::Proven => mycelium_diag::GuaranteeStrength::Proven,
        Strength::Empirical => mycelium_diag::GuaranteeStrength::Empirical,
        Strength::Declared => mycelium_diag::GuaranteeStrength::Declared,
    }
}

/// The boundary-crossing kinds DN-141 §3 names. See the module doc for which are wired at v0.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoundaryKind {
    /// A function's declared return grade (the "export" crossing — G-Sub at the function
    /// boundary, [`crate::grade::check_fn_grades`]). **Wired.**
    Export,
    /// A call's argument grade against its callee's declared parameter demand (the "Exact-demand"
    /// crossing — G-App, [`crate::grade::Gx::grade_app`]). **Wired.**
    ExactDemand,
    /// A `certified`-mode colony's admission of a `fast`-floored spore (P2-Q3/X7) — **not wired**;
    /// no row exists for this kind (see the module doc). Included so the enum's shape matches
    /// DN-141's three-crossing model without fabricating a check that does not exist.
    CertifiedConsumer,
}

impl BoundaryKind {
    /// The stable name for `EXPLAIN`/first-fault output.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            BoundaryKind::Export => "export",
            BoundaryKind::ExactDemand => "exact_demand",
            BoundaryKind::CertifiedConsumer => "certified_consumer",
        }
    }
}

/// The verdict at a boundary crossing (R5): `Allow` when the crossing value's grade is `⊒` the
/// demand (no seal needed — the honest, ordinary case); `Refuse` when it is not (a seal — v0 has
/// none, X6 — would be required to cross anyway; the checker refuses rather than launder).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoundaryVerdict {
    /// The crossing is allowed — `have` already satisfies `demand`.
    Allow,
    /// The crossing is refused — `have` does not satisfy `demand`, and v0 has no seal mechanism
    /// (X6) to admit it anyway.
    Refuse,
}

/// Table-driven allow/refuse at a boundary crossing (R5), derived — DRY, never a second arithmetic
/// — from [`Strength::satisfies`] (the one place the lattice order is encoded,
/// `crate::ast::Strength::rank`'s own doc). `pub(crate)`: not yet called from `grade.rs` (module
/// doc, "disclosed residual"); scoped `pub(crate)` rather than fully `pub` because
/// [`BoundaryKind::CertifiedConsumer`] has no row and must not be queried from outside this crate
/// until it does.
#[must_use]
pub(crate) fn check_boundary(
    kind: BoundaryKind,
    have: Strength,
    demand: Strength,
) -> BoundaryVerdict {
    debug_assert!(
        matches!(kind, BoundaryKind::Export | BoundaryKind::ExactDemand),
        "check_boundary called for an unwired boundary kind {kind:?} — CertifiedConsumer has no \
         row (module doc); a caller must not reach this function for it"
    );
    if have.satisfies(demand) {
        BoundaryVerdict::Allow
    } else {
        BoundaryVerdict::Refuse
    }
}

/// The `meet_boundary` first-fault event (RFC-0013 Amendment A1 §10.3 — `site_kind: meet_boundary`,
/// "export / certified demand / Exact partition") for a **refused** boundary crossing. `None` when
/// the crossing is [`BoundaryVerdict::Allow`] (RFC-0013 §4.6 "non-sites" — nothing to report).
///
/// `event_id`/`cert_mode` are caller-supplied, mirroring [`crate::regime::regime_type_lie_diag`]'s
/// own posture (this module has no CertMode-resolution mechanism of its own).
#[must_use]
pub fn meet_boundary_refuse_diag(
    kind: BoundaryKind,
    have: Strength,
    demand: Strength,
    what: &str,
    event_id: EventId,
    cert_mode: CertMode,
) -> Option<Diag> {
    if matches!(check_boundary(kind, have, demand), BoundaryVerdict::Allow) {
        return None;
    }
    let envelope = FirstFaultEnvelope::new(
        event_id,
        Phase::Check,
        SiteKind::MeetBoundary,
        Decision::Refuse,
        "meet_boundary.v0",
        cert_mode,
    )
    .with_grades(mycelium_diag::Grades {
        input: vec![to_guarantee_strength(have)],
        output: Some(to_guarantee_strength(demand)),
    })
    .with_basis_ref(format!(
        "R5 boundary crossing `{}`: {have:?} does not satisfy demand {demand:?} (RFC-0018 §4.3 \
         G-Sub; DN-141 §4 R5 — no seal mechanism exists at v0, X6)",
        kind.as_str()
    ));
    Some(
        Diag::with_severity(
            Severity::Error,
            mycelium_diag::Code::Other("MeetBoundaryRefuse".to_owned()),
        )
        .message(format!(
            "{what} has grade `{have:?}`, which does not satisfy the demanded `@ {demand:?}` at \
             the `{}` boundary",
            kind.as_str()
        ))
        .with_envelope(envelope),
    )
}
