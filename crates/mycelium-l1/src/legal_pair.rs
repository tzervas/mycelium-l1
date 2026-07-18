//! The **A1 legal-pair matrix** (DN-142 §7; DESIGN-01 §4.1 row A1) — a checker materialization of
//! RFC-0002 §5's legal-pair table. RFC-0002 §5 itself is the normative source ("this DN does not
//! restate that table"); this module's job is early, never-silent refusal of a swap pair the RFC
//! marks illegal, using exactly RFC-0002 §5's rows — no invented pairs.
//!
//! # Two static/dynamic layers (an honest, disclosed simplification)
//! RFC-0002 §5 lists **Binary ↔ Ternary (in range)** and **Binary ↔ Ternary (out of range)** as two
//! separate rows, but the range check is a **dynamic**, value-level property no static type-checker
//! can decide from `Binary{n}`/`Ternary{m}` alone (it depends on the concrete width *pair* and, for
//! some regimes, the runtime value). The static matrix here therefore collapses those two rows to
//! **one** admissible pair-kind (`Binary ↔ Ternary`); the in-range/out-of-range distinction is the
//! existing dynamic check ([`mycelium_cert::legal_pair`], `crates/mycelium-cert/src/lib.rs`) plus the
//! [`mycelium_cert::SwapCertificate`] machinery — not duplicated here (DRY; this module never re-hosts
//! that check). [`LEGAL_PAIR_TABLE`] still records **both** rows as *data*, verbatim, so the RFC-0002
//! §5 table is faithfully materialized even though the query function ([`classify_swap_pair`])
//! necessarily operates at the coarser, statically-decidable granularity.
//!
//! # The DN-52 freeze-ledger carve-out (a pre-existing, disclosed exception)
//! `Binary`/`Ternary → Dense` is **not** one of RFC-0002 §5's rows, but the checker has — since the
//! DN-52 FLAG-1 freeze-ledger resolution (`tests/runnable_gate.rs`, `tests/differential.rs`) —
//! deliberately **accepted** it and staged the refusal to an explicit elaboration `Residual` (no
//! Dense-capable swap engine exists yet; E2-1/ADR-033 lands one). [`classify_swap_pair`] preserves
//! that pre-existing, tested acceptance rather than silently narrowing it (verify-first — mitigation
//! #14): re-tightening it is a judgment call for a future wave, flagged, not applied here. Only the
//! **reverse** direction (`Dense → Binary`/`Ternary`) and **same-paradigm** pairs (`Binary → Binary`,
//! `Ternary → Ternary`) — neither tested nor stated anywhere — are newly refused by this module.

use crate::checkty::Ty;
use mycelium_diag::{
    CertMode, Decision, Diag, EventId, FirstFaultEnvelope, Phase, Severity, SiteKind,
};

/// A coarse repr-kind classification for the legal-pair matrix — coarser than [`Ty`] (widths/dims
/// erased), but at the granularity RFC-0002 §5's rows actually key on: paradigm, plus, for `Dense`,
/// the specific scalar dtype the F32→BF16 row names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReprKind {
    /// `Binary{n}`.
    Binary,
    /// `Ternary{m}`.
    Ternary,
    /// `Dense{d, F32}`.
    DenseF32,
    /// `Dense{d, BF16}`.
    DenseBf16,
    /// `Dense{d, s}` for any other scalar (`F16`/`F64`) — RFC-0002 §5 names no row for these; they
    /// fall through [`classify_swap_pair`]'s catch-all like any other unstated pair.
    DenseOther,
    /// `VSA{model, dim, sparsity}` (any model — RFC-0002 §5's "VSA model ↔ VSA model" row does not
    /// distinguish which models).
    Vsa,
}

/// Classify a checked [`Ty`] to its [`ReprKind`], for pairs the checker admits as *representation*
/// types (`Binary`/`Ternary`/`Dense`/`Vsa` — [`crate::checkty::Cx::check_swap`]'s own gate). `None`
/// for anything else (defensive totality; not currently reachable through `check_swap`, since that
/// gate runs first, but kept honest rather than partial).
#[must_use]
pub fn repr_kind_of(ty: &Ty) -> Option<ReprKind> {
    match ty {
        Ty::Binary(_) => Some(ReprKind::Binary),
        Ty::Ternary(_) => Some(ReprKind::Ternary),
        Ty::Dense(_, crate::ast::Scalar::F32) => Some(ReprKind::DenseF32),
        Ty::Dense(_, crate::ast::Scalar::Bf16) => Some(ReprKind::DenseBf16),
        Ty::Dense(_, crate::ast::Scalar::F16 | crate::ast::Scalar::F64) => {
            Some(ReprKind::DenseOther)
        }
        Ty::Vsa { .. } => Some(ReprKind::Vsa),
        _ => None,
    }
}

/// One row of the RFC-0002 §5 legal-pair table, materialized as data — a verbatim transcription
/// (label/regime/bound-basis) of that table's six rows, cited in the fixture the accompanying test
/// (`src/tests/legal_pair.rs`) checks this constant against.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LegalPairRow {
    /// The `R_src → R_target` column, verbatim.
    pub pair: &'static str,
    /// The `Regime` column, verbatim.
    pub regime: &'static str,
    /// The `Bound basis` column, verbatim.
    pub bound_basis: &'static str,
}

/// The RFC-0002 §5 legal-pair table, materialized verbatim (DN-142 §7 / DESIGN-01 §4.1 row A1) — six
/// rows, in the RFC's own order. This constant is *data*, not the query logic: see
/// [`classify_swap_pair`] for the checker-usable predicate, which necessarily collapses rows 1/2 to
/// one statically-decidable pair-kind (module doc, "two static/dynamic layers").
pub const LEGAL_PAIR_TABLE: [LegalPairRow; 6] = [
    LegalPairRow {
        pair: "Binary ↔ Ternary (in range)",
        regime: "LosslessWithinRange, Exact",
        bound_basis: "proof of enc/dec round-trip",
    },
    LegalPairRow {
        pair: "Binary ↔ Ternary (out of range)",
        regime: "rejected / explicit error",
        bound_basis: "— (never silent)",
    },
    LegalPairRow {
        pair: "Dense F32 → BF16",
        regime: "Bounded (ε)",
        bound_basis: "rounding-error theory (ADR-010 ErrorBound)",
    },
    LegalPairRow {
        pair: "Dense ↔ VSA",
        regime: "Bounded/probabilistic (ε, δ)",
        bound_basis: "VSA capacity results (RFC-0003, T0.2)",
    },
    LegalPairRow {
        pair: "VSA model ↔ VSA model",
        regime: "case-by-case",
        bound_basis: "per-pair derivation (RFC-0003 matrix)",
    },
    LegalPairRow {
        pair: "pair with no statable bound",
        regime: "type error",
        bound_basis: "— (not a Declared gamble)",
    },
];

/// The checker's verdict on a `(src, target)` swap pair (A1; DN-142 §7).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PairVerdict {
    /// The pair is legal — names the [`LEGAL_PAIR_TABLE`] row (or the disclosed DN-52 carve-out,
    /// which is not an RFC-0002 §5 row) it is admitted under.
    Legal {
        /// A human-readable row/reason label (EXPLAIN-able — never a bare "ok").
        row: &'static str,
    },
    /// The pair is refused — RFC-0002 §5 row 6 ("pair with no statable bound → type error"), never
    /// a silent accept-and-fail-later.
    Refuse {
        /// Why (always cites the RFC-0002 §5 row).
        reason: &'static str,
    },
}

/// Classify a swap `(src, target)` pair against the RFC-0002 §5 legal-pair table (A1) — the
/// queryable function [`crate::checkty::Cx::check_swap`] consults for early, never-silent refusal.
///
/// Legal: `Binary ↔ Ternary` (either direction; row 1/2, collapsed per the module doc), `Dense F32 →
/// BF16` (row 3, directional — only the stated direction), `Dense ↔ VSA` (row 4, any Dense dtype,
/// either direction), `VSA ↔ VSA` (row 5), and the pre-existing DN-52 carve-out `Binary`/`Ternary →
/// Dense` (module doc — not an RFC-0002 §5 row, preserved as-is, never narrowed).
///
/// Refused (row 6 — "pair with no statable bound"): same-paradigm pairs (`Binary → Binary`, `Ternary
/// → Ternary`), `Dense → Binary`/`Ternary` (the untested reverse of the carve-out), `Binary`/`Ternary
/// ↔ Vsa` directly (skipping Dense), `BF16 → F32` (the unstated reverse of row 3), and any pair
/// touching [`ReprKind::DenseOther`] (`F16`/`F64` — RFC-0002 §5 names no row for them).
#[must_use]
pub fn classify_swap_pair(src: ReprKind, target: ReprKind) -> PairVerdict {
    use ReprKind::{Binary, DenseBf16, DenseF32, DenseOther, Ternary, Vsa};
    match (src, target) {
        (Binary, Ternary) | (Ternary, Binary) => PairVerdict::Legal {
            row: "Binary ↔ Ternary (RFC-0002 §5 row 1/2)",
        },
        (DenseF32, DenseBf16) => PairVerdict::Legal {
            row: "Dense F32 → BF16 (RFC-0002 §5 row 3)",
        },
        (DenseF32 | DenseBf16 | DenseOther, Vsa) | (Vsa, DenseF32 | DenseBf16 | DenseOther) => {
            PairVerdict::Legal {
                row: "Dense ↔ VSA (RFC-0002 §5 row 4)",
            }
        }
        (Vsa, Vsa) => PairVerdict::Legal {
            row: "VSA model ↔ VSA model (RFC-0002 §5 row 5)",
        },
        // DN-52 FLAG-1 / freeze-ledger W5 (pre-existing, ratified separately — not an RFC-0002 §5
        // row): `Binary`/`Ternary → Dense` is accepted here and staged to an explicit elaboration
        // `Residual`, never silently refused nor silently run (`tests/runnable_gate.rs`,
        // `tests/differential.rs::dense_swap_is_an_explicit_residual_on_all_paths`).
        (Binary | Ternary, DenseF32 | DenseBf16 | DenseOther) => PairVerdict::Legal {
            row: "(DN-52 staged carve-out — Binary/Ternary → Dense; not an RFC-0002 §5 row)",
        },
        _ => PairVerdict::Refuse {
            reason: "pair with no statable bound (RFC-0002 §5 row 6 — a type error, never a \
                     Declared gamble)",
        },
    }
}

/// The `legal_pair_refuse` first-fault event (RFC-0013 Amendment A1 §10.3 — `site_kind:
/// legal_pair_refuse`, "illegal `Repr` pair (check)"; DESIGN-01 §4.3) for a
/// [`PairVerdict::Refuse`] verdict — an **instance** of the pack-03 first-fault envelope (never a
/// second, parallel diagnostic system — G-9), used by [`crate::checkty::Cx::check_swap`] (W-C X5) to
/// build the `illegal swap pair` [`crate::checkty::CheckError`]'s message so the same reason text
/// backs both the checker's `Result::Err` and the reified, `EXPLAIN`-able record.
///
/// `event_id`/`cert_mode` are caller-supplied — this is a **check-time** site, running before any
/// `@certification` scope resolution reaches the checker (`crate::ambient_policy`'s own module doc
/// makes the same disclosure), so a caller in that position passes the project default,
/// [`mycelium_diag::CertMode::Fast`].
#[must_use]
pub fn legal_pair_refuse_diag(
    src_display: &str,
    target_display: &str,
    reason: &str,
    event_id: EventId,
    cert_mode: CertMode,
) -> Diag {
    let envelope = FirstFaultEnvelope::new(
        event_id,
        Phase::Check,
        SiteKind::LegalPairRefuse,
        Decision::Refuse,
        "legal_pair_refuse.v0",
        cert_mode,
    )
    .with_basis_ref(format!("A1 legal-pair matrix (RFC-0002 §5): {reason}"));
    Diag::with_severity(
        Severity::Error,
        mycelium_diag::Code::Other("LegalPairRefuse".to_owned()),
    )
    .message(format!(
        "illegal swap pair {src_display} → {target_display}: {reason}"
    ))
    .with_envelope(envelope)
}

/// A **v0 seed** of the `std.swap.policy` catalog (DESIGN-01 §4.1 row A2; DN-142 §3.2) — the
/// least-specific ("catalog") tier `policy: ambient` falls through to when no scope declares an
/// ambient policy ([`crate::ambient_policy::resolve_policy`]). Deliberately small and closed: exactly
/// the two pairs the corpus already names a canonical policy for (`rt` — `tests/ambient.rs`'s
/// roundtrip policy for Binary ↔ Ternary; `bf16_round` — `tests/check.rs`'s Dense F32 → BF16 policy),
/// never invented names. A real `std.swap.policy` catalog artifact (DESIGN-01 §4.1 row A2's own,
/// larger scope) is a flagged future item, not this leaf's scope.
#[must_use]
pub fn catalog_default_policy(src: ReprKind, target: ReprKind) -> Option<&'static str> {
    use ReprKind::{Binary, DenseBf16, DenseF32, Ternary};
    match (src, target) {
        (Binary, Ternary) | (Ternary, Binary) => Some("rt"),
        (DenseF32, DenseBf16) => Some("bf16_round"),
        _ => None,
    }
}
