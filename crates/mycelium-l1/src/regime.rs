//! **Regime → result-type classification** (DESIGN-01 §4.2 row A5; W-C X3) — a direction-aware
//! Total/Partial classification of a resolved swap pair, computed from RFC-0002 §4/§5 (never from
//! how the swap was *spelled* — DN-142 §5 gate 3's own wording, "regime typing from the resolved
//! pair, never the spelling"), plus a [`mycelium_diag`] first-fault builder for the reserved
//! `regime_type_lie` [`mycelium_diag::SiteKind`] (RFC-0013 Amendment A1 §10.3).
//!
//! # Scope (verify-first — mitigation #14; a disclosed, honest residual)
//!
//! DESIGN-01 A5 / DN-141's aspirational reading is that **every** partial-regime swap should type
//! as `Option[T]`/`Result[T, E]` rather than bare `T`, with a **checker error** (`regime_type_lie`)
//! whenever a bare/total type is claimed over a partial regime. This module implements the
//! **classification** (below) and a **`Diag` builder** for that site — both genuinely new, tested,
//! and non-breaking. It does **not** wire a hard refusal into
//! [`crate::checkty::Cx::check_swap`]'s live control-flow path, for a concrete, checked reason:
//!
//! **The existing, already-shipped `swap` surface already types every admitted pair bare — on both
//! directions of `Binary ↔ Ternary` — and a battery of pre-existing, currently-green tests rely on
//! exactly that**, most concretely the round-trip chain `swap(swap(b, to: Ternary{6}, policy: rt),
//! to: Binary{8}, policy: rt)` (the **`dec`** direction — RFC-0002 §4's own `Option`-typed
//! function — typed bare `Binary{8}` at the outer `swap`), which `crates/mycelium-l1/tests/
//! differential.rs`, `crates/mycelium-l1/tests/runnable_gate.rs`, and
//! `crates/mycelium-bench/src/corpus.rs` all exercise and assert type-checks successfully. Making
//! `regime_type_lie` a hard refusal over the *existing* explicit `to:` spelling would retroactively
//! break that already-tested, already-shipped behavior — a semantics change outside a single leaf
//! task's authority absent an explicit maintainer decision to accept the break (mitigation #14: this
//! is scoped to the *residual* gap, not a silent redesign of landed behavior). The natural,
//! non-breaking trigger surface is the **`to:`-elision feature (X9)**, which DN-142 §5 gate 3
//! explicitly binds this same rule to — and X9 is itself **held** (`PROGRAM-HANDOFF-DESIGN-STEER-
//! 2026-07-17.md` §5, "AX-sugar... after walls"), not yet parsed or checked anywhere in this crate
//! (`grep to: elided/elision` in `parse.rs` — zero hits, verified 2026-07-18). Once X9 lands, its
//! own elision-resolution path is the correct call site for [`regime_type_lie_diag`]'s hard-refuse
//! form; wiring it there (rather than retrofitting the pre-existing explicit spelling) is the
//! disclosed judgment call this module ships instead of a breaking guess (G2/VR-5 — flagged, not
//! silently decided either way).
//!
//! Ledgered as a DN-141 implementation note (this leaf appends one; see that note's changelog).

use crate::legal_pair::{classify_swap_pair, PairVerdict, ReprKind};
use mycelium_diag::{
    CertMode, Decision, Diag, EventId, FirstFaultEnvelope, Phase, Severity, SiteKind,
};

/// A swap regime's fallibility shape (DESIGN-01 A5) — computed from the **resolved** `(src, target)`
/// pair, never from surface spelling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegimeKind {
    /// The swap is defined for every value of the source type — no `Option`/`Result` wrapper is
    /// ever needed at the kernel layer (RFC-0002 §4's `enc : Bin_n -> Tern_m`, and every `Bounded`/
    /// `Bounded-probabilistic` pair, which always produces a value with a *quality* bound — never an
    /// *absence* — RFC-0002 §5).
    Total,
    /// The swap may have no answer for some values of the source type (RFC-0002 §4's `dec : Tern_m
    /// -> Option Bin_n` — off-image ternary values have no binary representation). The kernel layer
    /// types this `Option`; the std surface (`mycelium-std-swap`, DN-16 §7-Q4) types it `Result` —
    /// a layer-presentation choice over the same regime (DN-142 §6), not a second regime.
    Partial,
}

/// Classify the regime of a resolved `(src, target)` pair (DESIGN-01 A5), reusing
/// [`classify_swap_pair`] for the legal/illegal gate (DRY — never a second admissibility check):
/// `None` if the pair is not legal at all (regime is meaningless for a pair the checker already
/// refuses at [`crate::legal_pair`]); `Some(RegimeKind::Partial)` for the RFC-0002 §4 `dec`
/// direction (`Ternary -> Binary`) — the only regime RFC-0002 states an explicit off-image failure
/// for; `Some(RegimeKind::Total)` for every other legal pair (the `enc` direction, and every
/// `Bounded`/`Bounded-probabilistic` pair, per the module doc's "Bounded is a quality bound, not an
/// absence" reading of RFC-0002 §5).
///
/// # Guarantee: `Declared`
/// A disclosed, direction-aware simplification at the [`ReprKind`] (width-erased) granularity —
/// matching [`crate::legal_pair::classify_swap_pair`]'s own disclosed collapsing (see that
/// function's doc for why a width-*precise* totality proof, e.g. "does `Binary{n}`'s full range fit
/// `Ternary{m}`'s image", is out of scope here: no static checker in this codebase decides that
/// today, and this module does not invent one — VR-5, no unbounded upgrade).
#[must_use]
pub fn regime_of(src: ReprKind, target: ReprKind) -> Option<RegimeKind> {
    if !matches!(classify_swap_pair(src, target), PairVerdict::Legal { .. }) {
        return None;
    }
    Some(match (src, target) {
        // RFC-0002 §4: `dec : Tern_m -> Option Bin_n` — the one regime the RFC itself types
        // partial. Balanced ternary can represent negative and larger-magnitude values than an
        // unsigned `Binary{n}` can hold, so `dec` has no answer for every ternary value in general.
        (ReprKind::Ternary, ReprKind::Binary) => RegimeKind::Partial,
        // Every other legal pair: RFC-0002 §4's `enc : Bin_n -> Tern_m` (no `Option` in its own
        // signature); every `Bounded`/`Bounded-probabilistic` pair (Dense F32->BF16, Dense<->VSA,
        // VSA<->VSA — RFC-0002 §5's "Bounded (ε)"/"Bounded/probabilistic (ε, δ)" rows describe a
        // *quality* bound on an always-produced result, never an absent one); and the disclosed
        // DN-52 carve-out (Binary/Ternary -> Dense — RFC-0002 states no row for it at all, and it is
        // not yet executable — `crate::legal_pair`'s own module doc — so no partial regime is
        // stated for it either).
        _ => RegimeKind::Total,
    })
}

/// The `regime_type_lie` first-fault event (RFC-0013 Amendment A1 §10.3 — `site_kind:
/// regime_type_lie`, "a total type over a partial regime"): an **observability-only** `Diag`
/// reporting that `(src, target)` resolves to [`RegimeKind::Partial`] while `claimed_bare` is
/// `true` (the caller is typing the swap's result as a bare/total type — the *existing* v0 surface
/// shape, see the module doc's "Scope" section for why this is not (yet) wired as a hard refusal).
///
/// `event_id`/`cert_mode` are caller-supplied (this function does not itself resolve a `CertMode` —
/// [`crate::checkty::Cx::check_swap`] runs before any `@certification` scope resolution reaches the
/// checker, so a caller in that position passes the project default,
/// [`mycelium_diag::CertMode::Fast`], with the same disclosure this module's doc carries).
///
/// `None` when the pair is [`RegimeKind::Total`] or not legal at all (`regime_of` returns `None` /
/// `Some(Total)`) — there is nothing to report (RFC-0013 §4.6 "non-sites": no event fires when
/// there is nothing dishonest to surface).
#[must_use]
pub fn regime_type_lie_diag(
    src: ReprKind,
    target: ReprKind,
    src_display: &str,
    target_display: &str,
    claimed_bare: bool,
    event_id: EventId,
    cert_mode: CertMode,
) -> Option<Diag> {
    if !claimed_bare {
        return None;
    }
    if regime_of(src, target)? != RegimeKind::Partial {
        return None;
    }
    let envelope = FirstFaultEnvelope::new(
        event_id,
        Phase::Check,
        SiteKind::RegimeTypeLie,
        Decision::Candidate,
        "regime_type_lie.v0",
        cert_mode,
    )
    .with_basis_ref(
        "RFC-0002 §4 dec: Tern_m -> Option Bin_n (kernel layer; DN-16 Result at the \
                      std surface, DN-142 §6)",
    );
    Some(
        Diag::with_severity(
            Severity::Info,
            mycelium_diag::Code::Other("RegimeTypeLieCandidate".to_owned()),
        )
        .message(format!(
            "swap {src_display} -> {target_display} resolves to a partial regime (RFC-0002 §4 \
             `dec`) but is typed as a bare/total type — candidate regime_type_lie (observability \
             only in v0; see `crate::regime`'s module doc for the disclosed deferral of a hard \
             checker refusal)"
        ))
        .with_envelope(envelope),
    )
}
