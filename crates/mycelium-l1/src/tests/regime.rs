//! Unit tests for the regime classification + `regime_type_lie` `Diag` builder (`crate::regime`,
//! W-C X3; DESIGN-01 A5).

use crate::legal_pair::ReprKind;
use crate::regime::*;
use mycelium_diag::{CertMode, Decision, EventId, SiteKind};

// ── Direction-aware classification (RFC-0002 §4) ─────────────────────────────────────────────────

#[test]
fn enc_direction_binary_to_ternary_is_total() {
    assert_eq!(
        regime_of(ReprKind::Binary, ReprKind::Ternary),
        Some(RegimeKind::Total),
        "RFC-0002 §4's `enc : Bin_n -> Tern_m` carries no `Option` in its own signature"
    );
}

#[test]
fn dec_direction_ternary_to_binary_is_partial() {
    assert_eq!(
        regime_of(ReprKind::Ternary, ReprKind::Binary),
        Some(RegimeKind::Partial),
        "RFC-0002 §4's `dec : Tern_m -> Option Bin_n` is the one regime the RFC itself types partial"
    );
}

#[test]
fn bounded_pairs_are_total_a_quality_bound_is_not_an_absence() {
    for &(src, target) in &[
        (ReprKind::DenseF32, ReprKind::DenseBf16),
        (ReprKind::DenseF32, ReprKind::Vsa),
        (ReprKind::Vsa, ReprKind::DenseF32),
        (ReprKind::DenseBf16, ReprKind::Vsa),
        (ReprKind::Vsa, ReprKind::DenseBf16),
        (ReprKind::DenseOther, ReprKind::Vsa),
        (ReprKind::Vsa, ReprKind::DenseOther),
        (ReprKind::Vsa, ReprKind::Vsa),
    ] {
        assert_eq!(
            regime_of(src, target),
            Some(RegimeKind::Total),
            "{src:?} -> {target:?}: RFC-0002 §5's Bounded/probabilistic rows describe a quality \
             bound on an always-produced result, not an absent one"
        );
    }
}

#[test]
fn the_dn_52_dense_carve_out_is_total_rfc_0002_states_no_row_for_it() {
    for &(src, target) in &[
        (ReprKind::Binary, ReprKind::DenseF32),
        (ReprKind::Ternary, ReprKind::DenseF32),
    ] {
        assert_eq!(regime_of(src, target), Some(RegimeKind::Total));
    }
}

#[test]
fn an_illegal_pair_has_no_regime() {
    // Regime is meaningless for a pair `crate::legal_pair` already refuses (never a second
    // admissibility gate — DRY).
    assert_eq!(regime_of(ReprKind::Binary, ReprKind::Binary), None);
    assert_eq!(regime_of(ReprKind::DenseF32, ReprKind::Binary), None);
}

/// Totality of `regime_of` over the legal pairs (exhaustive — [`ReprKind`] is a small closed enum):
/// every legal pair gets a `Some` classification, every illegal pair gets `None` — no pair is
/// silently unclassified.
#[test]
fn regime_of_is_total_over_legal_pairs_and_none_over_illegal_ones() {
    use ReprKind::{Binary, DenseBf16, DenseF32, DenseOther, Ternary, Vsa};
    const ALL: [ReprKind; 6] = [Binary, Ternary, DenseF32, DenseBf16, DenseOther, Vsa];
    for &src in &ALL {
        for &target in &ALL {
            let legal = matches!(
                classify_swap_pair_for_test(src, target),
                crate::legal_pair::PairVerdict::Legal { .. }
            );
            let regime = regime_of(src, target);
            assert_eq!(
                regime.is_some(),
                legal,
                "regime_of({src:?}, {target:?}) = {regime:?}, but legality = {legal}"
            );
        }
    }
}

/// Local re-export shim so the totality test above reads `crate::legal_pair::classify_swap_pair`
/// without importing it unqualified twice (keeps the `use` list at the top minimal/uncluttered).
fn classify_swap_pair_for_test(src: ReprKind, target: ReprKind) -> crate::legal_pair::PairVerdict {
    crate::legal_pair::classify_swap_pair(src, target)
}

// ── `regime_type_lie_diag` — the observability-only first-fault package ────────────────────────

#[test]
fn a_partial_regime_claimed_bare_produces_a_candidate_diag() {
    let diag = regime_type_lie_diag(
        ReprKind::Ternary,
        ReprKind::Binary,
        "Ternary{6}",
        "Binary{8}",
        true,
        EventId::new("test-event-1"),
        CertMode::Fast,
    )
    .expect("a partial regime claimed bare must produce a diag");
    let env = diag
        .envelope()
        .expect("the diag carries a FirstFaultEnvelope");
    assert_eq!(env.site_kind, SiteKind::RegimeTypeLie);
    assert_eq!(env.decision, Decision::Candidate);
    assert_eq!(env.cert_mode, CertMode::Fast);
    assert!(diag.human().contains("Ternary{6}"));
    assert!(diag.human().contains("Binary{8}"));
}

#[test]
fn a_total_regime_never_produces_a_diag_even_if_claimed_bare() {
    // Bounded pairs and the enc direction are honestly bare-typeable — no candidate to surface
    // (RFC-0013 §4.6 "non-sites": no event fires when nothing is dishonest).
    assert!(regime_type_lie_diag(
        ReprKind::Binary,
        ReprKind::Ternary,
        "Binary{8}",
        "Ternary{6}",
        true,
        EventId::new("test-event-2"),
        CertMode::Fast,
    )
    .is_none());
    assert!(regime_type_lie_diag(
        ReprKind::DenseF32,
        ReprKind::DenseBf16,
        "Dense{768, F32}",
        "Dense{768, BF16}",
        true,
        EventId::new("test-event-3"),
        CertMode::Fast,
    )
    .is_none());
}

#[test]
fn a_partial_regime_not_claimed_bare_produces_no_diag() {
    // `claimed_bare = false` — the caller is not making a total claim, so there is nothing
    // dishonest to report (this is the shape a future `to:`-elision-aware caller, or an
    // Option/Result-typed swap target, would pass).
    assert!(regime_type_lie_diag(
        ReprKind::Ternary,
        ReprKind::Binary,
        "Ternary{6}",
        "Binary{8}",
        false,
        EventId::new("test-event-4"),
        CertMode::Fast,
    )
    .is_none());
}

#[test]
fn an_illegal_pair_produces_no_diag_that_is_legal_pair_refuse_s_job() {
    assert!(regime_type_lie_diag(
        ReprKind::Binary,
        ReprKind::Binary,
        "Binary{8}",
        "Binary{16}",
        true,
        EventId::new("test-event-5"),
        CertMode::Fast,
    )
    .is_none());
}
