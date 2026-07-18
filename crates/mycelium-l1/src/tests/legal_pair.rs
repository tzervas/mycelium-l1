//! Unit tests for the A1 legal-pair matrix (DN-142 §7; `crate::legal_pair`).

use crate::legal_pair::*;

/// A verbatim transcription of RFC-0002 §5's legal-pair table (`docs/rfcs/RFC-0002-Swap-Certificate-
/// and-Split-Regime.md` §5), independent of `LEGAL_PAIR_TABLE`'s own literal — this is the fixture
/// the module's materialization is checked *against*, not a restatement that could silently drift
/// with it.
///
/// ```text
/// | R_src → R_target                    | Regime                        | Bound basis |
/// |--------------------------------------|--------------------------------|-------------|
/// | Binary ↔ Ternary (in range)          | LosslessWithinRange, Exact     | proof of enc/dec round-trip |
/// | Binary ↔ Ternary (out of range)      | rejected / explicit error      | — (never silent) |
/// | Dense F32 → BF16                     | Bounded (ε)                    | rounding-error theory (ADR-010 ErrorBound) |
/// | Dense ↔ VSA                          | Bounded/probabilistic (ε, δ)   | VSA capacity results (RFC-0003, T0.2) |
/// | VSA model ↔ VSA model                | case-by-case                   | per-pair derivation (RFC-0003 matrix) |
/// | pair with no statable bound          | type error                     | — (not a Declared gamble) |
/// ```
fn rfc_0002_section_5_rows() -> [(&'static str, &'static str, &'static str); 6] {
    [
        (
            "Binary ↔ Ternary (in range)",
            "LosslessWithinRange, Exact",
            "proof of enc/dec round-trip",
        ),
        (
            "Binary ↔ Ternary (out of range)",
            "rejected / explicit error",
            "— (never silent)",
        ),
        (
            "Dense F32 → BF16",
            "Bounded (ε)",
            "rounding-error theory (ADR-010 ErrorBound)",
        ),
        (
            "Dense ↔ VSA",
            "Bounded/probabilistic (ε, δ)",
            "VSA capacity results (RFC-0003, T0.2)",
        ),
        (
            "VSA model ↔ VSA model",
            "case-by-case",
            "per-pair derivation (RFC-0003 matrix)",
        ),
        (
            "pair with no statable bound",
            "type error",
            "— (not a Declared gamble)",
        ),
    ]
}

#[test]
fn legal_pair_table_materializes_rfc_0002_section_5_verbatim() {
    let rows = rfc_0002_section_5_rows();
    assert_eq!(
        LEGAL_PAIR_TABLE.len(),
        rows.len(),
        "RFC-0002 §5 has exactly {} rows",
        rows.len()
    );
    for (i, ((pair, regime, basis), row)) in rows.iter().zip(LEGAL_PAIR_TABLE.iter()).enumerate() {
        assert_eq!(row.pair, *pair, "row {i} pair label must match RFC-0002 §5");
        assert_eq!(row.regime, *regime, "row {i} regime must match RFC-0002 §5");
        assert_eq!(
            row.bound_basis, *basis,
            "row {i} bound basis must match RFC-0002 §5"
        );
    }
}

/// Property test (exhaustive — [`ReprKind`] is a small closed enum, so brute-forcing every pair is a
/// complete, not sampled, proof): [`classify_swap_pair`] is **total** (never panics) over every
/// `(src, target)` pair, and the set of `Legal` pairs is *exactly* the expected set — no pair is
/// silently admitted or silently refused outside that set. This is the bound property `classify_swap_pair`
/// exists to guarantee: A1's early-refusal gate never lets an unstated pair through, and never refuses a
/// stated one. Guarantee: `Exact` (a closed-form enumeration, not a statistical sample).
#[test]
fn classify_swap_pair_is_total_and_matches_the_expected_legal_set() {
    use ReprKind::{Binary, DenseBf16, DenseF32, DenseOther, Ternary, Vsa};
    const ALL: [ReprKind; 6] = [Binary, Ternary, DenseF32, DenseBf16, DenseOther, Vsa];

    // The exact expected `Legal` set (RFC-0002 §5 rows 1–5 plus the disclosed DN-52 carve-out).
    let expected_legal: Vec<(ReprKind, ReprKind)> = vec![
        (Binary, Ternary),
        (Ternary, Binary),
        (DenseF32, DenseBf16),
        (DenseF32, Vsa),
        (Vsa, DenseF32),
        (DenseBf16, Vsa),
        (Vsa, DenseBf16),
        (DenseOther, Vsa),
        (Vsa, DenseOther),
        (Vsa, Vsa),
        (Binary, DenseF32),
        (Binary, DenseBf16),
        (Binary, DenseOther),
        (Ternary, DenseF32),
        (Ternary, DenseBf16),
        (Ternary, DenseOther),
    ];

    for &src in &ALL {
        for &target in &ALL {
            let verdict = classify_swap_pair(src, target); // must not panic (totality)
            let is_legal = matches!(verdict, PairVerdict::Legal { .. });
            let should_be_legal = expected_legal.contains(&(src, target));
            assert_eq!(
                is_legal, should_be_legal,
                "classify_swap_pair({src:?}, {target:?}) = {verdict:?}, expected legal = \
                 {should_be_legal}"
            );
        }
    }
}

#[test]
fn same_paradigm_pairs_are_refused_as_no_statable_bound() {
    for &(src, target) in &[
        (ReprKind::Binary, ReprKind::Binary),
        (ReprKind::Ternary, ReprKind::Ternary),
    ] {
        let verdict = classify_swap_pair(src, target);
        match verdict {
            PairVerdict::Refuse { reason } => {
                assert!(reason.contains("no statable bound"), "got: {reason}");
            }
            other => panic!("expected a same-paradigm pair to be refused, got {other:?}"),
        }
    }
}

#[test]
fn reverse_of_the_stated_dense_f32_to_bf16_row_is_refused() {
    // RFC-0002 §5 states only the F32 → BF16 direction; the reverse is not a stated row.
    let verdict = classify_swap_pair(ReprKind::DenseBf16, ReprKind::DenseF32);
    assert!(
        matches!(verdict, PairVerdict::Refuse { .. }),
        "got: {verdict:?}"
    );
}

#[test]
fn reverse_of_the_dn_52_dense_carve_out_is_refused() {
    // The DN-52 freeze-ledger carve-out is Binary/Ternary → Dense only; untested/unstated reverse.
    let verdict = classify_swap_pair(ReprKind::DenseF32, ReprKind::Binary);
    assert!(
        matches!(verdict, PairVerdict::Refuse { .. }),
        "got: {verdict:?}"
    );
}

#[test]
fn catalog_default_policy_is_closed_and_matches_the_corpus_names() {
    assert_eq!(
        catalog_default_policy(ReprKind::Binary, ReprKind::Ternary),
        Some("rt")
    );
    assert_eq!(
        catalog_default_policy(ReprKind::Ternary, ReprKind::Binary),
        Some("rt")
    );
    assert_eq!(
        catalog_default_policy(ReprKind::DenseF32, ReprKind::DenseBf16),
        Some("bf16_round")
    );
    // Not in the v0 seed — no invented name (module doc).
    assert_eq!(
        catalog_default_policy(ReprKind::DenseF32, ReprKind::Vsa),
        None
    );
    assert_eq!(catalog_default_policy(ReprKind::Vsa, ReprKind::Vsa), None);
}
