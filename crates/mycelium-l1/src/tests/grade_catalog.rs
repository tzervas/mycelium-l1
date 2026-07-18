//! Unit tests for the structural grade catalog (`crate::grade_catalog`, DN-141 R3) and the
//! W-C X2 **overclaim guard**: exhaustive lattice-property tests over [`Strength`] (a small closed
//! 4-variant enum, so brute-forcing every combination is a complete proof, not a sample — the same
//! posture `crate::tests::legal_pair`'s `classify_swap_pair_is_total_and_matches_the_expected_legal_set`
//! takes over `ReprKind`) confirming the checker's own honesty invariant (VR-5: a grade may never be
//! upgraded without a checked basis) holds at the algebraic level every structural rule composes on.

use crate::ast::Strength;
use crate::grade_catalog::*;

// ── R3: the structural grade catalog is committed, named data (not ad hoc) ─────────────────────

#[test]
fn catalog_is_non_empty_and_every_rule_id_is_unique() {
    assert!(
        !STRUCTURAL_GRADE_CATALOG.is_empty(),
        "the catalog must name at least the RFC-0018 §4.3 structural rules"
    );
    let mut seen = std::collections::BTreeSet::new();
    for row in STRUCTURAL_GRADE_CATALOG {
        assert!(
            seen.insert(row.rule_id),
            "duplicate rule_id `{}` — each structural rule is named exactly once",
            row.rule_id
        );
        assert!(
            !row.construct.is_empty(),
            "row {} has no construct",
            row.rule_id
        );
        assert!(
            !row.summary.is_empty(),
            "row {} has no summary",
            row.rule_id
        );
        assert!(
            !row.citation.is_empty(),
            "row {} has no citation",
            row.rule_id
        );
    }
}

/// Completeness (the "no orphan rule" half): every RFC-0018 §4.3 rule id `crate::grade`'s own doc
/// comments name is present in the catalog. This is a hand-maintained closed list (mirrors DN-80's
/// `reject_ledger.rs` variant-set pattern) — if `crate::grade` grows a new structural form, this
/// test's `expected` list and the catalog must be updated together (never silently drift apart).
#[test]
fn catalog_names_every_structural_rule_grade_rs_implements() {
    const EXPECTED: &[&str] = &[
        "G-Const",
        "G-Var",
        "G-Let",
        "G-Match/A",
        "G-For",
        "G-Swap",
        "G-Wild",
        "G-App/G-Con/G-Op",
        "G-Sub / G-Weaken",
        "G-Fuse",
        "G-Reclaim",
        "G-Consume/G-Try",
        "G-Lambda",
        "G-Wrapping",
    ];
    let actual: std::collections::BTreeSet<&str> =
        STRUCTURAL_GRADE_CATALOG.iter().map(|r| r.rule_id).collect();
    let expected: std::collections::BTreeSet<&str> = EXPECTED.iter().copied().collect();
    assert_eq!(
        actual, expected,
        "the catalog's rule-id set has drifted from the hand-maintained EXPECTED list — update both \
         together when `crate::grade` gains/loses a structural form"
    );
}

#[test]
fn rule_lookup_finds_known_ids_and_refuses_unknown_ones() {
    let row = rule("G-Swap").expect("G-Swap is a catalog row");
    assert_eq!(row.construct, "`swap(value, to: T, policy: p)`");
    assert!(
        rule("G-Not-A-Real-Rule").is_none(),
        "unknown ids are None, never fabricated"
    );
}

// ── W-C X2 overclaim guard: exhaustive lattice-property tests over Strength ─────────────────────
//
// These tie VR-5's informal "never upgrade a grade without a checked basis" claim to the concrete
// algebra every structural rule in the catalog above composes on: `Strength::meet`/`Strength::rank`/
// `Strength::satisfies`. `Strength::ALL` has exactly 4 variants, so every loop below is a *complete*
// enumeration (16 or 64 cases), not a statistical sample — Guarantee: `Exact`.

#[test]
fn meet_never_exceeds_either_operand_rank_no_op_can_display_a_composed_grade_stronger_than_its_inputs(
) {
    // The overclaim guard's core bound: for every (a, b), meet(a, b)'s rank is <= both a's and b's
    // rank. This is the algebraic form of "no op's displayed/exported grade exceeds its catalog/
    // basis" (the W-C X2 DoD line) — a composed value can never be reported stronger than either of
    // the parts it was built from.
    for &a in &Strength::ALL {
        for &b in &Strength::ALL {
            let m = a.meet(b);
            assert!(
                m.rank() <= a.rank() && m.rank() <= b.rank(),
                "meet({a:?}, {b:?}) = {m:?} must never rank above either operand"
            );
        }
    }
}

#[test]
fn meet_is_commutative_associative_and_idempotent() {
    for &a in &Strength::ALL {
        for &b in &Strength::ALL {
            assert_eq!(
                a.meet(b),
                b.meet(a),
                "meet must be commutative: {a:?}, {b:?}"
            );
            assert_eq!(a.meet(a), a, "meet must be idempotent: {a:?}");
            for &c in &Strength::ALL {
                assert_eq!(
                    a.meet(b).meet(c),
                    a.meet(b.meet(c)),
                    "meet must be associative: {a:?}, {b:?}, {c:?}"
                );
            }
        }
    }
}

#[test]
fn satisfies_agrees_exactly_with_rank_order_never_a_looser_or_tighter_check() {
    // `have.satisfies(demand)` is the sole gate every G-Weaken/G-Sub/G-App check (grade.rs's
    // `require`) is built on — if this drifted from the rank order, either a genuinely-too-weak
    // value could pass (a silent overclaim) or a genuinely-sufficient one could be wrongly refused.
    for &have in &Strength::ALL {
        for &demand in &Strength::ALL {
            assert_eq!(
                have.satisfies(demand),
                have.rank() >= demand.rank(),
                "satisfies({have:?}, {demand:?}) must agree exactly with rank order"
            );
        }
    }
}

#[test]
fn a_strength_never_satisfies_a_strictly_stronger_demand() {
    // The direct restatement of VR-5 ("never upgrade without a checked basis") as a lattice fact:
    // Declared can never satisfy Empirical/Proven/Exact; Empirical can never satisfy Proven/Exact;
    // Proven can never satisfy Exact. Exhaustive over all 16 pairs.
    for &have in &Strength::ALL {
        for &demand in &Strength::ALL {
            if demand.rank() > have.rank() {
                assert!(
                    !have.satisfies(demand),
                    "{have:?} must NOT satisfy the strictly stronger {demand:?} — an upgrade \
                     without a checked basis would be a VR-5 violation"
                );
            }
        }
    }
}

#[test]
fn every_strength_satisfies_its_own_grade_and_every_weaker_demand() {
    for &have in &Strength::ALL {
        for &demand in &Strength::ALL {
            if demand.rank() <= have.rank() {
                assert!(
                    have.satisfies(demand),
                    "{have:?} must satisfy the equal-or-weaker demand {demand:?}"
                );
            }
        }
    }
}

/// `Strength::ALL` itself is honest: exactly 4 distinct variants, in strictly increasing rank order
/// (`Declared` weakest .. `Exact` strongest) — the non-vacuousness guard for every exhaustive loop
/// above (an `ALL` that silently dropped a variant would make every "exhaustive" test above a
/// silent under-count, not a complete proof).
#[test]
fn strength_all_is_exactly_four_distinct_variants_in_increasing_rank_order() {
    assert_eq!(Strength::ALL.len(), 4);
    let ranks: Vec<u8> = Strength::ALL.iter().map(|s| s.rank()).collect();
    assert_eq!(
        ranks,
        vec![0, 1, 2, 3],
        "ALL must be listed weakest -> strongest by rank"
    );
    let unique: std::collections::BTreeSet<u8> = ranks.into_iter().collect();
    assert_eq!(unique.len(), 4, "all 4 ranks must be distinct");
}
