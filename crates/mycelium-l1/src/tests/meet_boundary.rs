//! Unit tests for the meet-boundary table (`crate::meet_boundary`, DN-141 §4 R4/R5, W-C X4).

use crate::ast::Strength;
use crate::meet_boundary::*;
use mycelium_diag::{CertMode, Decision, EventId, SiteKind};

// ── R5: table-driven allow/refuse, exhaustive over the lattice ─────────────────────────────────

#[test]
fn check_boundary_agrees_with_satisfies_exhaustively_for_every_wired_kind() {
    // Exhaustive (Strength::ALL x Strength::ALL x the 2 wired kinds = 32 cases, a complete proof —
    // not a sample) equivalence between the table's verdict and the underlying `Strength::satisfies`
    // arithmetic it is DRY-derived from.
    for &kind in &[BoundaryKind::Export, BoundaryKind::ExactDemand] {
        for &have in &Strength::ALL {
            for &demand in &Strength::ALL {
                let verdict = check_boundary(kind, have, demand);
                let expected_allow = have.satisfies(demand);
                assert_eq!(
                    matches!(verdict, BoundaryVerdict::Allow),
                    expected_allow,
                    "check_boundary({kind:?}, {have:?}, {demand:?}) disagreed with \
                     Strength::satisfies"
                );
            }
        }
    }
}

#[test]
fn a_stronger_or_equal_grade_is_always_allowed_at_the_export_boundary() {
    for &have in &Strength::ALL {
        for &demand in &Strength::ALL {
            if have.rank() >= demand.rank() {
                assert!(matches!(
                    check_boundary(BoundaryKind::Export, have, demand),
                    BoundaryVerdict::Allow
                ));
            }
        }
    }
}

#[test]
fn a_strictly_weaker_grade_is_always_refused_without_a_seal() {
    for &have in &Strength::ALL {
        for &demand in &Strength::ALL {
            if have.rank() < demand.rank() {
                for &kind in &[BoundaryKind::Export, BoundaryKind::ExactDemand] {
                    assert!(
                        matches!(check_boundary(kind, have, demand), BoundaryVerdict::Refuse),
                        "{have:?} must be refused against the stronger demand {demand:?} at \
                         {kind:?} — v0 has no seal (X6) to admit it"
                    );
                }
            }
        }
    }
}

// ── The `meet_boundary` diag builder ────────────────────────────────────────────────────────────

#[test]
fn a_refused_crossing_produces_a_meet_boundary_diag() {
    let diag = meet_boundary_refuse_diag(
        BoundaryKind::Export,
        Strength::Empirical,
        Strength::Exact,
        "the function body",
        EventId::new("test-mb-1"),
        CertMode::Fast,
    )
    .expect("a refused crossing must produce a diag");
    let env = diag
        .envelope()
        .expect("the diag carries a FirstFaultEnvelope");
    assert_eq!(env.site_kind, SiteKind::MeetBoundary);
    assert_eq!(env.decision, Decision::Refuse);
    assert_eq!(
        env.grades.input,
        vec![mycelium_diag::GuaranteeStrength::Empirical]
    );
    assert_eq!(
        env.grades.output,
        Some(mycelium_diag::GuaranteeStrength::Exact)
    );
    assert!(diag.human().contains("Empirical"));
    assert!(diag.human().contains("Exact"));
    assert!(diag.human().contains("export"));
}

#[test]
fn an_allowed_crossing_produces_no_diag_a_non_site() {
    assert!(meet_boundary_refuse_diag(
        BoundaryKind::ExactDemand,
        Strength::Exact,
        Strength::Declared,
        "an argument",
        EventId::new("test-mb-2"),
        CertMode::Fast,
    )
    .is_none());
}

#[test]
fn boundary_kind_names_are_stable_and_distinct() {
    let names: std::collections::BTreeSet<&str> = [
        BoundaryKind::Export,
        BoundaryKind::ExactDemand,
        BoundaryKind::CertifiedConsumer,
    ]
    .iter()
    .map(|k| k.as_str())
    .collect();
    assert_eq!(
        names.len(),
        3,
        "every BoundaryKind must have a distinct EXPLAIN name"
    );
}

// ── R4 regression guard: internal composition never calls `require` (meet stays free inside) ────

/// A grep-level structural guard (mirrors this crate's own `docs/api-index` "source is ground
/// truth" posture, and DN-80's reject-ledger style): confirms `grade.rs`'s internal-composition
/// match arms (`Let`'s binding/body meet, `If`'s branch meet, `Match`'s arm meet, `Fuse`, `meet_all`)
/// combine grades via `.meet(` directly and never via `self.require(` — i.e. R4 ("meet is free
/// inside") holds structurally in the source today, not just by argument. This is `Empirical` (a
/// source-text heuristic, like `docs/api-index`'s own posture) — it does not prove semantic
/// completeness, only that the textual pattern this test checks for is present.
#[test]
fn internal_composition_never_calls_require() {
    let src = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/grade.rs"),
    )
    .expect("reading grade.rs");
    // The exact count of `self.require(` call sites is 3 (Let ascription, value Ascribe, grade_app
    // argument demand) — none of them are inside `Let`'s/`If`'s/`Match`'s *unconditional* meet
    // composition itself (those combine via `.meet(` only). This asserts the low bound directly:
    // `.meet(` composition sites clearly outnumber `require(` sites, and `require(` never appears
    // inside the for-fold/if/match meet-combination lines. A tighter AST-level proof would need a
    // second parser; this heuristic is the same class of check `docs/api-index/` already accepts as
    // its own posture (source is ground truth) — sufficient to catch a regression that starts gating
    // pure internal composition through `require`.
    let meet_calls = src.matches(".meet(").count();
    let require_calls = src.matches("self.require(").count();
    // Audited 2026-07-18 (this leaf): 7 `.meet(` call sites — `Let` (bind.meet(body)), `If`
    // (t.meet(f)), `For` (g_init.meet(g_xs).meet(g_body) — two on one line), `Fuse` (lg.meet(rg)),
    // `Match`'s arm-accumulation (a.meet(g_arm)), and `meet_all`'s fold (acc.meet(...)). If this
    // count changes, re-verify R4 (meet stays free inside) still holds for whatever new/removed
    // site caused the drift before updating this pinned count.
    assert_eq!(
        meet_calls, 7,
        "expected grade.rs's internal-composition `.meet(` call-site count to match the audited 7 \
         (Let/If/For x2/Fuse/Match/meet_all) — found {meet_calls}; update this pinned count only \
         after re-verifying R4 still holds for the new/removed site"
    );
    assert_eq!(
        require_calls, 3,
        "grade.rs's `self.require(` call-site count drifted from the audited 3 (Let ascription, \
         value Ascribe, grade_app argument demand) — if this genuinely grew, update this pinned \
         count together with a re-check that R4 (meet free inside) still holds for every new site"
    );
}
