//! End-to-end (parse → check) coverage of the A1 legal-pair matrix (DN-142 §7) through the real
//! `swap` checking path — the integration-level counterpart to `src/tests/legal_pair.rs`'s unit
//! tests of the pure `classify_swap_pair` function.

use mycelium_l1::{check_nodule, parse};

fn check_err(src: &str) -> String {
    check_nodule(&parse(src).expect("parses"))
        .expect_err(
            "an illegal swap pair must be refused by the checker, not later at runtime \
                     (DN-142 §7)",
        )
        .message
}

#[test]
fn a_same_paradigm_binary_to_binary_swap_is_refused_naming_the_pair() {
    // Binary → Binary is not one of RFC-0002 §5's legal-pair rows (row 6: "pair with no statable
    // bound" → type error) — refused at the checker, never accepted-then-failed at runtime.
    let msg = check_err(
        "nodule d;\nfn main(x: Binary{8}) => Binary{16} = swap(x, to: Binary{16}, policy: rt);",
    );
    assert!(msg.contains("illegal swap pair"), "got: {msg}");
    assert!(
        msg.contains("Binary{8}") && msg.contains("Binary{16}"),
        "must name the pair — got: {msg}"
    );
    assert!(
        msg.contains("no statable bound"),
        "must cite RFC-0002 §5 row 6 — got: {msg}"
    );
}

#[test]
fn a_same_paradigm_ternary_to_ternary_swap_is_refused_naming_the_pair() {
    let msg = check_err(
        "nodule d;\nfn main(x: Ternary{6}) => Ternary{4} = swap(x, to: Ternary{4}, policy: rt);",
    );
    assert!(msg.contains("illegal swap pair"), "got: {msg}");
    assert!(
        msg.contains("Ternary{6}") && msg.contains("Ternary{4}"),
        "must name the pair — got: {msg}"
    );
    assert!(
        msg.contains("no statable bound"),
        "must cite RFC-0002 §5 row 6 — got: {msg}"
    );
}

#[test]
fn a_legal_binary_ternary_pair_still_checks_cleanly() {
    // Sanity: the A1 gate is additive, not a regression — the RFC-0002 §5 row 1/2 pair (the one
    // every existing swap test in this crate already exercises) is unaffected.
    let ok = check_nodule(
        &parse(
            "nodule d;\nfn main(x: Binary{8}) => Ternary{6} = swap(x, to: Ternary{6}, policy: rt);",
        )
        .expect("parses"),
    );
    assert!(
        ok.is_ok(),
        "a legal Binary → Ternary pair must still check cleanly — got: {ok:?}"
    );
}

#[test]
fn the_pre_existing_dn_52_dense_carve_out_still_checks_cleanly() {
    // Sanity: the A1 gate preserves the pre-existing, tested DN-52 freeze-ledger acceptance of
    // Binary/Ternary → Dense (verify-first — mitigation #14; `tests/runnable_gate.rs`,
    // `tests/differential.rs::dense_swap_is_an_explicit_residual_on_all_paths`), never silently
    // narrowing an already-landed behavior.
    let ok = check_nodule(
        &parse(
            "nodule d;\nfn main() => Dense{4, F32} = swap(0b1011_0010, to: Dense{4, F32}, policy: rt);",
        )
        .expect("parses"),
    );
    assert!(
        ok.is_ok(),
        "the DN-52 Binary/Ternary → Dense carve-out must still check cleanly — got: {ok:?}"
    );
}
