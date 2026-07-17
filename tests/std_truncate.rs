//! `truncate` conformance (DN-51 §2 D3/§6 — maintainer-authorized DN-39 post-freeze promotion,
//! extends DN-41) — the differential proof that the explicit, total, lossy `Binary` narrow
//! genuinely drops the high bits unconditionally and **never refuses**, in contrast to
//! `width_cast`'s checked narrow (`std_widthcast.rs`).
//!
//! `truncate(value: Binary{N}, into: Binary{M}) -> Binary{M}` unconditionally keeps the low `M`
//! bits of `value` (MSB-first), with the target width `M` carried by the **second operand's
//! width** (a *width witness* — its bits are ignored, exactly `width_cast`'s DN-41 shape). Widen/
//! identity (`M >= N`) behaves exactly like `width_cast`'s zero-extend (DN-51 does not restrict
//! `truncate`'s domain to `M < N`); narrow (`M < N`) drops the high `N - M` bits unconditionally —
//! "total but lossy" (DN-51 §2 D3).
//!
//! Each case lands a **three-way differential** (L1-eval ≡ elaborate→L0-interp ≡ AOT) over the
//! same trusted prim registry, mirroring `std_widthcast.rs`/`enablement.rs`.
//!
//! # Honesty tags
//! - **`Declared`** — every `truncate` result, uniformly (DN-51 §4's guarantee matrix: "own honest
//!   lossy tag — never `Exact`"). Unlike `width_cast`, there is no in-range/out-of-range split:
//!   `truncate` never refuses, so there is no runtime contract to tag separately.
//! - **`Empirical`** — the three-way agreement is established by trial on the programs below.
//!
//! # Never-silent (G2/VR-5)
//! `truncate` never refuses (DN-51 §2 D3) — the never-silent contract here is that the loss is
//! **only ever opted into by name**: `width_cast`'s checked narrow stays the safe default, and a
//! program must call `truncate` explicitly to get the wrapping behavior. `truncate` is exercised
//! specifically where `width_cast` *would* refuse, to make that contrast a differential fact.

use mycelium_core::{GuaranteeStrength, Payload, Repr};
use mycelium_interp::{EvalError, Interpreter, PrimRegistry};
use mycelium_l1::{check_nodule, elaborate, parse, Evaluator};

/// Run the three-way differential on `src` (L1-eval ≡ elaborate→L0-interp ≡ AOT) and assert all
/// three paths agree on the observable (`repr + payload`) AND equal the `expected` reference value.
/// (A faithful copy of `std_widthcast.rs::assert_three_way`, kept local so this conformance suite
/// is self-contained.)
fn assert_three_way(label: &str, src: &str, expected_repr: &Repr, expected_payload: &Payload) {
    let interp = Interpreter::new(
        PrimRegistry::with_builtins(),
        Box::new(mycelium_cert::BinaryTernarySwapEngine),
    );
    let prims = PrimRegistry::with_builtins();
    let engine = mycelium_cert::BinaryTernarySwapEngine;

    let env = check_nodule(&parse(src).unwrap_or_else(|e| panic!("{label}: parse failed: {e}")))
        .unwrap_or_else(|e| panic!("{label}: check failed: {e}"));

    // Path 1: the L1 fuel-guarded evaluator.
    let l1 = Evaluator::new(&env)
        .call("main", vec![])
        .unwrap_or_else(|e| panic!("{label}: L1-eval failed: {e}"));
    let l1 = l1
        .as_repr()
        .unwrap_or_else(|| panic!("{label}: result must be a repr value"))
        .clone();

    // Path 2: elaborate to L0, run on the reference interpreter.
    let node =
        elaborate(&env, "main").unwrap_or_else(|e| panic!("{label}: must be in the fragment: {e}"));
    let l0 = interp
        .eval(&node)
        .unwrap_or_else(|e| panic!("{label}: L0-interp failed: {e}"));

    // Path 3: the same L0 term through the AOT path.
    let aot = mycelium_mlir::run(&node, &prims, &engine)
        .unwrap_or_else(|e| panic!("{label}: AOT failed: {e}"));

    for (path, v) in [("L1-eval", &l1), ("L0-interp", &l0), ("AOT", &aot)] {
        assert_eq!(v.repr(), expected_repr, "{label}: {path} repr mismatch");
        assert_eq!(
            v.payload(),
            expected_payload,
            "{label}: {path} payload mismatch"
        );
    }
    assert_eq!(
        (l1.repr(), l1.payload()),
        (l0.repr(), l0.payload()),
        "{label}: L1-eval vs L0-interp diverged"
    );
    assert_eq!(
        (l0.repr(), l0.payload()),
        (aot.repr(), aot.payload()),
        "{label}: L0-interp vs AOT diverged"
    );
    // The never-`Exact` honesty assertion (DN-51 §4) — checked on all three paths, not just one,
    // since the guarantee tag is exactly the thing this differential must not let drift between
    // paths (VR-5: an inconsistent tag across L1/L0/AOT would be its own silent honesty bug).
    for (path, v) in [("L1-eval", &l1), ("L0-interp", &l0), ("AOT", &aot)] {
        assert_eq!(
            v.meta().guarantee(),
            GuaranteeStrength::Declared,
            "{label}: {path} must be tagged Declared (DN-51 §4 — truncate is never Exact)"
        );
    }
}

/// The `Binary{w}` MSB-first encoding of the unsigned value `n`.
fn bin(w: u32, n: u64) -> (Repr, Payload) {
    let bits: Vec<bool> = (0..w).rev().map(|k| (n >> k) & 1 == 1).collect();
    (Repr::Binary { width: w }, Payload::Bits(bits))
}

/// A literal for `Binary{32}(n)` as the explicit 32 bits (mirrors `std_widthcast.rs::lit32`).
fn lit32(n: u32) -> String {
    let s: String = (0..32)
        .rev()
        .map(|k| if (n >> k) & 1 == 1 { '1' } else { '0' })
        .collect();
    format!("0b{s}")
}

// ── Widen (M > N): truncate matches width_cast's zero-extension ──────────────────────────────────

/// `truncate(0b1010_0101 : Binary{8}, witness : Binary{32}) -> Binary{32}` zero-extends `0xA5`
/// (165) to `Binary{32}` — identical bits to `width_cast`'s widen, but `Declared`, not `Exact`
/// (DN-51 does not restrict `truncate` to `M < N`; see the module note).
#[test]
fn widen_8_to_32_zero_extends() {
    let (r, p) = bin(32, 0xA5);
    let src = format!(
        "nodule d;\nfn main() => Binary{{32}} = truncate(0b1010_0101, {});",
        lit32(0)
    );
    assert_three_way("truncate widen 8->32 (0xA5)", &src, &r, &p);
}

// ── Identity (M == N) ─────────────────────────────────────────────────────────────────────────────

/// A same-width `truncate` is the identity (the value and width are unchanged).
#[test]
fn same_width_is_identity() {
    let (r, p) = bin(8, 0x3c);
    assert_three_way(
        "truncate identity 8->8 (0x3c)",
        "nodule d;\nfn main() => Binary{8} = truncate(0b0011_1100, 0b0000_0000);",
        &r,
        &p,
    );
}

// ── Narrow (M < N) that fits: total, matches width_cast's value, but Declared not Exact ───────────

/// `truncate(Binary{32}(5), witness : Binary{8}) -> Binary{8}` narrows `5` (whose high 24 bits are
/// all zero) to `Binary{8}(5)` — the same bits `width_cast`'s in-range narrow would produce, but
/// `truncate` is `Declared` uniformly (DN-51 §4), never `width_cast`'s `Exact`.
#[test]
fn narrow_32_to_8_fits() {
    let (r, p) = bin(8, 5);
    let src = format!(
        "nodule d;\nfn main() => Binary{{8}} = truncate({}, 0b0000_0000);",
        lit32(5)
    );
    assert_three_way("truncate narrow 32->8 (5 fits)", &src, &r, &p);
}

// ── Narrow that would overflow width_cast: truncate succeeds, total (G2/VR-5's contrast) ─────────

/// `truncate(Binary{32}(256), into Binary{8})` does **not** fit unconditionally-preserved
/// semantics (`256`'s bit 8 is dropped) — where `width_cast` would refuse
/// (`narrow_overflow_refuses_on_every_path`, `std_widthcast.rs`), `truncate` succeeds on **every**
/// path and keeps the low byte: `256 mod 256 = 0`.
#[test]
fn narrow_overflow_succeeds_and_keeps_low_bits_on_every_path() {
    let (r, p) = bin(8, 0); // 256 mod 256 = 0
    let src = format!(
        "nodule d;\nfn main() => Binary{{8}} = truncate({}, 0b0000_0000);",
        lit32(256)
    );
    assert_three_way(
        "truncate narrow-overflow 256 -> 8 (succeeds, keeps low bits = 0)",
        &src,
        &r,
        &p,
    );
}

/// A high value (`0xFFFF_FFFF`) narrowed to `Binary{8}` succeeds on all three paths and keeps the
/// low byte (`0xFF`) — never refuses, contrasting `std_widthcast.rs`'s
/// `narrow_overflow_high_value_refuses_on_every_path`.
#[test]
fn narrow_high_value_succeeds_and_keeps_low_byte_on_every_path() {
    let (r, p) = bin(8, 0xFF);
    let src = format!(
        "nodule d;\nfn main() => Binary{{8}} = truncate({}, 0b0000_0000);",
        lit32(0xFFFF_FFFF)
    );
    assert_three_way(
        "truncate narrow 0xFFFF_FFFF -> 8 (succeeds, keeps 0xFF)",
        &src,
        &r,
        &p,
    );
}

/// The direct differential contrast: on the **same** source value, `width_cast`'s narrow refuses
/// (`EvalError::Overflow`) while `truncate`'s narrow succeeds — the never-silent point of DN-51 §2
/// D3 made concrete at the `.myc`-source level (not just the Rust-prim level already covered in
/// `mycelium-interp`'s unit tests).
#[test]
fn width_cast_refuses_where_truncate_succeeds_same_value() {
    let src_width_cast = format!(
        "nodule d;\nfn main() => Binary{{8}} = width_cast({}, 0b0000_0000);",
        lit32(300)
    );
    let env = check_nodule(&parse(&src_width_cast).expect("parses")).expect("checks");
    let interp = Interpreter::new(
        PrimRegistry::with_builtins(),
        Box::new(mycelium_cert::BinaryTernarySwapEngine),
    );
    let node = elaborate(&env, "main").expect("in fragment");
    assert!(
        matches!(interp.eval(&node), Err(EvalError::Overflow { .. })),
        "width_cast must refuse: 300 does not fit Binary{{8}}"
    );

    let (r, p) = bin(8, 300 % 256); // 44
    let src_truncate = format!(
        "nodule d;\nfn main() => Binary{{8}} = truncate({}, 0b0000_0000);",
        lit32(300)
    );
    assert_three_way(
        "truncate succeeds on the same value width_cast refuses (300 -> 8)",
        &src_truncate,
        &r,
        &p,
    );
}

// ── Property: truncate(x, 4) == x mod 16, over a representative sample (DN-51 §2 D3) ──────────────

/// `truncate(x, M) == x mod 2^M` — checked over a representative sample of `Binary{8}` values
/// narrowed to `Binary{4}` via the L0-interp path directly (a full three-way per sample would be
/// AOT-costly for little extra signal beyond the dedicated three-way cases above; the exhaustive
/// 256-case sweep already runs three-way-agnostic in `mycelium-interp`'s
/// `truncate_narrow_keeps_low_bits_mod_2m`). This test pins the same property through the L1
/// surface/checker, not just the raw kernel prim.
#[test]
fn keeps_low_bits_mod_2m_through_the_l1_surface() {
    let interp = Interpreter::new(
        PrimRegistry::with_builtins(),
        Box::new(mycelium_cert::BinaryTernarySwapEngine),
    );
    for v in [0u32, 1, 5, 15, 16, 17, 31, 100, 200, 255] {
        let bits8: String = (0..8)
            .rev()
            .map(|k| if (v >> k) & 1 == 1 { '1' } else { '0' })
            .collect();
        let src = format!("nodule d;\nfn main() => Binary{{4}} = truncate(0b{bits8}, 0b0000);");
        let env = check_nodule(&parse(&src).expect("parses")).expect("checks");
        let node = elaborate(&env, "main").expect("in fragment");
        let result = interp.eval(&node).expect("truncate never refuses");
        let (r, p) = bin(4, u64::from(v % 16));
        assert_eq!(result.repr(), &r, "v={v}");
        assert_eq!(
            result.payload(),
            &p,
            "truncate({v}, 4) must equal {v} mod 16"
        );
        assert_eq!(result.meta().guarantee(), GuaranteeStrength::Declared);
    }
}

// ── Never-silent type refusals (G2): a non-Binary operand is a static error, exactly width_cast ──

/// `truncate` over a non-`Binary` value operand is a **static** type refusal (never a silent
/// coercion), exactly mirroring `width_cast`'s static typing. `<00+->` is `Ternary{4}`.
#[test]
fn truncate_non_binary_value_refuses_statically() {
    let src = format!(
        "nodule d;\nfn main() => Binary{{32}} = truncate(0t00+-, {});",
        lit32(0)
    );
    assert!(
        check_nodule(&parse(&src).expect("parses")).is_err(),
        "a Ternary value operand to truncate must be a static type error (DN-51)"
    );
}

/// `truncate` with a non-`Binary` width witness is a static refusal — the witness must be a
/// `Binary{M}` (it supplies the target width), exactly mirroring `width_cast`.
#[test]
fn truncate_non_binary_witness_refuses_statically() {
    let src = "nodule d;\nfn main() => Ternary{4} = truncate(0b0000_0011, 0t00+-);";
    assert!(
        check_nodule(&parse(src).expect("parses")).is_err(),
        "a Ternary width witness to truncate must be a static type error (DN-51)"
    );
}

/// Wrong arity is an explicit refusal (one operand is missing the width witness).
#[test]
fn truncate_wrong_arity_refuses() {
    let src = "nodule d;\nfn main() => Binary{8} = truncate(0b0000_0011);";
    assert!(
        check_nodule(&parse(src).expect("parses")).is_err(),
        "truncate requires two operands (value + width witness); one is a static error"
    );
}
