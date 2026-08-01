//! **G15 close — real host-contact programs execute** (RFC-0028 §4.3; A1 dual-reg consumer).
//!
//! Proves that an ordinary Mycelium program that touches the host — parse → check → elaborate →
//! L1-eval / L0-interp — **executes** when the A1 min host floor is installed, and **refuses
//! explicitly** when it is not. Guarantee tags follow VR-5:
//!
//! | op | guarantee | notes |
//! |---|---|---|
//! | `wild:mono_nanos` | **Declared** | process-local monotonic clock; OS contact |
//! | `wild:entropy_fill` | **Declared** | host RNG; non-deterministic |
//! | `wild:read_capped` | **Declared** | capped path read; fail-closed oversize |
//! | unregistered / no-`ffi` | **Refusal** | never a fabricated value (G2) |
//!
//! **Not claimed:** three-way L1≡L0≡AOT equality on non-deterministic host ops; AOT still routes
//! `wild:` through `PrimRegistry` at the current codegen pin (dual-reg residual — honest, not
//! silently papered over). Min-floor ops are interpreter/L1 only until AOT learns `HostOpRegistry`.

use mycelium_core::{binary, GuaranteeStrength, Payload, Repr};
use mycelium_interp::{HostCapabilities, HostOpRegistry, Interpreter, PrimRegistry};
use mycelium_l1::{check_nodule, elaborate, parse, Evaluator, L1Error};

/// Surface program: `@std-sys` + `!{ffi}` + real min-floor host op `mono_nanos`.
const MONO_NANOS_SRC: &str = r#"
nodule std.sys.clock @std-sys;
fn main() => Binary{64} !{ffi} = wild { mono_nanos() };
"#;

/// Surface program: host entropy fill of 8 bytes.
const ENTROPY_SRC: &str = r#"
nodule std.sys.rng @std-sys;
fn main() => Bytes !{ffi} = wild { entropy_fill(0b0000_1000) };
"#;

fn bits_to_u64(bits: &[bool]) -> u64 {
    binary::bits_to_uint(bits)
}

/// **The linchpin proof:** a checked `@std-sys` program with `wild { mono_nanos() }` elaborates
/// and **executes** on L1-eval + L0-interp when the min host floor is installed. Result is
/// `Binary{64}` tagged **Declared** (VR-5 — OS contact has no proven bound).
#[test]
fn wild_mono_nanos_host_contact_program_executes_on_l1_and_l0() {
    let env = check_nodule(&parse(MONO_NANOS_SRC).expect("parses")).expect("checks");
    let node = elaborate(&env, "main").expect("host-call form elaborates (M-720)");
    assert!(
        matches!(&node, mycelium_core::Node::Op { prim, args }
            if prim == "wild:mono_nanos" && args.is_empty()),
        "must lower to Op{{prim:\"wild:mono_nanos\"}}; got {node:?}"
    );

    // Path 1: L1 evaluator with the real min floor.
    let l1 = Evaluator::new(&env)
        .with_host_floor()
        .call("main", vec![])
        .expect("L1-eval must execute wild {{ mono_nanos() }} with the host floor");
    let l1v = l1.as_repr().expect("repr result").clone();
    assert_eq!(l1v.repr(), &Repr::Binary { width: 64 });
    assert_eq!(
        l1v.meta().guarantee(),
        GuaranteeStrength::Declared,
        "host results are Declared (VR-5), never Exact"
    );

    // Path 2: L0 interpreter with the same floor.
    let l0 = Interpreter::default()
        .with_host_floor()
        .eval(&node)
        .expect("L0-interp must execute wild:mono_nanos with the host floor");
    assert_eq!(l0.repr(), &Repr::Binary { width: 64 });
    assert_eq!(l0.meta().guarantee(), GuaranteeStrength::Declared);

    // Monotonicity of two successive L1 reads (process-local, Empirical on the clock itself).
    let l1_b = Evaluator::new(&env)
        .with_host_floor()
        .call("main", vec![])
        .expect("second mono_nanos");
    let t0 = match l1v.payload() {
        Payload::Bits(b) => bits_to_u64(b),
        other => panic!("expected Bits payload, got {other:?}"),
    };
    let t1 = match l1_b.as_repr().expect("repr").payload() {
        Payload::Bits(b) => bits_to_u64(b),
        other => panic!("expected Bits payload, got {other:?}"),
    };
    assert!(
        t1 >= t0,
        "mono_nanos must be non-decreasing in-process: {t0} → {t1}"
    );
}

/// Default evaluator (no host floor) refuses the same program — never fabricates a clock reading.
#[test]
fn wild_mono_nanos_without_host_floor_is_explicit_refusal() {
    let env = check_nodule(&parse(MONO_NANOS_SRC).expect("parses")).expect("checks");
    let err = Evaluator::new(&env)
        .call("main", vec![])
        .expect_err("default evaluator must refuse host contact");
    match &err {
        L1Error::Kernel(k) => {
            let msg = k.to_string();
            assert!(
                msg.contains("mono_nanos") || msg.contains("wild:mono_nanos"),
                "refusal must name the ungranted op; got: {msg}"
            );
        }
        other => panic!("expected Kernel refusal, got {other:?}"),
    }
}

/// `entropy_fill` executes through the floor (or refuses honestly if OS entropy is unavailable).
#[test]
fn wild_entropy_fill_host_contact_program_executes_or_honest_os_miss() {
    let env = check_nodule(&parse(ENTROPY_SRC).expect("parses")).expect("checks");
    let node = elaborate(&env, "main").expect("elaborates");
    assert!(
        matches!(&node, mycelium_core::Node::Op { prim, .. } if prim == "wild:entropy_fill"),
        "got {node:?}"
    );

    match Evaluator::new(&env).with_host_floor().call("main", vec![]) {
        Ok(v) => {
            let r = v.as_repr().expect("repr");
            assert_eq!(r.repr(), &Repr::Bytes);
            assert_eq!(r.bytes().expect("bytes").len(), 8);
            assert_eq!(r.meta().guarantee(), GuaranteeStrength::Declared);
        }
        Err(L1Error::Kernel(e)) => {
            let msg = e.to_string();
            assert!(
                msg.contains("entropy") || msg.contains("unavailable"),
                "OS miss must be an honest entropy refusal, not a silent zero-fill; got: {msg}"
            );
        }
        Err(other) => panic!("unexpected error: {other}"),
    }

    // L0 path agrees on the success shape (when entropy is available).
    match Interpreter::default().with_host_floor().eval(&node) {
        Ok(v) => {
            assert_eq!(v.repr(), &Repr::Bytes);
            assert_eq!(v.bytes().expect("bytes").len(), 8);
            assert_eq!(v.meta().guarantee(), GuaranteeStrength::Declared);
        }
        Err(e) => {
            let msg = e.to_string();
            assert!(
                msg.contains("entropy") || msg.contains("unavailable"),
                "L0 OS miss must be honest; got: {msg}"
            );
        }
    }
}

/// Registered host op + missing `ffi` capability → HostCapabilityDenied (security property).
#[test]
fn registered_host_op_without_ffi_capability_is_denied() {
    let env = check_nodule(&parse(MONO_NANOS_SRC).expect("parses")).expect("checks");
    // Min floor ops installed, but capability flag left false.
    let err = Evaluator::new(&env)
        .with_host_ops(HostOpRegistry::with_min_floor(), HostCapabilities::default())
        .call("main", vec![])
        .expect_err("ffi=false must deny even a registered floor op");
    let msg = err.to_string();
    assert!(
        msg.contains("mono_nanos")
            && (msg.contains("ffi") || msg.contains("not granted") || msg.contains("capability")),
        "must cite missing ffi capability; got: {msg}"
    );
}

/// AOT residual pin: min-floor host ops are **not** on `PrimRegistry`, so
/// `mycelium_mlir::run` on a `wild:mono_nanos` node is a typed miss — honest, not dual-greened.
#[test]
fn aot_min_floor_host_op_is_explicit_residual_until_codegen_migrates() {
    let env = check_nodule(&parse(MONO_NANOS_SRC).expect("parses")).expect("checks");
    let node = elaborate(&env, "main").expect("elaborates");
    let prims = PrimRegistry::with_builtins();
    let engine = mycelium_cert::BinaryTernarySwapEngine;
    let err = mycelium_mlir::run(&node, &prims, &engine)
        .expect_err("AOT must not silently invent a mono_nanos host op");
    let msg = err.to_string();
    assert!(
        msg.contains("mono_nanos") || msg.contains("wild:"),
        "AOT residual must name the missing wild op; got: {msg}"
    );
}
