# Gap note: FFI host-execution seam (`wild`) + language-surface gaps

**Context:** port-readiness review 2026-07-22 (`claude/mycelium-readiness-gaps`).
Full plan: `mycelium-lang` `docs/planning/PORT-READINESS-2026-07-22.md`.

## 1. The linchpin — `wild {}` host registry (G15)

`wild {}` is the language's audited FFI floor. Status against **mycelium-runtime gate A1**
(`4e8125b`, `HostOpRegistry` + `HostCapabilities::ffi`) and this crate's dual-reg consumer
migration:

| Path | Status |
|---|---|
| Parse / check (`@std-sys` + `!{ffi}`) | **Green** — RFC-0016 §8-Q6 / LR-9 |
| Elaborate host-call form → `Op{prim:"wild:name"}` | **Green** — M-720, KC-3 (no new Core-IR node) |
| L1-eval with `Evaluator::with_host_floor()` | **Green** — A1 min floor dispatches |
| L0-interp with `Interpreter::with_host_floor()` | **Green** — same registry |
| Default evaluator / interpreter (no floor) | **Fail-closed** — typed miss / capability denial (G2) |
| AOT (`mycelium_mlir::run`) min-floor ops | **Residual** — AOT still uses `PrimRegistry` only; min floor is interpreter/L1-only until codegen migrates |
| Three-way on deterministic mock host op | **Green** — dual-reg (`HostOpRegistry` + `PrimRegistry` `wild:echo`) in `tests/differential.rs` |

### Min built-in host ops (A1)

| prim key | signature | guarantee | effect |
|---|---|---|---|
| `wild:entropy_fill` | `Binary{N} → Bytes` | **Declared** | fill `n` bytes from host RNG (hard 1 MiB cap; refuse, never truncate) |
| `wild:mono_nanos` | `() → Binary{64}` | **Declared** | process-local monotonic nanoseconds |
| `wild:read_capped` | `(Bytes path, Binary{N} max) → Bytes` | **Declared** | read path; refuse if source > cap |

Witness: `tests/host_contact.rs` (`wild_mono_nanos_host_contact_program_executes_on_l1_and_l0`).

### Historical reproduction (empty registry — pre-A1)

```
# outside @std-sys:
error[myc-check]: `wild` is denied outside a `@std-sys` nodule … (RFC-0016 §8-Q6, LR-9)

# inside `nodule x @std-sys;`, with the ffi effect declared after the return type:
fn hostcall() => Binary{8} !{ffi} = wild { 0b0000_0001 };   # => myc check clean
$ myc run
error[myc-run-residual]: `hostcall` is outside the evaluation-complete fragment
  (RFC-0007 §4.6): a v0 `wild` block body must be a host-call form `name(args…)` …
```

`elab_wild` lowers a well-formed `wild { name(args) }` to a `Node::Op { prim: "wild:name" }`.
Before A1 the host-call registry was **empty by design** (RFC-0028 §4.3). A1 fills the
runtime registry; this crate wires the L1 evaluator to it and pins end-to-end host-contact
execution.

### Remaining (honest residuals)

- **A1b:** `HostFloor` adapter over `mycelium-std-sys` (no new cross-repo surface APIs).
- **AOT HostOpRegistry:** drop dual-reg once codegen routes `wild:` like L0/L1.
- **CLI `myc run`:** must opt into the host floor for host-contact programs (fail-closed by default is correct).

## 2. Language-surface gaps surfaced by porting real Rust

`mycelium-transpile --vet` on `gha-runner-ctl` (see
`mycelium-transpile/docs/vet-gha-runner-ctl-2026-07-22/`) could not compute a valid
`checked_fraction` in this standalone setup (the `--vet` oracle needs `mycelium-check`
in-workspace and recorded an un-run 0/192). Measured directly with `myc check`, one emitted
file (`pool.myc`) type-checks clean and another (`lib.myc`) fails (≈2.1% file-gated) — the
limit is idiomatic imperative Rust hitting frontend-surface gaps, not the logic being
unportable (the pure core ports fine by hand; see `gha-runner-ctl/mycelium-port/`). The dominant, quantified ones:

| Gap | Vet signal | Implication |
|---|---|---|
| **No unit value** — side-effecting / `()`-returning fns have no representation | 13 gaps ("no unit value is representable in this grammar") | imperative statement sequences can't be expressed as fns |
| **No method-call sugar** — `x.method()` has no free-fn referent | 31 gaps | every idiomatic Rust call site gaps |
| **Multi-statement bodies** | 38 gaps | only single-tail-expression (+ simple `let`) bodies emit |
| **Non-unsigned / string / struct types** | 14 gaps | `String`/`f64`/named-field structs not in the value fragment |

These are not all "must-fix to port" (the pure fragment is enough for the logic cores),
but they define the distance between "expresses pure total functions" and "expresses an
ordinary program." Tracking here as the frontend's side of the readiness picture; the
host-effect seam (§1) is closed for L1/L0 evaluation of the A1 min floor.

## 3. Changelog

- **2026-07-25** — G15 L1/L0 path: pin mycelium-runtime A1; `Evaluator::with_host_floor` /
  `with_host_ops`; `tests/host_contact.rs` proves `wild { mono_nanos() }` executes. AOT
  min-floor residual documented, not faked.
