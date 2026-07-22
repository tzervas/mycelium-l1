# Gap note: FFI host-execution seam (`wild`) + language-surface gaps

**Context:** port-readiness review 2026-07-22 (`claude/mycelium-readiness-gaps`).
Full plan: `mycelium-lang` `docs/planning/PORT-READINESS-2026-07-22.md`.

## 1. The linchpin — `wild {}` type-checks but does not execute

`wild {}` is the language's audited FFI floor and the **single highest-leverage gap**:
without it executing, no Rust/native function is callable from Mycelium, so "bridge
host-effect gaps with Rust" is not mechanically possible. Reproduced against the built
`v0.464.0` `myc`:

```
# outside @std-sys:
error[myc-check]: `wild` is denied outside a `@std-sys` nodule … (RFC-0016 §8-Q6, LR-9)

# inside `nodule x @std-sys;`, with the ffi effect declared after the return type:
fn hostcall() => Binary{8} !{ffi} = wild { 0b0000_0001 };   # => myc check clean
$ myc run
error[myc-run-residual]: `hostcall` is outside the evaluation-complete fragment
  (RFC-0007 §4.6): a v0 `wild` block body must be a host-call form `name(args…)` …
```

`elab_wild` (`src/elab.rs` ~:2035) lowers a well-formed `wild { name(args) }` to a
`Node::Op { prim: "wild:name" }`, but the host-call registry is **empty by design**
(RFC-0028 §4.3) — no `wild:` op is registered in `mycelium-interp` /
`mycelium-std-sys-host`. Confirmed genuine (not extraction-lag): the monorepo behaves
the same, with the registry empty by design.

**Ask:** define the host-function table + effect/host runtime so `wild { name(args) }`
executes against registered `wild:` ops (authored in the `@std-sys` floor —
see `mycelium-std-sys/docs/GAP-host-effects.md`). This is **Tier-0** in the plan and
gates every host capability (`std-net`, `std-process`, real-OS fs).

## 2. Language-surface gaps surfaced by porting real Rust

`mycelium-transpile --vet` on `gha-runner-ctl` (see
`mycelium-transpile/docs/vet-gha-runner-ctl-2026-07-22/`) produced **0.0%
`checked_fraction`** — not because the logic is unportable (the pure core ports fine by
hand; see `gha-runner-ctl/mycelium-port/`), but because idiomatic imperative Rust hits
frontend-surface gaps. The dominant, quantified ones:

| Gap | Vet signal | Implication |
|---|---|---|
| **No unit value** — side-effecting / `()`-returning fns have no representation | 13 gaps ("no unit value is representable in this grammar") | imperative statement sequences can't be expressed as fns |
| **No method-call sugar** — `x.method()` has no free-fn referent | 31 gaps | every idiomatic Rust call site gaps |
| **Multi-statement bodies** | 38 gaps | only single-tail-expression (+ simple `let`) bodies emit |
| **Non-unsigned / string / struct types** | 14 gaps | `String`/`f64`/named-field structs not in the value fragment |

These are not all "must-fix to port" (the pure fragment is enough for the logic cores),
but they define the distance between "expresses pure total functions" and "expresses an
ordinary program." Tracking here as the frontend's side of the readiness picture; the
host-effect seam (§1) is the blocking item.
