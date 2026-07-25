# Vendored pins

## `mycelium-runtime` @ A1 (`4e8125b`)

Path-patch target for workspace `[patch."https://github.com/tzervas/mycelium-runtime"]`.

**Why vendored:** Cargo refuses a same-URL git→git rev patch. `mycelium-mlir` (codegen
`505448c`) still declares the pre-A1 runtime rev, so without a path patch the graph loads
two `mycelium_interp` crates and the three-way differential fails to type-check.

**Contents:** exact tree of `tzervas/mycelium-runtime` at
`4e8125b231a78d14e0c882677b81b7048887a593` (gate A1: `HostOpRegistry` +
`HostCapabilities::ffi`). See `mycelium-runtime/A1_PIN`.

**Retire when:** codegen pin-bumps onto A1 (or later) and this workspace can depend on a
single git rev without a dual load.
