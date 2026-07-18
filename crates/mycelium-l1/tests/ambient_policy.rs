//! The DN-142 §3.3 **`policy: ambient` meaning-preservation differential** — the ambient policy
//! spelling is *sugar, not behavior*, exactly like the RFC-0012 paradigm ambient: a swap written
//! `policy: ambient` and its explicit longhand twin (`policy: <resolved-name>`) must elaborate to
//! the **identical** L0 — hence the **identical content hash** (RFC-0001 §4.6) — "mirroring
//! `tests/ambient.rs`'s existing methodology" (DN-142 §3.3, verbatim). This is the W-B exit
//! criterion CI golden (`PROGRAM-HANDOFF-DESIGN-STEER-2026-07-17.md` §5 W-B row).
//!
//! Also tests the DN-142 §3.1 **rejected-vocabulary** hard errors (`policy: _`/`auto`/`default`,
//! each naming `ambient` as the ratified spelling) and the DN-142 §3.2 **never-silent unresolved**
//! refusal ("no ambient policy declared for this pair in scope").

use mycelium_core::ContentHash;
use mycelium_l1::{check_nodule, elaborate, parse};

/// Elaborate `src`'s `main` to L0 and return its content hash — the identity the DN-142 §3.3
/// conformance law preserves. Mirrors `tests/ambient.rs::elaborated_hash` verbatim.
fn elaborated_hash(src: &str) -> ContentHash {
    let env = check_nodule(&parse(src).unwrap_or_else(|e| panic!("parse `{src}`: {e}")))
        .unwrap_or_else(|e| panic!("check `{src}`: {e}"));
    let node = elaborate(&env, "main").unwrap_or_else(|e| panic!("elaborate `{src}`: {e}"));
    node.content_hash()
}

/// `(ambient-policy program, explicit longhand twin)` — both must elaborate to the identical L0
/// (DN-142 §3.3). Every pair swaps `Binary ↔ Ternary` (the only RFC-0002 §5 pair the reference
/// interpreter's `BinaryTernarySwapEngine` covers — a Dense-target swap is *always* an explicit
/// elaboration `Residual` regardless of policy spelling, DN-52 FLAG-1, so it cannot appear in an
/// `elaborate`-based golden; the Dense/catalog resolution path is covered instead by
/// `dense_swap_ambient_resolves_the_catalog_default_even_though_elaboration_is_staged` below, at
/// the `check_nodule` level).
fn pairs() -> Vec<(&'static str, &'static str)> {
    vec![
        // A nodule-declared ambient policy (`default policy rt;`) — resolves `declared@nodule`.
        (
            "nodule d;\ndefault policy rt;\nfn main() => Ternary{6} = \
             swap(0b1011_0010, to: Ternary{6}, policy: ambient);",
            "nodule d;\nfn main() => Ternary{6} = swap(0b1011_0010, to: Ternary{6}, policy: rt);",
        ),
        // The reverse pair direction (Ternary → Binary), same nodule declaration.
        (
            "nodule d;\ndefault policy rt;\nfn main() => Binary{8} = \
             swap(0t00+0-+, to: Binary{8}, policy: ambient);",
            "nodule d;\nfn main() => Binary{8} = swap(0t00+0-+, to: Binary{8}, policy: rt);",
        ),
        // No nodule declaration at all — falls through to the `std.swap.policy` catalog's
        // canonical default for Binary ↔ Ternary (`rt`), origin `catalog`.
        (
            "nodule d;\nfn main() => Ternary{6} = swap(0b1011_0010, to: Ternary{6}, policy: ambient);",
            "nodule d;\nfn main() => Ternary{6} = swap(0b1011_0010, to: Ternary{6}, policy: rt);",
        ),
        // A nodule declaration naming a *different* policy than the catalog default — the
        // declaration must win (most-specific-wins), never the catalog.
        (
            "nodule d;\ndefault policy custom_swap;\nfn main() => Ternary{6} = \
             swap(0b1011_0010, to: Ternary{6}, policy: ambient);",
            "nodule d;\nfn main() => Ternary{6} = \
             swap(0b1011_0010, to: Ternary{6}, policy: custom_swap);",
        ),
        // Combined with the RFC-0012 paradigm ambient (both ambients active at once — orthogonal
        // mechanisms, DN-142 §3 names `policy: ambient` the third instance of the same mechanism).
        (
            "nodule d;\ndefault paradigm Binary;\ndefault policy rt;\n\
             fn main() => Ternary{6} = swap(0b1011_0010, to: Ternary{6}, policy: ambient);",
            "nodule d;\nfn main() => Ternary{6} = swap(0b1011_0010, to: Ternary{6}, policy: rt);",
        ),
    ]
}

#[test]
fn ambient_policy_and_longhand_twins_elaborate_to_the_identical_l0() {
    for (i, (ambient, longhand)) in pairs().iter().enumerate() {
        assert_eq!(
            elaborated_hash(ambient),
            elaborated_hash(longhand),
            "pair #{i}: the `policy: ambient` program and its longhand twin must share a content \
             hash (DN-142 §3.3)\n  ambient:  {ambient}\n  longhand: {longhand}"
        );
    }
}

#[test]
fn ambient_policy_twins_observe_the_identical_value() {
    // Mirrors `tests/ambient.rs::the_twins_observe_the_identical_value`'s own caveat: the
    // Binary↔Ternary swap pair needs the cert engine, which the default reference interpreter
    // lacks — its identity engine refuses it equally on both twins, so a matched `Err` is still
    // agreement (both twins are byte-identical L0 by the test above; a divergent *outcome* would
    // mean the interpreter dispatches on the *policy name*, which it must not — RFC-0005 §3 records
    // the policy, it never branches evaluation on it).
    use mycelium_interp::Interpreter;
    let interp = Interpreter::default();
    for (ambient, longhand) in pairs() {
        let run = |src: &str| {
            let env = check_nodule(&parse(src).unwrap()).unwrap();
            let node = elaborate(&env, "main").unwrap();
            interp
                .eval(&node)
                .map(|v| (v.repr().clone(), v.payload().clone()))
        };
        match (run(ambient), run(longhand)) {
            (Ok(a), Ok(b)) => assert_eq!(
                a, b,
                "twins diverged at runtime:\n  {ambient}\n  {longhand}"
            ),
            (Err(_), Err(_)) => {}
            (a, b) => {
                panic!("twins disagree on runnability: {a:?} vs {b:?}\n  {ambient}\n  {longhand}")
            }
        }
    }
}

/// DN-142 §3.2's "catalog" origin still resolves for a **staged** (DN-52 Explicit-Residual) pair —
/// resolution happens in `check_swap`, strictly before elaboration, so a Dense-target swap's
/// `policy: ambient` resolves (and is checker-accepted) exactly as if it had been written longhand,
/// even though `elaborate` then refuses the whole construct with a `Residual` (unrelated to, and
/// unaffected by, the policy spelling — DN-52 FLAG-1 is a target-repr staging, not a policy concern).
#[test]
fn dense_swap_ambient_resolves_the_catalog_default_even_though_elaboration_is_staged() {
    // Dense F32 → BF16 (RFC-0002 §5 row 3) is the pair the catalog names a canonical default for
    // (`bf16_round`, DN-142 §3.2's "catalog" origin) — no `default policy` is declared in this
    // nodule, so resolution must fall through to that catalog default rather than erroring, even
    // though `elaborate` then separately refuses the whole construct with a `Residual` (DN-52
    // FLAG-1's Dense-target staging is unrelated to, and unaffected by, the policy spelling).
    let src = "nodule d;\nfn main(x: Dense{768, F32}) => Dense{768, BF16} @ Proven = \
               swap(x, to: Dense{768, BF16}, policy: ambient);";
    let checked = check_nodule(&parse(src).expect("parses"));
    assert!(
        checked.is_ok(),
        "policy: ambient must resolve via the catalog default (`bf16_round`) for Dense F32 → BF16, \
         even though elaboration itself is staged — got: {checked:?}"
    );
}

// --- DN-142 §3.1 rejected vocabulary (never-silent — G2) ------------------------------------------

fn parse_err(src: &str) -> String {
    parse(src)
        .expect_err("must be a parse-time refusal")
        .message
}

#[test]
fn policy_underscore_is_rejected_naming_ambient_as_the_ratified_spelling() {
    let msg = parse_err(
        "nodule d;\nfn main() => Ternary{6} = swap(0b1011_0010, to: Ternary{6}, policy: _);",
    );
    assert!(msg.contains("rejected vocabulary"), "got: {msg}");
    assert!(
        msg.contains("ambient"),
        "must name the ratified spelling — got: {msg}"
    );
}

#[test]
fn policy_auto_is_rejected_naming_ambient_as_the_ratified_spelling() {
    let msg = parse_err(
        "nodule d;\nfn main() => Ternary{6} = swap(0b1011_0010, to: Ternary{6}, policy: auto);",
    );
    assert!(msg.contains("rejected vocabulary"), "got: {msg}");
    assert!(
        msg.contains("ambient"),
        "must name the ratified spelling — got: {msg}"
    );
}

#[test]
fn policy_default_is_rejected_naming_ambient_as_the_ratified_spelling() {
    let msg = parse_err(
        "nodule d;\nfn main() => Ternary{6} = swap(0b1011_0010, to: Ternary{6}, policy: default);",
    );
    assert!(msg.contains("rejected vocabulary"), "got: {msg}");
    assert!(
        msg.contains("ambient"),
        "must name the ratified spelling — got: {msg}"
    );
}

#[test]
fn a_default_policy_declaration_also_rejects_the_forbidden_words() {
    // The same guarded production backs `default policy <name>;` (DN-142 §3.2's declaration
    // surface), so the rejected vocabulary is refused there too — one guarded production, not two
    // (parse.rs `parse_policy_ref` doc comment).
    let msg = parse_err("nodule d;\ndefault policy auto;\nfn main() => Binary{8} = 0b0000_0000;");
    assert!(msg.contains("rejected vocabulary"), "got: {msg}");
    assert!(
        msg.contains("ambient"),
        "must name the ratified spelling — got: {msg}"
    );
}

// --- DN-142 §3.2 unresolved ambient (never-silent, never a fallback — G2) -------------------------

fn check_err(src: &str) -> String {
    check_nodule(&parse(src).expect("parses"))
        .expect_err("must refuse")
        .message
}

#[test]
fn an_ambient_policy_with_no_declaration_and_no_catalog_default_is_a_hard_error() {
    // Binary → Dense{4, F32} is a legal *pair* (the DN-52 staged carve-out), but the catalog names
    // no canonical default for it (only Binary ↔ Ternary and Dense F32 → BF16 are seeded) — and no
    // `default policy` is declared in this nodule. Never a silent substitute.
    let msg = check_err(
        "nodule d;\nfn main() => Dense{4, F32} = swap(0b1011_0010, to: Dense{4, F32}, policy: ambient);",
    );
    assert!(
        msg.contains("no ambient policy declared for this pair in scope"),
        "got: {msg}"
    );
}
