//! In-crate white-box tests for [`crate::reveal`] — M-1051 Increment-1 (DN-38 §5/§8.3;
//! DN-110-8.2-hygiene-deepdive §5/§7 E3/§10 OQ-H3). Per the repo test-layout rule: a data-driven
//! fixture table over landed elaboratable sugars/programs, plus a hand-built-`Node` corpus for
//! [`alpha_eq`]/[`reelaborate`]/[`render_surface`] cases that don't need the elaborator. This is the
//! seed harness the DN-110-8.2-hygiene-deepdive §7 E1/E3 hygiene experiments (`hygiene_expr_sugar.rs`,
//! a separate future file) will extend once expression-position sugar rules land — not built here.

use crate::checkty::{check_nodule, Env};
use crate::elab::elaborate;
use crate::parse;
use crate::reveal::{alpha_eq, reelaborate, render_surface, reveal_l0, RenderError, RevealError};
use mycelium_core::{Alt, FloatWidth, Meta, Node, Payload, Provenance, Repr, ScalarKind, Value};

fn env(src: &str) -> Env {
    check_nodule(&parse(src).expect("parses")).expect("checks")
}

/// A `(name, source, entry)` fixture — landed elaboratable programs exercising a spread of `Node`
/// variants: `Let`/`Swap`/`Op` (let_swap), inlined calls (call_inlined), `Fix` self-recursion
/// (self_recursion_fix), `FixGroup` mutual recursion (mutual_recursion_fixgroup), and nested
/// `Match`/`Construct` (nested_match_construct).
struct Case {
    name: &'static str,
    src: &'static str,
    entry: &'static str,
}

const CASES: &[Case] = &[
    Case {
        name: "let_swap",
        src: "nodule d;\nfn main() => Ternary{6} =\n  let a = 0b1011_0010 in swap(not(a), to: Ternary{6}, policy: rt);",
        entry: "main",
    },
    Case {
        name: "call_inlined",
        src: "nodule d;\nfn flip(x: Binary{8}) => Binary{8} = not(x);\nfn main() => Binary{8} = flip(flip(0b1010_1010));",
        entry: "main",
    },
    Case {
        name: "self_recursion_fix",
        src: "nodule d;\ntype Nat = Z | S(Nat);\nfn drop_(n: Nat) => Nat = match n { Z => Z, S(m) => drop_(m) };\nfn main() => Nat = drop_(S(S(Z)));",
        entry: "main",
    },
    Case {
        name: "mutual_recursion_fixgroup",
        src: "nodule d;\ntype Nat = Z | S(Nat);\nfn ping(n: Nat) => Nat = match n { Z => Z, S(m) => pong(m) };\nfn pong(n: Nat) => Nat = match n { Z => Z, S(m) => ping(m) };\nfn main() => Nat = ping(S(Z));",
        entry: "main",
    },
    Case {
        name: "nested_match_construct",
        src: "nodule d;\ntype Nat = Z | S(Nat);\nfn pred2(n: Nat) => Nat = match n { Z => Z, S(Z) => Z, S(S(m)) => m };\nfn main() => Nat = pred2(S(S(S(Z))));",
        entry: "main",
    },
];

// ---------------------------------------------------------------------------------------------
// reveal_l0 — v0 fidelity (DN-38 §8.3): the shown term IS elaborate()'s own output.
// ---------------------------------------------------------------------------------------------

#[test]
fn reveal_l0_shows_the_real_elaborated_l0_term_for_every_fixture() {
    for c in CASES {
        let e = env(c.src);
        let shown =
            reveal_l0(&e, c.entry).unwrap_or_else(|err| panic!("{}: reveal_l0: {err}", c.name));
        let direct = elaborate(&e, c.entry).expect("elaborates directly too");
        assert_eq!(
            shown, direct,
            "{}: reveal_l0 must equal elaborate()'s own output (v0 = true L0-term view, DN-38 §8.3)",
            c.name
        );
    }
}

// ---------------------------------------------------------------------------------------------
// Closedness-preservation through reelaborate (NOT the E3 alpha-equivalence regression test —
// see the honest-scoping callout below and in the reveal.rs module doc). `reelaborate` returns
// `shown.clone()` on its success path (v0 has no lossy step to invert — the module doc's
// "reelaborate at v0" section), so composing it with `alpha_eq` here compares a term to a
// bit-identical clone of itself: this validly checks that `reveal_l0`'s output survives an
// independent closedness re-derivation with its structure intact, but it would ALSO pass with a
// broken `alpha_eq` (identical operands don't distinguish a correct comparator from a broken one).
// `alpha_eq` itself is unit-tested against genuinely differently-spelled alpha-variant pairs
// separately, below. The real DN-110-8.2-hygiene-deepdive §7 E3 (expand → reveal_l0 → reelaborate →
// alpha_eq over actual sugar-expansion `%`-freshened pairs) needs expression-position sugar rules
// that don't exist yet — tracked as the M-1055 follow-on, not built in this increment. Do not cite
// this test as E3 evidence (VR-5 — the claim must not silently cover more than what is checked).
// ---------------------------------------------------------------------------------------------

#[test]
fn reveal_l0_output_is_closed_and_survives_reelaboration() {
    for c in CASES {
        let e = env(c.src);
        let shown =
            reveal_l0(&e, c.entry).unwrap_or_else(|err| panic!("{}: reveal_l0: {err}", c.name));
        let round_tripped =
            reelaborate(&shown).unwrap_or_else(|err| panic!("{}: reelaborate: {err}", c.name));
        assert!(
            alpha_eq(&round_tripped, &shown),
            "{}: closedness-preservation must hold (reelaborate returns a clone once its own \
             independent closedness re-derivation succeeds — this is NOT an alpha_eq correctness \
             check, since the compared operands are a bit-identical clone pair; see the module doc)",
            c.name
        );
        // Reinforce, at the assertion site, exactly what this DOES check beyond alpha_eq: the
        // clone really is structurally identical (a stronger, more direct witness than alpha_eq
        // alone would give here, since alpha_eq degenerates to `==`-equivalent on identical trees).
        assert_eq!(
            round_tripped, shown,
            "{}: reelaborate's success-path clone must be structurally identical to the shown term",
            c.name
        );
    }
}

// ---------------------------------------------------------------------------------------------
// render_surface — covers the fixture corpus, never silently.
// ---------------------------------------------------------------------------------------------

#[test]
fn render_surface_covers_the_fixture_corpus_never_silently() {
    for c in CASES {
        let e = env(c.src);
        let shown = reveal_l0(&e, c.entry).expect("elaborates");
        let rendered = render_surface(&shown)
            .unwrap_or_else(|err| panic!("{}: render_surface: {err}", c.name));
        assert!(
            !rendered.text.is_empty(),
            "{}: rendered text must be non-empty",
            c.name
        );
    }
}

/// `let_swap`'s entry has no `%`-names or resolved refs of its own except the `Swap::policy`
/// content hash (a real one, resolved from the `rt` policy path at elaboration) — so its render is
/// expected to be labelled non-reparseable via the `#policy:` marker, honestly.
#[test]
fn render_surface_flags_a_resolved_swap_policy_non_reparseable() {
    let e = env(CASES[0].src);
    let shown = reveal_l0(&e, CASES[0].entry).expect("elaborates");
    let rendered = render_surface(&shown).expect("renders");
    assert!(rendered.text.contains("policy: #"));
    assert!(
        !rendered.reparseable,
        "a resolved content-hash policy has no surviving surface Path spelling"
    );
}

// ---------------------------------------------------------------------------------------------
// alpha_eq — hand-built Node fixtures (no elaborator needed to exercise the comparator itself).
// ---------------------------------------------------------------------------------------------

fn byte(bits: [bool; 8]) -> Value {
    Value::new(
        Repr::Binary { width: 8 },
        Payload::Bits(bits.to_vec()),
        Meta::exact(Provenance::Root),
    )
    .expect("well-formed byte")
}

#[test]
fn alpha_eq_true_for_a_renamed_binder() {
    let a = Node::Lam {
        param: "x".to_owned(),
        body: Box::new(Node::Var("x".to_owned())),
    };
    let b = Node::Lam {
        param: "y".to_owned(),
        body: Box::new(Node::Var("y".to_owned())),
    };
    assert!(alpha_eq(&a, &b));
    // `Node`'s own structural `PartialEq` is NOT alpha-aware — this is exactly the gap `alpha_eq`
    // exists to close (DN-110-8.2-hygiene-deepdive §6's "false half" finding, cited in the module
    // doc); assert both halves of that claim here so a future accidental alpha-canonicalization of
    // `==` doesn't silently make this test stop exercising anything.
    assert_ne!(
        a, b,
        "sanity: literal Node equality is spelling-sensitive, unlike alpha_eq"
    );
}

#[test]
fn alpha_eq_false_for_a_structurally_different_term() {
    let a = Node::Lam {
        param: "x".to_owned(),
        body: Box::new(Node::Var("x".to_owned())),
    };
    let b = Node::Lam {
        param: "x".to_owned(),
        body: Box::new(Node::Const(byte([false; 8]))),
    };
    assert!(!alpha_eq(&a, &b));
}

#[test]
fn alpha_eq_respects_shadowing_not_just_spelling() {
    let inner_byte = || {
        Node::Const(byte([
            true, false, false, false, false, false, false, false,
        ]))
    };
    // let x = <b> in let x = <b> in x      -- refers to the INNER x
    let a = Node::Let {
        id: "x".to_owned(),
        bound: Box::new(inner_byte()),
        body: Box::new(Node::Let {
            id: "x".to_owned(),
            bound: Box::new(inner_byte()),
            body: Box::new(Node::Var("x".to_owned())),
        }),
    };
    // let a = <b> in let b = <b> in b      -- also refers to the INNER binding, different spellings
    let b = Node::Let {
        id: "a".to_owned(),
        bound: Box::new(inner_byte()),
        body: Box::new(Node::Let {
            id: "b".to_owned(),
            bound: Box::new(inner_byte()),
            body: Box::new(Node::Var("b".to_owned())),
        }),
    };
    assert!(
        alpha_eq(&a, &b),
        "both refer to the innermost binder — alpha-equivalent"
    );

    // let x = <b> in let x2 = <b> in x     -- refers to the OUTER binder now: NOT alpha_eq to `a`.
    let c = Node::Let {
        id: "x".to_owned(),
        bound: Box::new(inner_byte()),
        body: Box::new(Node::Let {
            id: "x2".to_owned(),
            bound: Box::new(inner_byte()),
            body: Box::new(Node::Var("x".to_owned())),
        }),
    };
    assert!(
        !alpha_eq(&a, &c),
        "referring to the outer vs. inner binder is a real semantic difference, not a renaming"
    );
}

#[test]
fn alpha_eq_free_variables_compare_by_name() {
    let a = Node::Var("free1".to_owned());
    let b = Node::Var("free1".to_owned());
    let c = Node::Var("free2".to_owned());
    assert!(alpha_eq(&a, &b));
    assert!(!alpha_eq(&a, &c));
}

// --- Fix / FixGroup / Match coverage (adversarial-review fix, coverage gap) ---------------------
//
// `alpha_eq_at`/`collect_free_vars` are two hand-maintained parallel walks over the same five
// binder-introducing `Node` forms (`Let`, `Lam`, `Fix`, `FixGroup`, `Alt::Ctor`) — a maintainability
// watch-item: a future sixth binder form must update both walks, and nothing currently enforces
// that mechanically (no shared "for each binder form" abstraction exists to fold them through).
// Until then, these forms are exercised directly here rather than only indirectly through the
// fixture corpus (which never actually reaches `alpha_eq_at`'s inequality branches — see the
// closedness-preservation test above).

/// A 2-field constructor `CtorRef` for [`Node::Construct`]/[`Alt::Ctor`] fixtures (mirrors
/// `mycelium-core/src/node.rs`'s own test helper pattern) — arity 2 so a binder-*position* (not
/// just binder-*spelling*) distinction is actually exercisable.
fn ctor_ref_pair() -> mycelium_core::CtorRef {
    use mycelium_core::{CtorSpec, DataRegistry, DeclSpec, FieldSpec};
    use std::collections::BTreeMap;
    let mut m = BTreeMap::new();
    m.insert(
        "Pair".to_owned(),
        DeclSpec {
            ctors: vec![CtorSpec {
                fields: vec![
                    FieldSpec::Repr(Repr::Binary { width: 8 }),
                    FieldSpec::Repr(Repr::Binary { width: 8 }),
                ],
            }],
        },
    );
    let reg = DataRegistry::build(&m).expect("registry builds");
    reg.ctor_ref("Pair", 0).expect("Pair#0 exists")
}

#[test]
fn alpha_eq_fix_renamed_binder() {
    let a = Node::Fix {
        name: "f".to_owned(),
        body: Box::new(Node::Var("f".to_owned())),
    };
    let b = Node::Fix {
        name: "g".to_owned(),
        body: Box::new(Node::Var("g".to_owned())),
    };
    assert!(
        alpha_eq(&a, &b),
        "a consistently-renamed self-reference is alpha_eq"
    );
}

#[test]
fn alpha_eq_fix_vs_free_same_spelling_false() {
    // Both sides are `Fix` (same node shape), so the comparison reaches the `Var` arm rather than
    // short-circuiting on a variant mismatch. `a`'s body "f" is bound (matches the Fix's own name
    // "f"); `b`'s body still spells "f" but `b`'s Fix binds "g" — so in `b`, "f" is free. Same
    // spelling, opposite bound/free status: must be unequal.
    let a = Node::Fix {
        name: "f".to_owned(),
        body: Box::new(Node::Var("f".to_owned())),
    };
    let b = Node::Fix {
        name: "g".to_owned(),
        body: Box::new(Node::Var("f".to_owned())),
    };
    assert!(
        !alpha_eq(&a, &b),
        "a bound occurrence must not be alpha_eq to a free occurrence of the same spelling"
    );
}

#[test]
fn alpha_eq_fixgroup_renamed_binders_mutual() {
    // f/g <-> p/q, a consistent bijective rename preserving relative position.
    let a = Node::FixGroup {
        defs: vec![
            ("f".to_owned(), Box::new(Node::Var("g".to_owned()))),
            ("g".to_owned(), Box::new(Node::Var("f".to_owned()))),
        ],
        body: Box::new(Node::Var("f".to_owned())),
    };
    let b = Node::FixGroup {
        defs: vec![
            ("p".to_owned(), Box::new(Node::Var("q".to_owned()))),
            ("q".to_owned(), Box::new(Node::Var("p".to_owned()))),
        ],
        body: Box::new(Node::Var("p".to_owned())),
    };
    assert!(
        alpha_eq(&a, &b),
        "a consistent bijective rename of a mutual-recursion group is alpha_eq"
    );
}

#[test]
fn alpha_eq_fixgroup_mismatched_arity_is_false_not_panic() {
    let one_def = Node::FixGroup {
        defs: vec![("f".to_owned(), Box::new(Node::Var("f".to_owned())))],
        body: Box::new(Node::Var("f".to_owned())),
    };
    let two_defs = Node::FixGroup {
        defs: vec![
            ("f".to_owned(), Box::new(Node::Var("g".to_owned()))),
            ("g".to_owned(), Box::new(Node::Var("f".to_owned()))),
        ],
        body: Box::new(Node::Var("f".to_owned())),
    };
    // Both directions — the early `d1.len() != d2.len()` check must fire symmetrically, never
    // index out of bounds (no panic in either direction).
    assert!(!alpha_eq(&one_def, &two_defs));
    assert!(!alpha_eq(&two_defs, &one_def));
}

/// Build a `match <scrutinee> { <ctor>(binders...) => <body_var> }` fixture — the shared shape
/// [`alpha_eq_match_ctor_renamed_binders`]/[`alpha_eq_ctor_binder_vs_free_same_spelling_false`]
/// vary only the binder spellings / body reference over.
fn match_with_ctor_alt(binders: [&str; 2], body_var: &str) -> Node {
    Node::Match {
        scrutinee: Box::new(Node::Var("scrutinee".to_owned())),
        alts: vec![Alt::Ctor {
            ctor: ctor_ref_pair(),
            binders: binders.iter().map(|s| (*s).to_owned()).collect(),
            body: Node::Var(body_var.to_owned()),
        }],
        default: None,
    }
}

#[test]
fn alpha_eq_match_ctor_renamed_binders() {
    let a = match_with_ctor_alt(["x", "y"], "x"); // refers to binder position 0
    let same_position = match_with_ctor_alt(["a", "b"], "a"); // renamed, still position 0
    let different_position = match_with_ctor_alt(["a", "b"], "b"); // renamed, now position 1
    assert!(
        alpha_eq(&a, &same_position),
        "a consistent binder rename at the same relative position is alpha_eq"
    );
    assert!(
        !alpha_eq(&a, &different_position),
        "referring to a different relative binder position is a real semantic difference"
    );
}

#[test]
fn alpha_eq_ctor_binder_vs_free_same_spelling_false() {
    // `a`'s body "x" is bound (binder position 0 is "x"); `b`'s binders are ["z","y"] — "x" no
    // longer appears among them, so `b`'s body "x" is free. Same spelling, opposite bound/free
    // status: must be unequal (the `Alt::Ctor` analogue of `alpha_eq_fix_vs_free_same_spelling_false`).
    let a = match_with_ctor_alt(["x", "y"], "x");
    let b = match_with_ctor_alt(["z", "y"], "x");
    assert!(
        !alpha_eq(&a, &b),
        "a bound ctor-binder occurrence must not be alpha_eq to a free occurrence of the same spelling"
    );
}

// ---------------------------------------------------------------------------------------------
// reelaborate — never-silent refusal on a not-closed shown term; accepts a closed one.
// ---------------------------------------------------------------------------------------------

#[test]
fn reelaborate_refuses_a_not_closed_shown_term_never_silently() {
    let open = Node::Var("dangling".to_owned());
    let err = reelaborate(&open).expect_err("a free-variable Node must be refused");
    assert_eq!(err, RevealError::NotClosed(vec!["dangling".to_owned()]));
}

#[test]
fn reelaborate_accepts_a_closed_shown_term() {
    let closed = Node::Lam {
        param: "x".to_owned(),
        body: Box::new(Node::Var("x".to_owned())),
    };
    let round = reelaborate(&closed).expect("closed term round-trips");
    assert_eq!(round, closed);
}

// ---------------------------------------------------------------------------------------------
// render_surface — OQ-H3 option (a): raw %-names, honestly labelled non-reparseable.
// ---------------------------------------------------------------------------------------------

#[test]
fn render_surface_labels_a_percent_hygienic_name_non_reparseable() {
    let node = Node::Var("t%0".to_owned());
    let rendered = render_surface(&node).expect("renders raw, never munged");
    assert_eq!(rendered.text, "t%0", "OQ-H3 (a): shown raw, never hidden");
    assert!(
        !rendered.reparseable,
        "OQ-H3 (a): a raw %-name must be labelled non-reparseable"
    );
}

#[test]
fn render_surface_reparseable_true_for_a_plain_closed_term() {
    let node = Node::Lam {
        param: "x".to_owned(),
        body: Box::new(Node::Var("x".to_owned())),
    };
    let rendered = render_surface(&node).expect("renders");
    assert!(
        rendered.reparseable,
        "no %/# marker present — mechanically reparseable"
    );
}

// ---------------------------------------------------------------------------------------------
// render_surface — never-silent refusal for Value payloads with no surface literal grammar.
// ---------------------------------------------------------------------------------------------

#[test]
fn render_surface_refuses_a_dense_const_never_silently() {
    let dense = Value::new(
        Repr::Dense {
            dim: 2,
            dtype: ScalarKind::F32,
        },
        Payload::Scalars(vec![1.0, 2.0]),
        Meta::exact(Provenance::Root),
    )
    .expect("well-formed dense value");
    let err = render_surface(&Node::Const(dense)).expect_err("no Dense literal grammar exists");
    assert!(matches!(
        err,
        RenderError::Unrenderable {
            node: "Const(Dense)",
            ..
        }
    ));
}

#[test]
fn render_surface_refuses_a_non_finite_float_const_never_silently() {
    let inf = Value::new(
        Repr::Float {
            width: FloatWidth::F64,
        },
        Payload::Float(f64::INFINITY),
        Meta::exact(Provenance::Root),
    )
    .expect("Value::new does not reject a non-finite float payload (only NaN is canonicalized)");
    let err = render_surface(&Node::Const(inf)).expect_err("no non-finite FloatLit grammar exists");
    assert!(matches!(
        err,
        RenderError::Unrenderable {
            node: "Const(NaN/±inf Float)",
            ..
        }
    ));
}

#[test]
fn render_surface_finite_float_renders_with_a_decimal_point() {
    let f = Value::new(
        Repr::Float {
            width: FloatWidth::F64,
        },
        Payload::Float(1.5),
        Meta::exact(Provenance::Root),
    )
    .expect("well-formed finite float");
    let rendered = render_surface(&Node::Const(f)).expect("renders");
    assert_eq!(rendered.text, "1.5");
    assert!(rendered.reparseable);
}
