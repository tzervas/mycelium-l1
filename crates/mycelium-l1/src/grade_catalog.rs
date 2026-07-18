//! **The structural grade catalog** (DN-141 R3 "matrix mint"; RFC-0018 §4.3) — a committed,
//! queryable table naming the grade rule each structural AST form is checked under, replacing "ad
//! hoc" (implicit, scattered) annotation with **data** the checker's own rules can be looked up
//! against (mirrors [`crate::legal_pair::LEGAL_PAIR_TABLE`]'s pattern: the rule text lives in one
//! place, as a `const`, not only in prose comments on match arms).
//!
//! # Scope (verify-first — mitigation #14; residual-gap disclosure)
//!
//! RFC-0018 names **two** grade-table deliverables, and only one is this module's job:
//! - **R18-Q3 (per-prim signature table)** — a *precision* upgrade for individual kernel prims
//!   (`bin.add`, `trit.xor`, …), explicitly named in RFC-0018 §8 as **"a separate tracked
//!   deliverable... the conservative G-Op default is sound meanwhile."** That per-prim table does
//!   **not** exist yet and is **out of this leaf's scope** — building it is a materially larger
//!   effort than a W-C residual-gap item, and RFC-0018 itself defers it. This module does not
//!   invent per-prim precision the RFC declines to require yet (VR-5: no unbounded upgrade).
//! - **R3 (the structural-form catalog, DN-141 §4)** — **this module's actual job**: the grading
//!   rule for each *structural* AST form (`let`, `if`, `match`, `swap`, application, …) is already
//!   fully implemented in [`crate::grade`], but only as Rust match arms + doc-comment prose — an
//!   author (or the overclaim guard, or a future `grade_annotation`/`grade_meet` EXPLAIN emitter,
//!   W-C X5) has no single, queryable place to ask "what rule governs this form, and what does
//!   RFC-0018 call it?" [`STRUCTURAL_GRADE_CATALOG`] is that place — committed data, not inferred
//!   from control flow.
//!
//! # Honesty (`Declared` — a naming/documentation layer, not new semantics)
//! This catalog **describes** [`crate::grade::Gx::grade`]'s existing, already-tested behavior; it
//! does not change what the checker accepts or refuses (a documentation/data addition — zero
//! behavioral risk to the pinned DN-80 reject-ledger counts in `grade.rs`). [`tests`] (the in-crate
//! `src/tests/grade_catalog.rs` module) is the completeness guard: every row here names a rule
//! [`crate::grade::Gx::grade`] actually implements, and — read the other way — every structural
//! form that match implements has a named row (a closed-enum-style "no orphan rule" check, DN-80's
//! own pattern applied to this catalog rather than to a reject enum).

/// One row of the structural grade catalog: the RFC-0018 §4.3 rule name, the construct it governs,
/// a one-line restatement of the rule, and the RFC section it cites. `rule_id` is the canonical,
/// short, EXPLAIN-friendly identifier (e.g. `"G-Swap"`) — the same vocabulary RFC-0018 §4.3's own
/// prose uses, so a `basis_ref` naming a rule id (W-C X5's `meet_boundary`/`grade_annotation`
/// first-fault packages) is directly greppable back to this table and to the RFC section.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GradeRule {
    /// The canonical RFC-0018 §4.3 rule id (`"G-Const"`, `"G-Swap"`, …).
    pub rule_id: &'static str,
    /// The surface construct(s) this rule governs (`"a literal"`, `"swap(...)"`, …).
    pub construct: &'static str,
    /// A one-line restatement of the rule (not a full derivation — the normative text stays
    /// RFC-0018 §4.3 / `crate::grade`'s own doc comments; this is the EXPLAIN-length summary).
    pub summary: &'static str,
    /// The RFC-0018 section this rule is drawn from.
    pub citation: &'static str,
}

/// The committed structural grade catalog (DN-141 R3) — one row per structural form
/// [`crate::grade::Gx::grade`] implements, in the same order that match's arms appear (source
/// order, for easy side-by-side review against `grade.rs`). See the module doc for scope (this is
/// the *structural*-form catalog, not the deferred R18-Q3 per-prim table).
pub const STRUCTURAL_GRADE_CATALOG: &[GradeRule] = &[
    GradeRule {
        rule_id: "G-Const",
        construct: "a literal (`Lit`, incl. a list literal's meet-of-elements case)",
        summary: "a written constant is Exact by construction; a list literal carries the meet of \
                   its elements",
        citation: "RFC-0018 §4.3 G-Const / G-Con",
    },
    GradeRule {
        rule_id: "G-Var",
        construct: "a variable reference (`Path`, single segment)",
        summary: "a variable carries the grade it was bound at in scope; an unbound single-segment \
                   name is a nullary constructor/constant, graded Exact",
        citation: "RFC-0018 §4.3 G-Var",
    },
    GradeRule {
        rule_id: "G-Let",
        construct: "`let name (: ty)? = bound in body`",
        summary: "the bound value's grade is weakened to any written ascription (G-Weaken), then \
                   the let's own grade is the meet of the (possibly weakened) binding and the body",
        citation: "RFC-0018 §4.3 G-Let",
    },
    GradeRule {
        rule_id: "G-Match/A",
        construct: "`if`/`match` (Design A)",
        summary: "the scrutinee/condition grade does NOT degrade the result (no `pc` taint); a \
                   destructured field binder inherits the scrutinee's grade (data provenance); the \
                   result is the meet of the arm/branch bodies",
        citation: "RFC-0018 §4.5 G-Match/A (Design A, R18-Q1)",
    },
    GradeRule {
        rule_id: "G-For",
        construct: "`for x in xs, acc = init => body`",
        summary: "the accumulator is graded at the conservative fixpoint bottom (Declared) inside \
                   the body (never the initial grade, which a later iteration may not preserve); the \
                   fold's result is the meet of the initial accumulator, the spine, and the body",
        citation: "RFC-0018 §4.3 (fold composition; stage-1a conservative treatment, RFC-0041 W1)",
    },
    GradeRule {
        rule_id: "G-Swap",
        construct: "`swap(value, to: T, policy: p)`",
        summary: "the endorsement point: a swap's certificate reference is trusted at the type \
                   level and grades Exact, satisfying any demand; certificate validity is a \
                   separate, never-silent elaboration/runtime obligation (RFC-0002)",
        citation: "RFC-0018 §4.3 G-Swap (R18-Q4)",
    },
    GradeRule {
        rule_id: "G-Wild",
        construct: "`wild { body }`",
        summary: "the audited FFI floor: opaque and untrusted, graded Declared (the least-trusted \
                   grade) regardless of its body — the body is not recursively graded",
        citation: "RFC-0018 §4.3 (LR-9/S6 audited-escape floor)",
    },
    GradeRule {
        rule_id: "G-App/G-Con/G-Op",
        construct: "an application (`App`) — a known user fn call, or a constructor/prim/trait-\
                     method call with no graded signature",
        summary: "a call to a known fn checks each argument against its parameter's demand and \
                   yields the callee's declared return grade (G-App); any other application head \
                   (constructor/prim/unqualified trait method) takes the conservative meet of its \
                   argument grades (G-Con/G-Op) — the R18-Q3-deferred per-prim table would refine \
                   this case; the meet default is sound meanwhile (RFC-0018 §8)",
        citation: "RFC-0018 §4.3 G-App / §4.6 G-Con / G-Op; §8 R18-Q3",
    },
    GradeRule {
        rule_id: "G-Sub / G-Weaken",
        construct: "an `@ g` ascription (`let`, value ascription, function return)",
        summary: "an ascription is a demand: the inferred grade must be at least as trusted (⊒) as \
                   the written `g`, and the ascribed expression then carries `g` — an ascription may \
                   only WEAKEN, never upgrade a grade past what the checker verified",
        citation: "RFC-0018 §4.3 G-Weaken / G-Sub (VR-5)",
    },
    GradeRule {
        rule_id: "G-Fuse",
        construct: "`fuse(a, b)`",
        summary: "the grade is the meet of both operands' grades, matching how App/G-Op grades a \
                   binary operation",
        citation: "DN-58 §A/§A.5 (M-667)",
    },
    GradeRule {
        rule_id: "G-Reclaim",
        construct: "`reclaim(policy) { body }`",
        summary: "the result's grade is the body's grade; the policy expression is graded (to \
                   surface any violation) but does not itself affect the result grade",
        citation: "DN-58 §B (M-667)",
    },
    GradeRule {
        rule_id: "G-Consume/G-Try",
        construct: "`consume expr` / `expr?`",
        summary: "both are grade-transparent: the result carries exactly the operand's grade — \
                   neither upgrades nor downgrades the operand's own attested basis",
        citation: "M-664 (`consume`); DN-102 §2/§3 (`?`, M-1025)",
    },
    GradeRule {
        rule_id: "G-Lambda",
        construct: "`lambda ...`",
        summary: "a closure is a Declared-grade construct — the construction itself attests no more \
                   than Declared, independent of the lowering's own (separately-tracked) fidelity",
        citation: "RFC-0024 §4A (M-704)",
    },
    GradeRule {
        rule_id: "G-Wrapping",
        construct: "`wrapping { expr }`",
        summary: "attests Declared — the enclosed modular-arithmetic opt-out is the author's \
                   explicit, never a fabricated stronger claim",
        citation: "RFC-0034 §10/§10.1 (CU-5)",
    },
];

/// Look up the [`GradeRule`] row by its `rule_id` (e.g. `"G-Swap"`), for an EXPLAIN caller that
/// already knows which rule fired (W-C X5's `grade_annotation`/`grade_meet` first-fault packages
/// can cite `row.citation` as their `basis_ref`). `None` if `rule_id` is not one of this catalog's
/// rows — never a fabricated default (G2).
#[must_use]
pub fn rule(rule_id: &str) -> Option<&'static GradeRule> {
    STRUCTURAL_GRADE_CATALOG
        .iter()
        .find(|r| r.rule_id == rule_id)
}
