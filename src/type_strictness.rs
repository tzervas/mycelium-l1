//! DN-126 — the **type-strictness axis**: a third axis, orthogonal to ADR-032/RFC-0034's
//! certification-depth (`CertMode::Fast`/`Certified`) and RFC-0018's guarantee-grade lattice
//! (`Exact ⊐ Proven ⊐ Empirical ⊐ Declared`). Neither existing axis governs whether the checker's
//! *type-level* refusals gate execution — today they unconditionally do (DN-126 §2.2). This module
//! is the "demotion switch" DN-126 §3/§5 Alt A ratifies: [`TypeStrictness::Strict`] (the unchanged
//! default — every existing behavior, byte-identical) and [`TypeStrictness::Loose`], which demotes a
//! **type-level** [`CheckError`](crate::checkty::CheckError) at specific, narrowly-classified sites
//! (`crate::checkty`'s `Cx::mismatch_or_flag`) to a [`TypeFlag`] and lets the checker continue with
//! the value's **actual** (inferred) type instead of refusing — never the declared/expected one, so
//! nothing is silently promoted to match a violated annotation (VR-5).
//!
//! **Scope of this landing (M-1077; honest, not the full DN-126 §3 model).** DN-126 §3.1 describes
//! per-*expression* demotion across the whole bidirectional checker; a full enumeration of which of
//! `checkty`'s ~30+ `CheckError` call sites are type-level-demotable vs runnable-floor-hard is a
//! large classification pass DN-126 §9.4 itself flags as **future work**, not a design hole. This
//! landing demotes exactly the **two** sites verified safe by inspection (both compare two already
//! *fully elaborated* concrete types — no AmbientInt/generic-hole resolution is needed, so no new
//! runtime-default policy is invented): an explicit type **ascription** (`e : T`, DN-126 §3.1's
//! textbook "Hinted" case) and a function **body vs. its declared return type**. Every other
//! `CheckError` site — unresolved name/ctor/type, arity mismatch, parse error, `wild`/FFI-gate
//! violation, trait-impl signature conformance, generic-instantiation ambiguity, unresolved
//! (`AmbientInt`) width — stays **hard in both modes** (the conservative default: untouched code
//! paths refuse exactly as they do today, so the runnable floor DN-126 §3.3 requires can never be
//! silently weakened by omission). See `checkty::mismatch_or_flag`'s call sites for the exact list.
//!
//! **The runtime is never perturbed (DN-126 §6.3/§9.2, ADR-003).** The evaluator ([`crate::eval`])
//! is repr-dynamic — it never consults a static [`Ty`](crate::checkty::Ty) to execute, only names/
//! arity (already-checked, unaffected by this axis). Demoting a mismatch changes only *what the
//! checker returns as the value's type* for further checking; it writes no new AST node and touches
//! no evaluator code path. A [`TypeFlagKind::Ascription`] flag is doubly inert at runtime:
//! `Expr::Ascribe`'s only evaluator effect is an optional post-hoc guarantee-index assertion
//! (`eval.rs`'s `Frame::AscribePost`), unrelated to the ascribed *type*, which the evaluator never
//! reads at all.

use std::fmt;

use crate::checkty::Ty;

/// The type-strictness mode (DN-126 §3). [`Strict`](TypeStrictness::Strict) is the default and is
/// **byte-identical to today's checker**: `TypeStrictness::default()` produces zero demotions, zero
/// [`TypeFlag`]s, ever — the existing `check_nodule`/`check_nodule_matured` entry points hardcode it,
/// so their behavior is unchanged by this axis's introduction (VR-5: nothing is upgraded or weakened
/// without an explicit, mode-level, never-silent choice — DN-126 §6 item 1).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum TypeStrictness {
    /// Every type-level refusal is a hard [`CheckError`](crate::checkty::CheckError), exactly as
    /// today. Required, unconditionally, for the `certified`-eligible / AOT-compile path
    /// (DN-126 §3.2 — "strict typing gates compile, unconditionally, exactly as today").
    #[default]
    Strict,
    /// A **type-level** refusal at a demotable site (see the module doc for the exact, currently
    /// narrow set) is recorded as a [`TypeFlag`] instead of refusing; checking continues with the
    /// value's *actual* type. The **runnable floor** (DN-126 §3.3 — unresolved name, arity, parse,
    /// `wild`/FFI-gate) is untouched: those sites never route through the demotion mechanism, so
    /// they refuse in `Loose` exactly as in `Strict` (the program would be un-runnable, not merely
    /// untyped — a `Loose` accept must never silently promise more than the runtime can honor).
    Loose,
}

impl TypeStrictness {
    /// `true` iff this mode demotes rather than refuses at a demotable site.
    #[must_use]
    pub fn is_loose(self) -> bool {
        matches!(self, TypeStrictness::Loose)
    }
}

impl fmt::Display for TypeStrictness {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeStrictness::Strict => write!(f, "strict"),
            TypeStrictness::Loose => write!(f, "loose"),
        }
    }
}

/// Which demotable class a [`TypeFlag`] came from — the (currently narrow, honestly-scoped) enum
/// twin of the site classification the module doc describes. Extending demotion to a further site
/// (DN-126 §9.4's residual enumeration) adds a variant here, never silently reuses an existing one
/// (a flag's `kind` must always name its real originating site class — G2).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeFlagKind {
    /// An explicit `e : T` ascription whose checked type disagreed with `T` (DN-126 §3.1's
    /// "Hinted" tier — a user-written annotation is a *hint*, not a *gate*, in loose mode).
    Ascription,
    /// A function (or impl-method) body's checked type disagreed with its declared return type.
    ReturnType,
}

impl fmt::Display for TypeFlagKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeFlagKind::Ascription => write!(f, "ascription"),
            TypeFlagKind::ReturnType => write!(f, "return-type"),
        }
    }
}

/// The checker's **principal-resolution verdict** for a demoted hole (DN-126 §4.1 — the soundness
/// spine). Every demotion site in this landing (see the module doc) only ever produces
/// [`Principal`](Resolution::Principal) — a value flowing through a type-level mismatch already had
/// a single, definite, fully-elaborated checked type on both sides (that is exactly why the site was
/// judged safe to demote: no AmbientInt/generic hole, no ambiguity). [`NonPrincipal`](Resolution::NonPrincipal)
/// models the DN-126 §9.1 adversarial case (a duck-typed value with **no** whole-program static
/// type, or more than one *observationally distinct* candidate) that a **future** wider demotion
/// (the unresolved-width / generic-instantiation classes DN-126 §9.4 flags as residual) could
/// produce; [`strictify`] below handles it correctly today even though no live call site constructs
/// one yet — the mechanism, not just today's narrow feed, is what must be sound.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Resolution {
    /// A unique inferred type — the *only* thing mechanical strictification may ever write down.
    Principal(Ty),
    /// No type satisfies every constraint (`candidates` empty — bottom, `Cx::infer` found nothing),
    /// or more than one *distinct* type does (`candidates.len() > 1` — ambiguous). Either way this
    /// is *definitionally* the surfaced residual (DN-126 §4.1): never guessed, never promoted.
    NonPrincipal { candidates: Vec<Ty> },
}

impl Resolution {
    /// The principal type, if this resolution has one. `None` for [`NonPrincipal`](Resolution::NonPrincipal)
    /// (⊥ or ambiguous) — the caller must surface, never guess a candidate (G2/VR-5).
    #[must_use]
    pub fn principal(&self) -> Option<&Ty> {
        match self {
            Resolution::Principal(ty) => Some(ty),
            Resolution::NonPrincipal { .. } => None,
        }
    }
}

/// A demoted type-level [`CheckError`](crate::checkty::CheckError) — a DN-04/RFC-0013-shaped
/// structured diagnostic (site + reason), additionally carrying what mechanical strictification
/// (DN-126 §4) needs: the declared/expected type, and the checker's own [`Resolution`] for the
/// value's actual type. Guarantee: `Declared` (VR-5) until a strict re-check of the materialized
/// program passes — this landing does not yet implement that re-check (DN-126 §4 step 4; flagged
/// residual, see `type_strictness` module doc / the M-1077 report).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeFlag {
    /// Which function (or item) the flag is in (mirrors [`CheckError::site`](crate::checkty::CheckError::site)).
    pub site: String,
    /// Which demotable class produced this flag.
    pub kind: TypeFlagKind,
    /// The declared/expected type strict mode demanded.
    pub declared: Ty,
    /// The checker's resolution for the value's actual type (DN-126 §4.1).
    pub resolution: Resolution,
    /// The human-readable reason (identical wording to what the `Strict`-mode `CheckError` would
    /// have carried at this site — never a different, softer message for the same failure).
    pub message: String,
}

impl fmt::Display for TypeFlag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[loose:{}] flagged in `{}`: {}",
            self.kind, self.site, self.message
        )
    }
}

/// The result of DN-126 §4's mechanical-strictification classification pass (steps 1-3: run strict,
/// collect the soft-flag set, split it by principality). **`materialized`** is exactly the set a
/// caller may mechanically write down as an annotation (DN-126 §4 step 2(a)) — each entry a
/// `(site, principal type)` pair. **`residual`** is exactly the set that must be surfaced to a human
/// via a DN-04/RFC-0013 diagnostic and **never** mechanically resolved (DN-126 §4.1's principality
/// invariant — the soundness spine: this function never promotes a [`NonPrincipal`](Resolution::NonPrincipal)
/// flag into `materialized`, by construction, not by a heuristic).
///
/// **Not yet implemented (flagged residual, DN-126 §4 step 4):** actually rewriting the checked
/// program's AST with the materialized annotations and re-running the strict checker to confirm the
/// soft-flag set is now empty. This function performs the *decidable-relative-to-the-checker*
/// classification (§4.1) — the sound-by-construction part — which is the soundness-critical half;
/// the AST-rewrite mechanization is comparatively boilerplate, left for a follow-up.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct StrictifyOutcome {
    /// `(site, principal type)` pairs safe to mechanically materialize as an annotation.
    pub materialized: Vec<(String, Ty)>,
    /// Flags whose resolution is non-principal (⊥ or ambiguous) — surfaced, never guessed.
    pub residual: Vec<TypeFlag>,
}

/// Classify a loose run's soft-flag set into the mechanically-materializable subset and the
/// human-resolution residual (DN-126 §4 steps 1-3 / §4.1). Pure and total: every flag lands in
/// exactly one of the two output lists, decided solely by its own [`Resolution`] — never by a
/// heuristic guess over `candidates`.
#[must_use]
pub fn strictify(flags: &[TypeFlag]) -> StrictifyOutcome {
    let mut out = StrictifyOutcome::default();
    for flag in flags {
        match flag.resolution.principal() {
            Some(ty) => out.materialized.push((flag.site.clone(), ty.clone())),
            None => out.residual.push(flag.clone()),
        }
    }
    out
}
