//! **`policy: ambient` scoped resolution** (DN-142 §3.2; RFC-0012/RFC-0034 §6) — the **third**
//! instance of the ambient/scoped-override mechanism (RFC-0012's paradigm ambient is the first;
//! `@certification`/[`CertMode`](mycelium_core::cert_mode::CertMode) —
//! `mycelium_proj::cert_scope` — is the second; the `LanguageRetentionPolicy` spec, DN-142 §3.1, names
//! a future fourth). This module mirrors `mycelium_proj::cert_scope`'s pure resolution shape as
//! closely as the two domains allow — a most-specific-wins scope stack, reified and `EXPLAIN`-able,
//! **never** a silent fallback — rather than inventing a second scoping algorithm (DN-142 §3.2: "no
//! new scoping machinery").
//!
//! # What differs from `cert_scope`, and why (disclosed, not silently narrowed)
//! `CertMode` resolution (`mycelium_proj::cert_scope::resolve_mode`) never fails — an undeclared
//! mode defaults to [`CertMode::Fast`](mycelium_core::cert_mode::CertMode::Fast). `policy: ambient`
//! resolution is **not** allowed that fallback (DN-142 §3.2: "unresolved is a hard error, never a
//! fallback") — so [`resolve_policy`] returns a `Result`, not a defaulted value.
//!
//! # Scope tiers wired at v0 (an honest, disclosed scope boundary — mirrors `cert_scope`'s own
//! FLAG-B)
//! [`PolicyScope`] carries the full RFC-0034 §6 lattice (`Global ⊐ Phylum ⊐ Nodule`) so the
//! precedence law is testable end-to-end today, exactly as `cert_scope::CertScope` does for its own
//! (also-unwired) `Global` tier. **Only the `Nodule` tier is wired at the `mycelium-l1` surface** in
//! this leaf (a `default policy <name>;` declaration, parsed in [`crate::parse`], resolved in
//! [`crate::checkty::Cx::check_swap`]): `@certification`'s `Phylum` tier lives one crate up, in
//! `mycelium-proj`'s manifest/header parsing (`cert_scope.rs`'s own module doc, FLAG-B) — genuinely
//! out of this leaf's crate scope (`mycelium-l1`/`mycelium-select`). Wiring a phylum-level `@policy`
//! manifest/header field is a flagged follow-on, not invented here.
//!
//! # The third, least-specific "catalog" tier
//! DN-142 §3.2's own EXPLAIN-origin vocabulary names exactly three origins — `declared@nodule`,
//! `declared@phylum`, **`catalog`** — with no `declared@global`. Read literally (and consistent with
//! `cert_scope`'s own unwired `Global`), the least-specific tier is realized here as a **catalog
//! lookup** ([`crate::legal_pair::catalog_default_policy`]) rather than a fourth declaration form:
//! when no scope declares an ambient policy, [`resolve_policy`] falls through to the pair's catalog
//! default (if the `std.swap.policy` catalog names one) before it is a hard error. This keeps
//! [`PolicyScope::Global`] structurally present (for the precedence-law shape) while not fabricating
//! an unrequested language declaration form for it.

use crate::ast::Path;
use mycelium_diag::{
    CertMode, Decision, Diag, EventId, FirstFaultEnvelope, Phase, Severity, SiteKind,
};

/// The scope an ambient-policy declaration was made at — the RFC-0034 §6 lattice `global ⊐ phylum ⊐
/// nodule`, reused verbatim (DN-142 §3.2), ordered **least-specific → most-specific**. Resolution is
/// most-specific-wins, mirroring `mycelium_proj::cert_scope::CertScope` exactly.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum PolicyScope {
    /// Project-/workspace-wide default — the least-specific *declaration* tier. Not wired at the
    /// `mycelium-l1` surface in v0 (module doc); [`resolve_policy`]'s actual least-specific
    /// fallback is the catalog, not a `Global` declaration.
    Global,
    /// The phylum tier (a manifest-level declaration, `mycelium-proj`'s domain — not wired here).
    Phylum,
    /// The nodule tier — a `default policy <name>;` declaration (DN-142 §3.2). The **most-specific**
    /// tier; the only one wired at the `mycelium-l1` surface in v0.
    Nodule,
}

impl PolicyScope {
    /// All three scopes, least-specific → most-specific — for exhaustive iteration in tests/tooling.
    pub const ALL: [PolicyScope; 3] = [
        PolicyScope::Global,
        PolicyScope::Phylum,
        PolicyScope::Nodule,
    ];

    /// Specificity rank, `0` = [`Global`](PolicyScope::Global) (least) … `2` =
    /// [`Nodule`](PolicyScope::Nodule) (most). Higher wins in [`resolve_policy`].
    #[must_use]
    pub fn specificity(self) -> u8 {
        match self {
            PolicyScope::Global => 0,
            PolicyScope::Phylum => 1,
            PolicyScope::Nodule => 2,
        }
    }

    /// A stable, lower-case label for `EXPLAIN` output (never ambient — G2), matching DN-142 §3.2's
    /// own `declared@nodule` / `declared@phylum` vocabulary via [`PolicyOrigin::label`].
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            PolicyScope::Global => "global",
            PolicyScope::Phylum => "phylum",
            PolicyScope::Nodule => "nodule",
        }
    }
}

/// One `default policy <name>` declaration: a policy [`Path`] declared at a given [`PolicyScope`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolicyDecl {
    /// The scope the declaration was made at.
    pub scope: PolicyScope,
    /// The declared policy name.
    pub policy: Path,
}

/// Where a resolved ambient policy came from (DN-142 §3.2's EXPLAIN-origin vocabulary, exactly):
/// `declared@nodule`, `declared@phylum`, or `catalog` — never ambient itself (G2).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PolicyOrigin {
    /// A `default policy <name>` declaration, at the given scope.
    Declared(PolicyScope),
    /// No scope declared one; the `std.swap.policy` catalog's canonical default for the pair
    /// resolved it instead (module doc — the realized least-specific tier).
    Catalog,
}

impl PolicyOrigin {
    /// The DN-142 §3.2 EXPLAIN-origin string — `declared@nodule` / `declared@phylum` /
    /// `declared@global` / `catalog`.
    #[must_use]
    pub fn label(self) -> String {
        match self {
            PolicyOrigin::Declared(scope) => format!("declared@{}", scope.label()),
            PolicyOrigin::Catalog => "catalog".to_owned(),
        }
    }
}

/// The resolved ambient policy plus its provenance — never silently just a bare name (G2).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedPolicy {
    /// The resolved, concrete catalog policy name (never the literal token `ambient` — DN-142 §3.2
    /// "resolve-and-record").
    pub policy: Path,
    /// Where it came from.
    pub origin: PolicyOrigin,
}

/// The never-silent resolution failure (DN-142 §3.2): no scope in the stack declares an ambient
/// policy, and the `std.swap.policy` catalog names no canonical default for the pair either — never
/// a silent substitute (G2).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnresolvedAmbientPolicy;

impl core::fmt::Display for UnresolvedAmbientPolicy {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "no ambient policy declared for this pair in scope — declare `default policy \
             <name>` or write an explicit `policy: <name>`; there is no implicit fallback \
             (DN-142 §3.2, never-silent)"
        )
    }
}

impl std::error::Error for UnresolvedAmbientPolicy {}

/// **Resolve `policy: ambient` most-specific-wins** over a set of `default policy` declarations
/// (DN-142 §3.2), mirroring `mycelium_proj::cert_scope::resolve_mode`'s precedence fold: the
/// declaration at the highest [`PolicyScope::specificity`] wins (ties are not possible by
/// construction — at most one declaration per scope, enforced upstream by
/// [`crate::ambient::resolve`]/`checkty`'s duplicate-declaration refusal).
///
/// **Unlike `mycelium_proj::cert_scope::resolve_mode`, this has no defaulted fallback value** — if
/// no scope declares one, resolution falls through to `catalog_default` (the pair's `std.swap.policy`
/// canonical entry, if any — the realized least-specific/`Global` tier, module doc); if that is also
/// absent, resolution is the explicit [`UnresolvedAmbientPolicy`] error (DN-142 §3.2: "unresolved is
/// a hard error, never a fallback").
///
/// # Errors
/// [`UnresolvedAmbientPolicy`] when neither a scoped declaration nor a catalog default resolves the
/// pair.
pub fn resolve_policy(
    decls: &[PolicyDecl],
    catalog_default: Option<&'static str>,
) -> Result<ResolvedPolicy, UnresolvedAmbientPolicy> {
    if let Some(winner) = decls.iter().max_by_key(|d| d.scope.specificity()) {
        return Ok(ResolvedPolicy {
            policy: winner.policy.clone(),
            origin: PolicyOrigin::Declared(winner.scope),
        });
    }
    if let Some(name) = catalog_default {
        return Ok(ResolvedPolicy {
            policy: Path(vec![name.to_owned()]),
            origin: PolicyOrigin::Catalog,
        });
    }
    Err(UnresolvedAmbientPolicy)
}

/// Whether a swap's `policy:` value is exactly the **ambient** spelling (DN-142 §3.1) — a single
/// path segment equal to `ambient`. A dotted path whose first segment happens to be `ambient`
/// (`ambient.custom`) is an ordinary explicit catalog name, not the reserved spelling — only the
/// bare word is special (mirrors RFC-0012's own paradigm-less `{…}` being a reserved *spelling*,
/// never a namespace prefix).
#[must_use]
pub fn is_ambient_spelling(p: &Path) -> bool {
    p.0.len() == 1 && p.0[0] == "ambient"
}

/// The `EXPLAIN` of an ambient-policy resolution (DN-142 §3.2): the resolved policy name plus its
/// origin tag, so the choice is never ambient (G2) — mirrors
/// `mycelium_proj::cert_scope::explain_mode`'s rendering shape.
///
/// **Scope note (honest, flagged — DN-142 §9-style).** This function computes the correct EXPLAIN
/// string from a [`ResolvedPolicy`] and is exercised directly by this module's tests; wiring it all
/// the way out through a first-class CLI/LSP `EXPLAIN` surface (the RFC-0013 `Diag` envelope /
/// first-fault-bus site, `policy_resolve`) is the separate, not-yet-landed W-A item DN-142 §3.2 names
/// but does not define ("this note names the site... [not] the envelope") — this function is that
/// site's computation, not the wired-up surface.
#[must_use]
pub fn explain_origin(r: &ResolvedPolicy) -> String {
    format!("policy: {}  [{}]", r.policy.0.join("."), r.origin.label())
}

/// The `policy_resolve` first-fault event (RFC-0013 Amendment A1 §10.3 — `site_kind:
/// policy_resolve`, "selection resolution to a `PolicyRef` (check)"; DESIGN-01 §4.3) for a
/// **successful** resolution — an `Info`-severity crumb (RFC-0013 §4.6 "non-sites": a resolved
/// selection is optional to consume, never mandatory), reusing [`explain_origin`]'s own rendering
/// so the envelope's message and the pre-existing EXPLAIN string never drift apart (DRY).
///
/// `event_id`/`cert_mode` are caller-supplied (this is a check-time site; see [`explain_origin`]'s
/// own scope note — `crate::checkty::Cx::check_swap` runs before `@certification` scope resolution
/// reaches the checker, so a caller there passes the project default, `CertMode::Fast`).
#[must_use]
pub fn policy_resolve_diag(r: &ResolvedPolicy, event_id: EventId, cert_mode: CertMode) -> Diag {
    let envelope = FirstFaultEnvelope::new(
        event_id,
        Phase::Check,
        SiteKind::PolicyResolve,
        Decision::Resolved,
        "policy_resolve.v0",
        cert_mode,
    )
    .with_basis_ref(format!("origin={}", r.origin.label()));
    Diag::with_severity(
        Severity::Info,
        mycelium_diag::Code::Other("PolicyResolved".to_owned()),
    )
    .message(explain_origin(r))
    .with_envelope(envelope)
}

/// The `policy_resolve` first-fault event for a **failed** resolution
/// ([`UnresolvedAmbientPolicy`]) — an `Error`-severity refuse event, used by
/// [`crate::checkty::Cx::check_swap`] (W-C X5) to build the "no ambient policy declared" error's
/// message so the same reason text backs both the `Result::Err` and the reified record.
#[must_use]
pub fn policy_resolve_refuse_diag(
    src_display: &str,
    target_display: &str,
    event_id: EventId,
    cert_mode: CertMode,
) -> Diag {
    let envelope = FirstFaultEnvelope::new(
        event_id,
        Phase::Check,
        SiteKind::PolicyResolve,
        Decision::Refuse,
        "policy_resolve.v0",
        cert_mode,
    );
    Diag::with_severity(
        Severity::Error,
        mycelium_diag::Code::Other("PolicyUnresolved".to_owned()),
    )
    .message(format!(
        "no ambient policy declared for this pair in scope ({src_display} → {target_display}) — \
         declare `default policy <name>` or write an explicit `policy: <name>`; there is no \
         implicit fallback (DN-142 §3.2, never-silent)"
    ))
    .with_envelope(envelope)
}
