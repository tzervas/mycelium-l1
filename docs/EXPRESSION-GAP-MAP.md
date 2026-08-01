# Expression Gap Map — measured surface inventory for Mycelium L1

| Field | Value |
|---|---|
| **Status** | Living inventory (`Empirical` where a test/file proves a cell; `UNVERIFIED` where not) |
| **Owner repo** | `tzervas/mycelium-l1` (parse / elaborate / L1 `Evaluator` / `lib/std/*.myc`) |
| **Authority** | Decision corpus: RFCs, ADRs, DNs, M-ids, VR-5/G2. DN-111 is the native-translation taxonomy. |
| **Revision** | 0 — measured against `mycelium-l1` tip on branch `dev` (crate version **0.464.0**) plus the archived monorepo corpus at `tzervas/mycelium@aad96b7a` (`archive/main-pre-component-transpile-2026-07-17`) |
| **Does not** | Implement surface sugar, close gaps, or cut a 1.x release. A separate unit owns `{ a; b }` block sequencing — **not duplicated here**. |

**One-sentence purpose.** For every expression form the corpus specifies, record whether it **parses → elaborates → evaluates → AOT-lowers**, name every gap between “specified” and “executes” with its **blocker class**, and map common logic problems to the **Mycelium-native** answer so Rust-first (then Python) transpilation coverage is assessable rather than aspirational.

**How to read columns**

| Column | Meaning |
|---|---|
| **Specified** | Named in grammar (`docs/spec/grammar/mycelium.ebnf`), RFC/DN surface, or deliberate exclusion |
| **Parses** | `parse` / `parse_phylum` accepts (or deliberate reject fixture) |
| **Elaborates** | `elaborate` → closed L0 **or** explicit `ElabError::Residual` (DN-50 / RFC-0007 §4.6) |
| **Evaluates** | L1 `Evaluator` and/or L0 interpreter produce a value (or explicit refusal) |
| **AOT** | `mycelium_mlir::run` / `run_core` agrees with L0 on the three-way corpus |

Honesty tags follow VR-5: never claim past the prim / witness. G2: refusals are never silent.

---

## 0. Executive summary

| | Count |
|---|---|
| **Surface forms inventoried** (expr + pattern + key item forms + deliberate non-forms) | **52** |
| **Full pipeline green** (parses + elaborates Ok + evaluates + AOT on a cited witness) | **24** |
| **Gaps by blocker class** | surface **9** · elaboration **6** · evaluation **2** · missing prim / host registry **5** (21 unique rows; G15 dual-tagged, counted under missing prim for the host registry) |
| **UNVERIFIED cells** | listed in §5 |

**Central measured finding (statement sequencing).** The multi-statement body gap is **surface syntax only**:

- Nested `let _ = a in let _ = b in c` **parses, checks Total, elaborates** — `the_desugar_target_already_works_end_to_end` (witness file on PR [#7](https://github.com/tzervas/mycelium-l1/pull/7) / branch `docs/multistmt-inventory`; same shape in `tests/enablement.rs` `stmt_sequencing_let_underscore_*_three_way`).
- `{ a; b }` is **not** in `expr` (`mycelium.ebnf`); refusal is `expected an expression, found LBrace` at `parse.rs` `parse_primary`.
- DN-106 (Accepted) already classifies L1 sequencing as **closed** via `let _ = e in body`; the residual for ports is transpiler emit + optional block sugar (separate unit).

**Linchpin for host interop.** `wild { name(args) }` type-checks inside `@std-sys` + `!{ffi}` and elaborates to `Node::Op { prim: "wild:…" }`. Gate A1 + this crate's dual-reg consumer wire the L1/L0 host floor (`Evaluator::with_host_floor` / `Interpreter::with_host_floor`); default remains fail-closed. AOT min-floor ops remain a residual until codegen migrates — see `docs/GAP-ffi-host-and-surface.md`.

---

## 1. Surface inventory

Legend: **Y** = witnessed green · **R** = explicit Residual / refusal (cited) · **—** = not applicable · **U** = UNVERIFIED · **N** = not in surface / deliberate absence.

### 1.1 Core expression forms (`Expr` / `mycelium.ebnf` `expr`)

| # | Form | Corpus | Spec | Parse | Elab | Eval | AOT | Proof / refusal site |
|---|---|---|---|---|---|---|---|---|
| 1 | `let x = e in body` | RFC-0006; DN-106 | Y | Y | Y | Y | Y | `runnable_gate` “let binding”; `enablement::stmt_sequencing_let_underscore_*_three_way` |
| 2 | `let _ = e in body` (discard / sequencing) | DN-106; DN-71/M-903 | Y | Y | Y | Y | Y | DN-106 §7; enablement three-way; multi_statement `the_desugar_target_already_works_end_to_end` |
| 3 | `if c then a else b` | DN-02; ebnf `if_expr` | Y | Y | Y | Y | Y | `differential.rs` (pick/True); `src/tests/elab.rs` |
| 4 | `match e { p => … }` | RFC-0011; RFC-0020 | Y | Y | Y | Y | Y | `runnable_gate` “data type with match”; accept `04-type-and-match.myc` |
| 5 | `for x in xs, acc = init => body` | RFC-0007 §4.8 | Y | Y | Y | Y | Y | `runnable_gate` “for-fold over a list spine”; accept `11-for-fold.myc` |
| 6 | `swap(v, to: T, policy: p)` Binary↔Ternary | RFC-0002; S1 | Y | Y | Y | Y | Y | `runnable_gate` “Binary→Ternary swap” |
| 7 | `swap` → Dense target | RFC-0002 §5; DN-52 | Y | Y | **R** | — | — | `runnable_gate` ExplicitResidual “Dense swap target”; engine residual until E2-1/ADR-033 Dense path |
| 8 | `with paradigm P { e }` | RFC-0012 §4.4 | Y | Y | Y† | Y† | U | Strips to body after ambient fill (`src/tests/ambient.rs`); †no dedicated Residual |
| 9 | `wild { name(args) }` host-call form | RFC-0028; ADR-014; M-661; A1 | Y | Y | Y‡ | **Y**§ | **R**/dual§ | L1/L0: `with_host_floor` executes min ops (`tests/host_contact.rs`); AOT min-floor residual; dual-reg three-way on deterministic mock — `docs/GAP-ffi-host-and-surface.md` |
| 10 | `wild { non-host body }` | RFC-0028 §4.2 | Y | Y | **R** | — | — | `runnable_gate` “wild body not in host-call form”; Residual text in `elab.rs` |
| 11 | `spore(e)` | RFC-0016; ADR-013 | Y | Y | **R** | — | — | `elab.rs`: `` `spore` is deferred (E2-5/M-260) ``; accept parse `07-spore.myc` |
| 12 | `wrapping { arith }` | RFC-0034 §10.1 CU-5 | Y | Y | **R** | Y (L1) | **R** | L1: `src/tests/wrapping.rs`; Elab Residual: Core-IR wrapping election staged |
| 13 | `consume e` | DN-03; LR-8; M-664 | Y | Y | **R**‖ | R‖ | — | Surface + check active; Substrate has no v0 value lowering (`ast.rs` Consume doc) |
| 14 | `e?` on `let` RHS | DN-102; M-1025 | Y | Y | Y¶ | Y¶ | Y¶ | `tests/try_operator.rs` ≡ hand-`match` desugar; ¶via desugar before elab |
| 15 | `e?` outside `let` RHS | DN-102 §5 FLAG-try-1 | Y | Y | — | — | — | Check refusal: `a_question_outside_a_let_binder_rhs_is_refused` |
| 16 | `colony { hypha e, … }` | RFC-0008 §4.7; M-666 | Y | Y | Y | Y | Y | `runnable_gate` “colony with single hypha”; accept `13-colony-hypha.myc` |
| 17 | orphan `hypha` (outside colony) | RFC-0008 RT7 | N | **R** | — | — | — | reject `13-orphan-hypha.myc` |
| 18 | `lambda(params) => body` | RFC-0024 §4A; M-704 | Y | Y | Y# | Y# | Y# | `tests/closures.rs` three-way via mono defunctionalization; #raw Lambda never reaches elab |
| 19 | `f(args)` application | RFC-0007 | Y | Y | Y | Y | Y | `runnable_gate` “function call” |
| 20 | `fuse(a, b)` | DN-58 §A; M-667 | Y | Y | Y | U | U | Parse/check: accept `24-fuse-reclaim-tier.myc`; `src/tests/fuse.rs` laws; three-way **UNVERIFIED** in this inventory |
| 21 | `reclaim(policy) { body }` | DN-58 §B; M-667 | Y | Y | Y | U | U | Accept fixture; sequential reference elab documented in `ast.rs`; three-way **UNVERIFIED** here |
| 22 | path / variable | — | Y | Y | Y | Y | Y | ubiquitous |
| 23 | Binary / Ternary literals | Q6; RFC-0030 | Y | Y | Y | Y | Y | `runnable_gate` bare literals; accept `10-literals.myc` |
| 24 | Float literal | ADR-040 | Y | Y | Y | Y | Y | `enablement` float three-ways |
| 25 | Bytes / string literal | RFC-0032 D4 | Y | Y | Y | Y | Y | `enablement::string_literal_*_surface_three_way` |
| 26 | `[…]` list literal → Cons/Nil | RFC-0040 | Y | Y | Y | Y | Y | `tests/list_literal.rs` AST identity + desugar |
| 27 | Seq literal | RFC-0032 D3 | Y | Y | Y | Y | Y | `enablement::seq_literal_surface_three_way` |
| 28 | `e : T` ascription | — | Y | Y | Y | Y | U | Parse/check ubiquitous; dedicated AOT row **UNVERIFIED** |
| 29 | `(a, b, …)` tuple lit (arity ≥ 2) | M-826 | Y | Y | Y | Y | Y | Closures/tuple fixtures; M-826 round-trip claim in `ast.rs` |
| 30 | Operator sugar `+ - * …` | RFC-0025 Enacted; M-705/M-745 | Y | Y | Y** | Y** | Y** | Accept `20-operator-syntax.myc` (parse); **word prims that exist** three-way in enablement; glyph→missing word = unknown prim (G2) |
| 31 | **`{ a; b }` block / multi-stmt body** | DN-106 target exists; block form **not** in ebnf `expr` | N†† | **R** | — | — | — | Refusal sites A–D: multi_statement inventory (PR #7); parse `found LBrace` / top-level item / missing `in` |
| 32 | **`()` unit value / type spelling** | DN-137 answers with prelude `Unit` | N (`()`) / Y (`Unit`) | **R** (`()`) / Y (`Unit`) | Y (`Unit`) | Y (`Unit`) | Y (`Unit`) | `unit_has_no_expression_spelling` / `unit_has_no_type_spelling`; `unit_prelude` in `checkty.rs` (DN-137/M-1102) |

† Ambient resolution removes the node before check.  
‡ Host-call shape only.  
§ Runtime: default empty + no `ffi` (fail closed). Opt-in min floor executes on L1/L0; AOT still PrimRegistry-only for min floor.  
‖ Substrate residual class.  
# After monomorphization.  
** Dependent on landed `prim_kernel_name` row.  
†† Deliberate: DN-106 keeps sequencing as nested `let`; block sugar is optional frontend (separate unit).

### 1.2 Pattern forms

| # | Form | Corpus | Spec | Parse | Check/Elab | Eval | Proof |
|---|---|---|---|---|---|---|---|
| 33 | `_` wildcard | RFC-0020 | Y | Y | Y | Y | match fixtures |
| 34 | literal pattern | RFC-0020 | Y | Y | Y | Y | match fixtures |
| 35 | `Ctor(subs…)` positional | LR-1 | Y | Y | Y | Y | runnable_gate match |
| 36 | ident binder / nullary ctor | — | Y | Y | Y | Y | — |
| 37 | `(p, q, …)` tuple pattern | M-826 | Y | Y | Y | Y | closures / tuple fixtures |
| 38 | `p \| q` or-pattern | RFC-0020 §9; M-823 | Y | Y | Y (desugar) | Y | checker expands before elab |
| 39 | named-field pattern `C { a, b }` | DN-119 L3-G1; DN-123 | N (today) | **R**/absent | — | — | `Pattern` enum has no Struct variant (`ast.rs`) |
| 40 | range / `@` bind patterns | DN-119 L3-G2/G3 | N | N | — | — | no tokens; idiom = guards |

### 1.3 Item / program forms (execution-relevant)

| # | Form | Corpus | Spec | Parse | Check | Runs | Proof / residual |
|---|---|---|---|---|---|---|---|
| 41 | `nodule` / `phylum` + `use` | DN-06; M-662 | Y | Y | Y | partial | `tests/phylum.rs`; runtime cross-nodule = M-1024 / DN-99 A0 residual |
| 42 | `fn` (incl. generics, effects `!{…}`) | RFC-0014; RFC-0019 | Y | Y | Y | Y | monomorphized generic: `runnable_gate` |
| 43 | `type` sum (positional ctors) | LR-1 | Y | Y | Y | Y | match / list spines |
| 44 | `trait` / `impl Trait for T` / inherent `impl T` | RFC-0019; M-664 | Y | Y | Y | Y | `runnable_gate` trait impl; accept `14-trait-impl.myc` |
| 45 | `object` composition | DN-53; M-811 | Y | Y | Y (desugar) | Y | `tests/object_desugar.rs` |
| 46 | `lower` / `derive` facility | DN-54; M-812 | Y | Y | partial | partial | `tests/lower_derive.rs` (rule elab); **std-derive library** residual (DN-128; language-completeness inventory §6) |
| 47 | `default paradigm` / `default policy` | RFC-0012; DN-142 | Y | Y | Y | — | ambient / ambient_policy modules |
| 48 | `@tier(compiled\|interpreted) fn` | DN-58 §C; RFC-0004 | Y | Y | Y | — | non-semantic NFR-7; accept `24-fuse-reclaim-tier.myc` |
| 49 | prelude `Unit` / `Bool` | DN-137; Bool seed | Y | — | Y | Y | `checkty::unit_prelude` / `PRELUDE_UNCONDITIONAL_TYPE_NAMES` |

### 1.4 Deliberate non-forms / reserved vocabulary (not gaps)

| # | Construct | Native posture | Corpus |
|---|---|---|---|
| 50 | Imperative `while` / unbounded `loop` | **Idiomatic Remapping** → structural recursion / `for`-fold | reject `08-imperative-while.myc`; RFC-0007 §4.8; DN-119 §5 |
| 51 | Silent numeric cast | **Idiomatic Remapping** → explicit `swap` | S1; DN-109 D13 |
| 52 | Runtime reserved keywords (`mesh`, `graft`, `cyst`, `xloc`, `backbone`, …) | Reserved, not active — parse as keywords, no production | DN-03; reject `12-runtime-vocab-reserved-not-active.myc`; `forage` D-lite only (M-906) |

---

## 2. Honest gap list

Each row is something the corpus **specifies or needs for ports** that does not yet **execute end-to-end**. Blocker classes:

- **surface** — grammar / desugar missing; semantic target may already exist  
- **elaboration** — parse+check ok; `elaborate` Residual (or strips only)  
- **evaluation** — L0/L1 run refuses or host missing after Ok elab  
- **missing prim** — no kernel/host prim (or empty registry)

| ID | Gap | Corpus id | Blocker | What blocks | Evidence |
|---|---|---|---|---|---|
| G1 | Multi-statement `{ a; b }` block body | DN-106; multi_statement inventory; transpiler MultiStmtBody class | **surface** | No `block` alternative in `expr`; `;` is component terminator (DN-57), not statement separator | PR #7 tests; desugar target **already** full pipeline |
| G2 | `()` value/type spelling | DN-137 (Accepted — prelude `Unit`); M-826 arity-0 | **surface** (spelling only) | `()` refused in expr/type; **`Unit` / `Unit` value already execute** | multi_statement unit spelling tests; `unit_prelude` |
| G3 | Method-call sugar `x.m(args)` | port vet “method-call”; free-fn native | **surface** | No method-call production; Dot is path only | parse path `Tok::Dot`; GAP-ffi-host-and-surface.md method-call row |
| G4 | Named-field records / `.field` / record update | DN-106 fork B **rejected**; DN-123 Draft | **surface** (optional faithfulness) | Positional ctors by design; reconstruct via `match` | DN-106 §2–§3; no Field Proj in `Expr` |
| G5 | `?` in general (non-`let`) position | DN-102 FLAG-try-1; DN-119 L3-G5 | **surface** / elab (CPS) | v0 position restriction in checkty | `try_operator` outside-let refusals |
| G6 | Impl-level generic params `impl[T] …` | DN-119 L3-G4; DN-99 A2 | **surface** | No type_params on `impl` head | DN-119 §3 |
| G7 | Range / `@`-bind patterns | DN-119 L3-G2/G3 | **surface** (or permanent idiom) | No tokens / Pattern variants | DN-119 §3 |
| G8 | Standard-derive *library* (Debug/Clone/…) | DN-54 facility landed; DN-128 | **surface** + facility completeness | Facility works; std library unbuilt | `lower_derive` ok; completeness inventory §6 DeriveAttr |
| G9 | External-trait impl MVP | DN-122 Accepted; M-1080 | **elaboration**/checker (build-ready design) | Prelude-scoped MVP build residual | language-completeness inventory §3 #1 |
| G10 | `wrapping {…}` Core-IR / AOT | RFC-0034 §10.1 | **elaboration** | L1 eval works; elab Residual until interp Node::Op elects wrapping | `elab.rs` Wrapping arm; `src/tests/wrapping.rs` |
| G11 | `spore(e)` execution | E2-5/M-260 | **elaboration** | Explicit Residual | `elab.rs` spore arm |
| G12 | Dense (and non Binary↔Ternary) swap execution | DN-52 FLAG-1; ADR-033 | **elaboration** | Explicit Residual; Dense engine staged | `runnable_gate` Dense row |
| G13 | `consume` / `Substrate` values | LR-8; M-664 | **elaboration** / value model | No Substrate value forms | `ast.rs` Consume honesty note |
| G14 | Raw `Lambda`/`Try` at elab (if unchecked) | RFC-0024; DN-102 | **elaboration** (invariant) | Must pass mono/check desugar first | Residual messages in `elab.rs` |
| G15 | `wild` host ops actually run | RFC-0028 §4.3; A1 | **partially closed** (L1/L0) | Min floor executes with `with_host_floor`; AOT dual-reg residual | `tests/host_contact.rs`; GAP-ffi-host-and-surface.md |
| G16 | Cross-nodule runtime link | M-1024; DN-99 A0; DN-101 | **evaluation** | Check-time `use` ok; single-nodule eval residual | phylum check vs runtime |
| G17 | Display / int→string / `write!` | DN-127; M-875 | **missing prim** + macro | No Display kernel prim | completeness inventory §3 #3 |
| G18 | Transcendentals `sqrt`/`exp`/… | DN-108 Accepted; M-1028 | **missing prim** | Design ready; build residual | completeness inventory §3 #12 |
| G19 | Never-type / divergence | DN-107; M-1030 | **missing prim** / type | Build-ready design | completeness inventory §3 #17 |
| G20 | Operator word targets without prim | RFC-0025; historical M-809 | **missing prim** (shrinking) | Glyph parses; unknown prim if unmapped | accept `20-operator-syntax.myc` comments vs current `prim_kernel_name` (many `_u`/`_s` ops **landed**) |
| G21 | `&mut self` / in-place receiver mapping | ADR-003 value-threading; DN-125 un-owned | **surface** emit (transpiler) + design | Substrate for value-thread exists; receiver mapping un-owned | completeness inventory §3 #2; DN-119 §5 exclusion for *mutation model* |

### 2.1 Gap counts by blocker class

| Blocker class | Count | IDs (primary class) |
|---|---|---|
| **surface** | 9 | G1–G8, G21 |
| **elaboration** | 6 | G9–G14 |
| **evaluation** | 2 | G15 (runtime after Ok elab), G16 |
| **missing prim** | 5 | G15 host registry, G17–G20 |

Unique gap rows: **21**. G15 is dual (evaluation + empty host registry); G5’s CPS follow-up is also partly elab — primary class remains surface position restriction.

**Shallow vs deep (operator lesson).** G1 looks like “cannot sequence statements” but is **surface-only**: nested `let` already evaluates. G15 looks like “FFI syntax missing” but is **registry/execution**. Always classify before scheduling.

---

## 3. Logic-problem map (DN-111)

Taxonomy (Accepted DN-111): **Native Equivalent · Idiomatic Remapping · Approximation · Interop Bridge**.  
Classify the *problem*, not the foreign syntax. “No native way yet” is stated explicitly.

| Logic problem | Foreign sketch | Mycelium-native answer | DN-111 class | Status | Needed if missing |
|---|---|---|---|---|---|
| Local binding | `let x = e;` | `let x = e in body` | Native Equivalent | **Executes** | — |
| Statement sequencing / discard | `{ a; b; c }` | `let _ = a in let _ = b in c` | Idiomatic Remapping (or Equivalent after block sugar) | **Semantic target executes**; block sugar surface open (G1) | Optional `{…}` desugar (separate unit) |
| Unit / void return | `()` / `fn f() {…}` | Prelude `type Unit = Unit;` value `Unit` | Native Equivalent (DN-137) | **Executes** as `Unit`; `()` spelling absent (G2) | Transpiler `() → Unit` map |
| Conditional | `if/else` | `if c then a else b` | Native Equivalent | **Executes** | — |
| Multi-way branch | `match` / `switch` | `match` + positional patterns + or-patterns | Native Equivalent | **Executes** | Named-field patterns optional (G4/G39) |
| Bounded iteration | `for x in xs` | `for x in xs, acc = init => body` (fold sugar) | Native Equivalent | **Executes** | — |
| Unbounded loop | `loop` / `while true` | Structural recursion / explicit fuel; **not** unbounded surface | Idiomatic Remapping / deliberate exclusion | Native path exists | Do not add `while` (reject fixture) |
| Early error return | `?` | `let x = e? in body` → `match` bind (DN-102) | Native Equivalent | **Executes** in `let` position | CPS for general position (G5) |
| Option/Result combinators | `map`/`and_then` | `match` or higher-order + lambda (DN-135) | Idiomatic Remapping | Partial / library | Closure emit + std combinators |
| Closures | `\|x\| e` | `lambda(x: T) => e` + Reynolds defunctionalization | Native Equivalent | **Executes** (closures.rs) | FnMut/`&mut` capture flagged |
| Higher-order / callbacks | fn pointers | First-class `A => B` types + defunc | Native Equivalent | **Executes** (M-924/RFC-0024) | — |
| Methods | `x.method()` | Free function / trait fn `method(x, …)` | Idiomatic Remapping | Check/dispatch **executes**; call sugar absent (G3) | Transpiler rewrite or surface sugar |
| Traits / typeclasses | `impl Trait for T` | `trait` + `impl` + mono static dispatch | Native Equivalent | **Executes** (intra-home) | External-trait MVP G9 |
| Algebraic data | `enum` | `type T = A \| B(T1,…)` positional | Native Equivalent | **Executes** | — |
| Product / records | `struct { fields }` | Positional ctor + tuple (M-826); field update via match reconstruct | Idiomatic Remapping | **Executes** positional path | DN-123 if named fields wanted |
| In-place mutation | `x.f = v` / `&mut` | Value-threading: return new value / rebind `let x = … in` | Idiomatic Remapping (ADR-003) | Substrate yes; `&mut self` emit **design-gated** (G21) | DN-125-class decision + transpiler |
| Representation change | `as` cast | `swap(v, to: T, policy: …)` never-silent | Idiomatic Remapping | Binary↔Ternary **executes**; Dense residual (G12) | Dense engine |
| Modular overflow arith | wrapping ops | `wrapping { add_s/sub_s/mul_s … }` | Native Equivalent | **L1 executes**; AOT/elab residual (G10) | Core-IR wrapping election |
| Bitwise / arithmetic ops | `+ & << …` | Word prims (`add_u`, `and`, …) + glyph sugar | Native Equivalent | **Most execute** via `prim_kernel_name` | Any unmapped glyph word (G20) |
| Equality / order | `==` `<` | `eq`/`lt`/`lt_s` / float `flt_*` | Native Equivalent | **Executes** (enablement) | — |
| Float numerics | `f64` ops | `Float` + `flt_*` prims (ADR-040) | Native Equivalent / Empirical tag | **Executes** arithmetic & cmp | Transcendentals G18 |
| Sequences / bytes | slices, `Vec` | `Seq{T,N}`, `Bytes`, list ADT, `bytes_*`/`seq_*` | Native Equivalent | **Executes** core ops | Full collections port residual |
| Error type as value | `Result` | `type Result[A,E] = Ok(A) \| Err(E)` in std | Native Equivalent | **Executes** | — |
| Affinity / linear resources | manual drop | `Substrate` + `consume` + affine check | Native Equivalent (staged runtime) | Check surface; **eval residual** (G13) | Substrate value model |
| Structured concurrency | async/tasks | `colony { hypha e, … }` RT2 sequential reference + optional concurrent driver | Native Equivalent (R1 fragment) | **Executes** sequential ref | Full runtime mesh etc. reserved |
| Supervision | supervisor trees | `reclaim(policy) { body }` | Native Equivalent (staged RT7) | Parse/elab; full RT7 driver separate | UNVERIFIED three-way here |
| CRDT / merge | custom join | `fuse(a,b)` + `Fuse` laws | Native Equivalent | Check laws; eval **UNVERIFIED** three-way | Confirm three-way |
| FFI / host effects | `extern` / syscalls | `wild { host(args) }` in `@std-sys` + `!{ffi}` | Interop Bridge | Syntax+elab; **no host prims** (G15) | Host registry + std-sys floor |
| Unsafe | `unsafe` | `wild` audited floor only | Interop Bridge | Same as FFI | — |
| Macros / derives | `#[derive]` | `lower` / `derive` facility + library | Native Equivalent (facility) | Facility **executes**; library G8 | std-derive set |
| Formatting | `format!` / `Display` | Display-as-Bytes composition + prim | Idiomatic Remapping | **No** int→string prim (G17) | DN-127 prim + expand-first |
| Shared mutability | `Mutex`/`RefCell` | Runtime tier / mesh (post Phase-7) — not L1 value semantics | Interop Bridge / exclusion | Not L1 | Runtime program |
| Divergence | `-> !` | DN-107 approximation | Approximation | Design-ready (G19) | M-1030 build |
| Modules | `mod`/`use` | `nodule`/`phylum`/`use` | Native Equivalent | Check yes; runtime link G16 | M-1024 |
| Python exceptions | `raise`/`try` | **No Python-native DN yet** (DN-119 §11 / completeness §8) | — | **UNVERIFIED / unspecified** | Dedicated Python DN-111 pass |
| Python generators | `yield` | No native form cited | — | **No native way yet** | Design DN |
| Python shared mut / duck typing | pervasive | Collides with deliberate exclusions | — | **No native way yet** for full fidelity | Approximation + Interop Bridge policy |

### 3.1 Runnable native idioms (real surface)

These are valid on the measured toolchain (parse → check → elaborate; three-way where cited).

**Sequencing without blocks** (DN-106; enablement three-way):

```text
nodule d;
fn g(x: Binary{8}) => Binary{8} = x;
fn f() => Binary{8} =
  let _ = g(0b0000_0001) in
  let _ = g(0b0000_0010) in
  0b0000_0011;
```

**Unit-returning body** (DN-137 prelude):

```text
nodule d;
fn h() => Unit = Unit;
fn f() => Unit = let _ = h() in let _ = h() in Unit;
```

**Error propagation** (DN-102; `tests/try_operator.rs`):

```text
nodule d;
type Result[A, E] = Ok(A) | Err(E);
fn step(x: Binary{8}) => Result[Binary{8}, Binary{8}] = Ok(x);
fn f() => Result[Binary{8}, Binary{8}] =
  let y = step(0b0000_0001)? in Ok(y);
```

**Bounded fold** (RFC-0007 §4.8; runnable_gate):

```text
nodule d;
type ByteList = End | More(Binary{8}, ByteList);
fn main() => Binary{8} =
  let bs = More(0b1111_0000, More(0b0000_1111, End)) in
  for b in bs, acc = 0b0000_0000 => xor(acc, b);
```

**Closure** (RFC-0024; `tests/closures.rs`):

```text
nodule d;
fn main() => Binary{8} =
  let c = 0b0000_1111 in
  let f = lambda(x: Binary{8}) => and(x, c) in
  f(0b1010_1010);
```

---

## 4. Measured test output (this inventory session)

Commands run on crate **0.464.0**, `cargo test --release`:

```text
$ cargo test --release --test multi_statement_body
running 7 tests
test goal_a_two_statement_block_body_parses_identically_to_its_let_desugar ... ignored, GOAL: `{ a; b }` block sequencing is not in the surface grammar yet …
test a_statement_let_without_in_is_refused_at_the_missing_in ... ok
test a_braced_block_is_not_an_expression_form_at_all ... ok
test unit_has_no_type_spelling ... ok
test unit_has_no_expression_spelling ... ok
test two_semicolon_separated_statements_are_refused_as_a_stray_top_level_item ... ok
test the_desugar_target_already_works_end_to_end ... ok
test result: ok. 6 passed; 0 failed; 1 ignored
```

*(Witness source: branch `docs/multistmt-inventory` / PR #7 — not re-implemented here.)*

```text
$ cargo test --release --test runnable_gate
test every_accepted_construct_elaborates_to_ok_or_explicit_residual ... ok
# 16 Runs + 2 ExplicitResidual categories (Dense swap; wild non-host body)
```

```text
$ cargo test --release --test differential -- l1_eval_l0_interp_and_aot_agree_on_the_fragment
test l1_eval_l0_interp_and_aot_agree_on_the_fragment ... ok
```

```text
$ cargo test --release --test enablement   # 144 passed
$ cargo test --release --test closures     # 6 passed
$ cargo test --release --test try_operator # 7 passed
$ cargo test --release --test list_literal # 4 passed
$ cargo test --release --test prim_table   # 10 passed
$ cargo test --release --test conformance  # 4 passed (accept/reject corpus gate)
```

Ignored goal when forced (`--include-ignored`):

```text
parse: parse error at 4:23: expected an expression, found LBrace
fn f() => Binary{8} = { g(0b0000_0001); 0b0000_0011 };
```

---

## 5. UNVERIFIED

Do not treat these as closed or open without a fresh witness:

| Item | Why UNVERIFIED |
|---|---|
| `fuse` / `reclaim` full L1≡L0≡AOT three-way | Laws + parse/check witnessed; no three-way row exercised in this session |
| `with paradigm` AOT differential | Ambient strip + swap body witnessed; not re-run as AOT row here |
| Ascription-only AOT row | No dedicated fixture cited |
| Every glyph operator → prim end-to-end | Parse corpus green; many word prims landed in `prim_kernel_name`; full glyph matrix not exhaustively three-way’d |
| Cross-nodule **runtime** eval matrix | Check-time phylum suite green; M-1024 completion not re-measured |
| Python construct map | Explicitly out of scope until its own DN (DN-119 §11) |
| Exact current transpiler `checked_fraction` | Completeness inventory cites ~7–8% historical; not re-vet’d here |
| mycelium-codegen native Dense/VSA AOT beyond differential corpus | ADR-019/ADR-034/RFC-0039 territory — not re-bench’d |

---

## 6. Related artifacts (do not duplicate)

| Artifact | Role |
|---|---|
| `docs/spec/grammar/mycelium.ebnf` + `conformance/` | Normative L3 oracle (RFC-0006 §4.3; RFC-0030) |
| `docs/GAP-ffi-host-and-surface.md` | FFI host registry + port surface gaps |
| `tests/runnable_gate.rs` | DN-50/DN-52 Runs vs Explicit-Residual standing gate |
| `tests/differential.rs` / `tests/enablement.rs` | Three-way evaluation-complete corpus |
| Archived monorepo `docs/notes/DN-106`, `DN-111`, `DN-119`, `DN-137` | Sequencing, taxonomy, L3 residual, Unit |
| Archived `docs/planning/language-completeness-gap-inventory.md` | Drive-hard worklist + DN-111 scoring |
| PR [#7](https://github.com/tzervas/mycelium-l1/pull/7) | Statement-sequencing refusal pin (do not re-implement here) |

---

## 7. Changelog

- **2026-07-25** — Initial measured inventory (this document). Forms: 52. Gaps by class: surface 9 / elaboration 6 / evaluation 2 / missing prim 5 (21 unique). No language code changes.
- **2026-07-25** — G15 L1/L0 path closed for A1 min floor (`with_host_floor`); host_contact witnesses; AOT residual documented. Form 9 Eval column → Y (opt-in).
