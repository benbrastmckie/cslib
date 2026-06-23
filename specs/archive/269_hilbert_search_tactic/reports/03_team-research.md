# Research Report: Task #269 (Round 2)

**Task**: hilbert_search_tactic — Tactic Design Deep Dive
**Date**: 2026-06-23
**Mode**: Team Research (4 teammates, round 2)
**Focus**: Tactic design and implementation in place of Zulip discussion

---

## Summary

Round 2 research resolves the architecture conflict from Round 1 in favor of MetaM-only
proof search, with concrete verified code demonstrating that the approach works across all
tested goal types. The MetaM `apply`-based approach eliminates the need for `HasImpView` /
`HasBoxView` typeclasses, which do not exist in CSLib and would require a new Foundations
contribution. A depth bound of 5 (rising to 8 with library lemmas pre-loaded) covers
approximately 85% of automatable theorems in the propositional, modal, and temporal layers.
The critical file is `Cslib/Foundations/Logic/Automation/HilbertSearch.lean`, split into
a term-mode `@[expose] public section` for any future pure term-mode helpers and a
`public meta section` for the tactic elaboration. The implementation plan requires one file,
one test file, and careful compliance with CSLib lint requirements (docBlame, defsWithUnderscore,
topNamespace, defLemma, and the `lake exe mk_all --module` barrel registration step).

---

## Key Findings

### Tactic Implementation Patterns (from Teammate A)

Teammate A provided fully verified MetaM/TacticM code patterns, confirmed working in a live
Lean session against CSLib imports. The central findings are:

**Goal shape**: Every `hilbert_search` goal appears as
`@InferenceSystem.DerivableIn.{u1, u2} α S inst φ` — an application of exactly 4 arguments.
Pattern B (`matchDerivableIn`) extracts `(S, φ)` via `isAppOfArity ``InferenceSystem.DerivableIn 4`
and `getAppArgs`. No `whnf` call is needed because `DerivableIn` is not a reducible definition.

**Core API**: `MVarId.apply` with `ApplyConfig { newGoals := .nonDependentOnly }` is the correct
handle for axiom application. Without `nonDependentOnly`, applying `ModusPonens.mp` yields three
goals instead of two (the unconstrained formula type `F` leaks as a third goal).
`mkConstWithFreshMVarLevels` (not `mkConst`) must be used to create axiom constants because the
axiom methods are universe-polymorphic.

**Backtracking**: `observing?` provides checkpoint/rollback over MetaM state. Every axiom
attempt is wrapped in `observing?` so that a failed `apply` does not corrupt the mvar state for
subsequent attempts.

**Rule stratification** (verified working):
1. Assumption lookup — `getLCtx` + `isDefEq` against each local declaration (no recursion)
2. Zero-subgoal axioms — direct closure, no recursion
3. One-subgoal rules — `identity`, `box_mono`, `nec` (one recursive call per branch)
4. Two-subgoal rules — `imp_trans`, `ModusPonens.mp` (two recursive calls, highest branching)

**Verified test results**: The prototype closed all five tested goals: ImplyK (depth 1), Identity
(depth 1 via `identity` rule), Box mono with hypothesis (depth 2), Nec(id) (depth 2), and MP
from hypotheses (depth 1). The `elab "hilbert_search" n:(num)? : tactic` wrapper is minimal and
correct.

**Gap flagged by Teammate A**: MP backward chaining leaves `?φ` in `DerivableIn S (imp ?φ ψ)`
unconstrained, creating potential exponential branching. Mitigation options include limiting MP
depth separately, iterative-deepening DFS, or cycle detection on visited goal types.

---

### CSLib Typeclass API (from Teammate B)

Teammate B provided a complete survey of what exists in CSLib and what is absent.

**What exists**: All concrete formula types (`PL.Proposition`, `Modal.Proposition`,
`Bimodal.Formula`) derive `DecidableEq` and `BEq`, and support direct constructor pattern
matching. The bimodal `AxiomMatcher.lean` demonstrates 42-case pattern matching on
`Formula Atom` at the term level. The combinator library (`Theorems/Combinators.lean`) provides
`imp_trans`, `identity`, `b_combinator`, `flip`, `app1`, `app2`, `dni`, `pairing`, and others
as `DerivableIn S (...)` values over `[MinimalHilbert S]`.

**What does not exist**: No `HasImpView`, `HasBoxView`, or any generic formula decomposition
typeclass exists in CSLib's `Foundations/` layer. Generic term-mode search over an abstract
formula type `F : Type*` with `[HasImp F]` cannot pattern-match on `φ : F` to detect whether
`φ = HasImp.imp a b`, because `F` is abstract and `HasImp.imp` is a function, not a constructor.

**Term-mode path is viable only for concrete types**: Teammate B's term-mode search design works
for `Bimodal.Formula Atom` by wrapping `matchAxiom` (existing) and `buildCompositionalProof`
(existing) — but this is concrete-type-specific and does not extend generically to the full
typeclass hierarchy.

**`noncomputable` boundary**: `DerivableIn.toDerivation` is noncomputable. A term-mode search
that only constructs new proofs from axioms and combinators (never extracts from a `Nonempty`
witness) is computable in principle, but `noncomputable` should be added conservatively if
`toDerivation` is needed anywhere.

**Two-layer clarification from Teammate B**: Teammate B concurs that MetaM's `whnf` enables
generic formula inspection in tactic-mode (the Tier 2 tactic layer), while term-mode inspection
requires either concrete types or new `HasImpView` / `HasBoxView` typeclasses. This alignment
with Teammate A's finding confirms the MetaM approach.

---

### Standards and Best Practices (from Teammate C)

Teammate C identified all CSLib compliance requirements for the new file.

**File structure**:
```
Cslib/Foundations/Logic/Automation/HilbertSearch.lean
```
Namespace: `Cslib.Logic.Automation`. Every file starts with `module` and
`public import Cslib.Init` on the first non-copyright lines.

**Section pattern**: Term-mode helpers (if any) go in `@[expose] public section`. All tactic
elaboration (`syntax`, `elab_rules`, `registerTraceClass`, `MVarId`-level search) goes in
`public meta section`. This split is enforced by CSLib's compilation model.

**Fuel termination**: Use structural recursion `match fuel with | 0 => none | n+1 => ...` rather
than `if fuel = 0 then`. The `partial def` annotation is acceptable for the MetaM search function
(it is a metalevel tool, not a proof-relevant term) but a fuel-based `def` with structural
recursion is preferred for term-mode helpers.

**Fuel defaults**: Teammate C's depth analysis (corroborated by Teammate D) recommends default
fuel of 30 for the tactic, covering all observed theorem depths in CSLib (max ~20 for `app2`,
with practical cap around 100).

**Lint checklist**:
- `docBlame`: Every `def`, `theorem`, `class`, `instance` needs a docstring; use
  `@[nolint docBlame]` for auto-generated helpers.
- `defsWithUnderscore`: No underscores in Lean declaration names (tactic syntax keyword is exempt).
- `topNamespace`: All instances inside `namespace Cslib.Logic.Automation ... end`.
- `defLemma`: Prop-valued declarations must use `lemma`/`theorem`, not `def`.
- `unusedSectionVars`: Use `omit` for section variables not used in a definition.
- After adding the file: `lake exe mk_all --module` to register in `Cslib.lean`.
- Then `lake shake --add-public --keep-implied --keep-prefix` to minimize imports.

**Error message pattern**: Use `throwTacticEx` with the depth limit, pretty-printed goal type,
and a remediation hint (e.g., "try `hilbert_search {fuel * 2}`"). Register a trace class with
`registerTraceClass` so users can debug with `set_option trace.Cslib.Logic.hilbertSearch true`.

**Testing**: Positive `example` blocks that compile; `success_if_fail_with_msg` for negative
tests; `#guard_msgs` for error output format. Test file uses `public meta import` (not
`public import`). Tests live in `CslibTests/HilbertSearch.lean` under namespace
`CslibTests.HilbertSearch`.

**CI order**: `lake build` → `lake exe checkInitImports` → `lake lint` → `lake exe lint-style`
→ `lake test` → `lake exe mk_all --module` → `lake shake`.

---

### Proof Pattern Analysis (from Teammate D)

Teammate D surveyed ~85 theorems across 9 files in the CSLib Hilbert layers.

**Pattern distribution**:
| Pattern | Count | Automatable | Depth |
|---------|-------|-------------|-------|
| Pure axiom wrappers | ~12 (14%) | Yes (depth 1) | 1 |
| Single MP (depth 2) | ~20 (24%) | Yes | 2 |
| MP chains 3–4 deep | ~40 (47%) | Yes with library | 3–5 |
| Necessitation + K (modal) | ~15 (18%) | Yes | 3–4 |
| Complex composition (depth 7–15) | ~10 (12%) | No | 7–15 |
| Induction over lists | 3 | No | N/A |
| Context-level (DerivationTree) | ~10 | Out of scope | N/A |

**Key depth insight**: Two tiers exist. Tier 1 (depth 1–4) covers ~65% of theorems using axioms
directly. Tier 2 (depth 5–8) covers an additional ~20% once combinators like `b_combinator`,
`flip`, `imp_trans`, and `identity` are in the search library. Depth beyond 6 creates
exponential branching; Teammate D recommends a default of 5 and a practical maximum of 8.

**Necessitation macro**: Modal proofs at K-level follow a 3-step macro: (1) apply `nec` to lift
a propositional theorem, (2) apply axiom K for distribution, (3) chain with `imp_trans`. This
pattern covers virtually every K-level modal theorem and is directly implementable as a one-rule
plus one-rule application.

**Critical library lemmas** (should be pre-loaded as search rules, not discovered by search):
`imp_trans`, `b_combinator`, `flip`, `identity`, `app1`, `dni`, `double_negation`,
`contrapose_imp`, `box_mono`, `contraposition`.

---

## Synthesis

### Architecture Decision: MetaM-Only vs. Two-Layer Term-Mode + MetaM

**The conflict**: Teammate A recommended MetaM-only search using `MVarId.apply` + `observing?`.
Teammate B designed a term-mode search function returning `Option (DerivableIn S φ)`.

**Resolution: MetaM-only wins decisively.**

The conflict dissolves when the preconditions for term-mode search are examined:

1. **Term-mode requires formula decomposition**. To match goal `φ` against axiom schema
   `ImplyK φ ψ = imp φ (imp ψ φ)`, a term-mode function must decompose `φ` as `imp _ _` and
   then further decompose the consequent. For a generic formula type `F` with `[HasImp F]`,
   this decomposition is impossible because `F` is abstract. `HasImp.imp : F → F → F` is a
   function, not a constructor.

2. **No view typeclasses exist**. Teammate B's analysis confirmed that `HasImpView` and
   `HasBoxView` do not exist in CSLib. They would need to be added to `Foundations/Logic/Connectives.lean`
   as new typeclasses with instances for all four concrete formula types. This is a non-trivial
   Foundations contribution outside the stated scope of task 269.

3. **MetaM eliminates the need for view typeclasses**. `MVarId.apply` uses Lean's unifier to
   match the goal expression against the axiom's type, resolving all implicit arguments including
   the formula variables `φ` and `ψ`. No explicit formula decomposition is needed. Teammate A
   verified this works: `apply HasAxiomImplyK.implyK` with `ApplyConfig { newGoals := .nonDependentOnly }`
   successfully closes goals of the form `DerivableIn S (imp φ (imp ψ φ))` without any explicit
   knowledge of the goal's formula structure.

4. **Typeclass availability is implicit**. When the tactic tries `HasAxiomK.K` on a goal under
   `[MinimalHilbert S]` (which lacks `HasAxiomK`), the `apply` call fails and `observing?` rolls
   back. No explicit typeclass check is required. The entire proof system hierarchy is handled by
   whether `apply` succeeds.

5. **Backtracking is native in MetaM**. `observing?` provides checkpoint/rollback. Term-mode
   would need to implement this manually via `Option` threading.

**Teammate B's term-mode design remains valuable as documentation of the CSLib API surface** and
clarifies the `noncomputable` boundary and the bimodal `AxiomMatcher` reuse pattern. However,
it is not the implementation path. The `buildCompositionalProof` pattern in `ProofExtraction.lean`
is concrete-type-specific and limited to `Bimodal.Formula`; it is not a general solution.

**Conclusion**: Implement `hilbertSearchCore` as `partial def ... : MetaM Bool` using
`MVarId.apply` + `observing?` + `mkConstWithFreshMVarLevels`. The term-mode approach is deferred
to a potential Phase 2 that would first add `HasImpView`/`HasBoxView` to Foundations.

---

### Recommended Rule Ordering

Synthesized from Teammate A's stratified search and Teammate D's depth and branching analysis:

**Priority 1 — Assumption lookup** (O(n) scan, no branching, no recursion):
Iterate `getLCtx`, skip implementation details, check `isDefEq decl.type goalTy`. If match,
`goal.assign decl.toExpr`. This handles goals with local hypotheses immediately and avoids
unnecessary axiom search.

**Priority 2 — Zero-subgoal axioms** (direct closure, no recursion, minimal cost):
```
HasAxiomImplyK.implyK, HasAxiomImplyS.implyS,
HasAxiomEFQ.efq, HasAxiomPeirce.peirce,
HasAxiomK.K, HasAxiomT.T, HasAxiom4.four,
HasAxiomB.B, HasAxiom5.five, HasAxiomD.D
```
Temporal axioms (`HasAxiomSerialFuture.serialFuture`, etc.) and bimodal axiom `HasAxiomMF.MF`
should be added here. Failed applications roll back silently via `observing?`.

**Priority 3 — One-subgoal derived rules** (one recursive call each):
```
Theorems.Combinators.identity, Theorems.Combinators.b_combinator,
Theorems.Modal.Basic.box_mono, Necessitation.nec
```
These encode Teammate D's "library lemmas" that dramatically extend coverage at low depth cost.
`identity` at depth 1 subsumes the three-step SKK construction. `box_mono` at depth 2 subsumes
the `nec` + K + MP modal macro.

**Priority 4 — Two-subgoal rules** (two recursive calls, highest branching factor):
```
Theorems.Combinators.imp_trans, ModusPonens.mp
```
MP should always be tried last. Teammate D's branching analysis shows O(n²) candidate pairs at
each MP node; trying it first causes exponential blowup even at depth 3.

**Rationale from Teammate D**: With this ordering, depth 4 covers ~65% of theorems without any
library, and depth 5 with the one-subgoal library rules covers ~75%. MP is the expensive rule
that expands coverage to ~85% at depth 8 with full library.

---

### Search Parameters

Teammates C and D provide complementary analysis. The synthesis is:

| Parameter | Teammate C | Teammate D | Synthesized |
|-----------|-----------|-----------|-------------|
| Default fuel (tactic) | 30 | 5 | **30** |
| Default depth (search) | 30 | 5 | **5 (MetaM DFS depth)** |
| Practical max | 100 | 8 | **8 (then warn user)** |

The discrepancy is resolved by distinguishing "fuel" (Teammate C's metric, counting one unit
per rule application) from "DFS depth" (Teammate D's metric, counting levels of backward
chaining). At depth 5 with 4 rule tiers, the fuel count can reach 20–30. A single fuel counter
decrementing on every rule application (Teammate C's recommended pattern) with a default of 30
aligns with Teammate D's depth-5 target: most theorem proofs consume 3–20 fuel units.

**Single fuel counter** (not two separate fast/search fuels as Teammate B suggested): Teammate
B's two-parameter design (`fastFuel`/`searchFuel`) adds complexity without observed benefit.
The stratified rule ordering (axioms before MP) achieves the same effect naturally: cheap rules
are tried first and most goals close without ever reaching MP, so MP fuel is only consumed when
necessary.

**Tactic syntax**: `hilbert_search` (default fuel 30) and `hilbert_search n` (explicit fuel).
A `hilbert_search?` verbose variant (reporting found proof via `Try this:`) is a Phase 2
nice-to-have using `Lean.MVarId.TryThis.addSuggestion`.

---

### Golden Test Cases

From Teammate D's Tier 1 list, refined by Teammates A and C's verified results and testing
patterns. These are the "must pass" tests for the implementation plan:

**Tier 1 — Must pass at default depth (hilbert_search or hilbert_search 30)**:

| # | Goal | Depth | Notes |
|---|------|-------|-------|
| 1 | `DerivableIn S (imp a (imp b a))` | 1 | ImplyK axiom — Teammate A verified |
| 2 | `DerivableIn S (imp a a)` | 1 | identity rule — Teammate A verified |
| 3 | `DerivableIn S b` from `h1 : DerivableIn S (imp a b)`, `h2 : DerivableIn S a` | 1 | MP + assumptions — Teammate A verified |
| 4 | `DerivableIn S (imp (box a) (box b))` from `h : DerivableIn S (imp a b)` | 2 | box_mono — Teammate A verified |
| 5 | `DerivableIn S (box (imp a a))` | 2 | nec(identity) — Teammate A verified |
| 6 | `DerivableIn S (HasBot.bot → φ)` under `[IntuitionisticHilbert S]` | 1 | EFQ axiom |
| 7 | `DerivableIn S (((φ → ψ) → φ) → φ)` under `[ClassicalHilbert S]` | 1 | Peirce axiom |
| 8 | `DerivableIn S (imp (imp ψ χ) (imp (imp φ ψ) (imp φ χ)))` | 3 | b_combinator via imp_trans K S |
| 9 | `DerivableIn S (imp (imp φ ψ) (imp (imp ψ φ) (imp φ ψ)))` | 4 | contrapose_imp depth 4 |
| 10 | `DerivableIn S (imp (dia φ) (dia ψ))` from `h : DerivableIn S (imp φ ψ)` | 5 | diamond_mono depth 5 |

**Tier 2 — Should pass with library lemmas in scope (hilbert_search 30)**:

| # | Goal | Depth | Notes |
|---|------|-------|-------|
| 11 | `DerivableIn S (imp (imp (imp φ ⊥) ⊥) φ)` | 5–6 | double_negation |
| 12 | `DerivableIn S (imp (box φ) (dia φ))` under `[ModalS5Hilbert S]` | 5–6 | t_box_to_diamond |
| 13 | `DerivableIn S (imp (dia φ) (box (dia φ)))` under `[ModalS5Hilbert S]` | 4 with diamond_4 in rules | axiom5_derived |

**Tier 3 — Must NOT hang (hilbert_search 5 fails gracefully)**:

| # | Goal | Reason to exclude |
|---|------|------------------|
| 14 | `demorgan_conj_neg_backward` | 12+ steps, exponential space |
| 15 | `diamond_4` | 10+ steps without library |
| 16 | `bigconj_mem_derivable` | Requires list induction |

**Negative test pattern** (from Teammate C):
```lean
example [MinimalHilbert S (F := F)] (φ : F) :
    InferenceSystem.DerivableIn S (HasImp.imp φ φ) := by
  success_if_fail_with_msg "hilbert_search failed"
    hilbert_search 0
  exact Theorems.Combinators.identity φ
```

---

### Conflicts Resolved

**Conflict 1: MetaM-only vs. two-layer term-mode + MetaM**

Teammate A found the MetaM `apply`-based approach strictly superior. Teammate B designed a
term-mode search function. Resolution: MetaM-only wins. The term-mode approach requires
`HasImpView`/`HasBoxView` typeclasses that do not exist in CSLib, while MetaM's unifier handles
formula matching transparently via `MVarId.apply`. Teammate B's analysis confirming the absence
of view typeclasses is the decisive evidence that closes the conflict in Teammate A's favor.

**Conflict 2: Default fuel — 30 (Teammate C) vs. depth 5 (Teammate D)**

Resolution: Both are correct in their own metric. Use fuel=30 for the tactic interface (Teammate
C), targeting depth≤5 for the primary test suite (Teammate D). The stratified rule ordering
means most goals close within 5 backward-chaining levels, which consumes at most ~20 fuel units.

**Conflict 3: Single fuel vs. two-parameter (Teammate B's fastFuel/searchFuel)**

Resolution: Single fuel counter (Teammates A, C, D). The stratified ordering achieves the
separation naturally. Two parameters complicate the tactic interface without observed benefit for
a first release.

---

### Gaps Identified

**Gap 1: Temporal and bimodal axioms not yet in rule table**. Teammate A's prototype includes
propositional + basic modal axioms. Temporal axioms (22+ axioms in `TemporalBXHilbert`) and
the bimodal `HasAxiomMF.MF` need to be added to the rule table. The same `apply` + `observing?`
pattern works for all of them — this is an enumeration task, not new infrastructure.

**Gap 2: And/Or axiom support**. `HasAxiomAndI`, `HasAxiomAndE1`, `HasAxiomAndE2`,
`HasAxiomOrI1`, `HasAxiomOrI2`, `HasAxiomOrE` are defined in `ProofSystem.lean` but have no
bundled proof system class yet. Phase 1 can omit these; they should be added in Phase 2 when a
bundled propositional connective system class is added to CSLib.

**Gap 3: MP branching mitigation not prototyped**. Teammate A flagged unconstrained `?φ` in
MP backward search as the main exponential risk but did not prototype a mitigation. The
recommended approach (iterative deepening or cycle detection) has not been verified. The
implementation plan should include a step to add cycle detection (tracking visited goal
expressions per search path) or limit MP depth separately.

**Gap 4: Performance benchmarking on large formulas**. The prototype was tested on small goals
with 2–4 variables. Performance on typical bimodal formulas with 8–12 subformulas has not been
measured. The implementation plan should include a performance benchmark step before the final
PR, using Teammate C's `registerTraceClass` mechanism.

**Gap 5: `hilbert_search?` verbose variant**. The `Try this:` proof-reporting variant is a
Phase 2 feature. Implementing it requires proof term reconstruction from the MetaM search trace,
which is non-trivial. Not a blocker for Phase 1.

**Gap 6: `@[hilbert_search_rule]` attribute**. Teammate A suggested an attribute for user-defined
rules (analogous to `@[simp]`). Teammate C noted that `@[aesop]` is used sparingly in CSLib and
new attributes trigger `GrindLint`. This is a Phase 2 feature; Phase 1 uses a hardcoded rule
table.

---

### Recommendations

Numbered actionable items for the revised implementation plan:

1. **Create `Cslib/Foundations/Logic/Automation/HilbertSearch.lean`** with the required
   `module` header, `public import Cslib.Init`, and
   `public import Cslib.Foundations.Logic.ProofSystem`. Split into `@[expose] public section`
   (any non-meta helpers) and `public meta section` (tactic elaboration).

2. **Implement `hilbertSearchCore : MVarId → Nat → MetaM Bool`** as a `partial def` using
   the four-priority stratified rule ordering: (1) assumption lookup, (2) zero-subgoal axioms,
   (3) one-subgoal derived rules, (4) two-subgoal rules (MP last). Use `mkConstWithFreshMVarLevels`,
   `MVarId.apply` with `{ newGoals := .nonDependentOnly }`, and `observing?` for backtracking.

3. **Add cycle detection or MP depth limit** to the MP backward search to prevent exponential
   blowup. Track a `HashSet Expr` of goal expressions on the current search path; skip a goal
   if it has already been seen in this branch. Alternatively, pass a separate `mpFuel : Nat`
   parameter that is decremented only on MP applications.

4. **Register a trace class** with `registerTraceClass ``Cslib.Logic.hilbertSearch` and add
   `withTraceNode` calls at each search step, gated on the trace flag. This enables debugging
   without impacting normal performance.

5. **Implement the tactic wrapper** using `elab "hilbert_search" n:(num)? : tactic` with
   default fuel 30. Use `throwTacticEx` on failure with the pattern:
   `m!"hilbert_search failed: no proof found within depth limit {fuel}.\nGoal: ..."`.

6. **Run `lake exe mk_all --module`** after adding the file to register it in `Cslib.lean`.

7. **Create `CslibTests/HilbertSearch.lean`** with all Tier 1 test cases (items 1–10 from
   golden test cases), Tier 2 tests (11–13), and Tier 3 failure tests (14–16). Use
   `public meta import Cslib.Foundations.Logic.Automation.HilbertSearch`. Wrap all tests in
   `namespace CslibTests.HilbertSearch`.

8. **Add all declared definitions and the tactic syntax to docstrings** to satisfy `docBlame`.
   Use `lowerCamelCase` for all Lean declaration names (e.g., `hilbertSearchCore`,
   `hilbertSearchFuel`). Do not add `@[simp]` to the search function or its helpers.

9. **Run the full CI pipeline** in order: `lake build`, `lake exe checkInitImports`,
   `lake lint`, `lake exe lint-style`, `lake test`, `lake shake`.

10. **Phase 2 scope** (not part of this plan): Add `HasImpView`/`HasBoxView` to
    `Foundations/Logic/Connectives.lean` with instances for all four concrete formula types;
    implement a generic term-mode search function using those view typeclasses; add temporal and
    bimodal axioms to the rule table; implement `hilbert_search?` verbose variant.

---

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Lean 4 tactic patterns — verified working prototype | completed | high |
| B | CSLib typeclass hierarchy and term-mode design | completed | high |
| C | Standards, best practices, pitfalls, and testing | completed | high |
| D | Proof pattern analysis and golden test cases | completed | high |

All four teammates completed with consistent confidence. Teammate A provided the most directly
implementable output (verified code). Teammate B provided the decisive negative evidence (no
view typeclasses exist) that resolved the architecture conflict. Teammate C provided the
compliance checklist. Teammate D provided the depth/branching data that calibrates the
search parameters.

---

## References

**CSLib source files examined**:
- `Cslib/Foundations/Logic/InferenceSystem.lean` — `DerivableIn`, `InferenceSystem` typeclass
- `Cslib/Foundations/Logic/ProofSystem.lean` — axiom typeclasses and bundled proof systems
- `Cslib/Foundations/Logic/Connectives.lean` — connective typeclasses
- `Cslib/Foundations/Logic/Theorems/Combinators.lean` — `identity`, `imp_trans`, `b_combinator`, `flip`
- `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` — `double_negation`, `raa`
- `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean` — `contrapose_imp`, `contraposition`
- `Cslib/Foundations/Logic/Theorems/Modal/Basic.lean` — `box_mono`, `diamond_mono`, `box_contrapose`
- `Cslib/Foundations/Logic/Theorems/Modal/S5.lean` — `axiom5_derived`, `t_box_to_diamond`, `diamond_4`
- `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` — temporal monotonicity
- `Cslib/Foundations/Logic/Theorems/BigConj.lean` — `bigconj_mem_derivable` (out of scope)
- `Cslib/Logics/Bimodal/Metalogic/Decidability/AxiomMatcher.lean` — 42-case formula pattern matcher
- `Cslib/Logics/Bimodal/Metalogic/Decidability/ProofExtraction.lean` — `buildCompositionalProof`
- `Cslib/Foundations/Relation/Attr.lean` — `public meta section` pattern reference
- `Cslib/Foundations/Semantics/LTS/Notation.lean` — `public meta section` with `elab`

**Lean 4 / Mathlib references**:
- `Mathlib.Tactic.ITauto` — G4ip algorithm (fuel-free, non-applicable to Hilbert search)
- `Mathlib.Tactic.Contrapose` — `throwTacticEx` pattern reference
- `Mathlib.Tactic.FunProp.Types` — `registerTraceClass` pattern reference
- `Aesop/Saturate.lean` — `withTraceNode` pattern reference

**CSLib compliance documentation**:
- `CONTRIBUTING.md` — naming conventions, docBlame, defLemma
- `ORGANISATION.md` — `Foundations/Logic/` directory structure
- `NOTATION.md` — notation style (not directly relevant to tactic implementation)
- `CslibTests/GrindLint.lean` — `#grind_lint check` pattern; `#guard_msgs` test format

**Prior research (Round 1)**:
- `specs/269_hilbert_search_tactic/reports/01_team-research.md` — high-level architecture
  establishing two-layer design (MetaM + TacticM); superseded by Round 2 on the question of
  whether a term-mode search layer is needed (answer: not for Phase 1)
