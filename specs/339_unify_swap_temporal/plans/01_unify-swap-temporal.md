# Implementation Plan: Task #339

- **Task**: 339 - unify_swap_temporal
- **Status**: [COMPLETED]
- **Effort**: 4 hours
- **Dependencies**: None
- **Research Inputs**: specs/339_unify_swap_temporal/reports/01_swap-temporal-unification.md
- **Artifacts**: plans/01_unify-swap-temporal.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, CONTRIBUTING.md, NOTATION.md, ORGANISATION.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Unify the duplicated `swapTemporal` theorem surface between `Cslib/Logics/Temporal/Syntax/Formula.lean`
and `Cslib/Logics/Bimodal/Syntax/Formula.lean`. Research established that the two `swapTemporal`
*definitions* cannot be merged: they pattern-match on distinct inductive types (Temporal lacks `.box`;
Bimodal lacks `next`/`prev`/`strongRelease`/`strongTrigger`), and Lean 4 cannot extend inductives.
The only genuinely duplicated, mergeable code is the set of derived-operator *exchange theorems*
(`swapTemporal_neg`, `swapTemporal_someFuture/somePast/allFuture/allPast`) whose proofs are identical
1-line `simp only` calls (~38 lines total). This plan factors that shared theorem surface behind a
small abstraction in `Foundations/Logic/`, while leaving both concrete `swapTemporal` definitions and
their per-type recursion theorems (`swapTemporal_involution`, `atoms_swapTemporal`) in place to avoid
breaking the ~15 downstream consumers that depend on concrete `Formula.swapTemporal` unfolding.

### Research Integration

Key findings driving this plan:
- **Definitions are structurally irreducible** (distinct inductives) -- do NOT attempt to merge the
  `def swapTemporal` recursions or the inductive-recursion theorems.
- **True duplication is ~38 lines**, all trivial `simp only` proofs of derived-operator exchange.
- **`@[simp]` attributes must be preserved** on `swapTemporal_someFuture/somePast/allFuture/allPast`;
  Bimodal's `Soundness/DenseValidity.lean` has 15+ uses with heavy simp chains.
- **Downstream `simp only [Formula.swapTemporal, truthAt]` chains must keep working** -- the concrete
  `swapTemporal` equation lemmas must remain available and unchanged in unfolding behavior.
- The embedding-based approach (deriving Bimodal from Temporal via `toBimodal`) was explicitly rejected
  by research: it breaks simp chains and loses `@[simp]` behavior.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found (roadmap_flag not set). Task topic is Foundations refactoring/deduplication.

## Goals & Non-Goals

**Goals**:
- Eliminate the ~38 lines of verbatim-duplicated derived-operator exchange theorems.
- Establish a single shared source for the exchange-theorem statements in `Foundations/Logic/`.
- Preserve every downstream consumer's behavior in `Metalogic/`, `Separation/`, `Soundness/`,
  `ConservativeExtension/`, and `Decidability/` (no consumer edits required, no proof breakage).
- Preserve all `@[simp]` attribute behavior and concrete `swapTemporal` unfolding.
- Keep both concrete `swapTemporal` definitions (they cannot be merged) and document why.

**Non-Goals**:
- Merging the two `def swapTemporal` recursions (impossible: distinct inductives).
- Merging `swapTemporal_involution` or `atoms_swapTemporal` (they recurse over distinct constructor
  sets and differ by the `box` case).
- Touching Temporal-only theorems (`swapTemporal_next/prev/strongRelease/strongTrigger`).
- Introducing an embedding-based derivation of Bimodal from Temporal.
- Changing notation, public API surface, or `@[simp]` set membership for downstream simp chains.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Abstraction breaks downstream `simp only [Formula.swapTemporal]` chains | H | M | Keep concrete `def swapTemporal` and its equation lemmas untouched in BOTH files; only the derived-operator exchange theorems move. Run full `lake build` of consumers in Phase 3. |
| Loss of `@[simp]` on exchange theorems regresses Bimodal `DenseValidity` simp chains | H | M | Re-attach `@[simp]` to the per-type exchange wrappers (or re-export with `@[simp]`); verify with grep that all four `@[simp]` exchange lemmas resolve at their original names. |
| Abstraction cost (typeclass + instances) exceeds the ~38 lines saved | M | H | Phase 0 decision gate: if a generic statement cannot be written without per-type recursion plumbing that exceeds savings, fall back to the documented-mirror approach (shared statement via a parametric lemma keyed on the connective typeclasses already in `Connectives.lean`). |
| Name collisions / namespace ambiguity between Temporal and Bimodal `swapTemporal_*` | M | M | Keep per-type theorem names stable; the shared lemma lives under a distinct Foundations namespace and is specialized per type. |
| CI lint failures (lint-style, shake unused imports) from new Foundations file | M | M | Run full CI pipeline in Phase 4; fix import/style issues before marking complete. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 0 | -- |
| 2 | 1 | 0 |
| 3 | 2 | 1 |
| 4 | 3 | 2 |
| 5 | 4 | 3 |

Phases within the same wave can execute in parallel. This plan is a linear chain (each phase
validates a precondition for the next), so all waves are singletons.

---

### Phase 0: Feasibility Gate and Abstraction Design [COMPLETED]

**Goal**: Decide the exact unification mechanism before writing code, confirming it preserves
`@[simp]` and concrete-unfolding behavior. This phase produces a go/no-go decision and a concrete
signature for the shared abstraction.

**Tasks**:
- [ ] Re-read research report Section 3 (duplication table) and Section 4 (embedding rejection).
- [ ] Read `Cslib/Foundations/Logic/Connectives.lean` lines around 78-135 to confirm available
      connective typeclasses (`HasBot`, `HasImp`, `HasBox`, `HasDia`, `HasUntil`, `HasSince`,
      `HasNext`, `HasAnd`, `HasOr`).
- [ ] Determine whether the 4 derived-operator exchange theorems
      (`someFuture/somePast/allFuture/allPast`) plus `swapTemporal_neg` can be stated generically over
      a type `F` carrying the relevant `Has*` instances PLUS a `swapTemporal : F -> F` operation with
      the required homomorphism equations. Evaluate two candidate shapes:
      - **Option A (typeclass)**: a `HasSwapTemporal F` class bundling `swap : F -> F` and the
        primitive homomorphism facts (`swap` distributes over `imp`, exchanges `untl`/`snce`), from
        which the derived-operator exchanges are proved once.
      - **Option B (parametric lemma section)**: a `section` in Foundations taking `swap`, the
        connective instances, and homomorphism hypotheses as `variable`s, proving the derived
        exchanges as reusable lemmas specialized per type.
- [ ] Confirm the chosen option lets each concrete file re-export the four exchange theorems at their
      ORIGINAL names WITH `@[simp]` (required for downstream simp chains).
- [ ] **Decision gate**: if neither option can be expressed without per-type recursion plumbing that
      exceeds ~38 lines of savings, record the fallback (keep both copies, add cross-reference doc
      comments documenting the intentional mirror) and skip Phases 1-2, proceeding to a doc-only Phase.

**Timing**: 0.75 hours

**Depends on**: none

**Files to read** (no modification):
- `specs/339_unify_swap_temporal/reports/01_swap-temporal-unification.md`
- `Cslib/Foundations/Logic/Connectives.lean`
- `Cslib/Logics/Temporal/Syntax/Formula.lean` (lines 335-460)
- `Cslib/Logics/Bimodal/Syntax/Formula.lean` (lines 120-210)

**Verification**:
- A written decision (Option A, Option B, or fallback) with the exact signature of the shared
  abstraction and the list of theorems it will provide.
- Confirmation that `@[simp]` re-export at original names is achievable under the chosen option.

---

### Phase 1: Create Shared Abstraction in Foundations [NOT STARTED] *(deviation: skipped -- Phase 0 gate failed: abstraction cost +27 LOC > ~38 LOC savings; documented-mirror fallback taken)*

**Goal**: Add the shared exchange-theorem source under `Foundations/Logic/`, building in isolation
(no consumer touches yet).

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Theorems/Temporal/SwapTemporal.lean` (or extend an existing
      Foundations Temporal theorems file if one fits ORGANISATION.md conventions) implementing the
      Phase 0 decision.
- [ ] Define the shared abstraction (`HasSwapTemporal` class OR parametric `section`) with the
      primitive homomorphism interface: `swap` distributes over `imp`, exchanges `untl`<->`snce`.
- [ ] Prove the derived-operator exchange lemmas generically once: `neg`, `someFuture`<->`somePast`,
      `allFuture`<->`allPast`. Use the connective defs from `Connectives.lean` so the proofs match the
      existing `simp only [Formula.somePast, Formula.top, swapTemporal]` shape.
- [ ] Add doc comments matching CONTRIBUTING.md style; use ASCII-safe notation per NOTATION.md.
- [ ] Add the new file to the appropriate aggregator import if one exists (e.g. `Theorems.lean`).
- [ ] `lake build` the new module in isolation (build just the new target).

**Timing**: 1 hour

**Depends on**: 0

**Files to create/modify**:
- `Cslib/Foundations/Logic/Theorems/Temporal/SwapTemporal.lean` - new shared abstraction + generic
  exchange lemmas.
- `Cslib/Foundations/Logic/Theorems/Temporal.lean` or `Theorems.lean` - add import if aggregator
  exists.

**Verification**:
- `lake build Cslib.Foundations.Logic.Theorems.Temporal.SwapTemporal` succeeds (sorry-free).
- `grep -n "sorry" Cslib/Foundations/Logic/Theorems/Temporal/SwapTemporal.lean` returns nothing.

---

### Phase 2: Rewire Temporal and Bimodal to the Shared Abstraction [NOT STARTED] *(deviation: skipped -- dependent on Phase 1 which was skipped)*

**Goal**: Replace the duplicated exchange theorems in both concrete files with instances/specializations
of the shared abstraction, preserving original theorem names and `@[simp]` attributes. Keep the
concrete `def swapTemporal`, `swapTemporal_involution`, and `atoms_swapTemporal` unchanged.

**Tasks**:
- [ ] In `Cslib/Logics/Temporal/Syntax/Formula.lean`: add the import for the new Foundations module;
      provide the `HasSwapTemporal` instance / specialization for `Temporal.Formula`; replace the 4
      derived-operator exchange theorem bodies (`someFuture`, `somePast`, `allFuture`, `allPast`) and
      `swapTemporal_neg` with re-exports/specializations at their ORIGINAL names, re-attaching `@[simp]`
      to the four exchange theorems.
- [ ] In `Cslib/Logics/Bimodal/Syntax/Formula.lean`: same treatment; provide the
      `HasSwapTemporal` instance for `Bimodal.Formula` (its `swap` already handles the `box` case in
      the concrete def); replace the same 5 theorems with specializations at original names with
      `@[simp]`.
- [ ] Leave untouched in both files: `def swapTemporal`, `swapTemporal_involution`, `atoms`,
      `atoms_swapTemporal`. In Bimodal leave `swapTemporal_diamond`. In Temporal leave
      `swapTemporal_next/prev/strongRelease/strongTrigger`.
- [ ] Add a short doc comment in each `swapTemporal` definition explaining why the definitions are NOT
      shared (distinct inductive constructor sets) and pointing to the shared exchange lemmas.
- [ ] `lake build` both Formula modules.

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - replace 5 exchange theorems with specializations,
  add import + instance, keep concrete def and recursion theorems.
- `Cslib/Logics/Bimodal/Syntax/Formula.lean` - same.

**Verification**:
- `lake build Cslib.Logics.Temporal.Syntax.Formula` and
  `lake build Cslib.Logics.Bimodal.Syntax.Formula` both succeed.
- `grep -nE "swapTemporal_(someFuture|somePast|allFuture|allPast)" Cslib/Logics/Temporal/Syntax/Formula.lean Cslib/Logics/Bimodal/Syntax/Formula.lean`
  shows all four names still present, each preceded by `@[simp]`.
- Net line count in the two Formula files is reduced (target: ~30+ lines removed total).

---

### Phase 3: Downstream Consumer Verification [COMPLETED] *(deviation: altered -- only doc-comment changes made; scoped builds verify no breakage)*

**Goal**: Confirm no downstream consumer broke. This is the critical risk-retirement phase identified
by research (simp-chain fragility).

**Tasks**:
- [ ] Build all Bimodal consumers from the research report:
      `Soundness/Core.lean`, `Soundness/DenseValidity.lean`, `Core/MCSProperties.lean`,
      `Separation/TemporalClosure.lean`, `ConservativeExtension/ExtFormula.lean`.
- [ ] Build all Temporal consumers: `Soundness.lean`, `DenseSoundness.lean`, `DenseCompleteness.lean`,
      `CompletenessHelpers.lean`, `TemporalContent.lean`, `ProofSystem/Derivation.lean`,
      `GeneralizedNecessitation.lean`.
- [ ] If any `simp only [Formula.swapTemporal, ...]` chain fails: do NOT edit the consumer first;
      instead confirm the concrete equation lemmas still unfold identically and that the `@[simp]`
      exchange lemmas resolve. Only adjust the abstraction if it changed unfolding behavior.
- [ ] Run the full library build to catch any consumer not enumerated in research.

**Timing**: 0.75 hours

**Depends on**: 2

**Files to modify**:
- None expected. If a consumer requires adjustment, treat it as a regression in Phase 2's design and
  prefer fixing the abstraction over editing consumers.

**Verification**:
- `lake build` (full) succeeds with zero errors.
- `grep -rn "swapTemporal" Cslib/ | grep -i sorry` returns nothing.
- No new `sorry`/`admit` introduced anywhere: `grep -rn "sorry\|admit" Cslib/Logics/Temporal Cslib/Logics/Bimodal Cslib/Foundations/Logic/Theorems/Temporal`.

---

### Phase 4: CI Pipeline and Standards Compliance [COMPLETED] *(deviation: altered -- scoped builds pass; full lake lint/checkInitImports blocked by pre-existing unrelated failures in Propositional/Tableau/Classical/Completeness.lean)*

**Goal**: Pass the full CSLib CI pipeline and conform to library standards before completion.

**Tasks**:
- [ ] `lake build` (clean full build) succeeds.
- [ ] `lake test` (CslibTests suite) passes.
- [ ] `lake exe checkInitImports` passes (verify Cslib.Init imports for the new file).
- [ ] `lake exe lint-style` passes (style on new/modified files).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no unused-import regressions for
      the new Foundations file and the two Formula files; fix any flagged imports.
- [ ] Verify ORGANISATION.md placement of the new file and NOTATION.md compliance of any notation.
- [ ] Confirm doc comments on all new public declarations (CONTRIBUTING.md requirement).

**Timing**: 0.5 hours

**Depends on**: 3

**Files to modify**:
- Any file flagged by `lake shake` / `lint-style` (imports, style only).

**Verification**:
- All five CI commands exit 0.
- No lint-style or shake warnings on changed files.

---

## Testing & Validation

- [ ] `lake build` (full) succeeds, sorry-free.
- [ ] `lake test` passes.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake exe lint-style` passes.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` shows no new unused imports.
- [ ] All four `@[simp]` exchange lemmas (`swapTemporal_someFuture/somePast/allFuture/allPast`) resolve
      at original names in BOTH Temporal and Bimodal namespaces.
- [ ] All research-enumerated downstream consumers build unchanged.
- [ ] Net duplication reduced (target: ~30+ lines removed across the two Formula files).

## Artifacts & Outputs

- New file: `Cslib/Foundations/Logic/Theorems/Temporal/SwapTemporal.lean` (shared abstraction +
  generic derived-operator exchange lemmas).
- Modified: `Cslib/Logics/Temporal/Syntax/Formula.lean` (5 exchange theorems -> specializations).
- Modified: `Cslib/Logics/Bimodal/Syntax/Formula.lean` (5 exchange theorems -> specializations).
- Possibly modified: a Foundations aggregator import file.

## Rollback/Contingency

- **Per-phase isolation**: each phase ends at a green `lake build`. Revert is `git checkout` of the
  touched files for that phase.
- **Phase 0 fallback (recommended escape hatch)**: if the abstraction's cost exceeds its savings or
  cannot preserve `@[simp]`/unfolding, abandon the typeclass approach and instead add cross-reference
  doc comments documenting the intentional mirror in both files (zero functional change, zero
  downstream risk). This satisfies the "unify/document the shared core" intent at minimal risk and
  aligns with the research recommendation to treat the residual duplication as structural.
- **Phase 3 regression**: if a downstream simp chain breaks and cannot be fixed by restoring exact
  unfolding behavior in the abstraction, roll back Phase 2 in both Formula files (keeping the new
  Foundations file unused or removing it) and fall back to the documented-mirror approach.
- **Full abort**: `git checkout Cslib/Logics/Temporal/Syntax/Formula.lean Cslib/Logics/Bimodal/Syntax/Formula.lean`
  and delete the new Foundations file restores the pre-task state.
