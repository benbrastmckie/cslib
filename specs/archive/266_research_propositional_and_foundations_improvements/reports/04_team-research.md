# Research Report: Task #266

- **Task**: 266 - Research Propositional and Foundations Improvements
- **Date**: 2026-06-23
- **Mode**: Team Research (4 teammates, standard mode)
- **Completed**: 2026-06-23
- **Sources/Inputs**:
  - `specs/266_research_propositional_and_foundations_improvements/reports/04_teammate-a-findings.md`
  - `specs/266_research_propositional_and_foundations_improvements/reports/04_teammate-b-findings.md`
  - `specs/266_research_propositional_and_foundations_improvements/reports/04_teammate-c-findings.md`
  - `specs/266_research_propositional_and_foundations_improvements/reports/04_teammate-d-findings.md`
  - `specs/266_research_propositional_and_foundations_improvements/plans/03_propositional-foundations-plan.md`
- **Artifacts**: `specs/266_research_propositional_and_foundations_improvements/reports/04_team-research.md`

---

## Summary

- Tasks 281-285 fully completed Phases 1 and most of Phase 2 of the 266 plan, delivering the Hilbert-primary architecture with algebraic completeness for MPL, IPL, and CPL — a genuine architectural milestone; the codebase is zero-sorry and passes all CI gates.
- Phase 2 is not fully complete: two stale comments remain (`ProofSystem.lean` line 44-45 still says "will be registered" for instances that are already registered; `NaturalDeduction/Basic.lean` line 275 still carries a misleading capture-avoidance TODO).
- Phases 3-7 are entirely not started: `HasDia` primitive, `Decidable (Tautology φ)`, GenericMCS bridge, propositional tableau extraction, and test coverage.
- Teammate B identified additional documentation gaps beyond the plan: empty `InferenceSystem.lean` module docstring, unbundled And/Or axiom typeclasses, implicit `HasAxiomDNE` asymmetry, and a spurious `Mathlib.Tactic.ToAdditive` import in `Conservative.lean`.
- The strategic sequencing after 266 is: complete 266 Phases 3-7 first, then run task 278 (proof normalization) and task 280 (gap analysis metatask), then proceed to tasks 269 (Hilbert search tactic) and 279 (sequent calculus).

---

## Key Findings

### Primary Approach (from Teammate A)

Teammate A performed a direct codebase audit against the `03_propositional-foundations-plan.md` plan, determining exactly which phases were done and which were not.

**Phases confirmed complete (by 281-285):**
- Phase 1: `HilbertCompleteness.lean` delivers `MPL.hilbert_alg_complete`, `IPL.hilbert_alg_complete`, `CPL.hilbert_alg_complete`; `HilbertConservativeGlivenko.lean` uses these at 17+ call sites. All 15 modal systems have full `InferenceSystem` + bundled Hilbert class instances. `Temporal/ProofSystem/Instances.lean` provides `TemporalBXHilbert` with all 22 `HasAxiom*` instances. `Bimodal/ProofSystem/Instances.lean` provides `BimodalTMHilbert`.
- Phase 2 (partial): `ProofSystem.lean` lines 41-57 now document the Hilbert-primary architecture. The plan's stale comment target (line 49-50) was fixed by task 285.

**Phases confirmed not done:**
- Phase 2 (partial): `NaturalDeduction/Basic.lean` line 275 still has the capture-avoidance TODO.
- Phase 3: No `class HasDia` in `Connectives.lean`; only forward-reference comments at lines 96, 142. `Axioms.lean` lines 152, 163, 175 confirm the gap.
- Phase 4: `Bool.lean` has `Tautology`, `BoolEvaluate`, and `instDecidableBoolEvaluate`, but no `instance : Decidable (Tautology φ)`. Infrastructure is 90% assembled; the missing step is `Fintype Atom` enumeration.
- Phase 5: No `GenericMCSBridge.lean` in `Cslib/Logics/Modal/Metalogic/`. Modal, temporal, and bimodal logics still use custom derivation systems (`modalDerivationSystem`, `temporalDerivationSystem`, `bimodalDerivationSystem`) rather than `algebraicDerivationSystem`.
- Phase 6: No `Foundations/Logic/PropositionalTableau.lean`. The 8 propositional tableau rules (`andPos`, `andNeg`, `orPos`, `orNeg`, `impPos`, `impNeg`, `negPos`, `negNeg`) remain embedded in `Bimodal/Metalogic/Decidability/Tableau.lean` lines 87-101.
- Phase 7: `CslibTests/` has 13 test files, none covering `Cslib.Logics.Propositional.*`. Zero test coverage for `BoolEvaluate`, `Tautology`, or propositional derivability.

**Effort estimates (Teammate A):**
- Phase 2 partial fix: trivial (< 5 min)
- Phase 4 (`Decidable Tautology`): ~20-30 lines in `Bool.lean`
- Phase 7 (test coverage): ~30-50 lines
- Phase 3 (`HasDia`): ~15 lines
- Phase 5 (GenericMCS bridge): highest effort, non-trivial compatibility proof
- Phase 6 (tableau extraction): medium effort (~200 lines), requires generalization

### Alternative Approaches (from Teammate B)

Teammate B investigated what the plan description might be missing — specifically, issues visible from a linter/style/API perspective rather than from the plan's own enumeration.

**Clean-build status confirmed:**
- Zero sorries in `Propositional/` and `Foundations/Logic/` (verified by grep).
- `lake lint` passes: "Linting passed for Cslib."
- `lake exe lint-style` produces no output for either directory.

**Issues beyond the plan (all high confidence unless noted):**

1. **In-docstring TODO tag** (`NaturalDeduction/Basic.lean` line 275): The `TODO:` is embedded inside the docstring, not a standalone comment. `/fix-it` scans would not catch it. Recommendation: extract to a standalone `NOTE:` or `FIX:` tag below the docstring.

2. **Empty module docstring** (`InferenceSystem.lean` line 11): `/-! -/` is present but empty. All other `Foundations/Logic/` files have substantive module docstrings. `InferenceSystem.lean` defines the core `InferenceSystem` typeclass, `Default` tag, `DerivableIn`, and `Derivable` — these merit documentation.

3. **And/Or axiom typeclasses not bundled** (`ProofSystem.lean`): `MinimalHilbert`, `IntuitionisticHilbert`, and `ClassicalHilbert` bundle only implication/bot axioms and MP. `HasAxiomAndI`, `HasAxiomAndE1`, `HasAxiomAndE2`, `HasAxiomOrI1`, `HasAxiomOrI2`, `HasAxiomOrE` are registered separately for each concrete propositional tag. Code working generically over `[ClassicalHilbert S]` cannot use and/or axioms without importing additional instances. No `PropAndOrHilbert` bundled class exists. The `PropositionalConnectives` docstring (`Connectives.lean` line 128) explicitly defers this to task 173. Recommendation: once task 173 is resolved, add a `ClassicalAndOrHilbert` bundled class.

4. **`HasAxiomDNE` gap** (`Axioms.lean` line 94): `DNE` exists as an axiom formula but `ProofSystem.lean` has no corresponding `HasAxiomDNE` typeclass. DNE is derived as `double_negation` from Peirce + EFQ. The asymmetry may confuse contributors. Recommendation: add a docstring note explaining DNE is derived, not axiomatized separately.

5. **`FUntilEquiv`/`PSinceEquiv` are definitional identities** (`Axioms.lean` lines 334-341): Both BX12 and BX12' degenerate to `φ → φ` under the Burgess 1982 convention. The docstrings acknowledge this. Two typeclasses and four instance registrations exist for tautologies. Not a bug, but a design note in `TemporalBXHilbert`'s docstring would help future contributors.

6. **`SetDeduction.lean` possibly unused Mathlib import** (medium confidence): `Mathlib.Tactic.SetLike` is imported but no `SetLike` usage was found by grep. Recommendation: run `lake shake` to verify.

7. **`DeductionHelpers.lean` uses `noncomputable` broadly** (medium confidence, acceptable): All four generic deduction helpers are `noncomputable` due to `Classical.choice`. This is correct; a module docstring note would be the only improvement.

### Gaps and Shortcomings (from Critic)

Teammate C verified the refactor completeness and identified two additional concrete issues beyond what Teammate A reported.

**Confirmed complete (Critic verification):**
- `Conservative.lean` contains only algebraic content (`IsBotFree`, `AlgEvaluate_botFree_independent`, `GHAValid_implies_HAValid`, etc.) — no ND code, no `ipl_conservative_over_mpl`, no `NaturalDeduction.Basic` import. Refactor is clean.
- `Glivenko.lean` contains only `eval_regular_val`, `glivenko_algebraic`, and the `IsIntuitionistic`/`IsClassical` instances for `IPL ∪ CPL` — no `glivenko` primary proof. Refactor is clean.
- No regressions from tasks 281-285: all CI gates passed (3038 build jobs, zero errors; `lake test` all pass; `checkInitImports` clean; `lint-style` clean; `lake shake` clean; axiom check confirms only `propext`, `Classical.choice`, `Quot.sound`).

**Additional concrete issues found by Critic:**

1. **`ProofSystem.lean` line 44-45 is still stale.** Teammate A reported that lines 41-57 were updated by task 285. Teammate C found that lines 44-45 specifically still say "Concrete `InferenceSystem` and `HasAxiom*` instances **will be** registered when derivation trees are defined." — which is false since propositional instances ARE registered in `Instances.lean`. The fix: change "will be" to "are", and add a note that modal/temporal/bimodal tags remain stubs pending derivation tree definitions.

2. **`Conservative.lean` spurious import** (`Mathlib.Tactic.ToAdditive` at line 10): Zero usage of `@[toAdditive]` or `toAdditive` tactic in the file. Not caught by `lake shake --keep-implied`. A leftover from a file template or copy-paste. Should be removed.

3. **Task 266 status is stale**: `state.json` shows `status: "researching"` despite a completed plan artifact (`plans/03_propositional-foundations-plan.md`). Should be updated to `implementing`.

4. **`Glivenko.lean` theory instances are in a surprising location** (medium confidence, architectural judgment): `IsIntuitionistic (IPL ∪ CPL)` and `IsClassical (IPL ∪ CPL)` live at the bottom of `Glivenko.lean` but are needed by `Completeness.lean` and `HilbertConservativeGlivenko.lean`. Not wrong, but a discoverability concern.

**Conflict with Teammate A on ProofSystem.lean line status:** Teammate A reported "Phase 2 target (fix line 49-50) is already done" while Teammate C found lines 44-45 still contain the stale "will be" text. Resolution: Teammate C's finding takes precedence — direct text comparison confirms the stale comment persists on lines 44-45 (the original plan targeted a slightly different line range; both are within the same documentation block). Phase 2 remains partially incomplete.

### Strategic Horizons (from Teammate D)

Teammate D examined post-refactor strategic implications and optimal task sequencing for the broader proof-system roadmap.

**Architecture assessment:**
The Hilbert-primary refactor is a genuine architectural milestone. The resulting stack — `Derivable`-level completeness as the primary theorem, `SetDerivable` and ND results as corollaries — means all metalogical reasoning is Hilbert-native. This eliminates the prior `[DecidableEq Atom]` constraint that ND-based completeness required.

**GenericMCS as the strategic unlock:**
Modal, temporal, and bimodal tag types (`Modal.HilbertK`, `Temporal.HilbertBX`, `Bimodal.HilbertTM`, etc.) have no `InferenceSystem` or `MinimalHilbert` instances. `GenericMCS.lean` provides free deduction theorem and MCS properties for any `[MinimalHilbert S]`, but no modal logic can use it. Following the 120-line propositional template, each modal system would need ~100-150 lines. Once these instances exist:
- `algebraic_mcs_*` wrappers become usable, eliminating ~200-300 lines of custom MCS code per logic
- `GenericMCS.lean` becomes the canonical route for all modal completeness proofs
- `HasDeductionTheorem` automatically provides the deduction theorem for modal logics

**Task dependency sequencing (Teammate D recommendation):**

| Wave | Tasks | Rationale |
|------|-------|-----------|
| Wave 1 | 266 Phases 3+4+6+7 (parallel), 266 Phase 5 | Independent of each other; Phase 5 is the strategic modal unlock |
| Wave 2 | 278 (proof normalization), 280 (gap analysis metatask) | Depend on 266 for stable proof patterns and cleaner landscape |
| Wave 3 | 269 (Hilbert search tactic), 279 (propositional LK/LJ) | 269 benefits from cross-logic instances; 279 is the main remaining proof system gap |

**Task 226 (Mathlib upstream PR):** The Hilbert-primary refactor does not directly affect the upstream PR difficulty — the key structural divergence (primitive `.bot` vs `[Bot Atom]`) is at the formula type level, predating the proof system. However, the `canonicalBotVal` mechanism in `HilbertCompleteness.lean` strengthens the argument for primitive `.bot`. The upstream PR should scope to `Semantics/` only (not metalogic).

**Research opportunities opened by 281-285:** Curry-Howard for Hilbert systems (CSLib already has `Combinators.lean`); modal completeness via generic infrastructure (new systems at ~500 lines instead of ~2000); `Decidable (Tautology φ)` as a verified tactic backend; the Hilbert+ND+LK proof-system triad as Mathlib-contribution-worthy infrastructure.

---

## Synthesis

### Conflicts Resolved

**Conflict 1: ProofSystem.lean line 44-45 status**

Teammate A claimed "the plan's Phase 2 target (fix line 49-50) is already done." Teammate C found lines 44-45 still contain the stale "will be" text.

Resolution: Teammate C's finding takes precedence. Teammate C quoted the exact stale text and confirmed it by direct text comparison. Teammate A may have correctly observed that some documentation in lines 41-57 was updated by task 285, but lines 44-45 specifically retain the incorrect future-tense claim. Phase 2 is partially incomplete: the stale "will be" comment persists alongside the correctly-updated metalogic section.

Confidence basis: Critic provided direct quoted evidence; Teammate A's claim was a general inference from the block being "accurately described." The specific line content governs.

**No other material conflicts found.** All four teammates agreed on the following core facts: (1) Phases 1 and partial Phase 2 are complete; (2) Phases 3-7 are entirely not started; (3) zero sorries, clean CI; (4) the capture-avoidance TODO at `Basic.lean` line 275 remains.

### Gaps Identified

1. **`InferenceSystem.lean` empty module docstring** (Teammate B only; not in the plan): The core `InferenceSystem` typeclass file lacks a module-level explanation. No teammate contradicts this; the plan simply did not identify it as a target.

2. **Unbundled And/Or axiom typeclasses** (Teammate B only; deferred from task 173): `ClassicalHilbert` does not bundle `HasAxiomAndI` etc. Generic proofs over `[ClassicalHilbert S]` cannot use and/or axioms without separate instance imports. The plan does not address this; task 173 is the dependency.

3. **`HasAxiomDNE` asymmetry** (Teammate B only): `DNE` is defined as an axiom formula but has no corresponding typeclass. Only a documentation fix is needed; no implementation gap.

4. **`FUntilEquiv`/`PSinceEquiv` design note absent** (Teammate B only): `TemporalBXHilbert` lacks a docstring explaining why BX12/BX12' are included as tautologies. Minor documentation gap.

5. **Modal/temporal/bimodal `InferenceSystem` instances absent** (Teammates A and D): `GenericMCS.lean` is unused by any downstream logic because no modal tag has an `InferenceSystem` instance. Teammate D identifies this as the highest-leverage remaining infrastructure gap. Phase 5 of the plan scopes this work.

6. **Task 266 status stale** (Teammate C only): `state.json` shows `researching` but a plan exists. Should be `implementing`.

### Recommendations

**Immediate (before implementing):**

1. Update task 266 status from `researching` to `implementing` in `state.json` and regenerate `TODO.md`.

**Phase 2 completion (30 minutes, two edits):**

2. Fix `ProofSystem.lean` line 44-45: change "will be registered" to "are registered" with a note that modal/temporal/bimodal tags remain stubs.

3. Fix `NaturalDeduction/Basic.lean` line 275: remove the capture-avoidance TODO or replace with an explanatory note that PL has no binding operators and capture avoidance does not apply.

4. Remove spurious `public import Mathlib.Tactic.ToAdditive` from `Conservative.lean` line 10 (zero usage in the file).

**Documentation fixes (quick wins, beyond the plan):**

5. Fill the empty module docstring in `InferenceSystem.lean` (10-15 lines explaining `InferenceSystem`, `Default`, `DerivableIn`, `Derivable`, and the notation `S⇓a`).

6. Add a docstring note to `Axioms.DNE` explaining it is defined for completeness but DNE is derived (not axiomatized) in `ClassicalHilbert`.

7. Add a design note to `TemporalBXHilbert`'s docstring in `ProofSystem.lean` explaining why BX12/BX12' are included despite being tautologies under the Burgess 1982 convention.

**Phases 3-7 (ordered by effort × value):**

8. Phase 4: Add `instance [Fintype Atom] [DecidableEq Atom] : Decidable (Tautology φ)` to `Bool.lean` (~20-30 lines). The infrastructure is 90% assembled.

9. Phase 7: Add `CslibTests/Propositional.lean` with `#eval BoolEvaluate` examples and basic derivability smoke tests (~30-50 lines). Depends on Phase 4 for `decide` tests.

10. Phase 3: Add `class HasDia (F : Type*) where dia : F → F` with scoped notation `◇` to `Connectives.lean`; update 3 comment lines in `Axioms.lean` (~15 lines).

11. Phase 6: Extract the 8 propositional tableau rules from `Bimodal/Metalogic/Decidability/Tableau.lean` to `Foundations/Logic/PropositionalTableau.lean`, generalizing to polymorphic `[HasImp F] [HasAnd F] [HasOr F]` (~200 lines).

12. Phase 5: Scope and implement the GenericMCS bridge for modal logic. Register `InferenceSystem (Modal.HilbertK)`, `ModusPonens`, and `HasAxiom*` instances (~100-150 lines per system). This is the highest-leverage strategic investment: once done, eliminates ~200-300 lines of custom MCS code per modal logic and enables cross-logic polymorphism in the task 269 search tactic.

**Post-266 sequencing:**

13. After 266 is complete: run task 278 (proof normalization audit) and task 280 (gap analysis metatask) in parallel.

14. After 280 spawns tasks: proceed to task 269 (Hilbert search tactic, benefits from Phase 5 modal instances) and task 279 (propositional LK/LJ sequent calculus, the sole remaining proof system gap).

---

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Post-Hilbert audit: plan phase-by-phase status verification | completed | high |
| B | Alternative angles: linter, API, and documentation gaps beyond the plan | completed | high (Findings 1-7), medium (Findings 8-9) |
| C | Critic: refactor correctness verification, stale comment location, spurious import, task status | completed | high |
| D | Horizons: strategic sequencing, modal infrastructure unlock, task dependency ordering | completed | high (Findings 1-3, 5-7), medium (Findings 4, 8) |

---

## References

- `Cslib/Foundations/Logic/ProofSystem.lean` — lines 41-57 (Hilbert-primary architecture docs), lines 44-45 (stale comment)
- `Cslib/Foundations/Logic/Connectives.lean` — lines 96, 142 (HasDia forward references)
- `Cslib/Foundations/Logic/Axioms.lean` — lines 94 (DNE formula), lines 152, 163, 175 (HasDia gaps), lines 334-341 (FUntilEquiv/PSinceEquiv)
- `Cslib/Foundations/Logic/InferenceSystem.lean` — line 11 (empty module docstring)
- `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` — `algebraicDerivationSystem` (unused by modal logics)
- `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean` — lines 83-118 (noncomputable helpers)
- `Cslib/Foundations/Logic/Metalogic/SetDeduction.lean` — lines 10-11 (possibly unused SetLike import)
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` — line 275 (capture-avoidance TODO)
- `Cslib/Logics/Propositional/Semantics/Bool.lean` — line 79 (`Tautology` definition), `instDecidableBoolEvaluate`
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean` — three `hilbert_alg_complete` theorems (Phase 1 complete)
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean` — `hilbertIplConservativeOverMpl`, `hilbertGlivenko`
- `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean` — line 10 (spurious ToAdditive import)
- `Cslib/Logics/Propositional/ProofSystem/Instances.lean` — propositional InferenceSystem instances
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` — line 198 (`modalDerivationSystem`, still custom)
- `Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean` — lines 87-101 (8 propositional tableau rules)
- `CslibTests.lean` — 13 imports, none for Propositional
- `specs/266_research_propositional_and_foundations_improvements/plans/03_propositional-foundations-plan.md` — existing plan (Phases 1-7)
- `specs/state.json` — task 266 status stale at "researching"
