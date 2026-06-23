# Research Report: Task #266 (Round 3, Teammate C — Critic)

**Task**: 266 - Research Propositional/ and Foundations Improvements
**Role**: Teammate C (Critic) — identify what is being overlooked
**Artifact Number**: 04
**Date**: 2026-06-23

---

## Key Findings

### Finding 1: Tasks 281–285 Completed Phase 1 and Most of Phase 2, But Phase 2 Is Incomplete

Tasks 281–285 delivered the Hilbert-primary refactor cleanly. The following **are fully done**:

- `HilbertCompleteness.lean` — `MPL.hilbert_alg_complete`, `IPL.hilbert_alg_complete`, `CPL.hilbert_alg_complete` (plan Phase 1)
- `HilbertConservativeGlivenko.lean` — `hilbertIplConservativeOverMpl`, `hilbertGlivenko`, three algebraic bridges, `ipl_conservative_over_mpl`, `glivenko` (plan Phase 1)
- `ProofSystem.lean` Metalogic section — added by task 285, correctly documents the Hilbert-primary theorems (partial Phase 2)
- `Algebra.lean` documentation updated (task 285, partial Phase 2)

**What is NOT done from Phase 2**:

1. **`ProofSystem.lean` line 44–45 is still stale.** The text reads:
   > "Concrete `InferenceSystem` and `HasAxiom*` instances **will be** registered when derivation trees are defined."
   
   This is wrong. Propositional instances (`HilbertCl`, `HilbertInt`, `HilbertMin`) ARE registered in `Cslib/Logics/Propositional/ProofSystem/Instances.lean` and `IntMinInstances.lean`. The word "will be" is a future tense claim that is already false.

2. **`NaturalDeduction/Basic.lean` line 275 `TODO` is still present.** The docstring still says:
   > "TODO: this implementation is not capture avoiding."
   
   The plan said to clarify or remove this. PL has no binding operators; capture avoidance is not applicable to `subs`. The TODO remains and misleads contributors.

### Finding 2: Conservative.lean Has a Suspicious Unused Import

`Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean` imports `Mathlib.Tactic.ToAdditive` at line 10. There is zero usage of `@[toAdditive]` or any `toAdditive`-related tactic in the file. This import appears to be a leftover from a different file template or a copy-paste artifact. It is not caught by `lake shake` because `--keep-implied` was used during CI verification in task 285.

The file is pure algebra (IsBotFree, WithBot, coe_AlgEvaluate). `ToAdditive` has no role here. This is a minor style issue but it will appear in a strict lint run.

### Finding 3: ND-Primary Code WAS Cleanly Removed from Conservative.lean and Glivenko.lean

This was the primary concern. The refactor IS complete in this regard:

- **Conservative.lean**: Contains only `IsBotFree`, `AlgEvaluate_botFree_independent`, `GHAValid_implies_HAValid`, `HAValid_implies_BAValid`, `withBotHimp`, `instHeytingAlgebraWithBot`, `coe_AlgEvaluate`. No `ipl_conservative_over_mpl`. No imports of `Completeness` or `NaturalDeduction.Basic`.

- **Glivenko.lean**: Contains only `evalR` (private), `eval_regular_val` (private), `glivenko_algebraic`, `IsIntuitionistic (IPL ∪ CPL)` instance, `IsClassical (IPL ∪ CPL)` instance. No `glivenko`. No imports of `Completeness` or `NaturalDeduction.Basic`.

- The canonical `ipl_conservative_over_mpl` and `glivenko` now live in `HilbertConservativeGlivenko.lean` as ND corollaries derived from Hilbert-primary proofs. This is architecturally correct.

### Finding 4: Phases 3–7 of the Plan Are Entirely Not Started

The following plan items have zero implementation:

| Phase | Item | Status |
|-------|------|--------|
| 3 | `HasDia` primitive in `Foundations/Logic/Connectives.lean` | NOT STARTED |
| 4 | `Decidable (Tautology φ)` instance in `Semantics/Bool.lean` | NOT STARTED |
| 5 | GenericMCS bridge/scoping for modal logic | NOT STARTED |
| 6 | Propositional tableau extraction from Bimodal to `Foundations/` | NOT STARTED |
| 7 | `CslibTests/Propositional.lean` test coverage | NOT STARTED |

Evidence:
- `grep -rn "HasDia" Cslib/` finds only forward-reference comments in `Connectives.lean` and `Axioms.lean`, no class definition.
- No `Decidable (Tautology φ)` instance anywhere in `Cslib/`.
- `CslibTests/` has no `Propositional.lean`.
- `Foundations/Logic/PropositionalTableau.lean` does not exist.

### Finding 5: Task 266 Is Still in [RESEARCHING] Status — Incorrect

Task 266's `state.json` shows `status: "researching"` with a plan artifact (`plans/03_propositional-foundations-plan.md`) already attached. The plan was created (artifact is present), so the status should be `planned` or `implementing`, not `researching`. The status was not updated after plan creation.

### Finding 6: No Regressions from Tasks 281–285

All CI gates passed for tasks 281–285:
- `lake build` (3038 jobs, zero errors)
- `lake test` — all pass
- `lake exe checkInitImports` — no issues
- `lake exe lint-style` — no violations
- `lake shake --add-public --keep-implied --keep-prefix` — clean
- `lake_verify` on all 7 new theorems — zero axioms beyond standard `propext`, `Classical.choice`, `Quot.sound`

No regressions were introduced.

### Finding 7: Glivenko.lean Theory Instances Are in a Surprising Location

`IsIntuitionistic (IPL ∪ CPL)` and `IsClassical (IPL ∪ CPL)` instances live at the bottom of `Glivenko.lean`. These are used by `Completeness.lean` (which requires `[IsIntuitionistic T]` and `[IsClassical T]` for the Lindenbaum Heyting/Boolean algebra instances). They are needed by `derivableInCplIffDerivableProp` in `HilbertConservativeGlivenko.lean` (which calls `alg_complete_classical`).

This placement is not wrong, but it is unexpected: theory instances for `IPL ∪ CPL` live in `Glivenko.lean` rather than in `Defs.lean` or a dedicated `Theories.lean`. This is a documentation/discoverability concern, not a bug.

---

## Recommended Approach

### Immediate: Complete Phase 2 (30 minutes)

Phase 2 of the plan was only half-done by tasks 281–285. Two edits remain:

1. **`Cslib/Foundations/Logic/ProofSystem.lean`, line 44–45**: Change "Concrete `InferenceSystem` and `HasAxiom*` instances **will be** registered when derivation trees are defined." to "Concrete `InferenceSystem` and `HasAxiom*` instances **are** registered in each logic's `ProofSystem/Instances.lean` (propositional) or `ProofSystem.lean` (modal/temporal/bimodal). Modal/temporal/bimodal tags remain stubs pending derivation tree definitions."

2. **`Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`, line 275–276**: Change the `subs` docstring from "TODO: this implementation is not capture avoiding." to "Note: PL has no binding operators (no binders in propositional formulas), so capture avoidance is not applicable here. The function substitutes hypotheses in a derivation's context." This clarifies rather than implies a bug.

### Also Immediate: Remove Spurious Import (10 minutes)

3. **`Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean`, line 10**: Remove `public import Mathlib.Tactic.ToAdditive`. This import is unused (no `@[toAdditive]` in the file, no `toAdditive` tactic). It does not cause a build error but is dead weight that misleads contributors about the module's dependencies.

### Short-Term: Phases 3–7 Remain Open

Phases 3–7 are entirely unaddressed. They are actionable, correctly scoped, and low-risk:

- Phase 3 (HasDia) and Phase 4 (Decidable Tautology): Independent, additive-only, non-breaking. Each is 1–2 hours.
- Phase 6 (Tableau extraction): Code reorganization, backward-compatible if done with aliasing.
- Phase 7 (Tests): Purely additive, no regression risk.
- Phase 5 (GenericMCS): Highest risk, should remain last.

### Task Status Should Be Updated

Task 266 should be moved from `researching` to `implementing` since it has a completed plan (`plans/03_propositional-foundations-plan.md`). The current status is stale.

---

## Evidence and Examples

### Conservative.lean: No ND Code Present (Confirmed)

```
grep -n "theorem\|def\|lemma\|open" Conservative.lean
# Output: IsBotFree, AlgEvaluate_botFree_independent, GHAValid_implies_HAValid, 
#         HAValid_implies_BAValid, withBotHimp, instHeytingAlgebraWithBot, coe_AlgEvaluate
# No ipl_conservative_over_mpl, no NaturalDeduction imports
```

### Glivenko.lean: No ND Primary Proof (Confirmed)

```
grep -n "theorem\|def\|lemma" Glivenko.lean
# Output: eval_regular_val (private), glivenko_algebraic, IsIntuitionistic instance, IsClassical instance
# No glivenko, no Completeness imports
```

### Stale Comment in ProofSystem.lean (Confirmed)

```
# File: Cslib/Foundations/Logic/ProofSystem.lean
# Line 44-45:
"Concrete InferenceSystem and HasAxiom* instances will be registered when derivation trees are defined."

# But: Cslib/Logics/Propositional/ProofSystem/Instances.lean line 46:
"instance : InferenceSystem Propositional.HilbertCl ..."
```

### TODO Not Removed in NaturalDeduction/Basic.lean (Confirmed)

```
# File: Cslib/Logics/Propositional/NaturalDeduction/Basic.lean
# Line 275-276:
"/-- Substitution of a family of derivations `D` for hypotheses in the context `Γ` of `E`. TODO:
this implementation is not capture avoiding. -/"
```

### HasDia Not Implemented (Confirmed)

```
grep -rn "class HasDia" Cslib/
# (no output)

grep -rn "HasDia" Cslib/Foundations/Logic/Connectives.lean
# Only: "require a separate `HasDia` typeclass, since `□` and `◇` become independent operators."
# No class definition present.
```

---

## Confidence Level

| Finding | Confidence | Basis |
|---------|------------|-------|
| Conservative.lean / Glivenko.lean ND code removed | HIGH | Direct file inspection, grep, theorem enumeration |
| Phase 2 partially incomplete (stale comments remain) | HIGH | Direct text comparison, grep |
| Phases 3–7 not started | HIGH | grep across entire Cslib/, file listing |
| ToAdditive unused import in Conservative.lean | HIGH | grep for usage, confirmed zero hits |
| Task 266 status stale | HIGH | state.json direct read |
| No regressions from 281–285 | HIGH | CI summary from task 284/285 summaries, lake shake clean exit |
| Theory instances in Glivenko.lean are unexpected placement | MEDIUM | Architectural judgment; not a bug |
