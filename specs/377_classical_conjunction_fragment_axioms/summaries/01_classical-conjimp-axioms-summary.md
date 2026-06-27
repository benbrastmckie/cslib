# Implementation Summary: Task #377

- **Task**: 377 - classical_conjunction_fragment_axioms
- **Status**: [COMPLETED]
- **Plan**: plans/01_classical-conjimp-axioms.md
- **Artifact**: Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean

## What Was Done

All 6 phases of the plan were executed in a single agent dispatch, appending new declarations
after the existing `ClassicalImpAxiom` block in `FragmentAxioms.lean`.

### Declarations Added

**Axiom Inductives** (Phase 1):
- `ClassicalConjImpAxiom` — 6 constructors: `implyK`, `implyS`, `peirce`, `andI`, `andE1`,
  `andE2` (CPL⟨∧,→,⊤⟩)
- `ClassicalConjImpBotAxiom` — 7 constructors: same as above + `efq` (CPL⟨∧,→,⊥,⊤⟩)

**Subsumption Maps** (Phase 3):
- `ConjImpAxiom.toClassicalConjImpAxiom` (5 arms)
- `ClassicalImpAxiom.toClassicalConjImpAxiom` (3 arms, including `peirce`)
- `ClassicalConjImpAxiom.toClassicalConjImpBotAxiom` (6 arms)
- `ClassicalConjImpAxiom.toPropAxiom` (6 arms)
- `ClassicalConjImpBotAxiom.toPropAxiom` (7 arms)

**Implication Witnesses** (Phase 2):
- `ClassicalConjImpAxiom.mem_implyK`, `ClassicalConjImpAxiom.mem_implyS`
- `ClassicalConjImpBotAxiom.mem_implyK`, `ClassicalConjImpBotAxiom.mem_implyS`

**Substitution Closure** (Phase 2):
- `subst_preserves_classicalConjImpAxiom` (6-arm cases proof)
- `subst_preserves_classicalConjImpBotAxiom` (7-arm cases proof including `efq`)

**Fragment Predicate Compatibility** (Phase 5):
- `ClassicalConjImpAxiom`: 6 `IsOrBotFree` lemmas incl. `peirce` variant
  (used `imp_isOrBotFree` in the same nested form as `classicalImpAxiom_peirce_isImpTopOnly`)
- `ClassicalConjImpBotAxiom`: 7 `IsOrFree` lemmas incl. `peirce` and `efq` variants
  (`efq` uses `imp_isOrFree (by simp [Proposition.IsOrFree]) hφ`, mirroring `conjImpBotAxiom_efq_isOrFree`)

**Deduction Theorem Instances** (Phase 4):
- `classicalConjImpAxiom_hasDeductionTheorem`
- `classicalConjImpBotAxiom_hasDeductionTheorem`

## Verification

- `lake build Cslib.Logics.Propositional.ProofSystem.FragmentAxioms` — green (585 jobs)
- `lake lint` — zero warnings for modified file
- `lake exe lint-style` — zero warnings
- `lake shake --add-public --keep-implied --keep-prefix` — zero new findings from modified file
- `grep sorry` — zero sorries
- `grep "^axiom"` — zero new Lean axioms introduced

Pre-existing failures in `Cslib.Logics.Modal.Tableau.Soundness` and bimodal modules are
unrelated to this task and were confirmed present before this dispatch.

## Plan Deviations

None. All phases were implemented as described in the plan. The implementation was completed
in a single agent dispatch (batching phases 1-5 together before the CI phase). No divergences
from the plan's stated approach were required — the `peirce` compat proof for `IsOrBotFree`
and `IsOrFree` used the same `imp_is*` nesting as the sibling `classicalImpAxiom_peirce_isImpTopOnly`,
exactly as the plan described.
