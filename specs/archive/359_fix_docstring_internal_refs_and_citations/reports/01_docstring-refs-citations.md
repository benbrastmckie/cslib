# Research Report: Fix Docstring Internal Refs and Citations (Task 359)

**Session**: sess_1782522754_5f0817_359
**Task type**: cslib
**Date**: 2026-06-26
**Source**: /vet of tasks 344, 351, 354

## Objective

Remove internal development task-number references from three docstrings and replace a
Zulip-only citation with a published source. All four edits are docstring-only (no proof
or definition changes), so the zero-debt gate is trivially satisfied.

## File Locations (Confirmed)

| File | Path |
|------|------|
| HilbertStrongCompleteness | `Cslib/Logics/Propositional/Semantics/Algebra/HilbertStrongCompleteness.lean` |
| MplConservativeChain | `Cslib/Logics/Propositional/Semantics/Algebra/MplConservativeChain.lean` |
| DeductionCharacterization | `Cslib/Foundations/Logic/Metalogic/DeductionCharacterization.lean` (NOT under Logics/) |

Note: the task description placed DeductionCharacterization under `Cslib/Logics/`. It is
actually under `Cslib/Foundations/Logic/Metalogic/`. The Zulip citation is at line 35
(the `## References` block opens at line 33), not line 36 — close enough; locate by content.

## Reuse Check

No new abstractions involved. The named theorems/lemmas the task references already exist
in the codebase and are confirmed by grep:

- `hilbert_alg_complete_theory` — defined at `HilbertCompleteness.lean:64` (the "task 341" target).
- `liftDerivationTree` — defined at `ConjImpConservative.lean:59` (a "task 353" target; already named in the docstring).
- `ConjImpBotMinAxiom.toMinPropAxiom` — defined at `FragmentAxioms.lean:446` (a "task 353" target; already named in the docstring).
- BibKey `TroelstraSchwichtenberg2000` already exists in `references.bib:832` (Troelstra & Schwichtenberg, *Basic Proof Theory*, 2nd ed., Cambridge, 2000).

## Replacement 1: HilbertStrongCompleteness.lean — three "task 341" references

The named theorem the docstrings allude to is `hilbert_alg_complete_theory` (already named
inline). Only the phrase "task 341" / "task-341" must be removed; replace with a reference
to the named theorem and its module.

### Line 31 (in the `## Main Results` block)

Current:
```
- `hilbert_alg_strong_complete_theory_empty`: Recovery lemma showing that the `Γ = ∅`
  case recovers task 341's `hilbert_alg_complete_theory` (regression guard).
```
Replacement:
```
- `hilbert_alg_strong_complete_theory_empty`: Recovery lemma showing that the `Γ = ∅`
  case recovers `hilbert_alg_complete_theory` (regression guard).
```

### Line 111 (section header) and lines 113–119 (the lemma docstring)

Current line 111:
```
/-! ## Recovery of Task-341 Weak Completeness -/
```
Replacement line 111:
```
/-! ## Recovery of Weak Completeness -/
```

Current lines 113–119:
```
/-- **Recovery Lemma**: the `Γ = ∅` case of `hilbert_alg_strong_complete_theory`
recovers task-341's `hilbert_alg_complete_theory`.

When `Γ = ∅`, the `SatisfiesTheory (AlgEvaluate v bot_val) ∅` premise is vacuously true,
and `SetDerivable Axioms ∅ φ` collapses to `Derivable Axioms φ` via `SetDerivable_empty_iff`.
This certifies that the strong completeness theorem is a genuine extension of task 341's
result (regression guard). -/
```
Replacement lines 113–119:
```
/-- **Recovery Lemma**: the `Γ = ∅` case of `hilbert_alg_strong_complete_theory`
recovers `hilbert_alg_complete_theory` (the weak/empty-context completeness theorem in
`HilbertCompleteness.lean`).

When `Γ = ∅`, the `SatisfiesTheory (AlgEvaluate v bot_val) ∅` premise is vacuously true,
and `SetDerivable Axioms ∅ φ` collapses to `Derivable Axioms φ` via `SetDerivable_empty_iff`.
This certifies that the strong completeness theorem is a genuine extension of the
weak-completeness result (regression guard). -/
```

## Replacement 2: MplConservativeChain.lean — "task 353" reference (line 229)

Both named items (`liftDerivationTree`, `ConjImpBotMinAxiom.toMinPropAxiom`) are already
cited by name; only the parenthetical "(from task 353)" is the internal reference. Replace
with the defining modules.

Current (lines 227–229):
```
The forward direction is the direct conservativity `hilbertMplConservativeOverConjImpBot_direct`.
The backward direction lifts via the axiom subsumption `ConjImpBotMinAxiom → MinPropAxiom`
using `liftDerivationTree` and `ConjImpBotMinAxiom.toMinPropAxiom` (from task 353). -/
```
Replacement:
```
The forward direction is the direct conservativity `hilbertMplConservativeOverConjImpBot_direct`.
The backward direction lifts via the axiom subsumption `ConjImpBotMinAxiom → MinPropAxiom`
using `liftDerivationTree` (`ConjImpConservative.lean`) and
`ConjImpBotMinAxiom.toMinPropAxiom` (`FragmentAxioms.lean`). -/
```

## Replacement 3: DeductionCharacterization.lean — Zulip-only citation (line ~35)

The module proves the converse of the deduction-theorem characterization: a derivation
system with the deduction theorem yields the K and S axioms, hence is an instance of
`MinimalHilbert` (implicational IPL). This is exactly the classical correspondence between
the deduction theorem and combinatory completeness (the K and S combinators), a standard
result in Troelstra & Schwichtenberg, *Basic Proof Theory*, Ch. 2 (Hilbert-type systems
and the deduction theorem). BibKey `TroelstraSchwichtenberg2000` already exists and is
used elsewhere in the library (e.g. `SequentCalculus/Defs.lean:35`), with the established
citation format:
`[A. S. Troelstra, H. Schwichtenberg, *Basic Proof Theory*][TroelstraSchwichtenberg2000]`.

Recommendation: **supplement** (keep the Zulip attribution for provenance, add the
published source). The task allows replace-or-supplement; supplementing preserves the
contributor credit while satisfying the published-source requirement.

Current `## References` block (lines 33–36):
```
## References

* B. Doty, CSLib Zulip Temporal Logic thread, 2026-06-25.
-/
```
Replacement:
```
## References

* [A. S. Troelstra, H. Schwichtenberg, *Basic Proof Theory*][TroelstraSchwichtenberg2000], Ch. 2.
* B. Doty, CSLib Zulip Temporal Logic thread, 2026-06-25.
-/
```

If a pure replacement is preferred over supplementation, drop the second bullet.

## Verification Plan (for implementation)

1. Apply the four edits above (docstring-only).
2. `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertStrongCompleteness`
3. `lake build Cslib.Logics.Propositional.Semantics.Algebra.MplConservativeChain`
4. `lake build Cslib.Foundations.Logic.Metalogic.DeductionCharacterization`
5. Confirm no remaining matches: `grep -rn "task 341\|task-341\|task 353" <three files>`

## Risks / Notes

- DeductionCharacterization line number drifted (~35 not 36); locate by content, not line number.
- HilbertStrongCompleteness has FOUR task-341 occurrences (lines 31, 111, 114, 118), one more
  than the three named in the task description (line 111 section header was omitted). All four
  are addressed above.
- No proof obligations, no new axioms, no sorries — pure documentation edit.
