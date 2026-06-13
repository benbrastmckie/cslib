# Execution Summary: Propositional Five-Primitive Refactor (Task 173)

- **Task**: 173 - propositional_five_primitive_refactor
- **Status**: [IMPLEMENTING] -> phases 5-7 completed
- **Phases Completed This Session**: 5, 6, 7 (phases 1-4 were completed in prior session)
- **Artifacts**: plans/01_implementation-plan.md, summaries/01_execution-summary.md

## Summary

Completed phases 5-7 of the five-primitive propositional logic refactor, extending the Hilbert ↔ ND equivalence bridge, the metalogic soundness/completeness proofs, and the external embeddings to handle the new `and`/`or` constructors.

## Phase 5: ND-Hilbert Equivalence Bridge

Fixed `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean`:
- Added missing import `HilbertDerivedRules`
- Updated `nd_to_hilbert_deriv` to accept all 9 axiom witnesses (K, S, EFQ, andI, andE1, andE2, orI1, orI2, orE)
- Updated `hilbert_iff_nd` with all 9 witnesses
- Updated `hilbert_iff_nd_int` and `hilbert_iff_nd_cl` with and/or axiom constructors

## Phase 6: Metalogic Soundness and Completeness

### Soundness files (all fully proved, no sorry):
- `Soundness.lean`: Added 6 cases to `prop_axiom_sound` (andI, andE1, andE2, orI1, orI2, orE)
- `IntSoundness.lean`: Added 6 cases to `int_axiom_sound` (Kripke soundness; orE uses `le_trans`)
- `MinSoundness.lean`: Added 6 cases to `min_axiom_sound` (same structure as Int)

### Completeness files (and cases fully proved; or backward has sorry):
- `Completeness.lean`: Added `and`/`or` cases to `prop_truth_lemma` (classical MCS canonical model)
  - Both `and` directions fully proved using andI/andE1/andE2 derivations
  - Both `or` directions fully proved (or backward uses `prop_negation_complete` + orE derivation)
- `IntCompleteness.lean`: Added `and`/`or` cases to `int_truth_lemma` (DCCS canonical model)
  - `and` forward/backward: fully proved using andI/andE1/andE2 with DCCS closure
  - `or` forward: fully proved using orI1/orI2 with DCCS closure
  - `or` backward: **sorry** -- requires disjunction property of IPC (prime theories, task 174)
- `MinCompleteness.lean`: Same structure as IntCompleteness
  - `or` backward: **sorry** -- same gap as IntCompleteness

### Design note on or-backward:
The canonical model for intuitionistic/minimal completeness uses DCCSs ordered by inclusion.
The truth lemma for `or` backward requires: `(A ∨ B) ∈ S → A ∈ S ∨ B ∈ S`, which is the
disjunction property for IPC. This fails for general DCCSs -- prime theories are needed.
Task 174 should upgrade to prime theories to close this gap.

## Phase 7: External Embeddings and CI

### Modal/FromPropositional.lean:
- Added `and`/`or` cases to `toModal` using Lukasiewicz encoding (Modal formula type has no
  native and/or constructors; those require task 174)
- `and φ ψ → φ.toModal.and ψ.toModal` (Modal.and is already a Lukasiewicz abbrev)
- `or φ ψ → φ.toModal.or ψ.toModal` (Modal.or is already a Lukasiewicz abbrev)
- Added `toModal_and`, `toModal_or` simp lemmas
- `modal_satisfies_toModal_iff_evaluate` and/or cases: **sorry** (semantic coherence requires
  `¬(A → ¬B) ↔ A ∧ B` which is classically but not intuitionistically valid; task 174)

### Temporal/FromPropositional.lean:
- Added `and`/`or` cases to `toTemporal` using explicit Lukasiewicz encoding
- Added `toTemporal_and`, `toTemporal_or` simp lemmas
- No semantic coherence theorem in Temporal, so no additional sorry needed

### Bimodal/Embedding/PropositionalEmbedding.lean:
- Added `and`/`or` cases to `toBimodal` using Lukasiewicz encoding
- Added `toBimodal_and`, `toBimodal_or` simp lemmas
- `toModal_toBimodal` and `toTemporal_toBimodal` induction proofs pass with `simp [*]`

## CI Verification

- `lake build`: passes (2976 jobs)
- `lake test`: passes (8976 jobs)
- `lake exe checkInitImports`: passes (exit code 0)
- `lake exe lint-style`: passes (exit code 0)
- `lake lint`: 837 errors (all pre-existing in Bimodal files; none introduced by task 173)

## Sorry Inventory

| File | Location | Reason | Blocking Task |
|------|----------|--------|---------------|
| `IntCompleteness.lean` | `int_truth_lemma` or-backward | Disjunction property (prime theories) | 174 |
| `MinCompleteness.lean` | `min_truth_lemma` or-backward | Same | 174 |
| `Modal/FromPropositional.lean` | `modal_satisfies_toModal_iff_evaluate` and case | Classical equivalence `¬(A→¬B)↔A∧B` | 174 |
| `Modal/FromPropositional.lean` | `modal_satisfies_toModal_iff_evaluate` or case | Classical equivalence `(¬A→B)↔A∨B` | 174 |

## Plan Deviations

- **Phase 6 IntCompleteness/MinCompleteness**: or backward direction uses sorry rather than a
  full proof. The plan noted this as a risk and explicitly allowed sorry with a follow-up task.
  The gap is documented as requiring prime theories (disjunction property).
- **Phase 7 Modal semantic coherence**: sorry rather than classical proofs. The user explicitly
  requested no classical assumptions, and the plan allowed sorry for task 174 to address with
  native constructors.
- **Phase 7 Temporal**: No semantic coherence theorem existed or was attempted (unlike Modal).
  Only the syntactic embedding and simp lemmas were added.
