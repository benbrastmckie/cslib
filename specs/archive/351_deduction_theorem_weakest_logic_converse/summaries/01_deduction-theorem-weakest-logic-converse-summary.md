# Implementation Summary: Task #351 - Deduction Theorem Weakest-Logic Converse

- **Task**: 351 - deduction_theorem_weakest_logic_converse
- **Status**: [COMPLETED]
- **Phases Completed**: 3/3
- **Artifacts**: 2 files modified, 1 file created

## What Was Accomplished

### Phase 1: Decouple DerivationSystem / HasDeductionTheorem from [HasBot F]

Modified `Cslib/Foundations/Logic/Metalogic/Consistency.lean`:
- Changed file-level `variable {F : Type*} [HasBot F] [HasImp F]` to `variable {F : Type*} [HasImp F]`.
- Changed `DerivationSystem (F : Type*) [HasBot F] [HasImp F]` to `DerivationSystem (F : Type*) [HasImp F]` — the structure itself no longer forces ⊥.
- Added `variable [HasBot F]` immediately before the consistency definitions so that `Consistent`, `SetConsistent`, `SetMaximalConsistent`, Lindenbaum, and closure properties retain their ⊥ constraint.
- Added `omit [HasBot F] in` before `derives_from_insert_to_cons` (private lemma that doesn't use ⊥) to suppress the `unusedSectionVars` linter warning.
- All 33+ `DerivationSystem`-referencing files built clean; no new failures introduced (pre-existing failures in `Propositional.Tableau.Classical.Completeness`, `Temporal.Metalogic.DenseCompleteness`, etc. are unchanged).

### Phase 2: Transcribe converse heart (dt_implies_implyK / dt_implies_implyS)

Created `Cslib/Foundations/Logic/Metalogic/DeductionCharacterization.lean`:
- `dt_implies_implyK`: Transcribed verbatim from research §3 — derives `⊢ A → (B → A)` from `HasDeductionTheorem D` using 2 applications of `hdt` and `D.assumption`. Uses `omit [HasBot F] in` since this theorem is truly ⊥-free.
- `dt_implies_implyS`: Transcribed verbatim from research §3 — derives the full S axiom from `HasDeductionTheorem D` using 3 applications of `hdt` and 3 applications of `D.mp`. Also ⊥-free.
- Both theorems use snake_case names, have full docstrings, and use `theorem` (Prop-valued, defLemma-safe).

### Phase 3: dtInferenceSystem bridge, MinimalHilbert instance, characterization

Added to `DeductionCharacterization.lean` (same file as Phase 2):
- `DtSystem`: Opaque tag structure `DtSystem (D : DerivationSystem F) (hdt : HasDeductionTheorem D) : Type` serving as the `InferenceSystem` index.
- `dt_inference_system`: `InferenceSystem (DtSystem D hdt) F` instance with `derivation φ := PLift (D.Deriv [] φ)`, making `DerivableIn (DtSystem D hdt) φ ↔ D.Deriv [] φ`.
- `DtSystem.dt_minimal_hilbert`: `MinimalHilbert (DtSystem D hdt) (F := F)` instance providing the three components: `ModusPonens` (via `D.mp` at `[]` and `PLift`), `HasAxiomImplyK` (via `dt_implies_implyK`), `HasAxiomImplyS` (via `dt_implies_implyS`).
- `dt_implies_minimal_hilbert`: Explicit theorem restating the instance.
- `minimal_hilbert_has_deduction_theorem`: Restates `algebraic_has_deduction_theorem` — closing the loop (forward direction of the characterization).
- Updated `Cslib.lean` barrel via `lake exe mk_all --module`.

## CI Verification

| Check | Result |
|-------|--------|
| `lake build` (task modules) | PASS |
| `lake exe checkInitImports` | Pre-existing failure (Bimodal.Perpetuity.Principles) |
| `lake lint` (modified files) | PASS (no new warnings) |
| `lake exe lint-style` (modified files) | PASS |
| `lake shake --add-public` | PASS (no new issues) |
| `lake exe mk_all --module` | PASS (barrel updated) |
| Zero `sorry` | PASS |
| Zero new axioms | PASS |
| Zero vacuous definitions | PASS |

Note: `lake test` and `lake exe checkInitImports` report pre-existing failures unrelated to this task.
The task-relevant modules (`Consistency`, `GenericMCS`, `DeductionCharacterization`, `MCSProperties`,
`Bimodal.Metalogic.Core`, `Temporal.Metalogic.DeductionTheorem`) all build clean.

## Plan Deviations

- **Phase 3 characterization theorem**: The plan called for `deduction_theorem_iff_minimal_hilbert` as a single iff. The universe polymorphism of `∃ (S : Type*), ...` made a clean direct iff awkward. Per the plan's fallback (§7): shipped the characterization as two explicit theorems (`dt_implies_minimal_hilbert` + `minimal_hilbert_has_deduction_theorem`) which together express the equivalence without the universe complexity. This is complete and sorry-free.
- **Axioms.ImplyK still needs [HasBot F]**: Even after Phase 1 decoupling, `Axioms.ImplyK`/`ImplyS` are defined in a section with `[HasBot F]`. However, since they are `abbrev`, Lean unfolds them at use sites and the `[HasBot F]` argument is not actually included (verified by the `unusedSectionVars` warning → `omit [HasBot F] in` fix). The theorems `dt_implies_implyK` and `dt_implies_implyS` are truly ⊥-free.
