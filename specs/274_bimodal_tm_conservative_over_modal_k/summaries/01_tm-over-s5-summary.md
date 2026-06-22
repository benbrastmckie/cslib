# Implementation Summary: TM Conservative over Modal S5

- **Task**: 274 - bimodal_tm_conservative_over_modal_s5
- **Status**: [COMPLETED]
- **Session**: sess_1782161605_f646ec_274
- **Date**: 2026-06-22

## What Was Implemented

Created `/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ModalConservativity.lean` (230 lines) proving:

**Main Theorem**: `bimodal_conservative_over_s5`
```lean
theorem bimodal_conservative_over_s5 {Atom : Type} {φ : Modal.Proposition Atom}
    (h : Cslib.Logic.Bimodal.Bimodal.ThDerivable φ.toBimodal) :
    Modal.Derivable (@Modal.ModalAxiom Atom) φ
```

If the bimodal translation `φ.toBimodal` is TM-derivable, then `φ` is S5-derivable.

## Key Definitions and Lemmas

1. **`kripkeAdapterFrame`** (`World : Type`) - `TaskFrame ℤ` with `WorldState = World` and identity-only task relation `taskRel w _ u := w = u`.

2. **`kripkeAdapterHistory`** - Constant-state world history: `domain = everything`, `states t _ = w`. The `respects_task` constraint holds because `taskRel` only requires `w = w` (reflexivity via `rfl`).

3. **`kripkeAdapterOmega`** - The Omega set: `{kripkeAdapterHistory w' | m.r w w'}` (the accessibility equivalence class as histories).

4. **`kripkeAdapterOmega_shiftClosed`** - ShiftClosed for adapter Omega. Key insight: `(kripkeAdapterHistory w').timeShift Δ` is definitionally equal to `kripkeAdapterHistory w'` (both constant-state at `w'`), so `rfl` closes the goal after `subst`.

5. **`kripkeAdapterOmega_eq_of_accessible`** - S5 equivalence class stability: if `m.r w w'` and `r` is transitive + Euclidean, then `kripkeAdapterOmega m w = kripkeAdapterOmega m w'`. This is the key lemma for the box case.

6. **`bimodal_truthAt_toBimodal_iff_satisfies`** - Semantic bridge lemma (by structural induction on `φ`).

## Plan Deviations

- **Universe constraint**: Plan specified `World : Type*` but `TaskFrame.WorldState : Type` (universe 0) forces `World : Type`. Accordingly, `Atom : Type` in the main theorem (not `Type*`). This is a genuine constraint of the `TaskFrame` structure.

- **`kripkeAdapterOmega_eq_of_accessible`**: Plan listed this as an inline `h_omega_eq` local lemma inside the bridge proof, but it was extracted to a named top-level lemma for clarity and reuse.

- **`h_refl` unused in bridge lemma**: The bridge lemma doesn't use `h_refl` (reflexivity) since it's not needed for any case of `toBimodal`. It's passed as `_h_refl` to suppress the warning. The main theorem still uses `h_refl` for `h_mem`.

- **ShiftClosed proof strategy**: Instead of `ext` (no `@[ext]` for `WorldHistory`), used definitional equality: after `subst h_eq`, the goal `(kripkeAdapterHistory w').timeShift Δ ∈ kripkeAdapterOmega m w` is closed by `⟨w', h_r, rfl⟩` because Lean's definitional equality recognizes that `(kripkeAdapterHistory w').timeShift Δ = kripkeAdapterHistory w'`.

## CI Verification Results

- `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ModalConservativity`: PASSED (clean)
- `lake lint` (filtered to new file): No warnings
- `lake exe lint-style`: No issues
- `lake shake --add-public --keep-implied --keep-prefix`: No issues for new file
- `lake exe mk_all --module`: New file added to `Cslib.lean`
- `lean_verify bimodal_conservative_over_s5`: Axioms = {propext, Classical.choice, Quot.sound} (standard Lean axioms only)
- `grep sorry`: 0 occurrences in the new file
- Vacuous definitions: 0

Note: Pre-existing failures in `TemporalConservativity.lean` (task 275) and `InterSystem/Conservativity.lean` (task 276) cause `lake build` (full project) to fail, but these are unrelated to this task.
