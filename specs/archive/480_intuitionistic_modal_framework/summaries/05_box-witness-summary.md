# Summary: Phase 2b — canonical_box_witness (Task 480)

- **Task**: 480 - Intuitionistic modal metalogic FRAMEWORK
- **Phase**: 2b (of 12), plan v4
- **Status**: [COMPLETED]
- **File**: `Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean`

## What was proved

Added a new `CanonicalBoxWitness` section to `CanonicalModel.lean`, appended after the
(preserved) `BoxWitnessSublemma` section:

- `box_context_deriv` (private, `noncomputable def`): K-closure helper -- if `Γ ⊢ ψ` then
  `(Γ.map □) ⊢ □ψ`, by induction on `Γ` via the deduction theorem + `h_K`. Used to show
  `{ψ | □ψ ∈ w.val}` is deductively closed.
- `modal_set_exclusion` (theorem): thin wrapper around `Metalogic.prime_set_exclusion`,
  mirroring `modal_prime_exclusion` (`PrimeTheory.lean`) but for the generalized
  set-exclusion (`DerivExcludes`) condition. Placed in `CanonicalModel.lean`, not
  `PrimeTheory.lean`, per the plan's postmortem constraint against re-opening Phase 1.
- `canonical_box_witness` (theorem): the corrected PAIR-shaped box witness --
  `∃ w' u, w ≤ w' ∧ canonicalR w' u ∧ φ ∉ u.val` from `(□φ) ∉ w.val`. Threads `h_K`, `h_Kdia`,
  `h_Idb` (plus the intuitionistic base and `h_andI`/`h_andE1`/`h_andE2`, inherited from
  `box_witness_pair_underivable`).

## Construction

- **Step 1**: `u` = prime extension (`modal_prime_exclusion`) of `{ψ | □ψ ∈ w.val}` excluding
  `φ`. Admissibility of `{ψ | □ψ ∈ w.val}` (deductive closure + consistency) is established
  directly rather than via `modalDeductiveClosure`: deductive closure via `box_context_deriv`;
  consistency because an inconsistency would force `□⊥ ∈ w.val`, hence (EFQ necessitated + K)
  `□φ ∈ w.val`, contradicting the hypothesis `h_notbox`.
- **Step 2**: `w'` = prime extension (`modal_set_exclusion`) of the deductive closure of
  `Γ := w.val ∪ {◇A | A ∈ u.val}`, excluding `Σ := {□B | B ∉ u.val}`. The `DerivExcludes Σ Γ`
  precondition is discharged directly by `box_witness_pair_underivable` (Phase 2b-sublemma);
  the raw union's `ModalSetConsistent` (needed for `Γ`'s admissibility) follows for free from
  `box_witness_pair_underivable` applied at the empty list (`bigOr [] = ⊥`).
- The three witness obligations then hold by construction: `w ≤ w'` and the diamond clause
  from the seeding (`w.val ∪ {◇A|A∈u.val} ⊆ closure ⊆ w'.val`); the box clause from
  `Σ`-exclusion (contrapositive via `DerivExcludes` on the singleton list `[□ψ]`); `φ ∉ u.val`
  from Step 1.

## Plan Deviations

`{ψ | □ψ ∈ w.val}`'s admissibility (Step 1's `modal_prime_exclusion` precondition) needed one
new private helper not spelled out verbatim in report 02/03: `box_context_deriv` (K-closure by
induction on the derivation context, via the deduction theorem + `h_K`). Its consistency proof
uses `h_notbox` itself (no new axiom hypothesis: an inconsistency in `{ψ|□ψ∈w.val}` would force
`□φ ∈ w.val` via EFQ + necessitation + K, contradicting `h_notbox`). No new parametric axiom
hypothesis beyond `h_K`, `h_Kdia`, `h_Idb` (+ intuitionistic base + `h_andI/h_andE1/h_andE2`,
already threaded by the sublemma) was required -- report 03's per-lemma table (row 2) is
confirmed accurate for this phase.

## Verification

- `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.CanonicalModel`: succeeded, no
  warnings.
- `lake exe checkInitImports`: passed.
- `grep -rn "\bsorry\b"` on the module: no matches.
- `lean_verify` on `canonical_box_witness` and `modal_set_exclusion`: axioms
  `[propext, Classical.choice, Quot.sound]` only (the three standard Lean/Mathlib foundational
  axioms; no new axiom introduced).
- `git diff --stat`: only `CanonicalModel.lean` changed (+215 lines, additive); Phase 1
  (`PrimeTheory.lean`), Phase 2a defs, and `PrimeExclusion.lean` (Phase 2-infra, frozen) are
  untouched.

## Next Action

Phase 2c: `canonical_diamond_witness` (mirror construction, `h_K`/`h_Kdia`/`h_Cd`, thread
`h_Idb` availability too per report 03's MEDIUM-HIGH residual note).
