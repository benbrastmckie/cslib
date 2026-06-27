/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Foundations.Logic.Metalogic.ListDeduction
public import Cslib.Foundations.Logic.Metalogic.Consistency

/-! # Algebraic Derivation System with Free Deduction Theorem

This module is the **algebraic seam** of CSLib's maximal-consistent-set (MCS)
infrastructure. It builds one generic `DerivationSystem` from `ListDeriv` and
proves `HasDeductionTheorem` once. Every logic in CSLib that reaches the algebraic
seam inherits the full MCS machinery (`closed_under_derivation`,
`implication_property`, `negation_complete`) for free.

## Architecture: predicate → type → seam

The bridge from a concrete logic to the seam involves three steps:

1. **Predicate**: `HasMinimalAxioms (Axioms : F → Prop)` witnesses that `Axioms`
   contains the K and S axiom schemata.

2. **Type**: `HilbertOf Axioms` (in each logic's `GenericMCSBridge.lean`) is an
   empty tag `inductive` type whose `InferenceSystem` maps closed derivability to
   `Nonempty (DerivationTree Axioms [] φ)`.  A `MinimalHilbert (HilbertOf Axioms)`
   instance is then constructed from the K/S/MP witnesses.

3. **Seam**: `algebraic_has_deduction_theorem` is proved once here using
   `list_deduction_theorem`. No per-logic tree induction is needed.

The deduction theorem for each structural logic then reduces to:
```
  DerivationTree ↔ algebraicDerivationSystem  (via *_deriv_iff_algebraic)
  algebraicDerivationSystem satisfies HasDeductionTheorem  (via algebraic_has_deduction_theorem)
```

## Frame-class parameterization (Option A outcome)

The seam was originally built only for single-frame-class systems (`FrameClass.Base`).
Task-366 extended the bridges to arbitrary `fc : FrameClass`:

- **Bimodal** (`Core/GenericMCSBridge.lean`): `HilbertTMFc fc` tag type with
  `MinimalHilbert (HilbertTMFc fc)` instance for any `fc`, yielding
  `bimodal_deriv_iff_algebraic_fc`.  The fc-polymorphic `deductionTheorem` and
  `deductionWithMem` in `Core/DeductionTheorem.lean` route through this bridge via
  `bimodal_has_deduction_theorem_fc`.

- **Temporal** (`Metalogic/GenericMCSBridge.lean`): `HilbertBXFc fc` tag type with
  `MinimalHilbert (HilbertBXFc fc)` instance for any `fc`, yielding
  `temporal_deriv_iff_algebraic_fc`.  The fc-polymorphic `deductionTheoremFc` and
  `deductionWithMemFc` in `DenseMCS.lean` route through this bridge via
  `temporal_has_deduction_theorem_fc`.

The K and S axioms are provable at any `fc` because their `minFrameClass = .Base`
and `FrameClass.base_le fc` holds universally.  No new axiom or `sorry` was
introduced; the generalization is conservative.

## Logics using this seam

- **Propositional**: tag `PL.HilbertOf Axioms`; bridge `PL/Metalogic/GenericMCSBridge.lean`;
  deduction theorem `PL/Metalogic/DeductionTheorem.lean`.
- **Modal**: tag `Modal.HilbertOf Axioms`; bridge `Modal/Metalogic/GenericMCSBridge.lean`;
  deduction theorem `Modal/Metalogic/DeductionTheorem.lean`.
- **Temporal (Base)**: tag `Temporal.HilbertBX`; bridge `Temporal/Metalogic/GenericMCSBridge.lean`;
  deduction theorem `Temporal/Metalogic/DeductionTheorem.lean`.
- **Temporal (fc)**: tag `HilbertBXFc fc`; same bridge; fc deduction theorem
  `Temporal/Metalogic/DenseMCS.lean`.
- **Bimodal (Base)**: tag `Bimodal.HilbertTM`;
  bridge `Bimodal/Metalogic/Core/GenericMCSBridge.lean`;
  deduction theorem `Bimodal/Metalogic/Core/DeductionTheorem.lean`.
- **Bimodal (fc)**: tag `HilbertTMFc fc`; same bridge; fc deduction theorem in same file.

## References

* `Cslib.Foundations.Logic.Metalogic.ListDeduction` — `list_deduction_theorem` (the core lemma)
* `Cslib.Foundations.Logic.Metalogic.Consistency` — MCS definitions and derived lemmas
* Isabelle `Propositional_Logic_Class.thy` — `list_deduction_logic` interpretation
-/

@[expose] public section

namespace Cslib.Logic.Metalogic.GenericMCS

open Cslib.Logic
open Cslib.Logic.Metalogic.ListImplication
open Cslib.Logic.Metalogic.ListDeduction
open Cslib.Logic.Metalogic

variable {F : Type*} [HasBot F] [HasImp F]
variable {S : Type*} [InferenceSystem S F]
variable [MinimalHilbert S (F := F)]

/-! ## Algebraic Derivation System -/

/-- The algebraic derivation system: contextual derivation defined via `ListDeriv`
(i.e., provability of the list-implication). This construction works for ANY
`MinimalHilbert` proof system, giving a `DerivationSystem` for free.

**Modal logics note**: Modal logics satisfying `MinimalHilbert` (e.g., `Modal.HilbertK`,
`Modal.HilbertS5`) can use this algebraic path directly for all propositional MCS reasoning
(lindenbaum, implication_property, negation_complete, closed_under_derivation). For
reasoning that requires the necessitation rule (e.g., box closure in canonical models),
the modal-specific `modalDerivationSystem` from
`Cslib.Logics.Modal.Metalogic.DerivationTree` must still be used, since `ListDeriv`
does not include necessitation. See `GenericMCSBridge.lean` for the full gap analysis. -/
def algebraicDerivationSystem : DerivationSystem F where
  Deriv := ListDeriv (S := S)
  weakening := fun hd hsub => list_deriv_monotonic hsub hd
  assumption := fun hmem => list_deriv_reflection hmem
  mp := fun h1 h2 => list_deriv_mp h1 h2

/-! ## Free Deduction Theorem -/

/-- The algebraic derivation system automatically has the deduction theorem.
This follows directly from `list_deduction_theorem`, which is proved once
generically using the flip lemmas. No per-logic induction on proof trees needed. -/
theorem algebraic_has_deduction_theorem :
    HasDeductionTheorem (algebraicDerivationSystem (S := S) (F := F)) := by
  intro Γ φ ψ h
  exact (list_deduction_theorem φ ψ Γ).mp h

/-! ## Convenience Wrappers -/

/-- MCS closed under derivation (algebraic version). Follows from
`SetMaximalConsistent.closed_under_derivation` with the free deduction theorem. -/
theorem algebraic_mcs_closed_under_derivation
    {G : Set F} (h_mcs : SetMaximalConsistent (algebraicDerivationSystem (S := S)) G)
    {L : List F} (h_sub : ∀ ψ ∈ L, ψ ∈ G) {φ : F}
    (h_deriv : ListDeriv (S := S) L φ) : φ ∈ G :=
  SetMaximalConsistent.closed_under_derivation
    algebraicDerivationSystem algebraic_has_deduction_theorem h_mcs h_sub h_deriv

/-- MCS implication property (algebraic version). -/
theorem algebraic_mcs_implication_property
    {G : Set F} (h_mcs : SetMaximalConsistent (algebraicDerivationSystem (S := S)) G)
    {φ ψ : F} (h_imp : HasImp.imp φ ψ ∈ G) (h_phi : φ ∈ G) : ψ ∈ G :=
  SetMaximalConsistent.implication_property
    algebraicDerivationSystem algebraic_has_deduction_theorem h_mcs h_imp h_phi

/-- MCS negation completeness (algebraic version). -/
theorem algebraic_mcs_negation_complete
    {G : Set F} (h_mcs : SetMaximalConsistent (algebraicDerivationSystem (S := S)) G)
    (φ : F) : φ ∈ G ∨ HasImp.imp φ HasBot.bot ∈ G :=
  SetMaximalConsistent.negation_complete
    algebraicDerivationSystem algebraic_has_deduction_theorem h_mcs φ

/-! ## HasMinimalAxioms Predicate Class -/

/-- Predicate-level class witnessing that an axiom predicate `Axioms : F → Prop`
contains the K and S axiom schemata.

This bridges the parameterized deduction theorem (which takes explicit `h_implyK`/`h_implyS`
witnesses) to the generic algebraic path via `MinimalHilbert (HilbertOf Axioms)`. The
`HilbertOf Axioms` wrapper type and its `MinimalHilbert` instance are built in the
per-logic bridge files (`GenericMCSBridge.lean`). -/
class HasMinimalAxioms (Axioms : F → Prop) : Prop where
  /-- K axiom (weakening): `φ → (ψ → φ)` is an axiom. -/
  hasImplyK : ∀ φ ψ, Axioms (HasImp.imp φ (HasImp.imp ψ φ))
  /-- S axiom (distribution): `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` is an axiom. -/
  hasImplyS : ∀ φ ψ χ, Axioms (HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ))
    (HasImp.imp (HasImp.imp φ ψ) (HasImp.imp φ χ)))

end Cslib.Logic.Metalogic.GenericMCS
