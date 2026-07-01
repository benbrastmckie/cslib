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

## Generic `HilbertTree` Bridge (task 452)

Beyond the predicate/type/seam architecture above, the four `GenericMCSBridge.lean` files
(Propositional, Modal, Temporal, Bimodal) also share a near-verbatim **tree-bridge trio**:
a backward helper (`unfoldListImpInTree`), the backward direction (`listDerivToTree`), and
the two consistency/MCS transfer lemmas (`*_setConsistent_iff_algebraic`,
`*_setMaxConsistent_iff_algebraic`). Unlike the predicate-level `HasMinimalAxioms` above,
this material operates on a **`Type`-valued contextual derivation-tree family**
`D : List F → F → Type*` with real `assumption`/`mp`/`weakening` constructors — the
`HilbertTree` class below captures exactly that interface, and `ClosedHilbert D` is the
generic analogue of each logic's per-file `HilbertOf`/`HilbertBX(Fc)`/`HilbertTM(Fc)` tag.

The **forward** direction (`derivTreeToList`, structural induction on the concrete tree)
stays per-logic: Lean's `induction d with | ctor ...` names concrete constructors, so it
cannot be written over an abstract `D`. Each per-logic bridge supplies its own forward map
and assembles the deriv-iff via `deriv_iff_algebraic_of_forward`.

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

/-! ## `HilbertTree`: Generic Type-Valued Derivation-Tree Bridge

The material below is parametric over an abstract `D : List F → F → Type*` and imports no
per-logic material — it is shared by every `GenericMCSBridge.lean` file (task 452). -/

variable {D : List F → F → Type*}

/-- A `Type`-valued contextual derivation-tree family closed under assumption, modus ponens,
weakening, and containing the K and S axiom schemata at the empty context. This is exactly
the interface the backward MCS-bridge direction needs; the forward direction (structural
induction on the concrete tree) stays per-logic. -/
class HilbertTree (D : List F → F → Type*) where
  /-- Every member of the context is derivable by assumption. -/
  assumption : ∀ {Γ : List F} {a : F}, a ∈ Γ → D Γ a
  /-- Modus ponens: `Γ ⊢ φ → ψ` and `Γ ⊢ φ` give `Γ ⊢ ψ`. -/
  mp : ∀ {Γ : List F} {φ ψ : F}, D Γ (HasImp.imp φ ψ) → D Γ φ → D Γ ψ
  /-- Weakening: derivability is monotone in the context under `⊆`. -/
  weakening : ∀ {Γ Δ : List F} {φ : F}, Γ ⊆ Δ → D Γ φ → D Δ φ
  /-- The K axiom schema is derivable at the empty context. -/
  axiomK : ∀ (φ ψ : F), D [] (HasImp.imp φ (HasImp.imp ψ φ))
  /-- The S axiom schema is derivable at the empty context. -/
  axiomS : ∀ (φ ψ χ : F), D [] (HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ))
    (HasImp.imp (HasImp.imp φ ψ) (HasImp.imp φ χ)))

/-- Tag type for the inference system of closed `D`-derivations: `ClosedHilbert D`'s
derivability at `φ` unfolds to `D [] φ`. The generic analogue of each per-logic
`HilbertOf`/`HilbertBX(Fc)`/`HilbertTM(Fc)` tag. -/
structure ClosedHilbert (D : List F → F → Type*) : Type where

instance (D : List F → F → Type*) : InferenceSystem (ClosedHilbert D) F where
  derivation φ := D [] φ

instance (D : List F → F → Type*) [HilbertTree (F := F) D] :
    ModusPonens (ClosedHilbert D) (F := F) where
  mp h₁ h₂ := by
    obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂
    exact ⟨HilbertTree.mp d₁ d₂⟩

instance (D : List F → F → Type*) [HilbertTree (F := F) D] :
    HasAxiomImplyK (ClosedHilbert D) (F := F) where
  implyK := ⟨HilbertTree.axiomK _ _⟩

instance (D : List F → F → Type*) [HilbertTree (F := F) D] :
    HasAxiomImplyS (ClosedHilbert D) (F := F) where
  implyS := ⟨HilbertTree.axiomS _ _ _⟩

instance (D : List F → F → Type*) [HilbertTree (F := F) D] :
    MinimalHilbert (ClosedHilbert D) (F := F) where

/-- The algebraic derivation system at the generic tag `ClosedHilbert D`. -/
@[reducible] def treeAlgDS (D : List F → F → Type*) [HilbertTree (F := F) D] :
    DerivationSystem F :=
  algebraicDerivationSystem (S := ClosedHilbert D)

/-- Generic backward helper (was `unfoldListImpInTree` × 4): given `Γ ⊢ listImp Ψ φ` and
`Ψ ⊆ Γ`, produce `Γ ⊢ φ` by iterating modus ponens with assumption trees. -/
noncomputable def unfoldListImp [HilbertTree (F := F) D] {Γ : List F} {φ : F} :
    (Ψ : List F) → D Γ (listImp Ψ φ) → (∀ a ∈ Ψ, a ∈ Γ) → D Γ φ
  | [], d, _ => by simpa only [listImp_nil] using d
  | a :: Ψ', d, h_sub => by
      simp only [listImp_cons] at d
      have ha : a ∈ Γ := h_sub a (List.mem_cons.mpr (Or.inl rfl))
      exact unfoldListImp Ψ' (HilbertTree.mp d (HilbertTree.assumption ha))
        (fun x hx => h_sub x (List.mem_cons.mpr (Or.inr hx)))

/-- Generic backward direction (was `listDerivToTree` × 4): extracts `d₀ : [] ⊢ listImp Γ φ`
from the algebraic derivation, weakens to `Γ`, then applies `unfoldListImp` to eliminate the
list-implication layers. -/
noncomputable def listDerivToTree [HilbertTree (F := F) D] {Γ : List F} {φ : F}
    (h : (treeAlgDS D).Deriv Γ φ) : D Γ φ := by
  simp only [treeAlgDS, algebraicDerivationSystem] at h
  unfold ListDeriv at h
  have d₀ : D [] (listImp Γ φ) := h.toDerivation
  exact unfoldListImp Γ (HilbertTree.weakening (List.nil_subset Γ) d₀) (fun _ ha => ha)

/-- Generic assembler for the derivability iff, taking the per-logic forward direction
(`forward`) and an identification of the per-logic tree system with `Nonempty (D Γ φ)`
(`h_tree`). -/
theorem deriv_iff_algebraic_of_forward [HilbertTree (F := F) D]
    {treeSys : DerivationSystem F}
    (h_tree : ∀ {Γ φ}, treeSys.Deriv Γ φ ↔ Nonempty (D Γ φ))
    (forward : ∀ {Γ φ}, D Γ φ → (treeAlgDS D).Deriv Γ φ)
    {Γ : List F} {φ : F} : treeSys.Deriv Γ φ ↔ (treeAlgDS D).Deriv Γ φ := by
  rw [h_tree]
  exact ⟨fun ⟨d⟩ => forward d, fun h => ⟨listDerivToTree h⟩⟩

/-- Fully generic consistency transfer (was `*_setConsistent_iff_algebraic` × 4): a pure
`DerivationSystem` corollary, independent of `HilbertTree`/`D`. -/
theorem setConsistent_iff_congr {D₁ D₂ : DerivationSystem F}
    (h : ∀ Γ φ, D₁.Deriv Γ φ ↔ D₂.Deriv Γ φ) {Ω : Set F} :
    SetConsistent D₁ Ω ↔ SetConsistent D₂ Ω := by
  unfold SetConsistent Consistent
  exact ⟨fun hc L hL hd => hc L hL ((h _ _).mpr hd),
         fun hc L hL hd => hc L hL ((h _ _).mp hd)⟩

/-- Fully generic MCS transfer (was `*_setMaxConsistent_iff_algebraic` × 4): a pure
`DerivationSystem` corollary, independent of `HilbertTree`/`D`. -/
theorem setMaxConsistent_iff_congr {D₁ D₂ : DerivationSystem F}
    (h : ∀ Γ φ, D₁.Deriv Γ φ ↔ D₂.Deriv Γ φ) {Ω : Set F} :
    SetMaximalConsistent D₁ Ω ↔ SetMaximalConsistent D₂ Ω := by
  unfold SetMaximalConsistent
  exact ⟨fun ⟨hc, hm⟩ => ⟨(setConsistent_iff_congr h).mp hc,
            fun φ hφ hi => hm φ hφ ((setConsistent_iff_congr h).mpr hi)⟩,
         fun ⟨hc, hm⟩ => ⟨(setConsistent_iff_congr h).mpr hc,
            fun φ hφ hi => hm φ hφ ((setConsistent_iff_congr h).mp hi)⟩⟩

end Cslib.Logic.Metalogic.GenericMCS
