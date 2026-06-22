/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Embedding.PropositionalEmbedding
public import Cslib.Logics.Bimodal.Metalogic.Core.DerivationTree
public import Cslib.Logics.Bimodal.Metalogic.Soundness.Soundness
public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.Int.Basic
public import Mathlib.Tactic.Bound.Init

/-! # Bimodal TM as a Conservative Extension of Classical Propositional Logic

This module proves that the base Bimodal system TM is a conservative extension of CPL:
any propositional formula `φ` that is derivable in TM (as `φ.toBimodal`) is already
derivable in CPL.

## Main Theorems

- `bimodal_truthAt_toBimodal_iff_evaluate`: Semantic bridge between Bimodal truthAt of
  propositional translations and PL evaluation.
- `bimodal_conservative_extension`: TM is a conservative extension of CPL.

## Proof Strategy

We use the direct semantic bridge approach (Approach B):
1. Construct a trivial TaskModel over ℤ with a constant valuation derived from `v`.
2. Prove that `truthAt M Omega τ t φ.toBimodal ↔ PL.Evaluate v φ` by structural induction.
3. Combine with TM soundness and CPL completeness.

## References

* Standard conservativity result: any purely propositional formula valid in a modal/temporal
  extension is already valid in the base propositional logic.
-/

@[expose] public section

namespace Cslib.Logic

open Bimodal Cslib.Logic.Bimodal Cslib.Logic.Bimodal.Metalogic PL

/-! ## Semantic Bridge Lemma -/

/-- **Semantic Bridge Lemma**: Bimodal truthAt of `φ.toBimodal` at any point in the trivial
model is equivalent to propositional evaluation of `φ` under the constant valuation.

We use the trivial task frame (WorldState = Unit, all task relations hold) over ℤ,
with the trivial world history (domain = everything) and the model whose valuation maps
the unique world state `()` to the propositional valuation `v`.

Proof: Structural induction on `φ`. The `and`/`or` cases follow because `toBimodal`
encodes them using the Lukasiewicz convention (`Bimodal.Formula` has no native `and`/`or`
constructors; the Lukasiewicz encoding is classically sound though not intuitionistically). -/
theorem bimodal_truthAt_toBimodal_iff_evaluate
    (v : Atom → Prop)
    (φ : PL.Proposition Atom) :
    let ℱ : TaskFrame ℤ := TaskFrame.trivialFrame
    let M : TaskModel Atom ℱ := { valuation := fun _ p => v p }
    let τ : WorldHistory ℱ := WorldHistory.trivial
    let Omega : Set (WorldHistory ℱ) := Set.univ
    truthAt M Omega τ 0 φ.toBimodal ↔ PL.Evaluate v φ := by
  induction φ with
  | atom p =>
    -- atom: truthAt M Omega τ 0 (Formula.atom p) = ∃ ht : True, v p
    simp only [PL.Proposition.toBimodal, truthAt, PL.Evaluate,
               WorldHistory.trivial]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨True.intro, h⟩⟩
  | bot =>
    -- bot: truthAt M Omega τ 0 Formula.bot = False
    simp only [PL.Proposition.toBimodal, truthAt, PL.Evaluate]
  | imp φ ψ ih1 ih2 =>
    simp only [PL.Proposition.toBimodal, PL.Evaluate, truthAt]
    exact ⟨fun h he => ih2.mp (h (ih1.mpr he)),
           fun h hm => ih2.mpr (h (ih1.mp hm))⟩
  | and φ ψ ih1 ih2 =>
    -- toBimodal: A ∧ B ↦ (A → B → ⊥) → ⊥  (Lukasiewicz encoding)
    simp only [PL.Proposition.toBimodal, PL.Evaluate, truthAt]
    constructor
    · intro h
      constructor
      · by_contra hna; exact h (fun ha _ => hna (ih1.mp ha))
      · by_contra hnb; exact h (fun _ hb => hnb (ih2.mp hb))
    · intro ⟨ha, hb⟩ h
      exact h (ih1.mpr ha) (ih2.mpr hb)
  | or φ ψ ih1 ih2 =>
    -- toBimodal: A ∨ B ↦ (A → ⊥) → B  (Lukasiewicz encoding)
    simp only [PL.Proposition.toBimodal, PL.Evaluate, truthAt]
    constructor
    · intro h
      by_cases ha : PL.Evaluate v φ
      · exact Or.inl ha
      · exact Or.inr (ih2.mp (h (fun hma => ha (ih1.mp hma))))
    · intro h hna
      cases h with
      | inl ha => exact absurd (ih1.mpr ha) hna
      | inr hb => exact ih2.mpr hb

/-! ## Conservative Extension Theorem -/

/-- **Bimodal TM Conservative Extension over CPL**:

If the bimodal translation `φ.toBimodal` is TM-derivable (at base frame class), then `φ`
is CPL-derivable.

Proof:
1. `Bimodal.ThDerivable φ.toBimodal` gives a derivation tree at `FrameClass.Base`.
2. TM soundness (`soundness`) applied to this derivation tree over ℤ with the trivial frame
   gives `truthAt M Omega τ 0 φ.toBimodal` for any choice of model/history.
3. The semantic bridge lemma `bimodal_truthAt_toBimodal_iff_evaluate` converts this to
   `PL.Evaluate v φ` for any valuation `v`.
4. CPL completeness (`prop_completeness`) then gives CPL derivability of `φ`. -/
theorem bimodal_conservative_extension {Atom : Type*} {φ : PL.Proposition Atom}
    (h : Cslib.Logic.Bimodal.Bimodal.ThDerivable φ.toBimodal) :
    PL.Derivable PropositionalAxiom φ := by
  apply prop_completeness
  intro v
  -- Unpack the derivation tree from ThDerivable
  obtain ⟨d⟩ := h
  -- Set up the trivial frame, model, and world history
  let ℱ : TaskFrame ℤ := TaskFrame.trivialFrame
  let M : TaskModel Atom ℱ := { valuation := fun _ p => v p }
  let τ : WorldHistory ℱ := WorldHistory.trivial
  let Omega : Set (WorldHistory ℱ) := Set.univ
  -- τ ∈ Omega trivially
  have h_mem : τ ∈ Omega := Set.mem_univ _
  -- Omega is shift-closed (universal set)
  have h_sc : ShiftClosed Omega := Set.univ_shift_closed
  -- Apply TM soundness (ℤ is Nontrivial, etc.)
  have hsat : truthAt M Omega τ 0 φ.toBimodal :=
    soundness [] φ.toBimodal d ℤ ℱ M Omega h_sc τ h_mem 0 (by simp)
  -- Apply the semantic bridge lemma
  exact (bimodal_truthAt_toBimodal_iff_evaluate v φ).mp hsat

end Cslib.Logic

end
