/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Metalogic.ConservativityLift
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
- `bimodal_conservative_over_cpl`: TM is a conservative extension of CPL.

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
  -- Unfold let bindings and apply the generic parametric bridge lemma.
  -- h_atom uses the existential collapse: truthAt at atom p = ∃ ht : True, v p.
  -- All other connectives (bot, imp, and, or) reduce to Iff.rfl via Lukasiewicz encoding.
  exact evaluate_iff_of_classicalBridge PL.Proposition.toBimodal
    (truthAt { valuation := fun _ p => v p }
      Set.univ (WorldHistory.trivial (D := ℤ)) (0 : ℤ))
    v
    (fun p => ⟨fun ⟨_, h⟩ => h, fun h => ⟨True.intro, h⟩⟩)
    id
    (fun _ _ => Iff.rfl)
    (fun _ _ => Iff.rfl)
    (fun _ _ => Iff.rfl)
    φ

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
theorem bimodal_conservative_over_cpl {Atom : Type*} {φ : PL.Proposition Atom}
    (h : Cslib.Logic.Bimodal.Bimodal.ThDerivable φ.toBimodal) :
    PL.Derivable PropositionalAxiom φ := by
  apply conservative_over_cpl
      (Tgt := Bimodal.Formula Atom)
      (emb := PL.Proposition.toBimodal)
      (sat := fun v ψ =>
        truthAt (ℱ := TaskFrame.trivialFrame) { valuation := fun _ p => v p }
          Set.univ WorldHistory.trivial (0 : ℤ) ψ)
  · -- bridge: bimodal_truthAt_toBimodal_iff_evaluate gives sat v (emb φ) ↔ PL.Evaluate v φ
    intro v
    exact bimodal_truthAt_toBimodal_iff_evaluate v φ
  · -- h_sat: TM soundness on the trivial ℤ-frame gives sat v (emb φ) for each v
    intro v
    obtain ⟨d⟩ := h
    let ℱ : TaskFrame ℤ := TaskFrame.trivialFrame
    let M : TaskModel Atom ℱ := { valuation := fun _ p => v p }
    let τ : WorldHistory ℱ := WorldHistory.trivial
    let Omega : Set (WorldHistory ℱ) := Set.univ
    exact soundness [] φ.toBimodal d ℤ ℱ M Omega Set.univ_shift_closed τ
      (Set.mem_univ _) 0 (by simp)

end Cslib.Logic

end
