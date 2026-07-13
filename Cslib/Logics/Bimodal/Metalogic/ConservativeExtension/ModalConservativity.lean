/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Embedding.ModalEmbedding
public import Cslib.Logics.Bimodal.Metalogic.Core.DerivationTree
public import Cslib.Logics.Bimodal.Metalogic.Soundness.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.S5.Completeness
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.Int.Basic

/-! # Bimodal TM as a Conservative Extension of Modal S5

This module proves that the base Bimodal system TM is a conservative extension of Modal S5
for the modal fragment: any modal formula `φ` that is derivable in TM (as `φ.toBimodal`)
is already derivable in S5.

## Main Theorems

- `bimodal_truthAt_toBimodal_iff_satisfies`: Semantic bridge between Bimodal truthAt of
  modal translations and modal Satisfies.
- `bimodal_conservative_over_s5`: TM is a conservative extension of S5 for the modal
  fragment.

## Proof Strategy

We use a semantic bridge approach:
1. Construct a Kripke adapter TaskFrame with `WorldState = World` and identity-only tasks.
2. For each Kripke world `w'`, construct a constant-state world history `tau_{w'}`.
3. Define `Omega` as the equivalence class `{tau_{w'} | m.r w w'}`.
4. Prove ShiftClosed for this Omega (constant histories are shift-invariant).
5. Prove the bridge lemma by structural induction on modal propositions.
   The box case uses S5 equivalence class stability: if `m.r w w'` and `r` is an S5
   equivalence relation, then `kripkeAdapterOmega m w = kripkeAdapterOmega m w'`.
6. Combine with TM soundness and S5 completeness.

## Universe Note

`TaskFrame.WorldState` has type `Type` (universe 0), which means all Kripke worlds used in
the adapter construction live in universe 0. Accordingly, this module fixes `Atom : Type`
(universe 0). The main theorem `bimodal_conservative_over_s5` thus applies when `Atom : Type`.

## References

* Standard conservativity result: TM's box axioms (T, 4, B, 5, K) exactly match S5.
-/

@[expose] public section

namespace Cslib.Logic

open Bimodal Cslib.Logic.Bimodal Cslib.Logic.Bimodal.Metalogic Modal

/-! ## Kripke Adapter Task Frame -/

/-- The Kripke adapter task frame: a `TaskFrame ℤ` with `WorldState = World` and
identity-only task relation `taskRel w d u := w = u`. This frame is used to embed
any Kripke model into the bimodal semantics.

The frame axioms hold because equality is reflexive (`nullity_identity`), transitive
(`forward_comp`), and symmetric (`converse`).

Note: `WorldState : Type` in `TaskFrame` constrains `World : Type` to universe 0. -/
def kripkeAdapterFrame (World : Type) : TaskFrame ℤ where
  WorldState := World
  taskRel := fun w _ u => w = u
  nullity_identity := fun _w _u => ⟨fun h => h, fun h => h⟩
  forward_comp := fun _w _u _v _x _y _hx _hy hwu huv => hwu.trans huv
  converse := fun _w _d _u => ⟨fun h => h.symm, fun h => h.symm⟩

/-! ## Constant-State World History Constructor -/

/-- Construct a constant-state world history for a given world `w` in the Kripke adapter
frame. The history has domain = everything and state = `w` at all times.

The `respects_task` constraint holds because `kripkeAdapterFrame`'s `taskRel` only
requires `states s _ = states t _`, i.e., `w = w`, which is `rfl`. -/
def kripkeAdapterHistory {World : Type} (w : World) :
    WorldHistory (kripkeAdapterFrame World) where
  domain := fun _ => True
  convex := fun _x _z _hx _hz _y _hxy _hyz => True.intro
  states := fun _ _ => w
  respects_task := fun _s _t _hs _ht _hst => rfl

/-! ## Kripke Adapter Omega and ShiftClosed -/

/-- The Omega set for a given Kripke model and world: the set of constant-state histories
for all worlds accessible from `w` in the model. -/
def kripkeAdapterOmega {World Atom : Type} (m : Modal.Model World Atom) (w : World) :
    Set (WorldHistory (kripkeAdapterFrame World)) :=
  {σ | ∃ w' : World, m.r w w' ∧ σ = kripkeAdapterHistory w'}

/-- The `kripkeAdapterOmega` is shift-closed: shifting a constant-state history by any
amount produces a history definitionally equal to the original constant-state history.

For any `σ ∈ kripkeAdapterOmega m w`, we have `σ = kripkeAdapterHistory w'` for some
accessible `w'`. The time-shifted history `σ.timeShift Δ` has the same domain and states
as `kripkeAdapterHistory w'`, so they are definitionally equal. -/
theorem kripkeAdapterOmega_shiftClosed {World Atom : Type} (m : Modal.Model World Atom)
    (w : World) : ShiftClosed (kripkeAdapterOmega m w) := by
  intro σ h_σ_mem Δ
  obtain ⟨w', h_r, h_eq⟩ := h_σ_mem
  subst h_eq; exact ⟨w', h_r, rfl⟩

/-- S5 equivalence class stability: if `m.r w w'` and `r` is an equivalence relation
(reflexive, transitive, Euclidean), then `kripkeAdapterOmega m w = kripkeAdapterOmega m w'`.

This is the key lemma for the box case of the semantic bridge: it ensures that the
`Omega` used for inner evaluations inside a box formula is the same set whether we
anchor at `w` or at any accessible `w'`. -/
theorem kripkeAdapterOmega_eq_of_accessible {World Atom : Type}
    (m : Modal.Model World Atom) (w w' : World)
    (h_trans : ∀ v₁ v₂ v₃, m.r v₁ v₂ → m.r v₂ v₃ → m.r v₁ v₃)
    (h_eucl : ∀ v₁ v₂ v₃, m.r v₁ v₂ → m.r v₁ v₃ → m.r v₂ v₃)
    (h_rw : m.r w w') :
    kripkeAdapterOmega m w = kripkeAdapterOmega m w' := by
  ext σ
  simp only [kripkeAdapterOmega, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, h_eucl w w' u h_rw hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, h_trans w w' u h_rw hu, rfl⟩

/-! ## Semantic Bridge Lemma -/

/-- **Semantic Bridge Lemma**: For any S5 Kripke model `m`, world `w`, and modal formula
`φ`, the bimodal truth of `φ.toBimodal` in the Kripke adapter model at
`(kripkeAdapterHistory w, 0)` with `Omega = kripkeAdapterOmega m w` is equivalent to
modal satisfaction `Satisfies m w φ`.

The proof proceeds by structural induction on `φ` with `w` generalized:
- `atom`: Both sides reduce to `m.v w p`.
- `bot`: Both sides are False.
- `imp`: Material implication; apply induction hypothesis to both parts.
- `box`: The critical S5 case. `truthAt` quantifies over all `σ ∈ kripkeAdapterOmega m w`;
  `Satisfies` quantifies over all `w'` with `m.r w w'`. These are equivalent because
  `kripkeAdapterOmega m w = {kripkeAdapterHistory w' | m.r w w'}`.
  S5 equivalence class stability (`kripkeAdapterOmega_eq_of_accessible`) ensures the
  recursive `truthAt` uses the correct `Omega` for the accessible world. -/
theorem bimodal_truthAt_toBimodal_iff_satisfies {World Atom : Type}
    (m : Modal.Model World Atom)
    (_h_refl : ∀ v, m.r v v)
    (h_trans : ∀ v₁ v₂ v₃, m.r v₁ v₂ → m.r v₂ v₃ → m.r v₁ v₃)
    (h_eucl : ∀ v₁ v₂ v₃, m.r v₁ v₂ → m.r v₁ v₃ → m.r v₂ v₃)
    (φ : Modal.Proposition Atom) (w : World) :
    let ℱ : TaskFrame ℤ := kripkeAdapterFrame World
    let M : TaskModel Atom ℱ := { valuation := fun ws => m.v ws }
    let Omega : Set (WorldHistory ℱ) := kripkeAdapterOmega m w
    truthAt M Omega (kripkeAdapterHistory w) 0 φ.toBimodal ↔
      Modal.Satisfies m w φ := by
  induction φ generalizing w with
  | atom p =>
    simp only [Modal.Proposition.toBimodal, truthAt, Modal.Satisfies, kripkeAdapterHistory]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨True.intro, h⟩⟩
  | bot =>
    simp only [Modal.Proposition.toBimodal, truthAt, Modal.Satisfies]
  | imp φ ψ ih1 ih2 =>
    simp only [Modal.Proposition.toBimodal, truthAt, Modal.Satisfies]
    exact ⟨fun h he => (ih2 w).mp (h ((ih1 w).mpr he)),
           fun h hm => (ih2 w).mpr (h ((ih1 w).mp hm))⟩
  | and φ ψ ih1 ih2 =>
    simp only [Modal.Proposition.toBimodal, Bimodal.Formula.and, truthAt, Modal.Satisfies]
    constructor
    · intro h
      constructor
      · by_contra h1
        exact h (fun hs => absurd ((ih1 w).mp hs) h1)
      · by_contra h2
        exact h (fun _ hs => absurd ((ih2 w).mp hs) h2)
    · intro ⟨h1, h2⟩ hf
      exact hf ((ih1 w).mpr h1) ((ih2 w).mpr h2)
  | or φ ψ ih1 ih2 =>
    simp only [Modal.Proposition.toBimodal, Bimodal.Formula.or, truthAt, Modal.Satisfies]
    constructor
    · intro h
      rcases Classical.em (Modal.Satisfies m w φ) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ((ih2 w).mp (h (fun hs => absurd ((ih1 w).mp hs) h1)))
    · intro h hn
      cases h with
      | inl h => exact absurd ((ih1 w).mpr h) hn
      | inr h => exact (ih2 w).mpr h
  | box φ ih =>
    simp only [Modal.Proposition.toBimodal, truthAt, Modal.Satisfies]
    constructor
    · -- Forward: (∀ σ ∈ Omega, truthAt M Omega σ 0 φ.toBimodal) → ∀ w', m.r w w' → Satisfies m w' φ
      intro h_box w' h_rw
      -- kripkeAdapterHistory w' ∈ kripkeAdapterOmega m w because m.r w w'
      have h_sigma_mem : kripkeAdapterHistory w' ∈ kripkeAdapterOmega m w :=
        ⟨w', h_rw, rfl⟩
      -- Apply h_box: truthAt M (kripkeAdapterOmega m w) (kripkeAdapterHistory w') 0 φ.toBimodal
      have h_truth := h_box (kripkeAdapterHistory w') h_sigma_mem
      -- Rewrite Omega: kripkeAdapterOmega m w = kripkeAdapterOmega m w' (S5 stability)
      rw [kripkeAdapterOmega_eq_of_accessible m w w' h_trans h_eucl h_rw] at h_truth
      -- Apply IH at w'
      exact (ih w').mp h_truth
    · -- Backward: (∀ w', m.r w w' → Satisfies m w' φ) →
      -- ∀ σ ∈ Omega, truthAt M Omega σ 0 φ.toBimodal
      intro h_sat σ h_sigma_mem
      -- σ ∈ Omega means σ = kripkeAdapterHistory w' for some accessible w'
      obtain ⟨w', h_rw, h_eq⟩ := h_sigma_mem
      subst h_eq
      -- IH at w' gives: truthAt M (kripkeAdapterOmega m w') (kripkeAdapterHistory w') 0 φ.toBimodal
      have h_truth := (ih w').mpr (h_sat w' h_rw)
      -- Rewrite Omega back to kripkeAdapterOmega m w (S5 stability)
      rw [← kripkeAdapterOmega_eq_of_accessible m w w' h_trans h_eucl h_rw] at h_truth
      exact h_truth
  | diamond φ ih =>
    simp only [Modal.Proposition.toBimodal, Bimodal.Formula.diamond, Bimodal.Formula.neg,
      Modal.Satisfies]
    constructor
    · -- Forward: ¬(∀ σ ∈ Omega, ¬truthAt ... φ.toBimodal) → ∃ w', m.r w w' ∧ Satisfies m w' φ
      intro h
      by_contra h_not_ex
      push Not at h_not_ex
      apply h
      intro σ hσ hφσ
      obtain ⟨w', h_rw, rfl⟩ := hσ
      rw [kripkeAdapterOmega_eq_of_accessible m w w' h_trans h_eucl h_rw] at hφσ
      exact h_not_ex w' h_rw ((ih w').mp hφσ)
    · -- Backward: (∃ w', m.r w w' ∧ Satisfies m w' φ) → ¬(∀ σ ∈ Omega, ¬truthAt ... φ.toBimodal)
      rintro ⟨w', h_rw, h_sat⟩ h_all
      have h_mem : kripkeAdapterHistory w' ∈ kripkeAdapterOmega m w := ⟨w', h_rw, rfl⟩
      have h_truth := (ih w').mpr h_sat
      rw [← kripkeAdapterOmega_eq_of_accessible m w w' h_trans h_eucl h_rw] at h_truth
      exact h_all (kripkeAdapterHistory w') h_mem h_truth

/-! ## Main Conservativity Theorem -/

/-- **Bimodal TM Conservative Extension over Modal S5**:

If the bimodal translation `φ.toBimodal` is TM-derivable (at base frame class), then `φ`
is S5-derivable.

Proof:
1. `Bimodal.ThDerivable φ.toBimodal` gives a derivation tree at `FrameClass.Base`.
2. TM soundness (`soundness`) applied to the Kripke adapter model gives
   `truthAt M Omega tau_w 0 φ.toBimodal`.
3. The semantic bridge lemma converts this to `Satisfies m w φ`.
4. S5 completeness (`s5_completeness`) then gives S5-derivability of `φ`.

Note: `Atom : Type` (universe 0) is required because `TaskFrame.WorldState : Type`. -/
theorem bimodal_conservative_over_s5 {Atom : Type} {φ : Modal.Proposition Atom}
    (h : Cslib.Logic.Bimodal.Bimodal.ThDerivable φ.toBimodal) :
    Modal.Derivable (@Modal.ModalAxiom Atom) φ := by
  -- Apply S5 completeness: reduce to showing φ is valid over all S5 frames
  apply s5_completeness
  intro World m h_refl h_trans h_eucl w
  -- Unpack the derivation tree from ThDerivable
  obtain ⟨d⟩ := h
  -- Set up the Kripke adapter frame, model, history, and Omega
  let ℱ : TaskFrame ℤ := kripkeAdapterFrame World
  let M : TaskModel Atom ℱ := { valuation := fun ws => m.v ws }
  let tau : WorldHistory ℱ := kripkeAdapterHistory w
  let Omega : Set (WorldHistory ℱ) := kripkeAdapterOmega m w
  -- tau ∈ Omega because m.r w w (reflexivity)
  have h_mem : tau ∈ Omega := ⟨w, h_refl w, rfl⟩
  -- Omega is shift-closed
  have h_sc : ShiftClosed Omega := kripkeAdapterOmega_shiftClosed m w
  -- Apply TM soundness to get truthAt
  have h_truth : truthAt M Omega tau 0 φ.toBimodal :=
    soundness [] φ.toBimodal d ℤ ℱ M Omega h_sc tau h_mem 0 (by simp)
  -- Apply the semantic bridge lemma to get Satisfies
  exact (bimodal_truthAt_toBimodal_iff_satisfies m h_refl h_trans h_eucl φ w).mp h_truth

end Cslib.Logic

end
