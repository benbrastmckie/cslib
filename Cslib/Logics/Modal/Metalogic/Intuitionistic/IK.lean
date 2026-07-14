/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.Completeness

/-! # IK: Intuitionistic Modal Logic K (Soundness + Completeness)

This module instantiates the task-480 birelational canonical-model framework at Simpson's `IK`
(Intuitionistic modal logic K, [Simpson1994] Ch. 3), the base intuitionistic analogue of
classical `K`. `IK` extends intuitionistic propositional logic with five modal axiom schemata
(`k1`-`k5`) formed from the box/diamond interaction ("K", "Kdia") and Fischer-Servi
("Cd", "Idb") axioms plus the intuitionistic falsum-diamond axiom "Nd". These five schemata are
*exactly* the task-480 framework's five modal hypotheses `{h_K, h_Kdia, h_Cd, h_Idb, h_dbot}`
(report 01, adversarially verified): `h_dbot` **is** Nd, not an additional axiom, and no `IK`
axiom needs a frame condition beyond up/down confluence (`BFrame.f1`/`BFrame.f2`, task 490)
already present in the framework.

## Main Definitions

- `IKModalAxiom`: the axiom schemata of `IK` -- 9 intuitionistic propositional schemata
  (mirroring `IntPropAxiom`) plus the 5 modal schemata `k`/`kdia`/`cd`/`idb`/`dbot`
  (`k1`-`k5` of [Simpson1994]).
- `ik_axiom_sound`: every `IKModalAxiom` instance is `IValid` (birelational, intuitionistic
  falsum semantics).
- `ik_soundness`/`ik_soundness_derivable`: birelational soundness for `IK`, by structural
  induction on `DerivationTree IKModalAxiom` -- the only genuinely new proof in this file.
- `ik_completeness`/`ik_consistent`/`ik_soundness_completeness`: pure instantiations of the
  task-480 parametric completeness (`ivalid_completeness`) at `Axioms := IKModalAxiom`.

## Implementation Notes

- **Nd (`dbot`) needs no frame condition.** Under `IValid`, `botForces` is fixed to
  `fun _ => False`, so `BForces _ _ (fun _ => False) w' (◇⊥)` reduces to `∃ u, r w' u ∧ False`,
  which is `False` at every world; `◇⊥ → ⊥` is therefore vacuously valid.
- **Idb (`k4`) consumes `BFrame.f2`** (down-confluence): the witness world for the `◇φ`
  premise is relocated upward along `≤` so that the `Idb` hypothesis (instantiated at that
  relocated world) can be applied.
- No new canonical-model machinery is introduced: `canonicalBModel`, `canonical_f1`/
  `canonical_f2`, `canonical_truth_lemma`, `modal_prime_exclusion`, and
  `ivalid_completeness`/`mvalid_completeness` (all from `Completeness.lean` and its
  dependencies) are reused wholesale.

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (axioms `k1`-`k5`, birelational semantics, `IValid`).
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43,
  Lemma 5.5.
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

variable {Atom : Type u}

/-! ## The `IK` Axiom Schemata -/

/-- Axiom schemata for intuitionistic modal logic `IK` ([Simpson1994], Ch. 3): the 9
intuitionistic propositional schemata (mirroring `IntPropAxiom`) plus the 5 modal schemata
`k1`-`k5`. The five modal constructors are exactly the task-480 framework's five modal
hypotheses `{h_K, h_Kdia, h_Cd, h_Idb, h_dbot}` (report 01 Deliverable 1): `k` = `k1`/Kb,
`kdia` = `k2`/Kd, `cd` = `k3`/Cd (Fischer-Servi, ◇ over ∨), `idb` = `k4`/Idb (Fischer-Servi
box), `dbot` = `k5`/Nd (`◇⊥ → ⊥`). -/
inductive IKModalAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)`. -/
  | implyK (φ ψ : Proposition Atom) :
      IKModalAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`. -/
  | implyS (φ ψ χ : Proposition Atom) :
      IKModalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Ex falso quodlibet: `⊥ → φ`. -/
  | efq (φ : Proposition Atom) :
      IKModalAxiom (Proposition.bot.imp φ)
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)`. -/
  | andI (φ ψ : Proposition Atom) :
      IKModalAxiom (Cslib.Logic.Axioms.AndI φ ψ)
  /-- Left conjunction elimination: `φ ∧ ψ → φ`. -/
  | andE1 (φ ψ : Proposition Atom) :
      IKModalAxiom (Cslib.Logic.Axioms.AndE1 φ ψ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ`. -/
  | andE2 (φ ψ : Proposition Atom) :
      IKModalAxiom (Cslib.Logic.Axioms.AndE2 φ ψ)
  /-- Left disjunction introduction: `φ → φ ∨ ψ`. -/
  | orI1 (φ ψ : Proposition Atom) :
      IKModalAxiom (Cslib.Logic.Axioms.OrI1 φ ψ)
  /-- Right disjunction introduction: `ψ → φ ∨ ψ`. -/
  | orI2 (φ ψ : Proposition Atom) :
      IKModalAxiom (Cslib.Logic.Axioms.OrI2 φ ψ)
  /-- Disjunction elimination: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))`. -/
  | orE (φ ψ χ : Proposition Atom) :
      IKModalAxiom (Cslib.Logic.Axioms.OrE φ ψ χ)
  /-- `k1` / Kb: `□(φ → ψ) → (□φ → □ψ)`. -/
  | k (φ ψ : Proposition Atom) :
      IKModalAxiom
        ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ)))
  /-- `k2` / Kd: `□(φ → ψ) → (◇φ → ◇ψ)`. -/
  | kdia (φ ψ : Proposition Atom) :
      IKModalAxiom ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ)))
  /-- `k3` / Cd (Fischer-Servi): `◇(φ ∨ ψ) → (◇φ ∨ ◇ψ)`. -/
  | cd (φ ψ : Proposition Atom) :
      IKModalAxiom ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ)))
  /-- `k4` / Idb (Fischer-Servi): `(◇φ → □ψ) → □(φ → ψ)`. -/
  | idb (φ ψ : Proposition Atom) :
      IKModalAxiom (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ)))
  /-- `k5` / Nd: `◇⊥ → ⊥`. -/
  | dbot :
      IKModalAxiom ((◇Proposition.bot).imp Proposition.bot)

/-! ## Soundness -/

/-- Every `IKModalAxiom` instance is `IValid` (birelational validity with intuitionistic
falsum semantics `botForces := fun _ => False`).

The nine non-modal cases mirror `PL.int_axiom_sound` exactly (`≤`-refl/trans plus
`bforces_persistence`, packaging the loose `r`/`f1`/`f2` parameters into a `BFrame` term to feed
`bforces_persistence`'s implicit frame argument). The five modal cases:
- `k`/`kdia`/`cd` need no frame condition (pure quantifier bookkeeping over `≤ ∘ r`/`r`).
- `idb` consumes `BFrame.f2` (down-confluence) to relocate the `◇φ`-witness world upward.
- `dbot` is vacuous: `BForces _ _ (fun _ => False) w' (◇⊥) = ∃ u, r w' u ∧ False = False`. -/
theorem ik_axiom_sound {φ : Proposition Atom} (h_ax : IKModalAxiom φ) : IValid.{u, v} φ := by
  intro World _ r f1 f2 val v_uc w
  have bf_uc : ∀ {w w' : World}, w ≤ w' →
      (fun _ : World => False) w → (fun _ : World => False) w' :=
    fun _ h => h.elim
  cases h_ax with
  | implyK φ ψ =>
    intro w' _ hφ w'' hw' _
    exact bforces_persistence (F := ⟨r, f1, f2⟩) v_uc bf_uc hw' hφ
  | implyS φ ψ χ =>
    intro w₁ hw₁ h_pqr w₂ hw₂ h_pq w₃ hw₃ h_p
    have h₁₃ : w₁ ≤ w₃ := le_trans hw₂ hw₃
    exact h_pqr w₃ h₁₃ h_p w₃ (le_refl w₃) (h_pq w₃ hw₃ h_p)
  | efq φ =>
    intro _ _ hbot
    exact hbot.elim
  | andI φ ψ =>
    intro w₁ _ hφ w₂ hw₂ hψ
    exact ⟨bforces_persistence (F := ⟨r, f1, f2⟩) v_uc bf_uc hw₂ hφ, hψ⟩
  | andE1 φ ψ =>
    intro _ _ h; exact h.1
  | andE2 φ ψ =>
    intro _ _ h; exact h.2
  | orI1 φ ψ =>
    intro _ _ h; exact Or.inl h
  | orI2 φ ψ =>
    intro _ _ h; exact Or.inr h
  | orE φ ψ χ =>
    intro w₁ _ h_pq w₂ hw₂ h_rq w₃ hw₃ h_pr
    have hw₁₃ : w₁ ≤ w₃ := le_trans hw₂ hw₃
    exact h_pr.elim (fun hp => h_pq w₃ hw₁₃ hp) (fun hr => h_rq w₃ hw₃ hr)
  | k φ ψ =>
    -- Goal: ∀ w' ≥ w, □(φ→ψ)@w' → ∀ w'' ≥ w', □φ@w'' → □ψ@w''
    intro w' _ hbox_imp w'' hw' hbox_phi w1 hw1 u hru
    exact hbox_imp w1 (le_trans hw' hw1) u hru u (le_refl u) (hbox_phi w1 hw1 u hru)
  | kdia φ ψ =>
    -- Goal: ∀ w' ≥ w, □(φ→ψ)@w' → ∀ w'' ≥ w', ◇φ@w'' → ◇ψ@w''
    intro w' _ hbox_imp w'' hw' hdia_phi
    obtain ⟨u, hru, hφu⟩ := hdia_phi
    exact ⟨u, hru, hbox_imp w'' hw' u hru u (le_refl u) hφu⟩
  | cd φ ψ =>
    -- Goal: ∀ w' ≥ w, ◇(φ∨ψ)@w' → (◇φ ∨ ◇ψ)@w'
    intro w' _ hdia
    obtain ⟨u, hru, hor⟩ := hdia
    cases hor with
    | inl hφ => exact Or.inl ⟨u, hru, hφ⟩
    | inr hψ => exact Or.inr ⟨u, hru, hψ⟩
  | idb φ ψ =>
    -- Goal: ∀ w' ≥ w, (◇φ→□ψ)@w' → □(φ→ψ)@w'
    intro w' _ h_hyp w1 hw1 u hru v hv hφv
    -- Relocate the `◇φ`-witness world upward along `≤` using F2 (down-confluence).
    obtain ⟨w1', hw1w1', hrw1'v⟩ := f2 hru hv
    have hdia_w1' : BForces r val (fun _ => False) w1' (◇φ) := ⟨v, hrw1'v, hφv⟩
    exact h_hyp w1' (le_trans hw1 hw1w1') hdia_w1' w1' (le_refl w1') v hrw1'v
  | dbot =>
    -- Goal: ∀ w' ≥ w, ◇⊥@w' → ⊥@w'; `◇⊥@w'` unfolds to `∃ u, r w' u ∧ False`, hence vacuous.
    intro w' _ hdia
    obtain ⟨_, _, hfalse⟩ := hdia
    exact hfalse.elim

/-- **Soundness**: if `DerivationTree IKModalAxiom Γ φ`, then for any birelational frame
(with `botForces := fun _ => False`) and world `w` where all formulas in `Γ` are forced, `φ` is
also forced at `w`. The `necessitation` case is handled exactly as the classical
`Cslib.Logic.Modal.soundness` (`Metalogic/Soundness.lean`): the premise `d'` has empty context,
so the box goal closes by recursing into `d'` at the successor world with the vacuous
empty-context hypothesis. -/
theorem ik_soundness
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree IKModalAxiom Γ φ)
    {World : Type v} [Preorder World]
    (r : World → World → Prop)
    (f1 : ∀ {w w' u : World}, w ≤ w' → r w u → ∃ u', r w' u' ∧ u ≤ u')
    (f2 : ∀ {w u u' : World}, r w u → u ≤ u' → ∃ w', w ≤ w' ∧ r w' u')
    (val : World → Atom → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (w : World)
    (h_ctx : ∀ ψ, ψ ∈ Γ → BForces r val (fun _ => False) w ψ) :
    BForces r val (fun _ => False) w φ := by
  match d with
  | .ax _ ψ h_ax =>
    exact ik_axiom_sound h_ax World r f1 f2 val v_uc w
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact ik_soundness d₁ r f1 f2 val v_uc w h_ctx w (le_refl w)
      (ik_soundness d₂ r f1 f2 val v_uc w h_ctx)
  | .necessitation ψ d' =>
    intro w' _hle u _hru
    exact ik_soundness d' r f1 f2 val v_uc u (fun _ h => nomatch h)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact ik_soundness d' r f1 f2 val v_uc w
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Soundness for derivable formulas**: if `Derivable IKModalAxiom φ`, then `φ` is `IValid`. -/
theorem ik_soundness_derivable {φ : Proposition Atom}
    (h : Derivable IKModalAxiom φ) : IValid.{u, v} φ := by
  intro World _ r f1 f2 val v_uc w
  obtain ⟨d⟩ := h
  exact ik_soundness d r f1 f2 val v_uc w (fun _ h => nomatch h)

/-! ## Completeness and Consistency -/

/-- **Completeness for `IK`**: any `IValid` formula is derivable from `IKModalAxiom`. Pure
instantiation of the task-480 parametric `ivalid_completeness` at `Axioms := IKModalAxiom`,
each discharger the matching `IKModalAxiom` constructor. -/
theorem ik_completeness {φ : Proposition Atom} (h_valid : IValid.{u, u} φ) :
    Derivable IKModalAxiom φ :=
  ivalid_completeness
    (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ) (fun φ => .efq φ)
    (fun φ ψ => .orI1 φ ψ) (fun φ ψ => .orI2 φ ψ) (fun φ ψ χ => .orE φ ψ χ)
    (fun φ ψ => .andI φ ψ) (fun φ ψ => .andE1 φ ψ) (fun φ ψ => .andE2 φ ψ)
    (fun φ ψ => .k φ ψ) (fun φ ψ => .kdia φ ψ) (fun φ ψ => .idb φ ψ)
    (fun φ ψ => .cd φ ψ) .dbot h_valid

/-- **Consistency of `IK`**: `⊥` is not derivable from `IKModalAxiom`. A corollary of
soundness: `ik_soundness_derivable` would give `IValid ⊥`, which is refuted by instantiating
at the trivial one-point birelational frame on `ℕ` (any world, e.g. `0`). -/
theorem ik_consistent : ¬ Derivable IKModalAxiom (Proposition.bot : Proposition Atom) := by
  intro h
  have hforces : BForces (fun _ _ : ℕ => True) (fun (_ : ℕ) (_ : Atom) => False)
      (fun _ : ℕ => False) 0 (Proposition.bot : Proposition Atom) :=
    ik_soundness_derivable h ℕ (fun _ _ => True)
      (fun {_ _ u} _ _ => ⟨u, trivial, le_refl u⟩)
      (fun {w0 _ _} _ _ => ⟨w0, le_refl w0, trivial⟩)
      (fun _ _ => False) (fun _ _ h => h) 0
  exact hforces

/-- **Soundness-completeness biconditional for `IK`**: `φ` is `IValid` iff `φ` is derivable
from `IKModalAxiom`. -/
theorem ik_soundness_completeness {φ : Proposition Atom} :
    IValid.{u, u} φ ↔ Derivable IKModalAxiom φ :=
  ⟨ik_completeness, ik_soundness_derivable⟩

end Cslib.Logic.Modal
