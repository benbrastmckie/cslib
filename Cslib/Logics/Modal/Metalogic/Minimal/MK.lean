/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.DerivationTree
public import Cslib.Logics.Modal.Semantics.Birelational

/-! # MK: Minimal Modal Logic K (Axioms + Soundness)

This module defines `MK`, the modal logic over the **minimal** propositional base (no `efq` /
explosion): `IK` minus `efq` minus `dbot`/Nd, over the task-490 birelational semantics with the
minimal `⊥` treatment (`⊥` an ordinary proposition, not forced-false). `MK` targets `MValid`
(birelational, ∃-diamond, F1/F2 confluence), the *same* semantics `IK` targets, but with an
*arbitrary* upward-closed `botForces` predicate rather than `fun _ => False`.

## Main Definitions

- `MKModalAxiom`: the 8 minimal-propositional schemata (mirroring `MinPropAxiom` / `IntPropAxiom`
  without `efq`) plus the 4 modal schemata `k`/`kdia`/`cd`/`idb` (**no** `efq`, **no** `dbot`/Nd).
- `mk_axiom_sound`: every `MKModalAxiom` instance is `MValid` (arbitrary `botForces`).
- `mk_soundness`/`mk_soundness_derivable`: birelational soundness for `MK`, by structural
  induction on `DerivationTree MKModalAxiom`.
- `mk_consistent`: `⊥` is not derivable from `MKModalAxiom`.

## Implementation Notes

- The 8 propositional cases and the 4 modal cases (`k`/`kdia`/`cd`/`idb`) of `ik_axiom_sound`
  (`Intuitionistic/IK.lean:131`) never inspect `botForces` (only the dropped `efq`/`dbot` cases
  did), so they transcribe verbatim under the `MValid` prologue (which threads an extra
  `botForces`/`bf_uc` pair through `intro`, replacing `IValid`'s hard-coded `fun _ => False`).
- `idb` still consumes `BFrame.f2` (down-confluence) exactly as in `IK`.
- `mk_consistent` is proved at a *non-fallible* one-point frame (`botForces := fun _ => False`),
  mirroring `ik_consistent` (`IK.lean:248`): even though `MK`'s semantics allows fallible worlds
  in general, soundness applied to `Derivable MKModalAxiom ⊥` gives `MValid ⊥`, which must hold
  at *every* birelational model including this non-fallible one, where `⊥` is forced nowhere.

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (axioms `k1`-`k4`, the Fischer-Servi fragment, birelational semantics, `MValid`).
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43,
  Lemma 5.5.
* [I. Johansson, *Der Minimalkalkül*][Johansson1937] — minimal (efq-free) propositional logic.
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

variable {Atom : Type u}

/-! ## The `MK` Axiom Schemata -/

/-- Axiom schemata for minimal modal logic `MK`: `IK` (`IKModalAxiom`) minus `efq` minus
`dbot`/Nd. The 8 propositional constructors mirror `MinPropAxiom`/`IntPropAxiom` without `efq`;
the 4 modal constructors are `k1`/Kb, `k2`/Kd, `k3`/Cd (Fischer-Servi, ◇ over ∨), `k4`/Idb
(Fischer-Servi box) — exactly the four hypotheses `{h_K, h_Kdia, h_Cd, h_Idb}` of the task-480
birelational framework, omitting `h_dbot`. -/
inductive MKModalAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)`. -/
  | implyK (φ ψ : Proposition Atom) :
      MKModalAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`. -/
  | implyS (φ ψ χ : Proposition Atom) :
      MKModalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)`. -/
  | andI (φ ψ : Proposition Atom) :
      MKModalAxiom (Cslib.Logic.Axioms.AndI φ ψ)
  /-- Left conjunction elimination: `φ ∧ ψ → φ`. -/
  | andE1 (φ ψ : Proposition Atom) :
      MKModalAxiom (Cslib.Logic.Axioms.AndE1 φ ψ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ`. -/
  | andE2 (φ ψ : Proposition Atom) :
      MKModalAxiom (Cslib.Logic.Axioms.AndE2 φ ψ)
  /-- Left disjunction introduction: `φ → φ ∨ ψ`. -/
  | orI1 (φ ψ : Proposition Atom) :
      MKModalAxiom (Cslib.Logic.Axioms.OrI1 φ ψ)
  /-- Right disjunction introduction: `ψ → φ ∨ ψ`. -/
  | orI2 (φ ψ : Proposition Atom) :
      MKModalAxiom (Cslib.Logic.Axioms.OrI2 φ ψ)
  /-- Disjunction elimination: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))`. -/
  | orE (φ ψ χ : Proposition Atom) :
      MKModalAxiom (Cslib.Logic.Axioms.OrE φ ψ χ)
  /-- `k1` / Kb: `□(φ → ψ) → (□φ → □ψ)`. -/
  | k (φ ψ : Proposition Atom) :
      MKModalAxiom
        ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ)))
  /-- `k2` / Kd: `□(φ → ψ) → (◇φ → ◇ψ)`. -/
  | kdia (φ ψ : Proposition Atom) :
      MKModalAxiom ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ)))
  /-- `k3` / Cd (Fischer-Servi): `◇(φ ∨ ψ) → (◇φ ∨ ◇ψ)`. -/
  | cd (φ ψ : Proposition Atom) :
      MKModalAxiom ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ)))
  /-- `k4` / Idb (Fischer-Servi): `(◇φ → □ψ) → □(φ → ψ)`. -/
  | idb (φ ψ : Proposition Atom) :
      MKModalAxiom (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ)))

/-! ## Soundness -/

/-- Every `MKModalAxiom` instance is `MValid` (birelational validity with an *arbitrary*
upward-closed `botForces` predicate).

The eight propositional cases mirror `ik_axiom_sound`'s propositional cases exactly (`≤`-refl/
trans plus `bforces_persistence`); the four modal cases (`k`/`kdia`/`cd`/`idb`) are transcribed
verbatim from `ik_axiom_sound` (`IK.lean:131`) -- none of them inspect `botForces`. `idb`
consumes `BFrame.f2` (down-confluence) to relocate the `◇φ`-witness world upward. -/
theorem mk_axiom_sound {φ : Proposition Atom} (h_ax : MKModalAxiom φ) : MValid.{u, v} φ := by
  intro World _ r f1 f2 val botForces v_uc bf_uc w
  cases h_ax with
  | implyK φ ψ =>
    intro w' _ hφ w'' hw' _
    exact bforces_persistence (F := ⟨r, f1, f2⟩) v_uc bf_uc hw' hφ
  | implyS φ ψ χ =>
    intro w₁ hw₁ h_pqr w₂ hw₂ h_pq w₃ hw₃ h_p
    have h₁₃ : w₁ ≤ w₃ := le_trans hw₂ hw₃
    exact h_pqr w₃ h₁₃ h_p w₃ (le_refl w₃) (h_pq w₃ hw₃ h_p)
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
    have hdia_w1' : BForces r val botForces w1' (◇φ) := ⟨v, hrw1'v, hφv⟩
    exact h_hyp w1' (le_trans hw1 hw1w1') hdia_w1' w1' (le_refl w1') v hrw1'v

/-- **Soundness**: if `DerivationTree MKModalAxiom Γ φ`, then for any birelational frame and
world `w` where all formulas in `Γ` are forced, `φ` is also forced at `w`. The `necessitation`
case is handled exactly as `ik_soundness`: the premise `d'` has empty context, so the box goal
closes by recursing into `d'` at the successor world with the vacuous empty-context
hypothesis. -/
theorem mk_soundness
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree MKModalAxiom Γ φ)
    {World : Type v} [Preorder World]
    (r : World → World → Prop)
    (f1 : ∀ {w w' u : World}, w ≤ w' → r w u → ∃ u', r w' u' ∧ u ≤ u')
    (f2 : ∀ {w u u' : World}, r w u → u ≤ u' → ∃ w', w ≤ w' ∧ r w' u')
    (val : World → Atom → Prop) (botForces : World → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    (w : World)
    (h_ctx : ∀ ψ, ψ ∈ Γ → BForces r val botForces w ψ) :
    BForces r val botForces w φ := by
  match d with
  | .ax _ ψ h_ax =>
    exact mk_axiom_sound h_ax World r f1 f2 val botForces v_uc bf_uc w
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact mk_soundness d₁ r f1 f2 val botForces v_uc bf_uc w h_ctx w (le_refl w)
      (mk_soundness d₂ r f1 f2 val botForces v_uc bf_uc w h_ctx)
  | .necessitation ψ d' =>
    intro w' _hle u _hru
    exact mk_soundness d' r f1 f2 val botForces v_uc bf_uc u (fun _ h => nomatch h)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact mk_soundness d' r f1 f2 val botForces v_uc bf_uc w
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Soundness for derivable formulas**: if `Derivable MKModalAxiom φ`, then `φ` is `MValid`. -/
theorem mk_soundness_derivable {φ : Proposition Atom}
    (h : Derivable MKModalAxiom φ) : MValid.{u, v} φ := by
  intro World _ r f1 f2 val botForces v_uc bf_uc w
  obtain ⟨d⟩ := h
  exact mk_soundness d r f1 f2 val botForces v_uc bf_uc w (fun _ h => nomatch h)

/-! ## Consistency -/

/-- **Consistency of `MK`**: `⊥` is not derivable from `MKModalAxiom`. A corollary of soundness:
`mk_soundness_derivable` would give `MValid ⊥`, which is refuted by instantiating at the trivial
one-point birelational frame on `ℕ` with a *non-fallible* `botForces := fun _ => False` (any
world, e.g. `0`); `MValid` quantifies over every upward-closed `botForces`, so this instance is
available even though `MK`'s canonical model in general admits fallible worlds. -/
theorem mk_consistent : ¬ Derivable MKModalAxiom (Proposition.bot : Proposition Atom) := by
  intro h
  have hforces : BForces (fun _ _ : ℕ => True) (fun (_ : ℕ) (_ : Atom) => False)
      (fun _ : ℕ => False) 0 (Proposition.bot : Proposition Atom) :=
    mk_soundness_derivable h ℕ (fun _ _ => True)
      (fun {_ _ u} _ _ => ⟨u, trivial, le_refl u⟩)
      (fun {w0 _ _} _ _ => ⟨w0, le_refl w0, trivial⟩)
      (fun _ _ => False) (fun _ : ℕ => False) (fun _ _ h => h) (fun _ h => h.elim) 0
  exact hforces

end Cslib.Logic.Modal
