/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Constructive.CKExtension

/-! # CS4: Constructive Modal Logic S4 (Soundness)

This module instantiates the task-501 frame-condition-parametrized segment scaffold
(`CKExtension.lean`) at the constructive analogue of `S4`: `CS4` = `CT` (`CT.lean`) plus the two
`4` schemata `fourBox : □A → □□A` and `fourDia : ◇◇A → ◇A`.

`CS4` is sound for `CKValidFC cs4FC` — Wijesekera-style fallible-world validity restricted to
frames whose modal relation `r` is reflexive and ≤-composed-transitive (`cs4FC`,
`CKExtension.lean`).

**Completeness for `CS4` is not established in this module** (see the task 501 implementation
summary for the recorded blocker). The obstruction: `ck_completeness`'s canonical model needs the
diamond-backward truth-lemma case to refute an unwarranted `◇A` via a *restricted*-tail witness
segment (`diamRefutingSegment`, `CKTruthLemma.lean`) whose tail excludes `A`. This exclusion is a
*one-step* property (`A ∉ t` for `t` a *direct* tail member) and does not propagate through the
further ≤-composed-transitive successors `cs4FC` universally quantifies over: writing
`P := diamRefutingSegment s h_not`, for `u ∈ P.tail` (so `A ∉ u.head`), an arbitrary `u' ≥ u` and
`t ∈ u'.tail` need not satisfy `A ∉ t.head` — nothing in the construction prevents `t` from being
(or extending to) the exploding theory `Set.univ`, which always contains `A`. Consequently `P`
itself cannot be shown to satisfy `cs4FC`'s ≤-composed-transitivity clause as a *source*, and
`cs4FC` must hold **globally** on whatever world type is chosen (it is a blanket hypothesis of
`CKValidFC`/`ckvalidFC_completeness`, not a per-world side condition). Resolving this requires a
*hereditary* diamond-refuting construction (propagating the `A`-exclusion through the transitive
closure of the restricted tail, not just one step) — substantially more machinery than
`dia_refuting_theory`/`diamRefutingSegment` provide as-is, and out of scope for a single-lemma
fix. Per the escalation protocol, no `sorry` or axiom is introduced; `CS4` completeness is left
as an open item (task 501 implementation summary, Phase 5).

## Main Definitions

- `CS4ModalAxiom`: `CTModalAxiom`'s constructors verbatim plus `fourBox`/`fourDia`.
- `cs4_axiom_sound`/`cs4_soundness`/`cs4_soundness_derivable`: soundness for `CKValidFC cs4FC`.

## References

* [D. Wijesekera, *Constructive modal logics I*][Wijesekera1990], §2 and Definition 1.1.4.
* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (the birelational `IS4`, the structural template for the box/diamond axiom pairing).
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

variable {Atom : Type u}

/-! ## The `CS4` Axiom Schemata -/

/-- Axiom schemata for constructive modal logic `CS4`: the 13 `CTModalAxiom` constructors
verbatim, plus the two `4` schemata `fourBox`/`fourDia`. Both box and diamond forms are required
since `◇` is primitive (not `□`-definable) in this framework's `Proposition` datatype (mirroring
`IS4.lean`'s `IS4` extension of `IT`). -/
inductive CS4ModalAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)`. -/
  | implyK (φ ψ : Proposition Atom) :
      CS4ModalAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`. -/
  | implyS (φ ψ χ : Proposition Atom) :
      CS4ModalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Ex falso quodlibet: `⊥ → φ`. -/
  | efq (φ : Proposition Atom) :
      CS4ModalAxiom (Proposition.bot.imp φ)
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)`. -/
  | andI (φ ψ : Proposition Atom) :
      CS4ModalAxiom (Cslib.Logic.Axioms.AndI φ ψ)
  /-- Left conjunction elimination: `φ ∧ ψ → φ`. -/
  | andE1 (φ ψ : Proposition Atom) :
      CS4ModalAxiom (Cslib.Logic.Axioms.AndE1 φ ψ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ`. -/
  | andE2 (φ ψ : Proposition Atom) :
      CS4ModalAxiom (Cslib.Logic.Axioms.AndE2 φ ψ)
  /-- Left disjunction introduction: `φ → φ ∨ ψ`. -/
  | orI1 (φ ψ : Proposition Atom) :
      CS4ModalAxiom (Cslib.Logic.Axioms.OrI1 φ ψ)
  /-- Right disjunction introduction: `ψ → φ ∨ ψ`. -/
  | orI2 (φ ψ : Proposition Atom) :
      CS4ModalAxiom (Cslib.Logic.Axioms.OrI2 φ ψ)
  /-- Disjunction elimination: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))`. -/
  | orE (φ ψ χ : Proposition Atom) :
      CS4ModalAxiom (Cslib.Logic.Axioms.OrE φ ψ χ)
  /-- Kb: `□(φ → ψ) → (□φ → □ψ)`. -/
  | k (φ ψ : Proposition Atom) :
      CS4ModalAxiom
        ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ)))
  /-- Kd: `□(φ → ψ) → (◇φ → ◇ψ)`. -/
  | kdia (φ ψ : Proposition Atom) :
      CS4ModalAxiom ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ)))
  /-- `T` box form: `□A → A`. -/
  | tBox (φ : Proposition Atom) :
      CS4ModalAxiom ((Proposition.box φ).imp φ)
  /-- `T` diamond form: `A → ◇A`. -/
  | tDia (φ : Proposition Atom) :
      CS4ModalAxiom (φ.imp (◇φ))
  /-- `4` box form: `□A → □□A`. -/
  | fourBox (φ : Proposition Atom) :
      CS4ModalAxiom ((Proposition.box φ).imp (Proposition.box (Proposition.box φ)))
  /-- `4` diamond form: `◇◇A → ◇A`. -/
  | fourDia (φ : Proposition Atom) :
      CS4ModalAxiom ((◇◇φ).imp (◇φ))

/-! ## Soundness -/

/-- Every `CS4ModalAxiom` instance is `CKValidFC cs4FC` (Wijesekera-style fallible-world validity
over reflexive, ≤-composed-transitive frames). The 13 non-`4` cases are `ct_axiom_sound`'s cases
verbatim (`CT.lean`), with the transitivity component of `hfc` threaded through unused. The two
new cases:
- `fourDia` (`◇◇A → ◇A`): the ∀∃ diamond clause introduces `w'' ≥ w'`; unfolding `◇◇A@w''` at
  `w''` (`le_refl`) gives a witness `u` with `r w'' u ∧ (◇A)@u`; unfolding `◇A@u` at `u`
  (`le_refl`) gives `t` with `r u t ∧ A@t`; witness `t` via **plain** transitivity
  (`htrans hru (le_refl u) hut`, the `u' := u` specialization).
- `fourBox` (`□A → □□A`): the nested box goal introduces `w'' ≥ w'`, `u` with `r w'' u`,
  `u' ≥ u`, `t` with `r u' t`; supply `A@t` from `□A@w'` at `w''` (`≥ w'`) and `t`, using the
  **≤-composed** transitivity clause `r w'' u → u ≤ u' → r u' t → r w'' t`. -/
theorem cs4_axiom_sound {φ : Proposition Atom} (h_ax : CS4ModalAxiom φ) :
    CKValidFC.{u, v} cs4FC φ := by
  intro World _ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  obtain ⟨hrefl, htrans⟩ := hfc
  cases h_ax with
  | implyK φ ψ =>
    intro w' _ hφ w'' hw' _
    exact ckforces_persistence v_uc bf_uc hw' hφ
  | implyS φ ψ χ =>
    intro w₁ hw₁ h_pqr w₂ hw₂ h_pq w₃ hw₃ h_p
    have h₁₃ : w₁ ≤ w₃ := le_trans hw₂ hw₃
    exact h_pqr w₃ h₁₃ h_p w₃ (le_refl w₃) (h_pq w₃ hw₃ h_p)
  | efq φ =>
    intro w' _ hbot
    exact ckforces_of_exploding bf_uc bf_val bf_r bf_r_wit hbot φ
  | andI φ ψ =>
    intro w₁ _ hφ w₂ hw₂ hψ
    exact ⟨ckforces_persistence v_uc bf_uc hw₂ hφ, hψ⟩
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
    intro w' _ hbox_imp w'' hw' hbox_phi w1 hw1 u hru
    exact hbox_imp w1 (le_trans hw' hw1) u hru u (le_refl u) (hbox_phi w1 hw1 u hru)
  | kdia φ ψ =>
    intro w' _ hbox_imp w'' hw' hdia_phi w₃ hw₃
    obtain ⟨u, hru, hφu⟩ := hdia_phi w₃ hw₃
    exact ⟨u, hru, hbox_imp w₃ (le_trans hw' hw₃) u hru u (le_refl u) hφu⟩
  | tBox φ =>
    intro w' _ hbox
    exact hbox w' (le_refl w') w' (hrefl w')
  | tDia φ =>
    intro w' _ hφ w'' hw''
    exact ⟨w'', hrefl w'', ckforces_persistence v_uc bf_uc hw'' hφ⟩
  | fourDia φ =>
    intro w' _ hdidia w'' hw''
    obtain ⟨u, hru, hdia_u⟩ := hdidia w'' hw''
    obtain ⟨t, hut, hφt⟩ := hdia_u u (le_refl u)
    exact ⟨t, htrans hru (le_refl u) hut, hφt⟩
  | fourBox φ =>
    intro w' _ hbox w'' hw'' u hru u' hu' t hrt
    exact hbox w'' hw'' t (htrans hru hu' hrt)

/-- **Soundness**: if `DerivationTree CS4ModalAxiom Γ φ`, then in any fallible-world model whose
modal relation is reflexive and ≤-composed-transitive (`cs4FC`), at any world `w` where all
formulas in `Γ` are forced, `φ` is also forced. Structural analogue of `ct_soundness`
(`CT.lean`), threading `hfc` through unused except at the `.ax` case. -/
theorem cs4_soundness
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree CS4ModalAxiom Γ φ)
    {World : Type v} [Preorder World]
    (r : World → World → Prop) (hfc : cs4FC r)
    (val : World → Atom → Prop) (botForces : World → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    (bf_val : ∀ {w : World} (p : Atom), botForces w → val w p)
    (bf_r : ∀ {w u : World}, botForces w → r w u → botForces u)
    (bf_r_wit : ∀ {w : World}, botForces w → ∃ u, r w u ∧ botForces u)
    (w : World)
    (h_ctx : ∀ ψ, ψ ∈ Γ → CKForces r val botForces w ψ) :
    CKForces r val botForces w φ := by
  match d with
  | .ax _ ψ h_ax =>
    exact cs4_axiom_sound h_ax World r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact cs4_soundness d₁ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w h_ctx
      w (le_refl w)
      (cs4_soundness d₂ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w h_ctx)
  | .necessitation ψ d' =>
    intro w' _hle u _hru
    exact cs4_soundness d' r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit u
      (fun _ h => nomatch h)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact cs4_soundness d' r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Soundness for derivable formulas**: if `Derivable CS4ModalAxiom φ`, then `φ` is
`CKValidFC cs4FC`. -/
theorem cs4_soundness_derivable {φ : Proposition Atom}
    (h : Derivable CS4ModalAxiom φ) : CKValidFC.{u, v} cs4FC φ := by
  intro World _ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  obtain ⟨d⟩ := h
  exact cs4_soundness d r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
    (fun _ h => nomatch h)

end Cslib.Logic.Modal
