/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Constructive.CKExtension

/-! # CS5: Constructive Modal Logic S5 (Soundness)

This module instantiates the task-501 frame-condition-parametrized segment scaffold
(`CKExtension.lean`) at the constructive analogue of `S5`: `CS5` = `CS4` (`CS4.lean`) plus the two
`B` schemata `bBox : A → □◇A` and `bDia : ◇□A → A`.

**Adversarial finding (research report, Deliverable 3.1; carried over from task 494
Deliverable 6): `CS5` is axiomatized here via `B` (symmetry), NOT via the classical euclidean/`5`
axiom `◇A → □◇A`.** The classical canonical-euclideanness route needs negation-completeness,
unavailable to quasi-prime theories (which are *further* from negation-complete than task 494's
prime theories — they additionally admit the exploding theory `Set.univ`). Symmetry closure is
fully positive (MP-closure only); reflexivity (`T`) + transitivity (`4`) + symmetry (`B`) give an
equivalence relation, Simpson's constructive `S5` frame class.

`CS5` is sound for `CKValidFC cs5FC` — Wijesekera-style fallible-world validity restricted to
frames whose modal relation `r` is reflexive, ≤-composed-transitive, and ≤-composed-symmetric
(`cs5FC`, `CKExtension.lean`).

**Completeness for `CS5` is not established in this module.** Unlike `CS4` (whose completeness
task 508 mechanizes — see `CS4.lean`), `CS5` is **not** closable by the same technique: this is
now a mechanized negative result, not merely an unattempted extension.

`bDia` (`◇□A → A`) is **not sound** over `cs5FCweak`, the natural `CS5` analogue of the weakened
frame condition that makes `CS4` work (reflexivity + both `cs4FC'` clauses + a weakened
≤-composed symmetry `FCsym_box : r w u → u ≤ u' → ∃ t, r u' t ∧ w ≤ t`). Witness: a two-world
`Bool` countermodel (`false` consistent, `true` exploding) in which `◇□p → p` fails — see
`bDia_not_valid_over_cs5FCweak` in
`specs/508_unblock_CK_CS4_CS5_completeness/probes/cs5-obstruction-verified.lean`. So the `CS4`
technique **cannot** be extended to `CS5`: this is a *soundness* failure of the weakened frame
condition, which no amount of canonical-model work on the completeness side can fix.

The frame condition strong enough to validate `bDia` canonically, `FCbdia`, fails on the
canonical model: at `w := ofHead(H)` with `H` consistent and `u := cexpl` (the exploding
world), any `u' ≥ cexpl` has head `Set.univ`, forcing the witness `t` in `FCbdia`'s clause to
equal `cexpl`; but `t ≤ w` would then give `Set.univ ⊆ H`, contradicting `H`'s consistency.

One lead remains for future work: **`CS5 ⊢ ◇⊥ → ⊥`** (mechanized as `cs5_dia_bot_imp_bot` in the
same probe file — unlike `CK`/`CT`/`CS4`, none of which prove this), which may permit a
`Set.univ`-free tail redesign. It does not finish the job on its own: `FCbdia` still needs
genuine canonical symmetry, whose classical proof needs negation-completeness
(`B ∉ w.head ⇒ ¬B ∈ w.head`), unavailable for quasi-prime heads. This is the known-hard core of
constructive `S5` canonical completeness. Note that `bBox` (`A → □◇A`) is *not* the problem
(the weakened symmetry `FCsym_box` validates it fine); `bDia` alone is the blocker.

`CS5` completeness is **genuinely open** and is re-scoped to a separate research task, not
deferred with placeholders. See
`specs/508_unblock_CK_CS4_CS5_completeness/reports/01_cs4-cs5-completeness-technique.md` §5 and
`specs/508_unblock_CK_CS4_CS5_completeness/probes/cs5-obstruction-verified.lean` for the full
mechanized analysis.

## Main Definitions

- `CS5ModalAxiom`: `CS4ModalAxiom`'s constructors verbatim plus `bBox`/`bDia` (B, not
  euclidean-5).
- `cs5_axiom_sound`/`cs5_soundness`/`cs5_soundness_derivable`: soundness for `CKValidFC cs5FC`.

## References

* [D. Wijesekera, *Constructive modal logics I*][Wijesekera1990], §2 and Definition 1.1.4.
* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (the birelational `IS5`, the structural template for the `B`-via-symmetry decision).
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

variable {Atom : Type u}

/-! ## The `CS5` Axiom Schemata -/

/-- Axiom schemata for constructive modal logic `CS5`: the 15 `CS4ModalAxiom` constructors
verbatim, plus the two `B` schemata `bBox`/`bDia`. Both box and diamond forms are required since
`◇` is primitive (not `□`-definable) in this framework's `Proposition` datatype (mirroring
`IS5.lean`'s `IS5` extension of `IS4`). Deliberately **not** the classical euclidean/`5` axiom
`◇A → □◇A` (see module docstring). -/
inductive CS5ModalAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)`. -/
  | implyK (φ ψ : Proposition Atom) :
      CS5ModalAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`. -/
  | implyS (φ ψ χ : Proposition Atom) :
      CS5ModalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Ex falso quodlibet: `⊥ → φ`. -/
  | efq (φ : Proposition Atom) :
      CS5ModalAxiom (Proposition.bot.imp φ)
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)`. -/
  | andI (φ ψ : Proposition Atom) :
      CS5ModalAxiom (Cslib.Logic.Axioms.AndI φ ψ)
  /-- Left conjunction elimination: `φ ∧ ψ → φ`. -/
  | andE1 (φ ψ : Proposition Atom) :
      CS5ModalAxiom (Cslib.Logic.Axioms.AndE1 φ ψ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ`. -/
  | andE2 (φ ψ : Proposition Atom) :
      CS5ModalAxiom (Cslib.Logic.Axioms.AndE2 φ ψ)
  /-- Left disjunction introduction: `φ → φ ∨ ψ`. -/
  | orI1 (φ ψ : Proposition Atom) :
      CS5ModalAxiom (Cslib.Logic.Axioms.OrI1 φ ψ)
  /-- Right disjunction introduction: `ψ → φ ∨ ψ`. -/
  | orI2 (φ ψ : Proposition Atom) :
      CS5ModalAxiom (Cslib.Logic.Axioms.OrI2 φ ψ)
  /-- Disjunction elimination: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))`. -/
  | orE (φ ψ χ : Proposition Atom) :
      CS5ModalAxiom (Cslib.Logic.Axioms.OrE φ ψ χ)
  /-- Kb: `□(φ → ψ) → (□φ → □ψ)`. -/
  | k (φ ψ : Proposition Atom) :
      CS5ModalAxiom
        ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ)))
  /-- Kd: `□(φ → ψ) → (◇φ → ◇ψ)`. -/
  | kdia (φ ψ : Proposition Atom) :
      CS5ModalAxiom ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ)))
  /-- `T` box form: `□A → A`. -/
  | tBox (φ : Proposition Atom) :
      CS5ModalAxiom ((Proposition.box φ).imp φ)
  /-- `T` diamond form: `A → ◇A`. -/
  | tDia (φ : Proposition Atom) :
      CS5ModalAxiom (φ.imp (◇φ))
  /-- `4` box form: `□A → □□A`. -/
  | fourBox (φ : Proposition Atom) :
      CS5ModalAxiom ((Proposition.box φ).imp (Proposition.box (Proposition.box φ)))
  /-- `4` diamond form: `◇◇A → ◇A`. -/
  | fourDia (φ : Proposition Atom) :
      CS5ModalAxiom ((◇◇φ).imp (◇φ))
  /-- `B` box form: `A → □◇A`. -/
  | bBox (φ : Proposition Atom) :
      CS5ModalAxiom (φ.imp (Proposition.box (◇φ)))
  /-- `B` diamond form: `◇□A → A`. -/
  | bDia (φ : Proposition Atom) :
      CS5ModalAxiom ((◇(Proposition.box φ)).imp φ)

/-! ## Soundness -/

/-- Every `CS5ModalAxiom` instance is `CKValidFC cs5FC` (Wijesekera-style fallible-world validity
over reflexive, ≤-composed-transitive, ≤-composed-symmetric frames). The 15 non-`B` cases are
`cs4_axiom_sound`'s cases verbatim (`CS4.lean`), with the symmetry component of `hfc` threaded
through unused. The two new cases:
- `bDia` (`◇□A → A`): at `w'` (`le_refl`) get `u` with `r w' u ∧ □A@u`; instantiate `□A@u` at `u`
  (`le_refl`) and `w'` via **plain** symmetry (`hsymm hru (le_refl u)`, the `u' := u`
  specialization of the ≤-composed clause).
- `bBox` (`A → □◇A`): the nested box goal introduces `w'' ≥ w'`, `u` with `r w'' u`; unfolding
  `◇A@u` introduces `u' ≥ u`; witness `w''` via **≤-composed** symmetry
  (`r w'' u → u ≤ u' → r u' w''`), with `A@w''` by persistence from `A@w'` (`w' ≤ w''`). -/
theorem cs5_axiom_sound {φ : Proposition Atom} (h_ax : CS5ModalAxiom φ) :
    CKValidFC.{u, v} cs5FC φ := by
  intro World _ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  obtain ⟨hrefl, htrans, hsymm⟩ := hfc
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
  | bDia φ =>
    intro w' _ hdia
    obtain ⟨u, hru, hboxA⟩ := hdia w' (le_refl w')
    exact hboxA u (le_refl u) w' (hsymm hru (le_refl u))
  | bBox φ =>
    intro w' _ hφ w'' hw'' u hru u' hu'
    exact ⟨w'', hsymm hru hu', ckforces_persistence v_uc bf_uc hw'' hφ⟩

/-- **Soundness**: if `DerivationTree CS5ModalAxiom Γ φ`, then in any fallible-world model whose
modal relation is reflexive, ≤-composed-transitive, and ≤-composed-symmetric (`cs5FC`), at any
world `w` where all formulas in `Γ` are forced, `φ` is also forced. Structural analogue of
`cs4_soundness` (`CS4.lean`), threading `hfc` through unused except at the `.ax` case. -/
theorem cs5_soundness
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree CS5ModalAxiom Γ φ)
    {World : Type v} [Preorder World]
    (r : World → World → Prop) (hfc : cs5FC r)
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
    exact cs5_axiom_sound h_ax World r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact cs5_soundness d₁ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w h_ctx
      w (le_refl w)
      (cs5_soundness d₂ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w h_ctx)
  | .necessitation ψ d' =>
    intro w' _hle u _hru
    exact cs5_soundness d' r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit u
      (fun _ h => nomatch h)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact cs5_soundness d' r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Soundness for derivable formulas**: if `Derivable CS5ModalAxiom φ`, then `φ` is
`CKValidFC cs5FC`. -/
theorem cs5_soundness_derivable {φ : Proposition Atom}
    (h : Derivable CS5ModalAxiom φ) : CKValidFC.{u, v} cs5FC φ := by
  intro World _ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  obtain ⟨d⟩ := h
  exact cs5_soundness d r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
    (fun _ h => nomatch h)

end Cslib.Logic.Modal
