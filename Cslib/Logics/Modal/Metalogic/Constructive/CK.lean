/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.DerivationTree
public import Cslib.Logics.Modal.Semantics.Birelational

/-! # CK: Constructive Modal Logic K (Axioms and Soundness)

This module defines bare constructive modal logic `CK` ([Wijesekera1990]) and proves its
soundness over the *minimal* birelational semantics (`MValid`, arbitrary upward-closed
`botForces`), the fallible-world semantics for which `CK` is also complete (see
`Constructive/SegmentLindenbaum.lean` and the completeness theorem below).

`CK` is the strict sub-system of Simpson's `IK` obtained by *dropping* the Fischer-Servi
axioms `Cd` (`◇(φ∨ψ) → ◇φ∨◇ψ`) and `Idb` (`(◇φ→□ψ) → □(φ→ψ)`) and the nullary axiom
`Nd` (`◇⊥ → ⊥`): only the two K-distribution schemata `Kb` and `Kd` remain, over the same
9 intuitionistic propositional schemata.

## Main Definitions

- `CKModalAxiom`: the axiom schemata of bare `CK` -- 9 intuitionistic propositional schemata
  plus `k` (Kb) and `kdia` (Kd). **No** `cd`/`idb`/`dbot` constructors.
- `ck_axiom_sound`: every `CKModalAxiom` instance is `MValid`.
- `ck_soundness`/`ck_soundness_derivable`: minimal birelational soundness for `CK`.

## Provenance of the axiom list

The constructor list is pinned against two independent sources:

- The ianshil/CK Coq mechanization: `CKH.v` defines the Hilbert system for bare `CK` with
  exactly the intuitionistic propositional axioms plus Kb and Kd, parametrized by additional
  axioms `AdAx`; bare `CK` is `NoAdAx := fun _ => False` (no additional axioms whatsoever).
  Its completeness for `CK` is `Completeness_seg/CK_seg_completeness.v`, over *segment*
  models with fallible (exploding) worlds -- deliberately not over intuitionistic-falsum
  models, for which bare `CK` is incomplete.
- [Wijesekera1990] §2: constructive `K` has Kb and Kd only. **Terminological caveat
  (resolved)**: Wijesekera's own system additionally validates `Nd = ◇⊥ → ⊥` because his
  models make falsum unforceable; some authors therefore call `CK + Nd` "CK". This
  formalization follows the ianshil/CK convention (`NoAdAx`): *bare* `CK` **excludes** `Nd`.
  Indeed `Nd` is not `MValid` (take `botForces := fun _ => True`), so bare `CK`'s soundness
  target `MValid` forces this choice; conversely `Nd` *is* `IValid` (vacuously), which is
  exactly why bare `CK` is incomplete for `IValid` and the completeness theorem here is
  stated over `MValid`.

## References

* [D. Wijesekera, *Constructive modal logics I*][Wijesekera1990], §2.
* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (the `IK` superset; frame conditions F1/F2).
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

variable {Atom : Type u}

/-! ## The bare-`CK` Axiom Schemata -/

/-- Axiom schemata for bare constructive modal logic `CK` ([Wijesekera1990] §2; ianshil
`CKH.v` with `NoAdAx`): the 9 intuitionistic propositional schemata (mirroring
`IntPropAxiom`) plus the two K-distribution schemata `k` (Kb) and `kdia` (Kd).

Deliberately **absent** relative to `IKModalAxiom` (do not add them -- each would change
the logic): `cd` (Fischer-Servi `◇(φ∨ψ) → ◇φ∨◇ψ`), `idb` (Fischer-Servi
`(◇φ→□ψ) → □(φ→ψ)`), and `dbot` (Nd, `◇⊥ → ⊥`). None of the three is `MValid`, and none
is derivable in bare `CK`. -/
inductive CKModalAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)`. -/
  | implyK (φ ψ : Proposition Atom) :
      CKModalAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`. -/
  | implyS (φ ψ χ : Proposition Atom) :
      CKModalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Ex falso quodlibet: `⊥ → φ`. -/
  | efq (φ : Proposition Atom) :
      CKModalAxiom (Proposition.bot.imp φ)
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)`. -/
  | andI (φ ψ : Proposition Atom) :
      CKModalAxiom (Cslib.Logic.Axioms.AndI φ ψ)
  /-- Left conjunction elimination: `φ ∧ ψ → φ`. -/
  | andE1 (φ ψ : Proposition Atom) :
      CKModalAxiom (Cslib.Logic.Axioms.AndE1 φ ψ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ`. -/
  | andE2 (φ ψ : Proposition Atom) :
      CKModalAxiom (Cslib.Logic.Axioms.AndE2 φ ψ)
  /-- Left disjunction introduction: `φ → φ ∨ ψ`. -/
  | orI1 (φ ψ : Proposition Atom) :
      CKModalAxiom (Cslib.Logic.Axioms.OrI1 φ ψ)
  /-- Right disjunction introduction: `ψ → φ ∨ ψ`. -/
  | orI2 (φ ψ : Proposition Atom) :
      CKModalAxiom (Cslib.Logic.Axioms.OrI2 φ ψ)
  /-- Disjunction elimination: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))`. -/
  | orE (φ ψ χ : Proposition Atom) :
      CKModalAxiom (Cslib.Logic.Axioms.OrE φ ψ χ)
  /-- Kb: `□(φ → ψ) → (□φ → □ψ)`. -/
  | k (φ ψ : Proposition Atom) :
      CKModalAxiom
        ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ)))
  /-- Kd: `□(φ → ψ) → (◇φ → ◇ψ)`. -/
  | kdia (φ ψ : Proposition Atom) :
      CKModalAxiom ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ)))

/-! ## Exploding-World Validity

Bare `CK` is **not** sound for raw `MValid`: `⊥ → p` is a `CK` axiom (`efq`), yet with
`botForces := fun _ => True` and `val := fun _ _ => False` (both trivially upward-closed) the
formula `⊥ → p` is not forced anywhere. Soundness requires the *fallible-model* ("exploding
world") conditions of [Wijesekera1990]-style semantics, mechanized in ianshil/CK
`Kripke/kripke_sem.v`: there, frames carry a distinguished exploding node `expl` with
`val_expl : ∀ p, val expl p`, `mreach_expl : mreachable expl u ↔ u = expl`, and
`ireach_expl : ireachable expl u → u = expl`, and the `Expl` lemma shows `expl` forces every
formula. `EValid` below states these conditions in predicate form over `botForces` (any
ianshil-style model instantiates them with `botForces := (· = expl)`):

- `botForces w → val w p` (every exploding world forces all atoms; `val_expl`),
- `botForces w → r w u → botForces u` (modal successors of exploding worlds explode;
  `mreach_expl`, forward direction),
- `botForces w → ∃ u, r w u ∧ botForces u` (every exploding world has an exploding modal
  successor; `mreach_expl`, backward direction — this is what forces exploding worlds to
  satisfy `◇⊥`),

plus the upward-closure `bf_uc` already present in `MValid` (generalizing `ireach_expl`).

Validity strength: `MValid → EValid → IValid` (each quantifies over a smaller model class).
`CK` is sound and complete for `EValid`; completeness from the stronger hypothesis `MValid`
follows as a corollary. -/

universe w₁

/-- Exploding-world (fallible) modal validity: forced at every world in every birelational
model whose `botForces` predicate satisfies the three explosion conditions of fallible-world
semantics ([Wijesekera1990]; ianshil/CK `kripke_sem.v`), in addition to the upward-closure
required by `MValid`. This is the validity notion for which bare `CK` is sound and complete. -/
def EValid (φ : Proposition Atom) : Prop :=
  ∀ (World : Type v) [Preorder World] (r : World → World → Prop)
    (_f1 : ∀ {w w' u : World}, w ≤ w' → r w u → ∃ u', r w' u' ∧ u ≤ u')
    (_f2 : ∀ {w u u' : World}, r w u → u ≤ u' → ∃ w', w ≤ w' ∧ r w' u')
    (val : World → Atom → Prop) (botForces : World → Prop),
    (∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p) →
    (∀ {w w' : World}, w ≤ w' → botForces w → botForces w') →
    (∀ {w : World} (p : Atom), botForces w → val w p) →
    (∀ {w u : World}, botForces w → r w u → botForces u) →
    (∀ {w : World}, botForces w → ∃ u, r w u ∧ botForces u) →
    ∀ w, BForces r val botForces w φ

/-- Minimal validity implies exploding-world validity: `EValid` quantifies over a smaller
class of models (those additionally satisfying the explosion conditions). -/
theorem mvalid_implies_evalid {φ : Proposition Atom}
    (h : MValid.{u, v} φ) : EValid.{u, v} φ :=
  fun World _ r f1 f2 val botForces v_uc bf_uc _ _ _ w =>
    h World r f1 f2 val botForces v_uc bf_uc w

/-- Exploding-world validity implies intuitionistic validity: with
`botForces := fun _ => False` all three explosion conditions hold vacuously. -/
theorem evalid_implies_ivalid {φ : Proposition Atom}
    (h : EValid.{u, v} φ) : IValid.{u, v} φ :=
  fun World _ r f1 f2 val v_uc w =>
    h World r f1 f2 val (fun _ => False) v_uc (fun _ hf => hf.elim)
      (fun _ hf => hf.elim) (fun hf => hf.elim) (fun hf => hf.elim) w

/-- Exploding worlds force every formula (the `Expl` lemma of ianshil/CK `kripke_sem.v`,
stated in predicate form): under the three explosion conditions plus upward-closure of
`botForces`, any world satisfying `botForces` forces every formula. By induction on the
formula; the `diamond` case consumes the exploding-successor witness, the `box` case the
exploding-successor propagation. -/
theorem bforces_of_exploding {World : Type w₁} [Preorder World]
    {r : World → World → Prop} {val : World → Atom → Prop} {botForces : World → Prop}
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    (bf_val : ∀ {w : World} (p : Atom), botForces w → val w p)
    (bf_r : ∀ {w u : World}, botForces w → r w u → botForces u)
    (bf_r_wit : ∀ {w : World}, botForces w → ∃ u, r w u ∧ botForces u)
    {w : World} (hw : botForces w) (φ : Proposition Atom) :
    BForces r val botForces w φ := by
  induction φ generalizing w with
  | atom p => exact bf_val p hw
  | bot => exact hw
  | imp φ ψ _ ihψ =>
    intro w' hle _
    exact ihψ (bf_uc hle hw)
  | and φ ψ ihφ ihψ => exact ⟨ihφ hw, ihψ hw⟩
  | or φ ψ ihφ _ => exact Or.inl (ihφ hw)
  | box φ ih =>
    intro w' hle u hru
    exact ih (bf_r (bf_uc hle hw) hru)
  | diamond φ ih =>
    obtain ⟨u, hru, hu⟩ := bf_r_wit hw
    exact ⟨u, hru, ih hu⟩

/-! ## Soundness -/

/-- Every `CKModalAxiom` instance is `EValid`.

The nine non-modal cases mirror `ik_axiom_sound`, with two changes: persistence routes
through the arbitrary upward-closed `botForces` (`bforces_persistence` is generic), and the
`efq` case — vacuous under `IValid` — here consumes `bforces_of_exploding` (an exploding
world forces the conclusion outright). The `k`/`kdia` cases never inspect `botForces` and
carry over unchanged. The `cd`/`idb`/`dbot` cases of `ik_axiom_sound` have no counterpart:
bare `CK` lacks those axioms (indeed none of them is `EValid`). -/
theorem ck_axiom_sound {φ : Proposition Atom} (h_ax : CKModalAxiom φ) : EValid.{u, v} φ := by
  intro World _ r f1 f2 val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  cases h_ax with
  | implyK φ ψ =>
    intro w' _ hφ w'' hw' _
    exact bforces_persistence (F := ⟨r, f1, f2⟩) v_uc bf_uc hw' hφ
  | implyS φ ψ χ =>
    intro w₁ hw₁ h_pqr w₂ hw₂ h_pq w₃ hw₃ h_p
    have h₁₃ : w₁ ≤ w₃ := le_trans hw₂ hw₃
    exact h_pqr w₃ h₁₃ h_p w₃ (le_refl w₃) (h_pq w₃ hw₃ h_p)
  | efq φ =>
    intro w' _ hbot
    exact bforces_of_exploding bf_uc bf_val bf_r bf_r_wit hbot φ
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
    intro w' _ hbox_imp w'' hw' hbox_phi w1 hw1 u hru
    exact hbox_imp w1 (le_trans hw' hw1) u hru u (le_refl u) (hbox_phi w1 hw1 u hru)
  | kdia φ ψ =>
    intro w' _ hbox_imp w'' hw' hdia_phi
    obtain ⟨u, hru, hφu⟩ := hdia_phi
    exact ⟨u, hru, hbox_imp w'' hw' u hru u (le_refl u) hφu⟩

/-- **Soundness**: if `DerivationTree CKModalAxiom Γ φ`, then in any birelational model
satisfying the explosion conditions, at any world `w` where all formulas in `Γ` are forced,
`φ` is also forced. The `necessitation` case recurses into the empty-context premise at the
successor world, exactly as `ik_soundness`. -/
theorem ck_soundness
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree CKModalAxiom Γ φ)
    {World : Type v} [Preorder World]
    (r : World → World → Prop)
    (f1 : ∀ {w w' u : World}, w ≤ w' → r w u → ∃ u', r w' u' ∧ u ≤ u')
    (f2 : ∀ {w u u' : World}, r w u → u ≤ u' → ∃ w', w ≤ w' ∧ r w' u')
    (val : World → Atom → Prop) (botForces : World → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    (bf_val : ∀ {w : World} (p : Atom), botForces w → val w p)
    (bf_r : ∀ {w u : World}, botForces w → r w u → botForces u)
    (bf_r_wit : ∀ {w : World}, botForces w → ∃ u, r w u ∧ botForces u)
    (w : World)
    (h_ctx : ∀ ψ, ψ ∈ Γ → BForces r val botForces w ψ) :
    BForces r val botForces w φ := by
  match d with
  | .ax _ ψ h_ax =>
    exact ck_axiom_sound h_ax World r f1 f2 val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact ck_soundness d₁ r f1 f2 val botForces v_uc bf_uc bf_val bf_r bf_r_wit w h_ctx
      w (le_refl w)
      (ck_soundness d₂ r f1 f2 val botForces v_uc bf_uc bf_val bf_r bf_r_wit w h_ctx)
  | .necessitation ψ d' =>
    intro w' _hle u _hru
    exact ck_soundness d' r f1 f2 val botForces v_uc bf_uc bf_val bf_r bf_r_wit u
      (fun _ h => nomatch h)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact ck_soundness d' r f1 f2 val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Soundness for derivable formulas**: if `Derivable CKModalAxiom φ`, then `φ` is
`EValid`. -/
theorem ck_soundness_derivable {φ : Proposition Atom}
    (h : Derivable CKModalAxiom φ) : EValid.{u, v} φ := by
  intro World _ r f1 f2 val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  obtain ⟨d⟩ := h
  exact ck_soundness d r f1 f2 val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
    (fun _ h => nomatch h)

end Cslib.Logic.Modal
