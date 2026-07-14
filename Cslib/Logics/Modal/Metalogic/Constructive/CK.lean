/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Constructive.CKTruthLemma
public import Cslib.Logics.Modal.Semantics.Birelational

/-! # CK: Constructive Modal Logic K (Soundness + Completeness)

This module defines bare constructive modal logic `CK` ([Wijesekera1990]) and proves its
soundness and completeness for the Wijesekera-style fallible-world semantics
(`CKForces`/`CKValid`, `Constructive/Forcing.lean`), via the canonical segment model
(`Constructive/Segment.lean`, `SegmentLindenbaum.lean`, `CKTruthLemma.lean`) —
transliterating ianshil/CK `Completeness_seg/CK_seg_completeness.v`.

`CK` is the strict sub-system of Simpson's `IK` obtained by *dropping* the Fischer-Servi
axioms `Cd` (`◇(φ∨ψ) → ◇φ∨◇ψ`) and `Idb` (`(◇φ→□ψ) → □(φ→ψ)`) and the nullary axiom
`Nd` (`◇⊥ → ⊥`): only the two K-distribution schemata `Kb` and `Kd` remain, over the same
9 intuitionistic propositional schemata.

## Main Definitions and Results

- `CKModalAxiom`: the axiom schemata of bare `CK` -- 9 intuitionistic propositional schemata
  plus `k` (Kb) and `kdia` (Kd). **No** `cd`/`idb`/`dbot` constructors.
- `ck_axiom_sound`/`ck_soundness`/`ck_soundness_derivable`: soundness for `CKValid`.
- `ck_completeness`: completeness for `CKValid`, via the segment canonical model.
- `ck_soundness_completeness`: `Derivable CKModalAxiom φ ↔ CKValid φ`.
- `ck_consistent`: `⊥` is not derivable.
- Secondary: `EValid` (explosion-conditioned validity over the *birelational* `BForces`)
  and `ck_soundness_derivable_bforces` — `CK` is sound, but **not** complete, for the
  birelational `∃`-diamond semantics (see the `EValid` section below).

## Why the semantics is `CKValid`, not `MValid`/`IValid`

Two counterexamples pin the choice (both verified against ianshil/CK `kripke_sem.v`):

1. **`MValid` soundness fails at `efq`**: with `botForces := fun _ => True` and
   `val := fun _ _ => False` (both upward-closed), `⊥ → p` is not `BForces`-forced anywhere,
   yet it is a `CK` axiom. Fallible-world semantics needs the *explosion conditions*
   (exploding worlds force all atoms; their modal successors explode; they have an exploding
   modal successor) — `MValid` has none.
2. **`BForces`-based completeness fails at `Cd`**: under the plain `∃` diamond clause of
   `BForces`, `Cd = ◇(φ∨ψ) → ◇φ∨◇ψ` is valid outright (no frame condition, no `botForces`
   facts — see the `cd` case of `ik_axiom_sound`), and `Idb` is validated by the `F2`
   confluence baked into `MValid`. Neither is derivable in bare `CK` (ianshil treats
   `CK+Cd`, `CK+Idb` as proper extensions). Bare `CK` therefore requires the **∀∃ diamond
   clause** over frames with **no confluence conditions** — exactly `CKForces`/`CKValid`.

Dually, under `IValid` (infallible `botForces = fun _ => False`) the non-theorem
`Nd = ◇⊥ → ⊥` is vacuously valid, so `CK` is incomplete for `IValid` as well: fallible
worlds are unavoidable.

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
  formalization follows the ianshil/CK convention (`NoAdAx`): *bare* `CK` **excludes** `Nd`
  (which is not `CKValid`: exploding worlds force `◇⊥`).

## References

* [D. Wijesekera, *Constructive modal logics I*][Wijesekera1990], §2 and Definition 1.1.4.
* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (the `IK` superset; the contrasting birelational semantics).
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Lemma 5.5.
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
`(◇φ→□ψ) → □(φ→ψ)`), and `dbot` (Nd, `◇⊥ → ⊥`). None of the three is derivable in bare
`CK`, and none is `CKValid` -- though `cd` and `idb` *are* valid for the birelational
`BForces` semantics (which is why `CK` completeness is stated over `CKValid`, not
`MValid`; see the module docstring). -/
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

/-! ## Soundness (for `CKValid`) -/

/-- Every `CKModalAxiom` instance is `CKValid`.

The nine non-modal cases mirror `ik_axiom_sound`, with persistence routed through
`ckforces_persistence` (no frame condition) and the `efq` case — vacuous under `IValid` —
consuming `ckforces_of_exploding` (an exploding world forces the conclusion outright).
`k` is pure quantifier bookkeeping; `kdia` threads the box hypothesis through the ∀∃
diamond clause. -/
theorem ck_axiom_sound {φ : Proposition Atom} (h_ax : CKModalAxiom φ) : CKValid.{u, v} φ := by
  intro World _ r val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
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

/-- **Soundness**: if `DerivationTree CKModalAxiom Γ φ`, then in any fallible-world model
(explosion conditions of `CKValid`), at any world `w` where all formulas in `Γ` are forced,
`φ` is also forced. The `necessitation` case recurses into the empty-context premise at the
successor world, exactly as `ik_soundness`. -/
theorem ck_soundness
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree CKModalAxiom Γ φ)
    {World : Type v} [Preorder World]
    (r : World → World → Prop)
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
    exact ck_axiom_sound h_ax World r val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact ck_soundness d₁ r val botForces v_uc bf_uc bf_val bf_r bf_r_wit w h_ctx
      w (le_refl w)
      (ck_soundness d₂ r val botForces v_uc bf_uc bf_val bf_r bf_r_wit w h_ctx)
  | .necessitation ψ d' =>
    intro w' _hle u _hru
    exact ck_soundness d' r val botForces v_uc bf_uc bf_val bf_r bf_r_wit u
      (fun _ h => nomatch h)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact ck_soundness d' r val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Soundness for derivable formulas**: if `Derivable CKModalAxiom φ`, then `φ` is
`CKValid`. -/
theorem ck_soundness_derivable {φ : Proposition Atom}
    (h : Derivable CKModalAxiom φ) : CKValid.{u, v} φ := by
  intro World _ r val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  obtain ⟨d⟩ := h
  exact ck_soundness d r val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
    (fun _ h => nomatch h)

/-! ## Completeness -/

/-- **Completeness for `CK`**: any `CKValid` formula is derivable from `CKModalAxiom`.

Contrapositive of the canonical-model argument: an underivable `φ` is excluded from the
head of some segment (`segment_realization`); the canonical segment model — worlds
`CKSegment CKModalAxiom`, accessibility `cmreach`, valuation `cval`, fallibility
`cbotForces` — satisfies the explosion conditions of `CKValid`
(`cbotForces_val`/`cbotForces_mreach`/`cbotForces_mreach_wit`), so `CKValid φ` forces `φ`
at that segment, and the truth lemma converts forcing back to head membership —
contradiction. -/
theorem ck_completeness {φ : Proposition Atom} (h_valid : CKValid.{u, u} φ) :
    Derivable CKModalAxiom φ := by
  by_contra h_nd
  obtain ⟨s, hs⟩ := segment_realization (Axioms := CKModalAxiom)
    (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ) (fun A B χ => .orE A B χ) h_nd
  have hf : CKForces cmreach cval cbotForces s φ :=
    h_valid (CKSegment CKModalAxiom) cmreach cval cbotForces
      (fun p hle hv => cval_upward_closed p hle hv)
      (fun hle hb => cbotForces_upward_closed hle hb)
      (fun p hb => cbotForces_val (fun φ => .efq φ) p hb)
      (fun hb hr => cbotForces_mreach (fun φ => .efq φ) hb hr)
      (fun hb => cbotForces_mreach_wit (fun φ => .efq φ) hb)
      s
  exact hs ((ck_truth_lemma
    (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ ψ => .orI1 φ ψ) (fun φ ψ => .orI2 φ ψ) (fun A B χ => .orE A B χ)
    (fun φ ψ => .andI φ ψ) (fun φ ψ => .andE1 φ ψ) (fun φ ψ => .andE2 φ ψ)
    (fun φ ψ => .k φ ψ) (fun φ ψ => .kdia φ ψ) s φ).mp hf)

/-- **Consistency of `CK`**: `⊥` is not derivable from `CKModalAxiom`. A corollary of
soundness, instantiated at the trivial one-point infallible model (`botForces := fun _ =>
False` satisfies the explosion conditions vacuously). -/
theorem ck_consistent : ¬ Derivable CKModalAxiom (Proposition.bot : Proposition Atom) := by
  intro h
  exact ck_soundness_derivable h Unit (fun _ _ => False) (fun _ _ => False) (fun _ => False)
    (fun _ _ hv => hv) (fun _ hb => hb) (fun _ hb => hb.elim) (fun hb _ => hb)
    (fun hb => hb.elim) ()

/-- **Soundness-completeness biconditional for `CK`**: `φ` is derivable from `CKModalAxiom`
iff `φ` is `CKValid`. -/
theorem ck_soundness_completeness {φ : Proposition Atom} :
    Derivable CKModalAxiom φ ↔ CKValid.{u, u} φ :=
  ⟨ck_soundness_derivable, ck_completeness⟩

/-! ## Secondary: Soundness for the Birelational `∃`-Diamond Semantics

`CK` is also *sound* for the birelational `BForces` semantics of task 490, provided the
explosion conditions are added to `MValid` — the notion `EValid` below. It is **not
complete** for `EValid`: `Cd = ◇(φ∨ψ) → ◇φ∨◇ψ` is `EValid` (indeed `MValid`) via the plain
`∃` diamond clause but not `CK`-derivable. These results document the precise relationship
between the two semantic layers; the sound-and-complete pairing for bare `CK` is
`CKValid` above. Validity strength: `MValid → EValid → IValid`, and
`Derivable CKModalAxiom φ → CKValid φ → ` (`EValid φ` on the common model class). -/

/-- Exploding-world validity over the *birelational* `BForces` semantics: `MValid`'s
quantification (frames with `F1`/`F2` up/down confluence, `∃`-diamond forcing) restricted
by the three explosion conditions of fallible-world semantics. Bare `CK` is sound
(`ck_soundness_derivable_bforces`) but **not** complete for `EValid` (`Cd` is a
counterexample — see the section docstring). -/
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

/-- Exploding worlds force every formula, `BForces` version (cf. `ckforces_of_exploding`):
under the three explosion conditions plus upward-closure of `botForces`, any world
satisfying `botForces` forces every formula. -/
theorem bforces_of_exploding {World : Type v} [Preorder World]
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

/-- Every `CKModalAxiom` instance is `EValid` (birelational version of `ck_axiom_sound`;
the `k`/`kdia` cases never inspect `botForces` and carry over from `ik_axiom_sound`
unchanged). -/
theorem ck_axiom_sound_bforces {φ : Proposition Atom} (h_ax : CKModalAxiom φ) :
    EValid.{u, v} φ := by
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

/-- Birelational soundness for `CK` derivations (BForces version of `ck_soundness`). -/
theorem ck_soundness_bforces
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
    exact ck_axiom_sound_bforces h_ax World r f1 f2 val botForces v_uc bf_uc bf_val bf_r
      bf_r_wit w
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact ck_soundness_bforces d₁ r f1 f2 val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
      h_ctx w (le_refl w)
      (ck_soundness_bforces d₂ r f1 f2 val botForces v_uc bf_uc bf_val bf_r bf_r_wit w h_ctx)
  | .necessitation ψ d' =>
    intro w' _hle u _hru
    exact ck_soundness_bforces d' r f1 f2 val botForces v_uc bf_uc bf_val bf_r bf_r_wit u
      (fun _ h => nomatch h)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact ck_soundness_bforces d' r f1 f2 val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Birelational soundness for derivable formulas**: if `Derivable CKModalAxiom φ`, then
`φ` is `EValid`. The converse fails (`Cd`), so this direction is strictly weaker than
`ck_soundness_completeness`. -/
theorem ck_soundness_derivable_bforces {φ : Proposition Atom}
    (h : Derivable CKModalAxiom φ) : EValid.{u, v} φ := by
  intro World _ r f1 f2 val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  obtain ⟨d⟩ := h
  exact ck_soundness_bforces d r f1 f2 val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
    (fun _ h => nomatch h)

end Cslib.Logic.Modal
