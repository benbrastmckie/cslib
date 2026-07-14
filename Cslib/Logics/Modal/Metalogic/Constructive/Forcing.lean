/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Basic

/-! # Constructive (Wijesekera-Style) Modal Forcing

This module defines the forcing relation and validity notion for *bare constructive* modal
logic `CK` ([Wijesekera1990]; mechanized in ianshil/CK `Kripke/kripke_sem.v`). It differs
from the birelational `BForces` (`Cslib/Logics/Modal/Semantics/Birelational.lean`, Simpson's
semantics for `IK`) in exactly two coupled respects:

1. **The `diamond` clause is the ∀∃ clause** (`◇φ` forced at `w` iff every `≤`-successor
   `w'` of `w` has an `r`-successor forcing `φ`), rather than Simpson's plain `∃` clause.
2. **Frames carry no confluence conditions** (`F1`/`F2` are absent), and none are needed:
   persistence of `CKForces` holds on arbitrary frames.

This is forced, not a preference: under the plain `∃`-diamond clause, the Fischer-Servi
axiom `Cd = ◇(φ∨ψ) → ◇φ ∨ ◇ψ` is valid outright (the existential witness distributes over
the disjunction — see the `cd` case of `ik_axiom_sound`, which uses no frame condition and
no `botForces` facts), and `Idb` is validated by `F2`. Neither is a theorem of bare `CK`
(ianshil treats `CK+Cd` and `CK+Idb` as proper extensions), so bare `CK` is *incomplete*
for every validity notion built on `BForces` with `F1`/`F2`. Under the ∀∃ clause the witness
may vary with the `≤`-successor, so `Cd` fails, matching `CK`'s proof theory.

## Main Definitions

- `CKForces`: the Wijesekera forcing relation — `BForces`' clauses with the ∀∃ `diamond`.
- `ckforces_persistence`: persistence under `≤`, on arbitrary frames (no `F1`).
- `CKValid`: validity over all fallible ("exploding-world") models: arbitrary preorder,
  arbitrary modal relation, upward-closed valuation and `botForces`, plus the three
  explosion conditions of ianshil `kripke_sem.v` in predicate form
  (`val_expl`/`mreach_expl` forward/`mreach_expl` backward).
- `ckforces_of_exploding`: exploding worlds force every formula (ianshil's `Expl` lemma).

## References

* [D. Wijesekera, *Constructive modal logics I*][Wijesekera1990], Definition 1.1.4
  (clauses (v)/(vi): the ∀∀ box and ∀∃ diamond).
* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (the contrasting `IK` semantics with the `∃` diamond and F1/F2).
-/

@[expose] public section

namespace Cslib.Logic.Modal

universe u v

variable {Atom : Type u}

/-- Wijesekera-style constructive forcing ([Wijesekera1990] Definition 1.1.4; ianshil/CK
`kripke_sem.v` `forces`), parameterized by the modal relation `r`, valuation `v`, and
`botForces` predicate.

The `atom`/`bot`/`and`/`or`/`imp`/`box` clauses coincide with `BForces`; the `diamond`
clause is the **∀∃ clause** (Wijesekera's clause (vi)): `◇φ` is forced at `w` iff every
`≤`-successor `w'` of `w` has an `r`-successor forcing `φ`. This makes persistence hold on
arbitrary frames (no `F1`) and — crucially — leaves `◇` non-distributive over `∨`, matching
bare `CK`. -/
def CKForces [Preorder World] (r : World → World → Prop)
    (v : World → Atom → Prop) (botForces : World → Prop)
    (w : World) : Proposition Atom → Prop
  | .atom p => v w p
  | .bot => botForces w
  | .imp φ ψ => ∀ w', w ≤ w' → CKForces r v botForces w' φ → CKForces r v botForces w' ψ
  | .and φ ψ => CKForces r v botForces w φ ∧ CKForces r v botForces w ψ
  | .or φ ψ => CKForces r v botForces w φ ∨ CKForces r v botForces w ψ
  | .box φ => ∀ w', w ≤ w' → ∀ u, r w' u → CKForces r v botForces u φ
  | .diamond φ => ∀ w', w ≤ w' → ∃ u, r w' u ∧ CKForces r v botForces u φ

@[simp] theorem CKForces_atom [Preorder World]
    (r : World → World → Prop) (v : World → Atom → Prop) (botForces : World → Prop)
    (w : World) (p : Atom) :
    CKForces r v botForces w (.atom p) = v w p := rfl

@[simp] theorem CKForces_bot [Preorder World]
    (r : World → World → Prop) (v : World → Atom → Prop) (botForces : World → Prop)
    (w : World) :
    CKForces r v botForces w .bot = botForces w := rfl

@[simp] theorem CKForces_imp [Preorder World]
    (r : World → World → Prop) (v : World → Atom → Prop) (botForces : World → Prop)
    (w : World) (φ ψ : Proposition Atom) :
    CKForces r v botForces w (.imp φ ψ) =
      ∀ w', w ≤ w' → CKForces r v botForces w' φ → CKForces r v botForces w' ψ := rfl

@[simp] theorem CKForces_and [Preorder World]
    (r : World → World → Prop) (v : World → Atom → Prop) (botForces : World → Prop)
    (w : World) (φ ψ : Proposition Atom) :
    CKForces r v botForces w (.and φ ψ) =
      (CKForces r v botForces w φ ∧ CKForces r v botForces w ψ) := rfl

@[simp] theorem CKForces_or [Preorder World]
    (r : World → World → Prop) (v : World → Atom → Prop) (botForces : World → Prop)
    (w : World) (φ ψ : Proposition Atom) :
    CKForces r v botForces w (.or φ ψ) =
      (CKForces r v botForces w φ ∨ CKForces r v botForces w ψ) := rfl

@[simp] theorem CKForces_box [Preorder World]
    (r : World → World → Prop) (v : World → Atom → Prop) (botForces : World → Prop)
    (w : World) (φ : Proposition Atom) :
    CKForces r v botForces w (.box φ) =
      ∀ w', w ≤ w' → ∀ u, r w' u → CKForces r v botForces u φ := rfl

@[simp] theorem CKForces_diamond [Preorder World]
    (r : World → World → Prop) (v : World → Atom → Prop) (botForces : World → Prop)
    (w : World) (φ : Proposition Atom) :
    CKForces r v botForces w (.diamond φ) =
      ∀ w', w ≤ w' → ∃ u, r w' u ∧ CKForces r v botForces u φ := rfl

/-- Persistence of `CKForces` under `≤` (ianshil `kripke_sem.v` `Persistence`), on
**arbitrary** frames: unlike `bforces_persistence`, no confluence condition is needed — the
`imp`/`box`/`diamond` cases all close by transitivity of `≤` because each clause universally
quantifies over `≤`-successors. -/
theorem ckforces_persistence [Preorder World]
    {r : World → World → Prop} {v : World → Atom → Prop} {botForces : World → Prop}
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → v w p → v w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    {w w' : World} (hww' : w ≤ w') {φ : Proposition Atom}
    (hf : CKForces r v botForces w φ) : CKForces r v botForces w' φ := by
  induction φ generalizing w w' with
  | atom p => exact v_uc p hww' hf
  | bot => exact bf_uc hww' hf
  | imp φ ψ _ _ =>
    intro u hu hfu
    exact hf u (le_trans hww' hu) hfu
  | and φ ψ ihφ ihψ =>
    exact ⟨ihφ hww' hf.1, ihψ hww' hf.2⟩
  | or φ ψ ihφ ihψ =>
    exact hf.elim (fun h => Or.inl (ihφ hww' h)) (fun h => Or.inr (ihψ hww' h))
  | box φ _ =>
    intro u hu w'' hruw''
    exact hf u (le_trans hww' hu) w'' hruw''
  | diamond φ _ =>
    intro u hu
    exact hf u (le_trans hww' hu)

/-- Constructive (fallible-model) modal validity for bare `CK`: forced at every world in
every Wijesekera-style model — arbitrary preordered worlds, arbitrary modal relation `r`
(**no** confluence conditions), upward-closed valuation and `botForces`, and the three
explosion conditions of ianshil/CK `kripke_sem.v` stated in predicate form (an ianshil model
instantiates them with `botForces := (· = expl)`):

- `botForces w → val w p` (exploding worlds force all atoms; `val_expl`),
- `botForces w → r w u → botForces u` (modal successors of exploding worlds explode;
  `mreach_expl`, forward),
- `botForces w → ∃ u, r w u ∧ botForces u` (exploding worlds have an exploding modal
  successor; `mreach_expl`, backward — this makes exploding worlds force `◇⊥`).

Bare `CK` is sound and complete for `CKValid` (`ck_soundness`/`ck_completeness` in
`Constructive/CK.lean`). -/
def CKValid (φ : Proposition Atom) : Prop :=
  ∀ (World : Type v) [Preorder World] (r : World → World → Prop)
    (val : World → Atom → Prop) (botForces : World → Prop),
    (∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p) →
    (∀ {w w' : World}, w ≤ w' → botForces w → botForces w') →
    (∀ {w : World} (p : Atom), botForces w → val w p) →
    (∀ {w u : World}, botForces w → r w u → botForces u) →
    (∀ {w : World}, botForces w → ∃ u, r w u ∧ botForces u) →
    ∀ w, CKForces r val botForces w φ

/-- Exploding worlds force every formula (ianshil/CK `kripke_sem.v` `Expl`, in predicate
form): under the three explosion conditions plus upward-closure of `botForces`, any world
satisfying `botForces` forces every formula. -/
theorem ckforces_of_exploding [Preorder World]
    {r : World → World → Prop} {val : World → Atom → Prop} {botForces : World → Prop}
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    (bf_val : ∀ {w : World} (p : Atom), botForces w → val w p)
    (bf_r : ∀ {w u : World}, botForces w → r w u → botForces u)
    (bf_r_wit : ∀ {w : World}, botForces w → ∃ u, r w u ∧ botForces u)
    {w : World} (hw : botForces w) (φ : Proposition Atom) :
    CKForces r val botForces w φ := by
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
    intro w' hle
    obtain ⟨u, hru, hu⟩ := bf_r_wit (bf_uc hle hw)
    exact ⟨u, hru, ih hu⟩

end Cslib.Logic.Modal
