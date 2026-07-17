import Cslib.Logics.Modal.Metalogic.Constructive.CS5
import Mathlib.Data.Fintype.Pi

/-! Probe C for task 509: the box-backward gap is REAL, not vacuous.

`cs5_symmetric_tail_box_gap` (probe B, C7) says: if `□(p ∨ □q) ∈ H` and `q ∉ H` then every
member of `H`'s symmetric tail contains `p`. That is only an obstruction if its hypotheses are
jointly satisfiable together with `□p ∉ H`. This probe exhibits a three-world `cs5FC''` model
whose world `w` realizes exactly that configuration, so `H := Th(w)` witnesses satisfiability
(`Th(w)` is quasi-prime: deductively closed by soundness over `cs5FC''`, prime because `∨` is
local in `CKForces`).

Worlds `w`, `wp = w'`, `u`; intuitionistic order `w ≤ w'` only; `r`-classes `{w}` and
`{w', u}`. Atom `false = p` holds at `w, w'`; atom `true = q` holds at `w', u`.
-/

namespace Cslib.Logic.Modal

open Cslib.Logic

/-- Three worlds. A fresh inductive type, NOT `Fin 3`: `Fin` carries its own `LE` instance,
which would collide with the intuitionistic order defined below. -/
inductive W3 | w | wp | u
  deriving DecidableEq

instance : Fintype W3 := ⟨{W3.w, W3.wp, W3.u}, fun x => by cases x <;> decide⟩

/-- Intuitionistic order: reflexive, plus `w ≤ w'` only. -/
def w3le (a b : W3) : Prop := a = b ∨ (a = .w ∧ b = .wp)

instance w3leDec (a b : W3) : Decidable (w3le a b) := by unfold w3le; infer_instance

instance : Preorder W3 where
  le := w3le
  lt a b := w3le a b ∧ ¬ w3le b a
  le_refl _ := Or.inl rfl
  le_trans a b c hab hbc := by revert hab hbc; revert a b c; decide
  lt_iff_le_not_ge _ _ := Iff.rfl

instance w3leDec' (a b : W3) : Decidable (a ≤ b) := w3leDec a b

/-- Modal relation: `r`-classes `{w}` and `{w', u}`. -/
def w3r (a b : W3) : Prop := a = b ∨ (a = .wp ∧ b = .u) ∨ (a = .u ∧ b = .wp)

instance w3rDec (a b : W3) : Decidable (w3r a b) := by unfold w3r; infer_instance

/-- Valuation: atom `false = p` at `{w, w'}`; atom `true = q` at `{w', u}`. -/
def w3val (a : W3) (x : Bool) : Prop := if x then (a = .wp ∨ a = .u) else (a = .w ∨ a = .wp)

instance w3valDec (a : W3) (x : Bool) : Decidable (w3val a x) := by unfold w3val; infer_instance

/-- No world is fallible. -/
def w3bot (_a : W3) : Prop := False

/-- The `cs5FC''` clauses, restated here (probe A defines the same predicate). -/
def cs5FC2 {World : Type*} [Preorder World] (r : World → World → Prop) : Prop :=
  (∀ w, r w w)
    ∧ (∀ {w u t}, r w u → r u t → r w t)
    ∧ (∀ {w u}, r w u → r u w)
    ∧ (∀ {w u u' t}, r w u → u ≤ u' → r u' t → ∃ v, w ≤ v ∧ r v t)
    ∧ (∀ {w u u'}, r w u → u ≤ u' → ∃ t, r u' t ∧ w ≤ t)

/-- **The three-world frame satisfies every `cs5FC''` clause.** -/
theorem w3r_fc : cs5FC2 w3r := by
  refine ⟨fun _ => Or.inl rfl, ?_, ?_, ?_, ?_⟩
  · intro a b c hab hbc; revert hab hbc; revert a b c; decide
  · intro a b hab; revert hab; revert a b; decide
  · intro a b b' c hab hbb' hb'c
    revert hab hbb' hb'c; revert a b b' c; decide
  · intro a b b' hab hbb'
    revert hab hbb'; revert a b b'; decide

/-! ## The configuration at `w` -/

/-- `□q` holds at `u`: `u`'s only `≤`-successor is `u`, whose `r`-successors are `u` and
`w'` — and `q` holds at both. -/
theorem w3_box_q_at_u :
    CKForces w3r w3val w3bot .u (Proposition.box (Proposition.atom true)) := by
  intro z hz t hrt
  show w3val t true
  revert hz hrt; revert z t; decide

/-- **`□(p ∨ □q)` holds at `w`.** In fact `p ∨ □q` holds at *every* world: `p` at `w` and
`w'`, and `□q` at `u`. -/
theorem w3_p_or_box_q (t : W3) :
    CKForces w3r w3val w3bot t
      ((Proposition.atom false).or (Proposition.box (Proposition.atom true))) := by
  show w3val t false
    ∨ CKForces w3r w3val w3bot t (Proposition.box (Proposition.atom true))
  by_cases hp : w3val t false
  · exact Or.inl hp
  · have ht2 : t = .u := by revert hp; revert t; decide
    exact ht2 ▸ Or.inr w3_box_q_at_u

theorem w3_box_p_or_box_q_at_w :
    CKForces w3r w3val w3bot .w
      (Proposition.box ((Proposition.atom false).or
        (Proposition.box (Proposition.atom true)))) :=
  fun _z _hz t _hrt => w3_p_or_box_q t

/-- **`□p` fails at `w`**: `w ≤ w'`, `r w' u`, and `p` fails at `u`. -/
theorem w3_not_box_p_at_w :
    ¬ CKForces w3r w3val w3bot .w (Proposition.box (Proposition.atom false)) := by
  intro h
  have hpu : w3val .u false := h .wp (Or.inr ⟨rfl, rfl⟩) .u (Or.inr (Or.inl ⟨rfl, rfl⟩))
  revert hpu; decide

/-- **`q` fails at `w`**. -/
theorem w3_not_q_at_w : ¬ CKForces w3r w3val w3bot .w (Proposition.atom true) := by
  show ¬ w3val .w true
  decide

/-! ## Model conditions (no fallible world; valuation upward closed) -/

theorem w3val_uc {a b : W3} (x : Bool) (hle : a ≤ b) : w3val a x → w3val b x := by
  revert hle; revert a b x; decide

end Cslib.Logic.Modal

#print axioms Cslib.Logic.Modal.w3r_fc
#print axioms Cslib.Logic.Modal.w3_box_p_or_box_q_at_w
#print axioms Cslib.Logic.Modal.w3_not_box_p_at_w
#print axioms Cslib.Logic.Modal.w3_not_q_at_w
#print axioms Cslib.Logic.Modal.w3val_uc
