/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Defs.Unbundled

/-! # Birelational Modal Kripke Semantics

This module defines the birelational (intuitionistic Kripke) semantics for the fully-primitive
modal `Proposition {atom, bot, imp, and, or, box, diamond}` (`Cslib.Logic.Modal.Proposition`).
It is the semantic base layer for intuitionistic and minimal modal logic.

## Main Definitions

- `BFrame`: A birelational frame bundles a preordered set of worlds with a modal accessibility
  relation `r`, subject to the up/down confluence conditions `f1`/`f2` relating `≤` and `r`.
- `BModel`: A birelational model extends `BFrame` with an upward-closed valuation `v` and an
  upward-closed `botForces` predicate, mirroring `PL.KripkeModel`.
- `BForces`: The forcing relation for birelational semantics, parameterized by `r`/`v`/`botForces`.
  Recursion on `Modal.Proposition` with seven cases: the five non-modal cases match
  `PL.IForces` exactly; `box` quantifies over `≤ ∘ r` (Simpson's clause 3.2) and `diamond`
  quantifies over `r` alone (clause 3.5).
- `bforces_persistence`: Persistence of forcing under `≤` (Simpson's monotonicity lemma). The
  `diamond` case uses frame condition `F1`; all other cases require no frame condition.
- `IValid`: Intuitionistic modal validity -- forced at every world in every birelational model
  (where `botForces = fun _ => False`).
- `MValid`: Minimal modal validity -- forced at every world in every birelational model (where
  `botForces` is an arbitrary upward-closed predicate).

## Design Notes

- Uses `Preorder World` rather than `PartialOrder World`: antisymmetry is never needed, matching
  `PL.KripkeModel`.
- The forcing relation is named `BForces` (not `Satisfies`) to avoid shadowing the existing
  classical `Modal.Satisfies` in the same `Cslib.Logic.Modal` namespace.
- `BForces` takes loose `r`/`v`/`botForces` parameters (mirroring `PL.IForces`); `BFrame`/`BModel`
  bundle the frame/model data and are used for the `IValid`/`MValid` validity definitions.
- Both `F1` (up-confluence) and `F2` (down-confluence) are included in `BFrame` now. `F2` is
  unused by the lemmas in this file but is the correct IK frame class for downstream
  intuitionistic and minimal completeness work.
- Reuses `Cslib.Logic.Modal.Proposition` and its `HasBox`/`HasDiamond`/`HasAnd`/`HasOr`/`Bot`
  connective instances from `Modal/Basic.lean`; no new formula datatype or connective typeclass
  is introduced.

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3, clauses 3.2 (`□`) and 3.5 (`◇`), frame conditions F1/F2.
-/

@[expose] public section

universe u v

namespace Cslib.Logic.Modal

variable {Atom : Type u}

/-- A birelational (intuitionistic Kripke) frame: a preordered set of worlds carrying a modal
accessibility relation `r`, subject to the up/down confluence conditions relating `≤` and `r`
([Simpson1994], Chapter 3). -/
structure BFrame (World : Type*) [Preorder World] where
  /-- Modal accessibility relation. -/
  r : World → World → Prop
  /-- (F1) up-confluence (`≤; r ⊆ r; ≤`): if `w ≤ w'` and `r w v`, then some `v' ≥ v` has
  `r w' v'`. This is what makes the standard `◇` clause monotone. -/
  f1 : ∀ {w w' v : World}, w ≤ w' → r w v → ∃ v', r w' v' ∧ v ≤ v'
  /-- (F2) down-confluence (`r; ≤ ⊆ ≤; r`): if `r w v` and `v ≤ v'`, then some `w' ≥ w` has
  `r w' v'`. Needed to validate the IK interaction axioms and for completeness of the
  intuitionistic/constructive modal calculi built on this frame (IK, CK, and their
  extensions). -/
  f2 : ∀ {w v v' : World}, r w v → v ≤ v' → ∃ w', w ≤ w' ∧ r w' v'

/-- A birelational model adds a heredity (upward-closed) valuation and a `botForces` predicate
(`fun _ => False` for the intuitionistic case; arbitrary upward-closed for the minimal case) to a
`BFrame`, mirroring `PL.KripkeModel`. -/
structure BModel (World : Type*) (Atom : Type*) [Preorder World] extends BFrame World where
  /-- Valuation assigning propositions to atoms at each world. -/
  v : World → Atom → Prop
  /-- Predicate controlling whether falsum is forced at a world. Set to `fun _ => False` for
  intuitionistic semantics. -/
  botForces : World → Prop
  /-- The valuation is upward-closed: if `v w p` and `w ≤ w'`, then `v w' p`. -/
  v_upward_closed : ∀ {w w' : World} (p : Atom), w ≤ w' → v w p → v w' p
  /-- `botForces` is upward-closed: if `botForces w` and `w ≤ w'`, then `botForces w'`. -/
  bf_upward_closed : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w'

/-- Birelational forcing for the primitive modal `Proposition`, parameterized by the modal
relation `r`, valuation `v`, and `botForces` predicate.

The five non-modal cases match the intuitionistic propositional clauses (`PL.IForces`) exactly:
- `atom p`: forced iff the valuation assigns `p` at world `w`
- `bot`: forced iff `botForces w`
- `imp φ ψ`: forced iff for every successor `w' ≥ w`, forcing `φ` at `w'` implies forcing `ψ`
  at `w'`
- `and φ ψ`: forced iff both `φ` and `ψ` are forced at `w`
- `or φ ψ`: forced iff `φ` or `ψ` is forced at `w`

The two modal cases follow Simpson's birelational clauses ([Simpson1994], clauses 3.2/3.5):
- `box φ` (clause 3.2): forced iff for every `w' ≥ w` and every `u` with `r w' u`, `φ` is forced
  at `u`, i.e. `box` quantifies over the composition `≤ ∘ r`.
- `diamond φ` (clause 3.5): forced iff some `u` with `r w u` forces `φ`, i.e. `diamond`
  quantifies over `r` alone. -/
def BForces [Preorder World] (r : World → World → Prop)
    (v : World → Atom → Prop) (botForces : World → Prop)
    (w : World) : Proposition Atom → Prop
  | .atom p => v w p
  | .bot => botForces w
  | .imp φ ψ => ∀ w', w ≤ w' → BForces r v botForces w' φ → BForces r v botForces w' ψ
  | .and φ ψ => BForces r v botForces w φ ∧ BForces r v botForces w ψ
  | .or φ ψ => BForces r v botForces w φ ∨ BForces r v botForces w ψ
  | .box φ => ∀ w', w ≤ w' → ∀ u, r w' u → BForces r v botForces u φ
  | .diamond φ => ∃ u, r w u ∧ BForces r v botForces u φ

@[simp] theorem BForces_atom [Preorder World]
    (r : World → World → Prop) (v : World → Atom → Prop) (botForces : World → Prop)
    (w : World) (p : Atom) :
    BForces r v botForces w (.atom p) = v w p := rfl

@[simp] theorem BForces_bot [Preorder World]
    (r : World → World → Prop) (v : World → Atom → Prop) (botForces : World → Prop)
    (w : World) :
    BForces r v botForces w .bot = botForces w := rfl

@[simp] theorem BForces_imp [Preorder World]
    (r : World → World → Prop) (v : World → Atom → Prop) (botForces : World → Prop)
    (w : World) (φ ψ : Proposition Atom) :
    BForces r v botForces w (.imp φ ψ) =
      ∀ w', w ≤ w' → BForces r v botForces w' φ → BForces r v botForces w' ψ := rfl

@[simp] theorem BForces_and [Preorder World]
    (r : World → World → Prop) (v : World → Atom → Prop) (botForces : World → Prop)
    (w : World) (φ ψ : Proposition Atom) :
    BForces r v botForces w (.and φ ψ) =
      (BForces r v botForces w φ ∧ BForces r v botForces w ψ) := rfl

@[simp] theorem BForces_or [Preorder World]
    (r : World → World → Prop) (v : World → Atom → Prop) (botForces : World → Prop)
    (w : World) (φ ψ : Proposition Atom) :
    BForces r v botForces w (.or φ ψ) =
      (BForces r v botForces w φ ∨ BForces r v botForces w ψ) := rfl

@[simp] theorem BForces_box [Preorder World]
    (r : World → World → Prop) (v : World → Atom → Prop) (botForces : World → Prop)
    (w : World) (φ : Proposition Atom) :
    BForces r v botForces w (.box φ) =
      ∀ w', w ≤ w' → ∀ u, r w' u → BForces r v botForces u φ := rfl

@[simp] theorem BForces_diamond [Preorder World]
    (r : World → World → Prop) (v : World → Atom → Prop) (botForces : World → Prop)
    (w : World) (φ : Proposition Atom) :
    BForces r v botForces w (.diamond φ) =
      ∃ u, r w u ∧ BForces r v botForces u φ := rfl

/-- Persistence of forcing under `≤` (Simpson's monotonicity lemma, [Simpson1994], Lemma 2.2.1
generalized to the modal setting). The proof is by structural induction on the formula:
- **atom**: follows from upward-closure of the valuation.
- **bot**: follows from upward-closure of `botForces`.
- **imp**/**box**: follow from transitivity of the preorder (no frame condition needed).
- **and**/**or**: follow directly from the inductive hypotheses.
- **diamond**: uses frame condition **F1** to transport the witness world along `≤`. -/
theorem bforces_persistence [Preorder World] {F : BFrame World}
    {v : World → Atom → Prop} {botForces : World → Prop}
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → v w p → v w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    {w w' : World} (hww' : w ≤ w') {φ : Proposition Atom}
    (hf : BForces F.r v botForces w φ) : BForces F.r v botForces w' φ := by
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
  | diamond φ ih =>
    obtain ⟨u, hru, hfu⟩ := hf
    obtain ⟨u', hru', huu'⟩ := F.f1 hww' hru
    exact ⟨u', hru', ih huu' hfu⟩

/-- A formula is intuitionistically modally valid (`IValid`) if it is forced at every world in
every birelational model, i.e., for every preordered type of worlds, every modal relation `r`
satisfying F1/F2, every upward-closed valuation, and with `botForces = fun _ => False`. -/
def IValid (φ : Proposition Atom) : Prop :=
  ∀ (World : Type v) [Preorder World] (r : World → World → Prop)
    (_f1 : ∀ {w w' u : World}, w ≤ w' → r w u → ∃ u', r w' u' ∧ u ≤ u')
    (_f2 : ∀ {w u u' : World}, r w u → u ≤ u' → ∃ w', w ≤ w' ∧ r w' u')
    (val : World → Atom → Prop),
    (∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p) →
    ∀ w, BForces r val (fun _ => False) w φ

/-- A formula is minimally modally valid (`MValid`) if it is forced at every world in every
birelational model, i.e., for every preordered type of worlds, every modal relation `r`
satisfying F1/F2, every upward-closed valuation, and every upward-closed `botForces`
predicate. -/
def MValid (φ : Proposition Atom) : Prop :=
  ∀ (World : Type v) [Preorder World] (r : World → World → Prop)
    (_f1 : ∀ {w w' u : World}, w ≤ w' → r w u → ∃ u', r w' u' ∧ u ≤ u')
    (_f2 : ∀ {w u u' : World}, r w u → u ≤ u' → ∃ w', w ≤ w' ∧ r w' u')
    (val : World → Atom → Prop) (botForces : World → Prop),
    (∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p) →
    (∀ {w w' : World}, w ≤ w' → botForces w → botForces w') →
    ∀ w, BForces r val botForces w φ

/-- Minimal modal validity implies intuitionistic modal validity.

Since `IValid` is `MValid` with `botForces = fun _ => False` (which is trivially
upward-closed), any minimally valid formula is also intuitionistically valid. -/
theorem mvalid_implies_ivalid {φ : Proposition Atom}
    (h : (MValid.{u, v} φ)) : IValid.{u, v} φ :=
  fun World _ r f1 f2 val v_uc w =>
    h World r f1 f2 val (fun _ => False) v_uc (fun {_ _} _ hf => absurd hf id) w

end Cslib.Logic.Modal
