/-
Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

module

public import Cslib.Foundations.Relation.Restriction
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.TFAE

/-! # Relations: Euclidean Relations

This module proves basic properties about left and right Euclidean relations, which are use
in modal logic.

TODO: develop an attribute to dualize theorems to the converse of a relation

## References

* [*Simple Laws about Nonprominent Properties of Binary Relations*][Burghardt2018]

-/

@[expose] public section

open Relator

namespace Relation

variable {α : Type*} {r : α → α → Prop}

instance [RightEuclidean r] (s : Set α) : RightEuclidean (α := s) r :=
  ⟨RightEuclidean.rightEuclidean⟩

instance [LeftEuclidean r] (s : Set α) : LeftEuclidean (α := s) r :=
  ⟨LeftEuclidean.leftEuclidean⟩

@[scoped grind →]
lemma refl_serial (r : α → α → Prop) (h : Std.Refl r) : Serial r where
  serial a := ⟨a, h.refl a⟩

instance [instRefl : Std.Refl r] : Serial r := refl_serial r instRefl

namespace RightEuclidean

variable [RightEuclidean r]

/-- A `RightEuclidean` relation is reflexive on its codomain -/
theorem reflOn_cod : (cod r).ReflOn r := fun _ ⟨_, ab⟩ ↦ rightEuclidean ab ab

/-- The converse of a `RightEuclidean` relation is `LeftEuclidean` -/
theorem leftEuclidean_swap : LeftEuclidean (fun a b => r b a) where
  leftEuclidean ca cb := rightEuclidean cb ca

instance [Std.Refl r] : Std.Symm r where
  symm a _ ab := rightEuclidean ab (refl a)

theorem trichotomous_trans [Std.Trichotomous r] : IsTrans α r where
  trans a b c ab bc := by
    have := Std.Trichotomous.trichotomous (r := r) a c
    have cc := reflOn_cod.of_cod bc
    have (ca : r c a) := rightEuclidean ca cc
    grind

theorem antisymm_rightUnique [Std.Antisymm r] : Relator.RightUnique r := by
  intros a b c ab ac
  exact antisymm (rightEuclidean ab ac) (rightEuclidean ac ab)

theorem rightUnique_antisymm (h : Relator.RightUnique r) : Std.Antisymm r where
  antisymm _ _ ab ba := h ba (reflOn_cod.of_cod ab)

theorem rightUnique_trans (h : Relator.RightUnique r) : IsTrans α r where
  trans a b c ab bc := by
    have eq : c = b := h bc (reflOn_cod.of_cod ab)
    simpa [eq]

theorem rightTotal_equiv (h : Relator.RightTotal r) : IsEquiv α r := by
  have : Std.Refl r := ⟨fun a => reflOn_cod.of_cod (h a).choose_spec⟩
  exact {toIsTrans := ⟨fun _ _ _ ab bc => rightEuclidean (symm ab) bc⟩}

omit [RightEuclidean r] in
theorem leftTotal_rightUnique_trans (h₁ : LeftTotal r) (h₂ : RightUnique r) [IsTrans α r] :
    RightEuclidean r where
  rightEuclidean {a b c} ab ac := by
    obtain ⟨d, dc⟩ := h₁ c
    have : b = c := h₂ ab ac
    have : d = c := h₂ (_root_.trans ac dc) ac
    grind

private theorem three_contra [Std.Trichotomous r] [Std.Antisymm r] :
    ¬ ∃ (a b c : α), a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  rintro ⟨a, b, c, _⟩
  have := @Std.Trichotomous.rel_or_eq_or_rel_swap _ r _ a b
  have := @Std.Trichotomous.rel_or_eq_or_rel_swap _ r _ a c
  have := @Std.Trichotomous.rel_or_eq_or_rel_swap _ r _ b c
  have := antisymm_rightUnique (r := r)
  have := @reflOn_cod (r := r)
  simp [Set.ReflOn] at this
  grind [Relator.RightUnique]

theorem trichotomous_antisymm_finite [Std.Trichotomous r] [Std.Antisymm r] : Finite α := by
  classical
  by_contra! h
  apply three_contra (r := r)
  have ⟨_, hcard⟩ := Infinite.exists_subset_card_eq α 3
  have ⟨a, b, c, _, _, _, _⟩ := Finset.card_eq_three.mp hcard
  use a, b, c

theorem trichotomous_antisymm_card [Std.Trichotomous r] [Std.Antisymm r] [Fintype α] :
    Fintype.card α ≤ 2 := by
  by_contra! h
  apply three_contra (r := r)
  have ⟨a, b, c, _⟩ := Fintype.two_lt_card_iff.mp h
  use a, b, c

theorem cod_subset_dom : cod r ⊆ dom r := fun _ ⟨_, ab⟩ ↦ of_cod (reflOn_cod.of_cod ab)

theorem rightTotal_cod : Relator.RightTotal (α := cod r) (β := cod r) r :=
  fun ⟨_, _, h⟩ => of_cod (reflOn_cod.of_cod h)

theorem equiv_cod : IsEquiv (cod r) r := rightTotal_equiv rightTotal_cod

end RightEuclidean

/-- The least right-Euclidean relation containing `r`, defined inductively.

This is the right-Euclidean member of the closure-operator family typified by `Relation.ReflGen`,
`Relation.SymmGen`, and `Relation.EqvGen` in the sibling module
`Cslib/Foundations/Relation/Confluence.lean` (cf. `SymmGen.to_eqvGen` and the closure
characterization `reflTransGen_compRel : ReflTransGen (SymmGen r) = EqvGen r`): an inductive whose
constructors are exactly the generating edges (`base`) together with the closure property being
imposed (`eucl`, the right-Euclidean law).

Semantically `EuclGen r` is the least right-Euclidean relation containing `r`. Such a least
relation exists because right-Euclideanness is closed under arbitrary intersection and the full
relation is right-Euclidean; hence the intersection of all right-Euclidean relations containing
`r` is itself right-Euclidean and contains `r`. `EuclGen.least` is exactly that characterization
in usable form. -/
inductive EuclGen (r : α → α → Prop) : α → α → Prop
  | base {a b} : r a b → EuclGen r a b
  | eucl {a b c} : EuclGen r a b → EuclGen r a c → EuclGen r b c

/-- `EuclGen r` is right-Euclidean -- directly by its `eucl` constructor. -/
instance : RightEuclidean (EuclGen r) where
  rightEuclidean := EuclGen.eucl

/-- `r` embeds into its right-Euclidean closure `EuclGen r`. -/
theorem EuclGen.mono {a b : α} (h : r a b) : EuclGen r a b := EuclGen.base h

/-- **`EuclGen` preserves symmetry of its base relation.** If `r` is symmetric, so is `EuclGen r`:
the `base` case reduces to `r`'s own symmetry, and the `eucl` case needs no induction hypothesis
at all -- given `EuclGen r a b` and `EuclGen r a c` (sharing source `a`), swapping their order
(`eucl hac hab`) directly yields `EuclGen r c b`, the symmetric partner of the constructor's own
conclusion `EuclGen r b c`. Used to build a symmetric-*and*-right-Euclidean (KB5/PER) closure as
`EuclGen (Relation.SymmGen r)`, right-Euclidean unconditionally (the instance above) and symmetric
by this lemma applied to `Relation.SymmGen r` (always symmetric, `Mathlib.Logic.Relation`). -/
theorem EuclGen.symm_of_symm (hsymm : Std.Symm r) {a b : α} (h : EuclGen r a b) :
    EuclGen r b a := by
  cases h with
  | base hab => exact EuclGen.base (hsymm.symm _ _ hab)
  | eucl hab hac => exact EuclGen.eucl hac hab

/-- `EuclGen r` is symmetric whenever `r` is -- the `Std.Symm` instance packaging
`EuclGen.symm_of_symm`. -/
instance [Std.Symm r] : Std.Symm (EuclGen r) where
  symm _ _ h := EuclGen.symm_of_symm ‹Std.Symm r› h

/-- `EuclGen r` is the *least* right-Euclidean relation containing `r`: it lies below every
right-Euclidean relation `s` that contains `r`. This is the intersection characterization of the
closure made usable -- given any right-Euclidean `s` with `r ≤ s`, induction on the closure shows
`EuclGen r ≤ s`. -/
theorem EuclGen.least {s : α → α → Prop} {a b : α} (hs : RightEuclidean s)
    (hle : ∀ a b, r a b → s a b) : EuclGen r a b → s a b := by
  haveI := hs
  intro h
  induction h with
  | base hr => exact hle _ _ hr
  | eucl _ _ ihab ihac => exact RightEuclidean.rightEuclidean ihab ihac

namespace LeftEuclidean

variable [LeftEuclidean r]

/-- A `LeftEuclidean` relation is reflexive on its domain -/
theorem reflOn_dom : (dom r).ReflOn r := fun _ ⟨_, ab⟩ ↦ leftEuclidean ab ab

/-- The converse of a `LeftEuclidean` relation is `RightEuclidean` -/
theorem rightEuclidean_swap : RightEuclidean (fun a b => r b a) where
  rightEuclidean ab ac := leftEuclidean ac ab

instance [Std.Refl r] : Std.Symm r where
  symm _ b ab := leftEuclidean (refl b) ab

theorem trichotomous_trans [Std.Trichotomous r] : IsTrans α r where
  trans a b c ab bc := by
    have := Std.Trichotomous.trichotomous (r := r) a c
    have aa := reflOn_dom.of_dom ab
    have (ca : r c a) := leftEuclidean aa ca
    grind

theorem antisymm_leftUnique [Std.Antisymm r] : Relator.LeftUnique r := by
  intros a b c ac bc
  exact antisymm (leftEuclidean ac bc) (leftEuclidean bc ac)

theorem leftUnique_antisymm (h : Relator.LeftUnique r) : Std.Antisymm r where
  antisymm _ _ ab ba := h ab (reflOn_dom.of_dom ba)

theorem leftUnique_trans (h : Relator.LeftUnique r) : IsTrans α r where
  trans a b c ab bc := by
    have eq : a = b := h ab (reflOn_dom.of_dom bc)
    simpa [eq]

theorem leftTotal_equiv (h : Relator.LeftTotal r) : IsEquiv α r := by
  have : Std.Refl r := ⟨fun a => reflOn_dom.of_dom (h a).choose_spec⟩
  exact {toIsTrans := ⟨fun _ _ _ ab bc => leftEuclidean ab (symm bc)⟩}

omit [LeftEuclidean r] in
theorem rightTotal_leftUnique_trans (h₁ : RightTotal r) (h₂ : LeftUnique r) [IsTrans α r] :
    LeftEuclidean r where
  leftEuclidean {a b c} ac bc := by
    obtain ⟨d, da⟩ := h₁ a
    have : a = b := h₂ ac bc
    have : a = d := h₂ ac (_root_.trans da ac)
    grind

private theorem three_contra [Std.Trichotomous r] [Std.Antisymm r] :
    ¬ ∃ (a b c : α), a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  rintro ⟨a, b, c, _⟩
  have := @Std.Trichotomous.rel_or_eq_or_rel_swap _ r _ a b
  have := @Std.Trichotomous.rel_or_eq_or_rel_swap _ r _ a c
  have := @Std.Trichotomous.rel_or_eq_or_rel_swap _ r _ b c
  have := antisymm_leftUnique (r := r)
  have := @reflOn_dom (r := r)
  simp [Set.ReflOn] at this
  grind [Relator.LeftUnique]

theorem trichotomous_antisymm_finite [Std.Trichotomous r] [Std.Antisymm r] : Finite α := by
  classical
  by_contra! h
  apply three_contra (r := r)
  have ⟨_, hcard⟩ := Infinite.exists_subset_card_eq α 3
  have ⟨a, b, c, _, _, _, _⟩ := Finset.card_eq_three.mp hcard
  use a, b, c

theorem trichotomous_antisymm_card [Std.Trichotomous r] [Std.Antisymm r] [Fintype α] :
    Fintype.card α ≤ 2 := by
  by_contra! h
  apply three_contra (r := r)
  have ⟨a, b, c, _⟩ := Fintype.two_lt_card_iff.mp h
  use a, b, c

theorem dom_subset_cod : dom r ⊆ cod r := fun _ ⟨_, ab⟩ ↦ of_dom (reflOn_dom.of_dom ab)

theorem leftTotal_dom : Relator.LeftTotal (α := dom r) (β := dom r) r :=
  fun ⟨a, _, h⟩ => ⟨⟨a, of_dom h⟩, reflOn_dom.of_dom h⟩

theorem equiv_dom : IsEquiv (dom r) r := leftTotal_equiv leftTotal_dom

end LeftEuclidean

section euclidean_symm

variable [Std.Symm r]

open RightEuclidean LeftEuclidean in
private theorem symm_equivalents : [RightEuclidean r, LeftEuclidean r, IsTrans α r].TFAE := by
  tfae_have 1 → 2 := fun _ => ⟨fun ac bc => rightEuclidean (symm ac) (symm bc)⟩
  tfae_have 2 → 3 := fun _ => ⟨fun _ _ _ ab bc => leftEuclidean ab (symm bc)⟩
  tfae_have 3 → 1 := fun _ => ⟨fun ab ac => _root_.trans (symm ab) ac⟩
  tfae_finish

/-- For a symmetric relation, `LeftEuclidean` and `RightEuclidean` are equivalent. -/
theorem symm_leftEuclidean_iff_rightEuclidean : LeftEuclidean r ↔ RightEuclidean r :=
  List.TFAE.out symm_equivalents 1 0

/-- For a symmetric relation, `LeftEuclidean` and transitivity are equivalent. -/
theorem symm_leftEuclidean_iff_trans : LeftEuclidean r ↔  IsTrans α r :=
  List.TFAE.out symm_equivalents 1 2

/-- For a symmetric relation, `RightEuclidean` and transitivity are equivalent. -/
theorem symm_rightEuclidean_iff_trans : RightEuclidean r ↔ IsTrans α r :=
  List.TFAE.out symm_equivalents 0 2

end euclidean_symm

theorem leftEuclidean_rightEuclidean_dom_cod_eq [LeftEuclidean r] [RightEuclidean r] :
    dom r = cod r := by
  have : dom r ⊆ cod r := LeftEuclidean.dom_subset_cod
  have : cod r ⊆ dom r := RightEuclidean.cod_subset_dom
  grind

theorem dom_cod_leftEuclidean (eq : dom r = cod r) [equiv_dom : IsEquiv (dom r) r] :
    LeftEuclidean r where
  leftEuclidean {a b c} ac bc := by
    have cb : r c b := equiv_dom.symm ⟨_, _, bc⟩ ⟨c, by grind⟩ bc
    exact equiv_dom.trans ⟨_, _, ac⟩ ⟨_, _, cb⟩ ⟨_, by grind⟩ ac cb

lemma dom_cod_rightEuclidean (eq : dom r = cod r) [equiv_dom : IsEquiv (dom r) r] :
    RightEuclidean r where
  rightEuclidean {a b c} ab ac := by
    have ba : r b a := equiv_dom.symm ⟨a, _, ab⟩ ⟨b, by grind⟩ ab
    exact equiv_dom.trans ⟨_, _, ba⟩ ⟨_, _, ac⟩ ⟨c, by grind⟩ ba ac

/-- A relation is both left and right Euclidean if and only if the relation is an equivalence on
  coinciding domain and codomain. -/
theorem leftEuclidean_rightEuclidean_iff_dom_cod :
    LeftEuclidean r ∧ RightEuclidean r ↔ dom r = cod r ∧ IsEquiv (dom r) r where
  mp := fun ⟨_, _⟩ ↦ ⟨leftEuclidean_rightEuclidean_dom_cod_eq, LeftEuclidean.equiv_dom⟩
  mpr := fun ⟨eq, _⟩ ↦ ⟨dom_cod_leftEuclidean eq, dom_cod_rightEuclidean eq⟩

/-! ## Rooted normal form

A right-Euclidean frame reachable from a distinguished root `w` is a *root above a universal
cluster*: the successors of `w` are mutually related (`rooted_cluster_universal`) and carry an
equivalence relation (`rooted_cluster_isEquiv`, consuming `RightEuclidean.equiv_cod`), while the
root itself is related *into* the cluster but -- unlike an S5 frame -- need not be related to
itself. That missing root-reflexivity is the entire difference from S5 and is exactly what the
modal axiom `□p → p` detects. The symmetric case is a partial equivalence relation, yielding the
KB5 dichotomy: a rooted symmetric right-Euclidean frame is either edge-isolated at the root or a
full cluster containing it. -/

/-- **Universality of the cluster.** In a right-Euclidean frame, all successors of a common root
`w` are mutually related: `R(w) × R(w) ⊆ R`. This is `rightEuclidean` read at the root, and is
what makes a rooted Euclidean frame a root together with a *universal* cluster of successors. -/
theorem rooted_cluster_universal [RightEuclidean r] {w a b : α}
    (hwa : r w a) (hwb : r w b) : r a b :=
  RightEuclidean.rightEuclidean hwa hwb

/-- **The cluster is an equivalence.** The successor cluster `cod r` of a right-Euclidean frame
carries an equivalence relation. This consumes `RightEuclidean.equiv_cod` directly rather than
re-deriving it: the successor cluster of a rooted Euclidean frame is an S5 cluster. -/
theorem rooted_cluster_isEquiv [RightEuclidean r] : IsEquiv (cod r) r :=
  RightEuclidean.equiv_cod

/-- **The root sits above the cluster.** Every successor of the root lies in the successor cluster
`cod r`. Combined with `rooted_cluster_isEquiv`, this exhibits a rooted right-Euclidean frame as a
root `w` sitting above the universal cluster `cod r`. The root is related *into* the cluster but
-- unlike in an S5 frame -- need not be related to itself: `r w w` can fail. -/
theorem rooted_mem_cod [RightEuclidean r] {w a : α} (hwa : r w a) : a ∈ cod r :=
  ⟨w, hwa⟩

/-- **KB5, the partial-equivalence case.** A symmetric right-Euclidean relation is transitive --
a partial equivalence relation on its field. This is the `IsTrans` direction of
`symm_rightEuclidean_iff_trans`, packaged for direct use. -/
theorem symm_rightEuclidean_isTrans [Std.Symm r] [RightEuclidean r] : IsTrans α r :=
  symm_rightEuclidean_iff_trans.mp inferInstance

/-- **KB5 dichotomy witness.** For a symmetric right-Euclidean relation, if the root `w` has any
successor then it is reflexive at `w` -- the full-cluster branch of the dichotomy. The only way
`r w w` fails is the edge-isolated root with no successor at all, in which case `□p → p` can fail
vacuously at the root. -/
theorem symm_rightEuclidean_root_refl [Std.Symm r] [RightEuclidean r] {w a : α}
    (hwa : r w a) : r w w :=
  RightEuclidean.rightEuclidean (Std.Symm.symm w a hwa) (Std.Symm.symm w a hwa)

end Relation
