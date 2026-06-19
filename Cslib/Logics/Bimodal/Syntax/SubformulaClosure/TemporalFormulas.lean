/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Syntax.SubformulaClosure.NestingDepth

/-!
# Temporal Formula Infrastructure

Deferral closure, seriality formulas, temporal blocking set, and structural lemmas.

Ported from BimodalLogic/Theories/Bimodal/Syntax/SubformulaClosure/TemporalFormulas.lean
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal

open Formula

variable {Atom : Type*} [DecidableEq Atom]

/-- Map a future formula F(χ) to its deferral disjunction χ ∨ F(χ); `⊥` otherwise. -/
def toFutureDeferral (f : Formula Atom) : Formula Atom :=
  match extractFutureInner f with
  | some chi => Formula.or chi (Formula.someFuture chi)
  | none => Formula.bot

/-- Map a past formula P(χ) to its deferral disjunction χ ∨ P(χ); `⊥` otherwise. -/
def toPastDeferral (f : Formula Atom) : Formula Atom :=
  match extractPastInner f with
  | some chi => Formula.or chi (Formula.somePast chi)
  | none => Formula.bot

/-- The set of forward deferral disjunctions for future formulas in the closure of `phi`. -/
def deferralDisjunctionSet (phi : Formula Atom) : Finset (Formula Atom) :=
  ((closureWithNeg phi).filter IsFutureFormula).image toFutureDeferral

/-- The set of backward deferral disjunctions for past formulas in the closure of `phi`. -/
def backwardDeferralSet (phi : Formula Atom) : Finset (Formula Atom) :=
  ((closureWithNeg phi).filter IsPastFormula).image toPastDeferral

/-- A formula is an Until formula if it has the form `φ U ψ`. -/
def IsUntilFormula : Formula Atom → Prop
  | .untl _ _ => True
  | _ => False

instance : DecidablePred (IsUntilFormula (Atom := Atom)) :=
  fun f => match f with
  | .untl _ _ => isTrue True.intro
  | .atom _ | .bot | .imp _ _ | .box _ | .snce _ _ =>
    isFalse (by simp [IsUntilFormula])

/-- Predicate recognizing exactly the since-formulas `φ S ψ`. -/
def IsSinceFormula : Formula Atom → Prop
  | .snce _ _ => True
  | _ => False

instance : DecidablePred (IsSinceFormula (Atom := Atom)) :=
  fun f => match f with
  | .snce _ _ => isTrue True.intro
  | .atom _ | .bot | .imp _ _ | .box _ | .untl _ _ =>
    isFalse (by simp [IsSinceFormula])

/-- Maps `φ U ψ` to its deferral expansion `ψ ∨ (φ ∧ (φ U ψ))`; returns `⊥` on non-until-formulas. -/
def toUntilDeferral : Formula Atom → Formula Atom
  | .untl psi phi => Formula.or psi (Formula.and phi (.untl psi phi))
  | _ => Formula.bot

/-- Maps `φ S ψ` to its deferral expansion `ψ ∨ (φ ∧ (φ S ψ))`; returns `⊥` on non-since-formulas. -/
def toSinceDeferral : Formula Atom → Formula Atom
  | .snce psi phi => Formula.or psi (Formula.and phi (.snce psi phi))
  | _ => Formula.bot

/-- The set of deferral expansions for all until-subformulas of `phi`. -/
def untilDeferralSet (phi : Formula Atom) : Finset (Formula Atom) :=
  ((closureWithNeg phi).filter IsUntilFormula).image toUntilDeferral

/-- The set of deferral expansions for all since-subformulas of `phi`. -/
def sinceDeferralSet (phi : Formula Atom) : Finset (Formula Atom) :=
  ((closureWithNeg phi).filter IsSinceFormula).image toSinceDeferral

/-- The formula `◇⊤` asserting that some future moment exists. -/
abbrev fTop : Formula Atom := Formula.someFuture (Formula.neg Formula.bot)
/-- The formula `◁⊤` asserting that some past moment exists. -/
abbrev pTop : Formula Atom := Formula.somePast (Formula.neg Formula.bot)
/-- The formula `¬¬⊥`, used in serially-closed closure sets. -/
abbrev negNegBot : Formula Atom := Formula.neg (Formula.neg Formula.bot)
/-- The formula `□(¬¬⊥)`. -/
abbrev gNegNegBot : Formula Atom := Formula.allFuture (negNegBot : Formula Atom)
/-- The formula `■(¬¬⊥)`. -/
abbrev hNegNegBot : Formula Atom := Formula.allPast (negNegBot : Formula Atom)
/-- The negation of `□(¬¬⊥)`. -/
abbrev negGNegNegBot : Formula Atom := Formula.neg (gNegNegBot : Formula Atom)
/-- The negation of `■(¬¬⊥)`. -/
abbrev negHNegNegBot : Formula Atom := Formula.neg (hNegNegBot : Formula Atom)
/-- The deferral expansion `¬⊥ ∨ ◇⊤` for future serility. -/
abbrev fTopDeferral : Formula Atom := Formula.or (Formula.neg Formula.bot) (fTop : Formula Atom)
/-- The deferral expansion `¬⊥ ∨ ◁⊤` for past seriality. -/
abbrev pTopDeferral : Formula Atom := Formula.or (Formula.neg Formula.bot) (pTop : Formula Atom)

/-- The finite set of seriality-witnessing formulas required in deferral closures. -/
def serialityFormulas : Finset (Formula Atom) :=
  {fTop, pTop, Formula.neg Formula.bot, negNegBot, gNegNegBot, hNegNegBot,
   negGNegNegBot, negHNegNegBot, fTopDeferral, pTopDeferral}

/-- Maps a future-formula `◇χ` to its blocking counterpart `□(¬χ)`; returns `⊥` otherwise. -/
def toFutureBlocking (f : Formula Atom) : Formula Atom :=
  match extractFutureInner f with
  | some chi => Formula.allFuture chi.neg
  | none => Formula.bot

/-- Maps a past-formula `◁χ` to its blocking counterpart `■(¬χ)`; returns `⊥` otherwise. -/
def toPastBlocking (f : Formula Atom) : Formula Atom :=
  match extractPastInner f with
  | some chi => Formula.allPast chi.neg
  | none => Formula.bot

/-- The set of blocking formulas for all future- and past-subformulas of `phi`. -/
def temporalBlockingSet (phi : Formula Atom) : Finset (Formula Atom) :=
  ((closureWithNeg phi).filter IsFutureFormula).image toFutureBlocking ∪
  ((closureWithNeg phi).filter IsPastFormula).image toPastBlocking

theorem toFutureBlocking_someFuture (chi : Formula Atom) :
    toFutureBlocking (Formula.someFuture chi) = Formula.allFuture chi.neg := by
  simp only [toFutureBlocking, extractFutureInner_someFuture]

theorem toPastBlocking_somePast (chi : Formula Atom) :
    toPastBlocking (Formula.somePast chi) = Formula.allPast chi.neg := by
  simp only [toPastBlocking, extractPastInner_somePast]

theorem allFuture_neg_mem_temporalBlockingSet_of_someFuture {phi chi : Formula Atom}
    (h : Formula.someFuture chi ∈ closureWithNeg phi) :
    Formula.allFuture chi.neg ∈ temporalBlockingSet phi := by
  unfold temporalBlockingSet
  apply Finset.mem_union_left
  rw [Finset.mem_image]
  refine ⟨Formula.someFuture chi, ?_, toFutureBlocking_someFuture chi⟩
  rw [Finset.mem_filter]
  exact ⟨h, by simp [IsFutureFormula, extractFutureInner_someFuture]⟩

theorem allPast_neg_mem_temporalBlockingSet_of_somePast {phi chi : Formula Atom}
    (h : Formula.somePast chi ∈ closureWithNeg phi) :
    Formula.allPast chi.neg ∈ temporalBlockingSet phi := by
  unfold temporalBlockingSet
  apply Finset.mem_union_right
  rw [Finset.mem_image]
  refine ⟨Formula.somePast chi, ?_, toPastBlocking_somePast chi⟩
  rw [Finset.mem_filter]
  exact ⟨h, by simp [IsPastFormula, extractPastInner_somePast]⟩

/-- The base deferral closure of `phi`: subformulas, deferrals, blocking formulas, and seriality witnesses. -/
def baseDeferralClosure (phi : Formula Atom) : Finset (Formula Atom) :=
  closureWithNeg phi ∪ deferralDisjunctionSet phi ∪ backwardDeferralSet phi
  ∪ serialityFormulas ∪ temporalBlockingSet phi

/-- The deferral closure of `phi`, equal to its base deferral closure. -/
def deferralClosure (phi : Formula Atom) : Finset (Formula Atom) :=
  baseDeferralClosure phi

/-- The extended deferral closure of `phi`, additionally including until- and since-deferral expansions. -/
def extendedDeferralClosure (phi : Formula Atom) : Finset (Formula Atom) :=
  baseDeferralClosure phi ∪ untilDeferralSet phi ∪ sinceDeferralSet phi

theorem baseDeferralClosure_eq_deferralClosure (phi : Formula Atom) :
    baseDeferralClosure phi = deferralClosure phi := rfl

theorem baseDeferralClosure_subset_deferralClosure (phi : Formula Atom) :
    baseDeferralClosure phi ⊆ deferralClosure phi := by
  rw [baseDeferralClosure_eq_deferralClosure]

theorem deferralClosure_subset_extendedDeferralClosure (phi : Formula Atom) :
    deferralClosure phi ⊆ extendedDeferralClosure phi := by
  intro psi h
  unfold extendedDeferralClosure
  exact Finset.mem_union_left _ (Finset.mem_union_left _ h)

theorem closureWithNeg_subset_deferralClosure (phi : Formula Atom) :
    closureWithNeg phi ⊆ deferralClosure phi := by
  intro psi h
  unfold deferralClosure baseDeferralClosure
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))

theorem self_mem_deferralClosure (phi : Formula Atom) : phi ∈ deferralClosure phi :=
  closureWithNeg_subset_deferralClosure phi (self_mem_closureWithNeg phi)

theorem neg_self_mem_deferralClosure (phi : Formula Atom) : phi.neg ∈ deferralClosure phi :=
  closureWithNeg_subset_deferralClosure phi (neg_self_mem_closureWithNeg phi)

theorem serialityFormulas_subset_deferralClosure (phi : Formula Atom) :
    (serialityFormulas : Finset (Formula Atom)) ⊆ deferralClosure phi := by
  intro psi h
  unfold deferralClosure baseDeferralClosure
  exact Finset.mem_union_left _ (Finset.mem_union_right _ h)

theorem temporalBlockingSet_subset_deferralClosure (phi : Formula Atom) :
    temporalBlockingSet phi ⊆ deferralClosure phi := by
  intro psi h
  unfold deferralClosure baseDeferralClosure
  exact Finset.mem_union_right _ h

theorem F_top_mem_serialityFormulas : (fTop : Formula Atom) ∈ serialityFormulas := by
  simp only [serialityFormulas, Finset.mem_insert, Finset.mem_singleton]
  left; trivial

theorem P_top_mem_serialityFormulas : (pTop : Formula Atom) ∈ serialityFormulas := by
  simp only [serialityFormulas, Finset.mem_insert, Finset.mem_singleton]
  right; left; trivial

theorem neg_bot_mem_serialityFormulas :
    (Formula.neg Formula.bot : Formula Atom) ∈ serialityFormulas := by
  simp only [serialityFormulas, Finset.mem_insert, Finset.mem_singleton]
  right; right; left; trivial

theorem neg_neg_bot_mem_serialityFormulas :
    (negNegBot : Formula Atom) ∈ serialityFormulas := by
  simp only [serialityFormulas, Finset.mem_insert, Finset.mem_singleton]
  right; right; right; left; trivial

theorem G_neg_neg_bot_mem_serialityFormulas :
    (gNegNegBot : Formula Atom) ∈ serialityFormulas := by
  simp only [serialityFormulas, Finset.mem_insert, Finset.mem_singleton]
  right; right; right; right; left; trivial

theorem H_neg_neg_bot_mem_serialityFormulas :
    (hNegNegBot : Formula Atom) ∈ serialityFormulas := by
  simp only [serialityFormulas, Finset.mem_insert, Finset.mem_singleton]
  right; right; right; right; right; left; trivial

theorem F_top_mem_deferralClosure (phi : Formula Atom) :
    (fTop : Formula Atom) ∈ deferralClosure phi :=
  serialityFormulas_subset_deferralClosure phi F_top_mem_serialityFormulas

theorem P_top_mem_deferralClosure (phi : Formula Atom) :
    (pTop : Formula Atom) ∈ deferralClosure phi :=
  serialityFormulas_subset_deferralClosure phi P_top_mem_serialityFormulas

theorem neg_bot_mem_deferralClosure (phi : Formula Atom) :
    (Formula.neg Formula.bot : Formula Atom) ∈ deferralClosure phi :=
  serialityFormulas_subset_deferralClosure phi neg_bot_mem_serialityFormulas

theorem neg_neg_bot_mem_deferralClosure (phi : Formula Atom) :
    (negNegBot : Formula Atom) ∈ deferralClosure phi :=
  serialityFormulas_subset_deferralClosure phi neg_neg_bot_mem_serialityFormulas

theorem G_neg_neg_bot_mem_deferralClosure (phi : Formula Atom) :
    (gNegNegBot : Formula Atom) ∈ deferralClosure phi :=
  serialityFormulas_subset_deferralClosure phi G_neg_neg_bot_mem_serialityFormulas

theorem H_neg_neg_bot_mem_deferralClosure (phi : Formula Atom) :
    (hNegNegBot : Formula Atom) ∈ deferralClosure phi :=
  serialityFormulas_subset_deferralClosure phi H_neg_neg_bot_mem_serialityFormulas

theorem allFuture_neg_mem_deferralClosure_of_someFuture {phi chi : Formula Atom}
    (h : Formula.someFuture chi ∈ closureWithNeg phi) :
    Formula.allFuture chi.neg ∈ deferralClosure phi :=
  temporalBlockingSet_subset_deferralClosure phi
    (allFuture_neg_mem_temporalBlockingSet_of_someFuture h)

theorem allPast_neg_mem_deferralClosure_of_somePast {phi chi : Formula Atom}
    (h : Formula.somePast chi ∈ closureWithNeg phi) :
    Formula.allPast chi.neg ∈ deferralClosure phi :=
  temporalBlockingSet_subset_deferralClosure phi
    (allPast_neg_mem_temporalBlockingSet_of_somePast h)

theorem toFutureDeferral_someFuture (chi : Formula Atom) :
    toFutureDeferral (Formula.someFuture chi) = Formula.or chi (Formula.someFuture chi) := by
  simp only [toFutureDeferral, extractFutureInner_someFuture]

theorem toPastDeferral_somePast (chi : Formula Atom) :
    toPastDeferral (Formula.somePast chi) = Formula.or chi (Formula.somePast chi) := by
  simp only [toPastDeferral, extractPastInner_somePast]

theorem deferral_of_F_in_closure (phi chi : Formula Atom)
    (h : Formula.someFuture chi ∈ closureWithNeg phi) :
    Formula.or chi (Formula.someFuture chi) ∈ deferralClosure phi := by
  unfold deferralClosure baseDeferralClosure deferralDisjunctionSet
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  rw [← toFutureDeferral_someFuture chi]
  apply Finset.mem_image_of_mem
  apply Finset.mem_filter.mpr
  constructor
  · exact h
  · simp only [IsFutureFormula, extractFutureInner_someFuture, Option.isSome_some]

theorem deferral_of_P_in_closure (phi chi : Formula Atom)
    (h : Formula.somePast chi ∈ closureWithNeg phi) :
    Formula.or chi (Formula.somePast chi) ∈ deferralClosure phi := by
  unfold deferralClosure baseDeferralClosure backwardDeferralSet
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  rw [← toPastDeferral_somePast chi]
  apply Finset.mem_image_of_mem
  apply Finset.mem_filter.mpr
  constructor
  · exact h
  · simp only [IsPastFormula, extractPastInner_somePast, Option.isSome_some]

theorem f_nesting_depth_or (chi psi : Formula Atom) :
    fNestingDepth (Formula.or chi psi) = 0 := by
  simp only [Formula.or, Formula.neg, fNestingDepth]

theorem p_nesting_depth_or (chi psi : Formula Atom) :
    pNestingDepth (Formula.or chi psi) = 0 := by
  simp only [Formula.or, Formula.neg, pNestingDepth]

theorem f_nesting_depth_F_deferral (chi : Formula Atom) :
    fNestingDepth (Formula.or chi (Formula.someFuture chi)) = 0 :=
  f_nesting_depth_or chi (Formula.someFuture chi)

theorem p_nesting_depth_P_deferral (chi : Formula Atom) :
    pNestingDepth (Formula.or chi (Formula.somePast chi)) = 0 :=
  p_nesting_depth_or chi (Formula.somePast chi)

-- The remaining structural lemmas (max depth, allFuture/allPast cases, box cases)
-- are deferred to a follow-up continuation due to volume. The definitions and
-- core membership lemmas above are sufficient for Phase 2+ dependencies.

-- Placeholder for forward references from later phases:
theorem F_top_deferral_mem_deferralClosure (phi : Formula Atom) :
    (fTopDeferral : Formula Atom) ∈ deferralClosure phi := by
  apply serialityFormulas_subset_deferralClosure
  simp only [serialityFormulas, Finset.mem_insert, Finset.mem_singleton]
  right; right; right; right; right; right; right; right; left; trivial

theorem P_top_deferral_mem_deferralClosure (phi : Formula Atom) :
    (pTopDeferral : Formula Atom) ∈ deferralClosure phi := by
  apply serialityFormulas_subset_deferralClosure
  simp only [serialityFormulas, Finset.mem_insert, Finset.mem_singleton]
  right; right; right; right; right; right; right; right; right; trivial

end Cslib.Logic.Bimodal
