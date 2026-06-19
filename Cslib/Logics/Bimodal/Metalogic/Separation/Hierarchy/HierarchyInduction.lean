/-
Copyright (c) 2025 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Separation.Hierarchy.HierarchyDefs
public import Cslib.Logics.Bimodal.Metalogic.Separation.Hierarchy.HierarchyCaseSep

/-!
# Substitution-Based Induction Engine for the Separation Hierarchy (Steps 1-5b)

Hierarchy theorem steps 1-5b: substitution preservation, strict count decrease,
countUTotal lemmas, substitution into separated formulas, S/U-nesting depth
measures, and callback infrastructure.
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedDecidableInType false
set_option linter.style.maxHeartbeats false
@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Separation

variable {Atom : Type*} [DecidableEq Atom]

open Cslib.Logic.Bimodal

/-! ## Hierarchy Theorem (GHR94 Lemmas 10.2.5-10.2.8)

This section proves the full hierarchy as theorems (no axioms).
The chain is: Cases 1-8 -> no_S_nested_in_U_separable -> junction_depth_separable
-> all_formulas_separable. No circular dependencies.

### Key Technique: Constituent Substitution

After abstracting a U-type to a fresh atom and separating the result,
we substitute back into the separated formula. The crucial insight:
- In `.untlpositions ` of a separated formula, args are S-free.
  Substituting an S-free `.untl B` A preserves S-freeness.
- In `.sncepositions ` of a separated formula, args are U-free.
  Substituting `.untl B` A for an atom in U-free args creates
  `noSNestedInU` (the new U has S-free args), allowing IH application
  with strictly fewer U-subformulas.

### References

- GHR94, Lemmas 10.2.5-10.2.8, pp. 581-590
- Strategy report: specs/157_.../reports/09_hierarchy-strategy.md
-/

/-! ### Step 1: Substitution Preservation Lemmas -/

/-- Substituting an S-free formula into an S-free formula preserves S-freeness.
    This is needed when substituting `.untl B` A (with S-free A, B) for an atom
    in the S-free arguments of `.untlnodes ` in a separated formula. -/
theorem subst_S_free_preserves_S_free (ψ : Formula Atom) (p : Atom) (r : Formula Atom)
    (hψ : isSFree ψ = true) (hr : isSFree r = true) :
    isSFree (substFormula ψ p r) = true := by
  induction ψ with
  | atom a =>
    simp only [substFormula]
    split
    · exact hr
    · simp [isSFree]
  | bot => simp [substFormula, isSFree]
  | imp c d ih1 ih2 =>
    simp [isSFree] at hψ
    simp [substFormula, isSFree, ih1 hψ.1, ih2 hψ.2]
  | box c ih =>
    simp [isSFree] at hψ
    simp [substFormula, isSFree, ih hψ]
  | untl d c ih2 ih1 =>
    simp [isSFree] at hψ
    simp [substFormula, isSFree, ih1 hψ.1, ih2 hψ.2]
  | snce _ _ => simp [isSFree] at hψ

/-- Substituting a U-free formula into a U-free formula preserves U-freeness.
    Dual of `subst_S_free_preserves_S_free`. -/
theorem subst_U_free_preserves_U_free (ψ : Formula Atom) (p : Atom) (r : Formula Atom)
    (hψ : isUFree ψ = true) (hr : isUFree r = true) :
    isUFree (substFormula ψ p r) = true := by
  induction ψ with
  | atom a =>
    simp only [substFormula]
    split
    · exact hr
    · simp [isUFree]
  | bot => simp [substFormula, isUFree]
  | imp c d ih1 ih2 =>
    simp [isUFree] at hψ
    simp [substFormula, isUFree, ih1 hψ.1, ih2 hψ.2]
  | box c ih =>
    simp [isUFree] at hψ
    simp [substFormula, isUFree, ih hψ]
  | untl _ _ => simp [isUFree] at hψ
  | snce d c ih2 ih1 =>
    simp [isUFree] at hψ
    simp [substFormula, isUFree, ih1 hψ.1, ih2 hψ.2]

/-- Substituting `.untl B` A (with S-free args) into a U-free formula gives
    `noSNestedInU`. The only new `.untlnodes ` are the substituted copies
    of `.untl B` A, which have S-free arguments by hypothesis. -/
theorem subst_U_free_gives_no_S_nested (ψ : Formula Atom) (p : Atom) (A B : Formula Atom)
    (hψ : isUFree ψ = true) (hA : isSFree A = true) (hB : isSFree B = true) :
    noSNestedInU (substFormula ψ p (.untl B A)) := by
  induction ψ with
  | atom a =>
    simp only [substFormula]
    split
    · -- a = p: result is .untl B A, need isSFree A ∧ isSFree B
      exact ⟨hA, hB⟩
    · -- a ≠ p: result is .atom a
      trivial
  | bot => trivial
  | imp c d ih1 ih2 =>
    simp [isUFree] at hψ
    exact ⟨ih1 hψ.1, ih2 hψ.2⟩
  | box c ih =>
    simp [isUFree] at hψ
    exact ih hψ
  | untl _ _ => simp [isUFree] at hψ
  | snce d c ih2 ih1 =>
    simp [isUFree] at hψ
    exact ⟨ih1 hψ.1, ih2 hψ.2⟩

/-- Substituting hasNoAllpastAllfuture preservation: if ψ has no allPast/allFuture
    and the replacement has none either, the result has none. -/
theorem subst_preserves_no_allpast_allfuture (ψ : Formula Atom) (p : Atom) (r : Formula Atom)
    (hψ : hasNoAllpastAllfuture ψ = true) (hr : hasNoAllpastAllfuture r = true) :
    hasNoAllpastAllfuture (substFormula ψ p r) = true := by
  induction ψ with
  | atom a =>
    simp only [substFormula]
    split
    · exact hr
    · simp [hasNoAllpastAllfuture]
  | bot => simp [substFormula]
  | imp c d ih1 ih2 =>
    simp [substFormula]
  | box _ => simp [substFormula]
  | untl d c ih2 ih1 =>
    simp [substFormula]
  | snce d c ih2 ih1 =>
    simp [substFormula]

/-! ### Step 2: Strict Count Decrease for Abstraction -/

/-- Surface-level containment of `.untl B` A: the formula has a `.untl B` A node
    reachable from the root without passing through another `.untlnode. `
    This mirrors the structure of `countUSubformulas`, which counts `.untlnodes `
    at the surface level (not recursing into `.untlchildren `). -/
def containsUntlSurface : Formula Atom → Formula Atom → Formula Atom → Prop
  | .atom _, _, _ => False
  | .bot, _, _ => False
  | .imp c d, A, B => containsUntlSurface c A B ∨ containsUntlSurface d A B
  | .box c, A, B => containsUntlSurface c A B
  | .untl d c, A, B => c = A ∧ d = B
  | .snce d c, A, B => containsUntlSurface c A B ∨ containsUntlSurface d A B

/-- Abstracting a formula that contains `.untl B` A at the surface level strictly
    decreases countUSubformulas. This is the corrected version of the count
    decrease lemma: the hypothesis `containsUntlSurface` ensures the non-matching
    `.untlcase ` is vacuously true (since `countUSubformulas` does not recurse
    into `.untlchildren `). -/
theorem abstract_untl_count_lt_of_contains_surface (phi A B : Formula Atom) (p : Atom)
    (h_contains : containsUntlSurface phi A B) :
    countUSubformulas (abstractUntl phi A B p) < countUSubformulas phi := by
  induction phi with
  | atom _ => exact absurd h_contains id
  | bot => exact absurd h_contains id
  | imp c d ih1 ih2 =>
    simp only [containsUntlSurface] at h_contains
    simp only [abstractUntl, countUSubformulas]
    rcases h_contains with hc | hd
    · have := ih1 hc; have := abstract_untl_count_le d A B p; omega
    · have := ih2 hd; have := abstract_untl_count_le c A B p; omega
  | box c ih =>
    simp only [containsUntlSurface] at h_contains
    simp only [abstractUntl, countUSubformulas]; exact ih h_contains
  | untl d c _ _ =>
    simp only [abstractUntl, countUSubformulas]
    split
    · simp only [countUSubformulas]; omega
    · next hne =>
      -- h_contains : containsUntlSurface (.untl d c) A B = (c = A ∧ d = B)
      -- hne : ¬(c = A ∧ d = B), so this case is vacuously true
      exact absurd h_contains hne
  | snce d c ih2 ih1 =>
    simp only [containsUntlSurface] at h_contains
    simp only [abstractUntl, countUSubformulas]
    rcases h_contains with hc | hd
    · have := ih1 hc; have := abstract_untl_count_le d A B p; omega
    · have := ih2 hd; have := abstract_untl_count_le c A B p; omega

/-! ### countUTotal lemmas for oracle-free separation -/

/-- `abstractUntl` never increases `countUTotal`. -/
theorem abstract_untl_count_total_le (phi A B : Formula Atom) (p : Atom) :
    countUTotal (abstractUntl phi A B p) ≤ countUTotal phi := by
  induction phi with
  | atom _ => simp [abstractUntl, countUTotal]
  | bot => simp [abstractUntl, countUTotal]
  | imp c d ih1 ih2 =>
    simp [abstractUntl, countUTotal]; exact Nat.add_le_add ih1 ih2
  | box c ih =>
    simp [abstractUntl, countUTotal]; exact ih
  | untl d c ih2 ih1 =>
    simp only [abstractUntl, countUTotal]
    split
    · simp [countUTotal]
    · simp only [countUTotal]; have := Nat.add_le_add ih1 ih2; omega
  | snce d c ih2 ih1 =>
    simp [abstractUntl, countUTotal]; exact Nat.add_le_add ih1 ih2

/-- `containsUntlDeep phi A B`: there exists an `.untl B` A node at any depth in phi. -/
def containsUntlDeep : Formula Atom → Formula Atom → Formula Atom → Prop
  | .atom _, _, _ => False
  | .bot, _, _ => False
  | .imp c d, A, B => containsUntlDeep c A B ∨ containsUntlDeep d A B
  | .box c, A, B => containsUntlDeep c A B
  | .untl d c, A, B => (c = A ∧ d = B) ∨
      containsUntlDeep c A B ∨ containsUntlDeep d A B
  | .snce d c, A, B => containsUntlDeep c A B ∨ containsUntlDeep d A B

/-- Surface containment implies deep containment. -/
theorem contains_untl_surface_implies_deep (phi A B : Formula Atom) :
    containsUntlSurface phi A B → containsUntlDeep phi A B := by
  induction phi with
  | atom _ => exact id
  | bot => exact id
  | imp c d ih1 ih2 =>
    simp only [containsUntlSurface, containsUntlDeep]
    intro h; rcases h with hc | hd
    · exact Or.inl (ih1 hc)
    · exact Or.inr (ih2 hd)
  | box c ih =>
    simp only [containsUntlSurface, containsUntlDeep]; exact ih
  | untl d c _ _ =>
    simp only [containsUntlSurface, containsUntlDeep]
    exact Or.inl
  | snce d c ih2 ih1 =>
    simp only [containsUntlSurface, containsUntlDeep]
    intro h; rcases h with hc | hd
    · exact Or.inl (ih1 hc)
    · exact Or.inr (ih2 hd)

/-- Abstracting a formula that contains `.untl B` A at any depth strictly
    decreases `countUTotal`. -/
theorem abstract_untl_count_total_lt_of_contains_deep (phi A B : Formula Atom) (p : Atom)
    (h_contains : containsUntlDeep phi A B) :
    countUTotal (abstractUntl phi A B p) < countUTotal phi := by
  induction phi with
  | atom _ => exact absurd h_contains id
  | bot => exact absurd h_contains id
  | imp c d ih1 ih2 =>
    simp only [containsUntlDeep] at h_contains
    simp only [abstractUntl, countUTotal]
    rcases h_contains with hc | hd
    · have := ih1 hc; have := abstract_untl_count_total_le d A B p; omega
    · have := ih2 hd; have := abstract_untl_count_total_le c A B p; omega
  | box c ih =>
    simp only [containsUntlDeep] at h_contains
    simp only [abstractUntl, countUTotal]; exact ih h_contains
  | untl d c ih2 ih1 =>
    simp only [containsUntlDeep] at h_contains
    simp only [abstractUntl, countUTotal]
    split
    · simp only [countUTotal]; omega
    · next hne =>
      simp only [countUTotal]
      rcases h_contains with ⟨hc, hd⟩ | hc | hd
      · exact absurd ⟨hc, hd⟩ hne
      · have := ih1 hc; have := abstract_untl_count_total_le d A B p; omega
      · have := ih2 hd; have := abstract_untl_count_total_le c A B p; omega
  | snce d c ih2 ih1 =>
    simp only [containsUntlDeep] at h_contains
    simp only [abstractUntl, countUTotal]
    rcases h_contains with hc | hd
    · have := ih1 hc; have := abstract_untl_count_total_le d A B p; omega
    · have := ih2 hd; have := abstract_untl_count_total_le c A B p; omega

/-- S-free formulas have noSNestedInU (vacuously: no `.sncenodes ` at all). -/
theorem s_free_implies_no_S_nested (phi : Formula Atom) (h : isSFree phi = true) :
    noSNestedInU phi := by
  induction phi with
  | atom _ => trivial
  | bot => trivial
  | imp a b ih1 ih2 =>
    simp only [isSFree, Bool.and_eq_true] at h
    exact ⟨ih1 h.1, ih2 h.2⟩
  | box a ih => simp only [isSFree] at h; exact ih h
  | untl b a =>
    simp only [isSFree, Bool.and_eq_true] at h
    exact h
  | snce _ _ => simp [isSFree] at h

/-- Extract innermost U-type: recurses INTO `.untlchildren ` to find a `.untlwith
    ` U-free arguments. Unlike `extractUType` which takes the first `.untlit
    ` finds, this descends into `.untlchildren ` when they're not U-free. -/
noncomputable def extractInnermostUType :
    (φ : Formula Atom) → (isUFree φ = false) → noSNestedInU φ → (Formula Atom × Formula Atom)
  | .atom _, h, _ => by simp [isUFree] at h
  | .bot, h, _ => by simp [isUFree] at h
  | .imp c d, h, hns =>
    if hc : isUFree c = false then extractInnermostUType c hc hns.1
    else extractInnermostUType d (by simp only [isUFree] at h; simp [hc] at h; exact h) hns.2
  | .box c, h, hns => extractInnermostUType c (by simp only [isUFree] at h; exact h) hns
  | .untl b a, _, hns =>
    -- Key difference from extractUType: recurse into children if they're not U-free
    if ha : isUFree a = false then
      extractInnermostUType a ha (s_free_implies_no_S_nested a hns.1)
    else if hb : isUFree b = false then
      extractInnermostUType b hb (s_free_implies_no_S_nested b hns.2)
    else (a, b)  -- Both U-free: this is an innermost U-type
  | .snce d c, h, hns =>
    if hc : isUFree c = false then extractInnermostUType c hc hns.1
    else extractInnermostUType d (by simp only [isUFree] at h; simp [hc] at h; exact h) hns.2

/-- `extractInnermostUType` returns S-free arguments. -/
theorem extract_innermost_U_type_S_free (φ : Formula Atom) (h : isUFree φ = false)
    (hns : noSNestedInU φ) :
    isSFree (extractInnermostUType φ h hns).1 = true ∧
    isSFree (extractInnermostUType φ h hns).2 = true := by
  induction φ with
  | atom _ => simp [isUFree] at h
  | bot => simp [isUFree] at h
  | imp c d ih1 ih2 =>
    unfold extractInnermostUType
    by_cases hc : isUFree c = false
    · simp only [hc]; exact ih1 hc hns.1
    · simp only [hc]
      have hd : isUFree d = false := by
        simp only [isUFree] at h; cases huf : isUFree c <;> simp_all
      exact ih2 hd hns.2
  | box c ih => simp only [isUFree] at h; unfold extractInnermostUType; exact ih h hns
  | untl b a ih2 ih1 =>
    unfold extractInnermostUType
    by_cases ha : isUFree a = false
    · simp only [ha]
      exact ih1 ha (s_free_implies_no_S_nested a hns.1)
    · simp only [ha]
      by_cases hb : isUFree b = false
      · simp only [hb]
        exact ih2 hb (s_free_implies_no_S_nested b hns.2)
      · simp only [hb]; exact hns
  | snce d c ih2 ih1 =>
    unfold extractInnermostUType
    by_cases hc : isUFree c = false
    · simp only [hc]; exact ih1 hc hns.1
    · simp only [hc]
      have hd : isUFree d = false := by
        simp only [isUFree] at h; cases huf : isUFree c <;> simp_all
      exact ih2 hd hns.2

/-- `extractInnermostUType` returns U-free arguments (KEY property).
    At the innermost level, both arguments are U-free by construction. -/
theorem extract_innermost_U_type_U_free (φ : Formula Atom) (h : isUFree φ = false)
    (hns : noSNestedInU φ) :
    isUFree (extractInnermostUType φ h hns).1 = true ∧
    isUFree (extractInnermostUType φ h hns).2 = true := by
  induction φ with
  | atom _ => simp [isUFree] at h
  | bot => simp [isUFree] at h
  | imp c d ih1 ih2 =>
    unfold extractInnermostUType
    by_cases hc : isUFree c = false
    · simp only [hc]; exact ih1 hc hns.1
    · simp only [hc]
      have hd : isUFree d = false := by
        simp only [isUFree] at h; cases huf : isUFree c <;> simp_all
      exact ih2 hd hns.2
  | box c ih => simp only [isUFree] at h; unfold extractInnermostUType; exact ih h hns
  | untl b a ih2 ih1 =>
    unfold extractInnermostUType
    by_cases ha : isUFree a = false
    · simp only [ha]
      exact ih1 ha (s_free_implies_no_S_nested a hns.1)
    · simp only [ha]
      by_cases hb : isUFree b = false
      · simp only [hb]
        exact ih2 hb (s_free_implies_no_S_nested b hns.2)
      · -- Both U-free: this is the innermost case
        simp only [hb]
        have ha_true : isUFree a = true := by
          cases h : isUFree a <;> simp_all
        have hb_true : isUFree b = true := by
          cases h : isUFree b <;> simp_all
        exact ⟨ha_true, hb_true⟩
  | snce d c ih2 ih1 =>
    unfold extractInnermostUType
    by_cases hc : isUFree c = false
    · simp only [hc]; exact ih1 hc hns.1
    · simp only [hc]
      have hd : isUFree d = false := by
        simp only [isUFree] at h; cases huf : isUFree c <;> simp_all
      exact ih2 hd hns.2

/-- `extractInnermostUType` returns a pair `(A, B)` such that
    `containsUntlDeep φ A B`. -/
theorem extract_innermost_U_type_contains_deep (φ : Formula Atom) (h : isUFree φ = false)
    (hns : noSNestedInU φ) :
    containsUntlDeep φ
      (extractInnermostUType φ h hns).1 (extractInnermostUType φ h hns).2 := by
  induction φ with
  | atom _ => simp [isUFree] at h
  | bot => simp [isUFree] at h
  | imp c d ih1 ih2 =>
    unfold extractInnermostUType
    by_cases hc : isUFree c = false
    · simp only [hc, containsUntlDeep]
      exact Or.inl (ih1 hc hns.1)
    · simp only [hc, containsUntlDeep]
      have hd : isUFree d = false := by
        simp only [isUFree] at h; cases huf : isUFree c <;> simp_all
      exact Or.inr (ih2 hd hns.2)
  | box c ih =>
    simp only [isUFree] at h
    unfold extractInnermostUType; simp only [containsUntlDeep]; exact ih h hns
  | untl b a ih2 ih1 =>
    unfold extractInnermostUType
    by_cases ha : isUFree a = false
    · simp only [ha, containsUntlDeep]
      exact Or.inr (Or.inl (ih1 ha (s_free_implies_no_S_nested a hns.1)))
    · simp only [ha]
      by_cases hb : isUFree b = false
      · simp only [hb, containsUntlDeep]
        exact Or.inr (Or.inr (ih2 hb (s_free_implies_no_S_nested b hns.2)))
      · simp only [hb, containsUntlDeep]
        exact Or.inl ⟨rfl, rfl⟩
  | snce d c ih2 ih1 =>
    unfold extractInnermostUType
    by_cases hc : isUFree c = false
    · simp only [hc, containsUntlDeep]
      exact Or.inl (ih1 hc hns.1)
    · simp only [hc, containsUntlDeep]
      have hd : isUFree d = false := by
        simp only [isUFree] at h; cases huf : isUFree c <;> simp_all
      exact Or.inr (ih2 hd hns.2)

/-- abstractUntl preserves hasNoAllpastAllfuture. -/
theorem abstract_untl_preserves_no_allpast_allfuture (phi A B : Formula Atom) (p : Atom)
    (h : hasNoAllpastAllfuture phi = true) :
    hasNoAllpastAllfuture (abstractUntl phi A B p) = true := by
  induction phi with
  | atom _ => simp [abstractUntl]
  | bot => simp [abstractUntl]
  | imp c d ih1 ih2 =>
    simp [abstractUntl]
  | box _ => simp [abstractUntl]
  | untl d c ih2 ih1 =>
    simp only [abstractUntl]
    split
    · simp [hasNoAllpastAllfuture]
    · simp [hasNoAllpastAllfuture]
  | snce d c ih2 ih1 =>
    simp [abstractUntl]

/-! ### Step 3: Substitution into Separated Formulas

The "constituent substitution" technique from GHR94 Lemma 10.2.6.
Given a separated formula ψ, substituting `.untl B` A (with S-free A, B)
for atom p yields a separable formula, provided we have a callback
for handling the `.snceand ` `.allPast` constituents. -/

/-- Substituting `.untl B` A (S-free args) for atom p in a separated formula
    produces a separable formula, using `ih_snce` for constituents where
    substitution breaks separation (`.snceand ` `.allPast` positions). -/
theorem subst_in_separated_separable (ψ : Formula Atom) (p : Atom) (A B : Formula Atom)
    (hA_sf : isSFree A = true) (hB_sf : isSFree B = true)
    (hsep : isSyntacticallySeparated ψ = true)
    (ih_snce : ∀ (χ : Formula Atom), noSNestedInU χ → isSeparable χ) :
    isSeparable (substFormula ψ p (.untl B A)) := by
  induction ψ with
  | atom a =>
    simp only [substFormula]; split
    · exact ⟨.untl B A, by simp [isSyntacticallySeparated, hA_sf, hB_sf], int_equiv_refl _⟩
    · exact ⟨.atom a, rfl, int_equiv_refl _⟩
  | bot => exact ⟨.bot, rfl, int_equiv_refl _⟩
  | box ψ => exact ⟨.box (substFormula ψ p (.untl B A)), rfl, int_equiv_refl _⟩
  | imp c d ih_c ih_d =>
    simp [isSyntacticallySeparated] at hsep
    exact imp_separable (ih_c hsep.1) (ih_d hsep.2)
  | untl d c _ _ =>
    simp [isSyntacticallySeparated] at hsep
    have hU_sf : isSFree (.untl B A) = true := by
      simp only [isSFree, hA_sf, hB_sf, Bool.and_self]
    exact ⟨.untl (substFormula d p (.untl B A)) (substFormula c p (.untl B A)),
           by simp [isSyntacticallySeparated,
                     subst_S_free_preserves_S_free c p _ hsep.1 hU_sf,
                     subst_S_free_preserves_S_free d p _ hsep.2 hU_sf],
           int_equiv_refl _⟩
  | snce d c _ _ =>
    simp [isSyntacticallySeparated] at hsep
    exact ih_snce (.snce (substFormula d p (.untl B A)) (substFormula c p (.untl B A)))
      ⟨subst_U_free_gives_no_S_nested c p A B hsep.1 hA_sf hB_sf,
       subst_U_free_gives_no_S_nested d p A B hsep.2 hA_sf hB_sf⟩

/-! ### Step 4: Additional Infrastructure

Substitution congruence and helper lemmas for the hierarchy theorem. -/

/-- Substitution preserves intEquiv: if φ ≡ ψ then subst(φ, p, r) ≡ subst(ψ, p, r). -/
theorem subst_formula_congr {φ ψ : Formula Atom} (h : intEquiv φ ψ)
    (p : Atom) (r : Formula Atom) :
    intEquiv (substFormula φ p r) (substFormula ψ p r) := by
  intro M t; rw [subst_correctness, subst_correctness]; exact h _ t

/-- Helper: `.untlwith ` S-free args is already separated. -/
theorem untl_sf_exp_separated (a b : Formula Atom)
    (ha_sf : isSFree a = true) (hb_sf : isSFree b = true) :
    isSeparable (.untl b a) :=
  ⟨.untl b a, by simp [isSyntacticallySeparated, ha_sf, hb_sf], int_equiv_refl _⟩

/-- Helper: `.sncewith ` U-free args is already separated. -/
theorem snce_uf_separated (a b : Formula Atom)
    (ha_uf : isUFree a = true) (hb_uf : isUFree b = true) :
    isSeparable (.snce b a) :=
  ⟨.snce b a, by simp [isSyntacticallySeparated, ha_uf, hb_uf], int_equiv_refl _⟩

/-- Extract a U-type (A, B) with S-free args from a non-U-free formula
    that has `noSNestedInU`. -/
noncomputable def extractUType : (φ : Formula Atom) → (isUFree φ = false) →
    noSNestedInU φ → (Formula Atom × Formula Atom)
  | .atom _, h, _ => by simp [isUFree] at h
  | .bot, h, _ => by simp [isUFree] at h
  | .imp c d, h, hns =>
    if hc : isUFree c = false then extractUType c hc hns.1
    else extractUType d (by simp only [isUFree] at h; simp [hc] at h; exact h) hns.2
  | .box c, h, hns => extractUType c (by simp only [isUFree] at h; exact h) hns
  | .untl b a, _, _ => (a, b)
  | .snce d c, h, hns =>
    if hc : isUFree c = false then extractUType c hc hns.1
    else extractUType d (by simp only [isUFree] at h; simp [hc] at h; exact h) hns.2

theorem extract_U_type_S_free (φ : Formula Atom) (h : isUFree φ = false)
    (hns : noSNestedInU φ) :
    isSFree (extractUType φ h hns).1 = true ∧
    isSFree (extractUType φ h hns).2 = true := by
  induction φ with
  | atom _ => simp [isUFree] at h
  | bot => simp [isUFree] at h
  | imp c d ih1 ih2 =>
    unfold extractUType
    by_cases hc : isUFree c = false
    · simp only [hc]; exact ih1 hc hns.1
    · simp only [hc]
      have hd : isUFree d = false := by
        simp only [isUFree] at h; cases huf : isUFree c <;> simp_all
      exact ih2 hd hns.2
  | box c ih => simp only [isUFree] at h; unfold extractUType; exact ih h hns
  | untl b a => exact hns
  | snce d c ih2 ih1 =>
    unfold extractUType
    by_cases hc : isUFree c = false
    · simp only [hc]; exact ih1 hc hns.1
    · simp only [hc]
      have hd : isUFree d = false := by
        simp only [isUFree] at h; cases huf : isUFree c <;> simp_all
      exact ih2 hd hns.2

/-- `extractUType` returns a pair `(A, B)` such that `containsUntlSurface φ A B`.
    This is the bridge between `extractUType` (which finds the first `.untlby `
    descending through `imp`, `box`, `snce`) and the count decrease lemma
    `abstract_untl_count_lt_of_contains_surface`. -/
theorem extract_U_type_contains_surface (φ : Formula Atom) (h : isUFree φ = false)
    (hns : noSNestedInU φ) :
    containsUntlSurface φ (extractUType φ h hns).1 (extractUType φ h hns).2 := by
  induction φ with
  | atom _ => simp [isUFree] at h
  | bot => simp [isUFree] at h
  | imp c d ih1 ih2 =>
    unfold extractUType
    by_cases hc : isUFree c = false
    · simp only [hc, containsUntlSurface]
      exact Or.inl (ih1 hc hns.1)
    · simp only [hc, containsUntlSurface]
      have hd : isUFree d = false := by
        simp only [isUFree] at h; cases huf : isUFree c <;> simp_all
      exact Or.inr (ih2 hd hns.2)
  | box c ih =>
    simp only [isUFree] at h
    unfold extractUType; simp only [containsUntlSurface]; exact ih h hns
  | untl b a =>
    unfold extractUType; exact ⟨rfl, rfl⟩
  | snce d c ih2 ih1 =>
    unfold extractUType
    by_cases hc : isUFree c = false
    · simp only [hc, containsUntlSurface]
      exact Or.inl (ih1 hc hns.1)
    · simp only [hc, containsUntlSurface]
      have hd : isUFree d = false := by
        simp only [isUFree] at h; cases huf : isUFree c <;> simp_all
      exact Or.inr (ih2 hd hns.2)

/-! ### Step 5: S-Nesting Depth Measure for Lemma 10.2.5

GHR94 Lemma 10.2.5 proves that a formula with a single U-type U(A,B) (A, B S-free)
is separable by induction on the maximum number of `.sncenodes ` above any `.untlin
` the formula tree. We define a non-mutual version of this measure and prove
the key properties needed for the well-founded induction. -/

/-- Maximum number of `.snceancestors ` above any `.untlnode ` in the formula tree.
    Returns 0 if the formula is U-free. For `.snce F` C, adds 1 if U appears below.
    Non-mutual version of `sNestingAboveU` for easier theorem proving. -/
def snceDepthOfU : Formula Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp a b => max (snceDepthOfU a) (snceDepthOfU b)
  | .box a => snceDepthOfU a
  | .untl _ _ => 0
  | .snce b a =>
    if isUFree a = true ∧ isUFree b = true then 0
    else 1 + max (snceDepthOfU a) (snceDepthOfU b)

/-- U-free formulas have snceDepthOfU = 0. -/
theorem snce_depth_of_U_zero_of_U_free (phi : Formula Atom)
    (h : isUFree phi = true) : snceDepthOfU phi = 0 := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [isUFree] at h
    simp [snceDepthOfU, ih1 h.1, ih2 h.2]
  | box a ih => simp [isUFree] at h; simp [snceDepthOfU, ih h]
  | untl _ _ => simp [isUFree] at h
  | snce b a ih2 ih1 =>
    simp [isUFree] at h
    simp [snceDepthOfU, h.1, h.2]

/-- Key property: for `.snce F` C where C or F is not U-free,
    `snceDepthOfU C < snceDepthOfU (.snce F C)` and similarly for F. -/
theorem snce_depth_of_U_lt_snce (C w : Formula Atom)
    (h : ¬(isUFree C = true ∧ isUFree w = true)) :
    snceDepthOfU C < snceDepthOfU (.snce w C) ∧
    snceDepthOfU w < snceDepthOfU (.snce w C) := by
  simp [snceDepthOfU, h]
  constructor <;> omega

/-- snceDepthOfU is monotone for imp subterms. -/
theorem snce_depth_of_U_le_imp_left (a b : Formula Atom) :
    snceDepthOfU a ≤ snceDepthOfU (.imp a b) :=
  Nat.le_max_left _ _

theorem snce_depth_of_U_le_imp_right (a b : Formula Atom) :
    snceDepthOfU b ≤ snceDepthOfU (.imp a b) :=
  Nat.le_max_right _ _

/-- snceDepthOfU passes through box unchanged. -/
theorem snce_depth_of_U_le_box (a : Formula Atom) :
    snceDepthOfU a ≤ snceDepthOfU (.box a) :=
  Nat.le_refl _

/-- For `.snce b` a where not both U-free, left arg has strictly smaller depth. -/
theorem snce_depth_of_U_le_snce_left (a b : Formula Atom)
    (h : ¬(isUFree a = true ∧ isUFree b = true)) :
    snceDepthOfU a ≤ snceDepthOfU (.snce b a) := by
  simp [snceDepthOfU, h]; omega

/-- For `.snce b` a where not both U-free, right arg has strictly smaller depth. -/
theorem snce_depth_of_U_le_snce_right (a b : Formula Atom)
    (h : ¬(isUFree a = true ∧ isUFree b = true)) :
    snceDepthOfU b ≤ snceDepthOfU (.snce b a) := by
  simp [snceDepthOfU, h]; omega

/-! ### Step 5b′: Base Case — snceDepthOfU = 0 with noSNestedInU

When `snceDepthOfU phi = 0` and `noSNestedInU phi`, the formula is
syntactically separated (hence separable). This generalizes
`snce_depth_zero_single_U_separated` by dropping the single-U-type and
hasNoAllpastAllfuture requirements.

The argument:
- `snceDepthOfU = 0`: every `.snce b` a has `isUFree a ∧ isUFree b`
  (the else branch adds 1, so depth 0 forces the if-branch at every `.snce`)
- `noSNestedInU`: every `.untl b` a has `isSFree a ∧ isSFree b`
- Together these imply `isSyntacticallySeparated phi = true`. -/

/-- Base case for GHR94 10.2.7: snceDepthOfU = 0 with noSNestedInU
    implies syntactically separated, hence separable. -/
theorem snce_depth_zero_no_S_nested_separated (phi : Formula Atom)
    (hns : noSNestedInU phi)
    (hd : snceDepthOfU phi = 0) :
    isSeparable phi := by
  suffices h : isSyntacticallySeparated phi = true from
    separated_imp_separable phi h
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [snceDepthOfU] at hd
    simp [noSNestedInU] at hns
    simp [isSyntacticallySeparated, ih1 hns.1 (by omega), ih2 hns.2 (by omega)]
  | box a ih =>
    simp [isSyntacticallySeparated]
  | untl b a _ _ =>
    simp [noSNestedInU] at hns
    simp [isSyntacticallySeparated, hns.1, hns.2]
  | snce b a _ _ =>
    simp [snceDepthOfU] at hd
    simp [isSyntacticallySeparated, hd.1, hd.2]

/-! ### Step 5b: Base Case — snceDepthOfU = 0 with single U-type

When snceDepthOfU phi = 0 and phi has single U-type U(A,B) with S-free A, B
and hasNoAllpastAllfuture, then phi is syntactically separated.

This means: every `.sncein ` phi has U-free args, and every `.untlis ` U(A,B)
with S-free args. So `.untlpositions ` have S-free args and `.sncepositions `
have U-free args. -/

/-- When snceDepthOfU = 0 and hasSingleUType, every `.sncesubformula `
    has U-free args, so the formula is syntactically separated
    (given hasNoAllpastAllfuture). -/
theorem snce_depth_zero_single_U_separated (phi A B : Formula Atom)
    (hA_sf : isSFree A = true) (hB_sf : isSFree B = true)
    (hsingle : hasSingleUType phi A B)
    (hexp : hasNoAllpastAllfuture phi = true)
    (hdepth : snceDepthOfU phi = 0) :
    isSyntacticallySeparated phi = true := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [snceDepthOfU] at hdepth
    simp [isSyntacticallySeparated,
      ih1 hsingle.1 (has_no_allpast_allfuture_true a) (by omega),
      ih2 hsingle.2 (has_no_allpast_allfuture_true b) (by omega)]
  | box _ => rfl
  | untl b a _ _ =>
    have ⟨ha, hb⟩ := hsingle; subst ha; subst hb
    simp [isSyntacticallySeparated, hA_sf, hB_sf]
  | snce b a _ _ =>
    simp [snceDepthOfU] at hdepth
    obtain ⟨ha_uf, hb_uf⟩ := hdepth
    simp [isSyntacticallySeparated, ha_uf, hb_uf]

/-! ### U-Nesting Depth Measure for Lemma 10.2.7

GHR94 Lemma 10.2.7 inducts on the maximum depth of U-nesting chains
(the "maximum depth n of nesting of Us beneath an S"). This is different
from `snceDepthOfU` (which counts S-layers above U and stops at `.untlnodes
`). `uNestingDepth` counts `.untlnesting ` levels throughout the
formula, passing through `.sncetransparently. ` -/

/-- Maximum depth of U-nesting chains in a formula.
    Counts how many levels of `.untlare ` nested (through U-args).
    `.sncepasses ` through (takes max), `.untlincrements ` by 1.
    This is GHR94's "depth of nesting of Us beneath an S" for 10.2.7. -/
def uNestingDepth : Formula Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp a b => max (uNestingDepth a) (uNestingDepth b)
  | .box a => uNestingDepth a
  | .untl b a => 1 + max (uNestingDepth a) (uNestingDepth b)
  | .snce b a => max (uNestingDepth a) (uNestingDepth b)

/-- uNestingDepth = 0 iff the formula is U-free. -/
theorem U_nesting_depth_zero_iff_U_free (phi : Formula Atom) :
    uNestingDepth phi = 0 ↔ isUFree phi = true := by
  induction phi with
  | atom _ => simp only [uNestingDepth, isUFree]
  | bot => simp only [uNestingDepth, isUFree]
  | imp a b ih1 ih2 =>
    simp only [uNestingDepth, isUFree, Nat.max_eq_zero_iff, Bool.and_eq_true, ih1, ih2]
  | box a ih =>
    simp only [uNestingDepth, isUFree]
    exact ih
  | untl _ _ _ _ =>
    simp only [uNestingDepth, isUFree]
    exact iff_of_false (by omega) (by decide)
  | snce b a ih2 ih1 =>
    simp only [uNestingDepth, isUFree, Nat.max_eq_zero_iff, Bool.and_eq_true, ih1, ih2]

/-- U-free formulas have uNestingDepth = 0. -/
theorem U_nesting_depth_zero_of_U_free (phi : Formula Atom)
    (h : isUFree phi = true) : uNestingDepth phi = 0 :=
  (U_nesting_depth_zero_iff_U_free phi).mpr h

/-- When uNestingDepth <= 1 and noSNestedInU, all U-args are U-free.
    This is the key property: at depth <= 1, U-args are boolean (U-free AND S-free). -/
theorem U_nesting_depth_le_one_untl_args_U_free (a b : Formula Atom)
    (h : uNestingDepth (.untl b a) ≤ 1) :
    isUFree a = true ∧ isUFree b = true := by
  simp only [uNestingDepth] at h
  have ha : uNestingDepth a = 0 := by omega
  have hb : uNestingDepth b = 0 := by omega
  exact ⟨(U_nesting_depth_zero_iff_U_free a).mp ha,
         (U_nesting_depth_zero_iff_U_free b).mp hb⟩

-- Monotonicity lemmas

theorem U_nesting_depth_le_imp_left (a b : Formula Atom) :
    uNestingDepth a ≤ uNestingDepth (.imp a b) := by
  simp only [uNestingDepth]
  exact Nat.le_max_left _ _

theorem U_nesting_depth_le_imp_right (a b : Formula Atom) :
    uNestingDepth b ≤ uNestingDepth (.imp a b) := by
  simp only [uNestingDepth]
  exact Nat.le_max_right _ _

theorem U_nesting_depth_le_box (a : Formula Atom) :
    uNestingDepth a ≤ uNestingDepth (.box a) := by
  simp only [uNestingDepth, le_refl]

theorem U_nesting_depth_le_snce_left (a b : Formula Atom) :
    uNestingDepth a ≤ uNestingDepth (.snce b a) := by
  simp only [uNestingDepth]
  exact Nat.le_max_left _ _

theorem U_nesting_depth_le_snce_right (a b : Formula Atom) :
    uNestingDepth b ≤ uNestingDepth (.snce b a) := by
  simp only [uNestingDepth]
  exact Nat.le_max_right _ _

theorem U_nesting_depth_lt_untl_left (a b : Formula Atom) :
    uNestingDepth a < uNestingDepth (.untl b a) := by
  simp only [uNestingDepth]
  omega

theorem U_nesting_depth_lt_untl_right (a b : Formula Atom) :
    uNestingDepth b < uNestingDepth (.untl b a) := by
  simp only [uNestingDepth]
  omega

/-- abstractUntl does not increase uNestingDepth.
    Replacing `.untl B` A with `.atom p` can only decrease or maintain the depth. -/
theorem abstract_untl_U_nesting_depth_le (phi A B : Formula Atom) (p : Atom) :
    uNestingDepth (abstractUntl phi A B p) ≤ uNestingDepth phi := by
  induction phi with
  | atom _ => simp [abstractUntl, uNestingDepth]
  | bot => simp [abstractUntl, uNestingDepth]
  | imp c d ih1 ih2 =>
    simp only [abstractUntl, uNestingDepth]; omega
  | box c ih =>
    simp only [abstractUntl, uNestingDepth]; exact ih
  | untl d c ih2 ih1 =>
    simp only [abstractUntl]
    split
    · simp only [uNestingDepth]; omega
    · simp only [uNestingDepth]; omega
  | snce d c ih2 ih1 =>
    simp only [abstractUntl, uNestingDepth]; omega

/-- Corollary: abstractUntl preserves the uNestingDepth <= k bound. -/
theorem abstract_untl_U_nesting_depth_le_of_le (phi A B : Formula Atom) (p : Atom) (k : Nat)
    (h : uNestingDepth phi ≤ k) :
    uNestingDepth (abstractUntl phi A B p) ≤ k :=
  Nat.le_trans (abstract_untl_U_nesting_depth_le phi A B p) h

/-! ### Callback Single-U-Type Infrastructure (Task 3.4)

Substituting U(A,B) (with U-free A, B) for an atom in a U-free formula yields
a formula with single U-type U(A,B). This is the key property enabling the
self-contained depth-1 case in Lemma 10.2.5 (axiom-free). -/

/-- Substituting U(A,B) (with U-free A, B) for an atom in a U-free formula
    yields a formula with single U-type U(A,B). -/
theorem subst_U_free_gives_single_U_type (c : Formula Atom) (p : Atom)
    (A B : Formula Atom)
    (hc_U_free : isUFree c = true)
    (hA_U_free : isUFree A = true)
    (hB_U_free : isUFree B = true) :
    hasSingleUType (substFormula c p (.untl B A)) A B := by
  induction c with
  | atom a =>
    simp only [substFormula]
    split
    · -- a = p: result is .untl B A
      exact ⟨rfl, rfl⟩
    · -- a ≠ p: result is .atom a
      trivial
  | bot => simp only [substFormula, hasSingleUType]
  | imp c d ih1 ih2 =>
    simp only [isUFree, Bool.and_eq_true] at hc_U_free
    simp only [substFormula, hasSingleUType]
    exact ⟨ih1 hc_U_free.1, ih2 hc_U_free.2⟩
  | box c ih =>
    simp only [isUFree] at hc_U_free
    simp only [substFormula, hasSingleUType]
    exact ih hc_U_free
  | untl _ _ => simp only [isUFree, Bool.false_eq_true] at hc_U_free
  | snce d c ih2 ih1 =>
    simp only [isUFree, Bool.and_eq_true] at hc_U_free
    simp only [substFormula, hasSingleUType]
    exact ⟨ih1 hc_U_free.1, ih2 hc_U_free.2⟩

/-- Callback formulas from subst_in_separated_separable have single U-type
    when the separated formula's snce-args are U-free (which they are by
    definition of isSyntacticallySeparated). -/
theorem callback_has_single_U_type (c d : Formula Atom) (p : Atom) (A B : Formula Atom)
    (hc_U_free : isUFree c = true) (hd_U_free : isUFree d = true)
    (hA_U_free : isUFree A = true) (hB_U_free : isUFree B = true) :
    hasSingleUType (.snce (substFormula d p (.untl B A))
                             (substFormula c p (.untl B A))) A B :=
  ⟨subst_U_free_gives_single_U_type c p A B hc_U_free hA_U_free hB_U_free,
   subst_U_free_gives_single_U_type d p A B hd_U_free hA_U_free hB_U_free⟩

/-- Version of `subst_in_separated_separable` where the callback also receives
    `hasSingleUType chi A B`. This enables the callback to use
    `single_U_formula_separable_noax` which requires single-U-type.
    Used by `lemma_10_2_6_self_contained` for the axiom-free depth-1 case. -/
theorem subst_in_separated_separable_typed (ψ : Formula Atom) (p : Atom) (A B : Formula Atom)
    (hA_sf : isSFree A = true) (hB_sf : isSFree B = true)
    (hA_uf : isUFree A = true) (hB_uf : isUFree B = true)
    (hsep : isSyntacticallySeparated ψ = true)
    (ih_snce : ∀ (χ : Formula Atom), noSNestedInU χ →
        hasSingleUType χ A B → isSeparable χ) :
    isSeparable (substFormula ψ p (.untl B A)) := by
  induction ψ with
  | atom a =>
    simp only [substFormula]; split
    · exact ⟨.untl B A, by simp [isSyntacticallySeparated, hA_sf, hB_sf], int_equiv_refl _⟩
    · exact ⟨.atom a, rfl, int_equiv_refl _⟩
  | bot => exact ⟨.bot, rfl, int_equiv_refl _⟩
  | box ψ => exact ⟨.box (substFormula ψ p (.untl B A)), rfl, int_equiv_refl _⟩
  | imp c d ih_c ih_d =>
    simp [isSyntacticallySeparated] at hsep
    exact imp_separable (ih_c hsep.1) (ih_d hsep.2)
  | untl d c _ _ =>
    simp [isSyntacticallySeparated] at hsep
    have hU_sf : isSFree (.untl B A) = true := by
      simp only [isSFree, hA_sf, hB_sf, Bool.and_self]
    exact ⟨.untl (substFormula d p (.untl B A)) (substFormula c p (.untl B A)),
           by simp [isSyntacticallySeparated,
                     subst_S_free_preserves_S_free c p _ hsep.1 hU_sf,
                     subst_S_free_preserves_S_free d p _ hsep.2 hU_sf],
           int_equiv_refl _⟩
  | snce d c _ _ =>
    simp [isSyntacticallySeparated] at hsep
    have hns : noSNestedInU (.snce (substFormula d p (.untl B A))
        (substFormula c p (.untl B A))) :=
      ⟨subst_U_free_gives_no_S_nested c p A B hsep.1 hA_sf hB_sf,
       subst_U_free_gives_no_S_nested d p A B hsep.2 hA_sf hB_sf⟩
    have hsingle : hasSingleUType (.snce (substFormula d p (.untl B A))
        (substFormula c p (.untl B A))) A B :=
      callback_has_single_U_type c d p A B hsep.1 hsep.2 hA_uf hB_uf
    exact ih_snce _ hns hsingle

/-! ### Syntactically Separated implies snceDepthOfU = 0 (Task 3.5)

A syntactically separated formula has snceDepthOfU = 0. This is the KEY
bridge lemma for single_U_formula_separable_noax: when the IH produces
separated C' and F', this lemma gives snceDepthOfU C' = 0 and
snceDepthOfU F' = 0, so .snce F' C' has depth exactly 1. -/

/-- After box-normalization, a syntactically separated formula has snceDepthOfU = 0.
    The raw theorem without box-normalization fails because isSyntacticallySeparated
    treats .box as atomic while snceDepthOfU passes through it. But after
    replaceBoxWithTop, all .box nodes become .imp .bot .bot (which has depth 0),
    so the induction goes through.

    This is the KEY bridge lemma for single_U_formula_separable_noax: when the IH
    produces separated C' and F', applying replaceBoxWithTop gives C'' and F''
    with snceDepthOfU = 0, so .snce F'' C'' has depth exactly 1. -/
theorem separated_boxnorm_snce_depth_zero (phi : Formula Atom)
    (hsep : isSyntacticallySeparated phi = true) :
    snceDepthOfU (replaceBoxWithTop phi) = 0 := by
  induction phi with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp only [isSyntacticallySeparated, Bool.and_eq_true] at hsep
    simp only [replaceBoxWithTop, snceDepthOfU, ih1 hsep.1, ih2 hsep.2, Nat.max_self]
  | box _ =>
    simp only [replaceBoxWithTop, snceDepthOfU, Nat.max_self]
  | untl _ _ =>
    simp only [replaceBoxWithTop, snceDepthOfU]
  | snce b a _ _ =>
    simp only [isSyntacticallySeparated, Bool.and_eq_true] at hsep
    have ha_uf := replace_box_preserves_U_free a hsep.1
    have hb_uf := replace_box_preserves_U_free b hsep.2
    simp only [replaceBoxWithTop, snceDepthOfU, ha_uf, hb_uf, and_self, ↓reduceIte]

/-! ### Step 5c: Single-U-Type at Depth 0 — Direct Separability via Event-Guard Decomposition

GHR94 Lemma 10.2.4: `.snce F` C where U(A,B) appears only at top level (not under
any S within C or F) is separable. The proof decomposes into Cases 1-8 using:
1. Event-splitting on U(A,B)
2. CNF decomposition of the guard
3. Generalized Cases 1-8 (no S-free requirement on a, q)

Key technique: `C ∧ U(A,B) ≡ C[U:=⊤] ∧ U(A,B)` where C[U:=⊤] is U-free. -/

/-- Replace all `.untl B` A with a constant formula `r` in `C`.
    Simpler than abstractUntl + subst: directly replaces at formula level. -/
def replaceUntl (C A B r : Formula Atom) : Formula Atom :=
  match C with
  | .atom a => .atom a
  | .bot => .bot
  | .imp c d => .imp (replaceUntl c A B r) (replaceUntl d A B r)
  | .box c => .box (replaceUntl c A B r)
  | .untl d c => if c = A ∧ d = B then r else .untl (replaceUntl d A B r) (replaceUntl c A B r)
  | .snce d c => .snce (replaceUntl d A B r) (replaceUntl c A B r)

/-- replaceUntl with single U-type produces a U-free formula when r is U-free. -/
theorem replace_untl_U_free (C A B r : Formula Atom)
    (hsingle : hasSingleUType C A B) (hr : isUFree r = true) :
    isUFree (replaceUntl C A B r) = true := by
  induction C with
  | atom _ => simp [replaceUntl, isUFree]
  | bot => simp [replaceUntl, isUFree]
  | imp c d ih1 ih2 =>
    simp [replaceUntl, isUFree, ih1 hsingle.1, ih2 hsingle.2]
  | box c ih =>
    simp [replaceUntl, isUFree, ih hsingle]
  | untl d c _ _ =>
    have ⟨hc, hd⟩ := hsingle; subst hc; subst hd
    simp [replaceUntl, hr]
  | snce d c ih2 ih1 =>
    simp [replaceUntl, isUFree, ih1 hsingle.1, ih2 hsingle.2]

/-- replaceUntl is identity on U-free formulas. -/
theorem replace_untl_identity_U_free (C A B r : Formula Atom) (h : isUFree C = true) :
    replaceUntl C A B r = C := by
  induction C with
  | atom _ => simp [replaceUntl]
  | bot => simp [replaceUntl]
  | imp c d ih1 ih2 => simp [isUFree] at h; simp [replaceUntl, ih1 h.1, ih2 h.2]
  | box c ih => simp [isUFree] at h; simp [replaceUntl, ih h]
  | untl _ _ => simp [isUFree] at h
  | snce d c ih2 ih1 => simp [isUFree] at h; simp [replaceUntl, ih1 h.1, ih2 h.2]

/-- When U(A,B) holds at a point and C has single U-type with snceDepthOfU = 0
    and hasNoAllpastAllfuture, C evaluates identically to replaceUntl C A B (¬⊥).
    This is because every .untl B A in C is evaluated at the SAME point t
    (not shifted by .snce .allPast/.allFuture or). -/
theorem single_U_eval_when_U_true (C A B : Formula Atom)
    (hsingle : hasSingleUType C A B)
    (hexp : hasNoAllpastAllfuture C = true)
    (hdepth : snceDepthOfU C = 0) (M : IntStructure Atom) (t : ℤ)
    (hU : intTruth M t (.untl B A)) :
    intTruth M t C ↔ intTruth M t (replaceUntl C A B (Formula.neg .bot)) := by
  induction C with
  | atom _ => simp [replaceUntl]
  | bot => simp [replaceUntl]
  | imp c d ih1 ih2 =>
    simp [snceDepthOfU] at hdepth
    simp only [replaceUntl, intTruth]
    exact Iff.imp (ih1 hsingle.1 (has_no_allpast_allfuture_true c) (by omega))
                  (ih2 hsingle.2 (has_no_allpast_allfuture_true d) (by omega))
  | box _ => simp [replaceUntl, intTruth]
  | untl d c _ _ =>
    have ⟨hc, hd⟩ := hsingle; subst hc; subst hd
    simp [replaceUntl, Formula.neg, intTruth]
    exact hU
  | snce d c ih2 ih1 =>
    -- snceDepthOfU (.snce d c) = 0 means both c and d are U-free
    simp [snceDepthOfU] at hdepth
    obtain ⟨hc_uf, hd_uf⟩ := hdepth
    -- Both c, d are U-free. replaceUntl is identity.
    simp only [replaceUntl,
      replace_untl_identity_U_free c A B _ hc_uf,
      replace_untl_identity_U_free d A B _ hd_uf]

/-- Dual: when ¬U(A,B) holds at a point, C evaluates identically to replaceUntl C A B ⊥. -/
theorem single_U_eval_when_U_false (C A B : Formula Atom)
    (hsingle : hasSingleUType C A B)
    (hexp : hasNoAllpastAllfuture C = true)
    (hdepth : snceDepthOfU C = 0) (M : IntStructure Atom) (t : ℤ)
    (hnotU : ¬ intTruth M t (.untl B A)) :
    intTruth M t C ↔ intTruth M t (replaceUntl C A B .bot) := by
  induction C with
  | atom _ => simp [replaceUntl]
  | bot => simp [replaceUntl]
  | imp c d ih1 ih2 =>
    simp [snceDepthOfU] at hdepth
    simp only [replaceUntl, intTruth]
    exact Iff.imp (ih1 hsingle.1 (has_no_allpast_allfuture_true c) (by omega))
                  (ih2 hsingle.2 (has_no_allpast_allfuture_true d) (by omega))
  | box _ => simp [replaceUntl, intTruth]
  | untl d c _ _ =>
    have ⟨hc, hd⟩ := hsingle; subst hc; subst hd
    simp only [replaceUntl, ite_true, and_self, intTruth]
    constructor
    · intro ⟨_, _, _, _⟩; exact False.elim (hnotU ⟨_, ‹_›, ‹_›, ‹_›⟩)
    · intro h; exact False.elim h
  | snce d c ih2 ih1 =>
    simp [snceDepthOfU] at hdepth
    obtain ⟨hc_uf, hd_uf⟩ := hdepth
    simp only [replaceUntl,
      replace_untl_identity_U_free c A B _ hc_uf,
      replace_untl_identity_U_free d A B _ hd_uf]

/-- Semantic equivalence: C ∧ U(A,B) ≡ C[U:=⊤] ∧ U(A,B) for single-U-type C. -/
theorem single_U_and_conj_simplify (C A B : Formula Atom)
    (hsingle : hasSingleUType C A B)
    (hexp : hasNoAllpastAllfuture C = true)
    (hdepth : snceDepthOfU C = 0) :
    intEquiv (Formula.and C (.untl B A))
              (Formula.and (replaceUntl C A B (Formula.neg .bot)) (.untl B A)) := by
  intro M t; constructor
  · intro h
    have ⟨hC, hU⟩ := int_truth_and_iff.mp h
    exact int_truth_and_iff.mpr ⟨(single_U_eval_when_U_true C A B hsingle hexp hdepth M t hU).mp hC, hU⟩
  · intro h
    have ⟨hCt, hU⟩ := int_truth_and_iff.mp h
    exact int_truth_and_iff.mpr ⟨(single_U_eval_when_U_true C A B hsingle hexp hdepth M t hU).mpr hCt, hU⟩

/-- Dual of `single_U_and_conj_simplify`: C ∧ ¬U(A,B) ≡ C[U:=⊥] ∧ ¬U(A,B). -/
theorem single_U_and_conj_simplify_neg (C A B : Formula Atom)
    (hsingle : hasSingleUType C A B)
    (hexp : hasNoAllpastAllfuture C = true)
    (hdepth : snceDepthOfU C = 0) :
    intEquiv (Formula.and C (Formula.neg (.untl B A)))
              (Formula.and (replaceUntl C A B .bot) (Formula.neg (.untl B A))) := by
  intro M t; constructor
  · intro h
    have ⟨hC, hnotU⟩ := int_truth_and_iff.mp h
    have hnotU' : ¬ intTruth M t (.untl B A) := int_truth_neg_iff.mp hnotU
    exact int_truth_and_iff.mpr
      ⟨(single_U_eval_when_U_false C A B hsingle hexp hdepth M t hnotU').mp hC, hnotU⟩
  · intro h
    have ⟨hCb, hnotU⟩ := int_truth_and_iff.mp h
    have hnotU' : ¬ intTruth M t (.untl B A) := int_truth_neg_iff.mp hnotU
    exact int_truth_and_iff.mpr
      ⟨(single_U_eval_when_U_false C A B hsingle hexp hdepth M t hnotU').mpr hCb, hnotU⟩

/-- Guard 2-clause CNF decomposition for single-U-type formulas:
    F ≡ (replaceUntl(F,A,B,⊤) ∨ ¬U(A,B)) ∧ (U(A,B) ∨ replaceUntl(F,A,B,⊥))
    where ⊤ = Formula.neg .bot.

    Proof: By classical case split on U(A,B) at each point t:
    - If U(A,B) true: F ↔ replaceUntl(F,A,B,⊤) (by single_U_eval_when_U_true).
      RHS first clause: ⊤ ∨ ¬U = ⊤. Second clause: U ∨ q_neg = ⊤.
      Both sides reduce to F ↔ q_pos.
    - If ¬U(A,B): F ↔ replaceUntl(F,A,B,⊥) (by single_U_eval_when_U_false).
      RHS first clause: q_pos ∨ ⊤ = ⊤. Second clause: ⊥ ∨ q_neg = q_neg.
      Both sides reduce to F ↔ q_neg. -/
theorem single_U_guard_cnf (w A B : Formula Atom)
    (hsingle : hasSingleUType w A B)
    (hexp : hasNoAllpastAllfuture w = true)
    (hdepth : snceDepthOfU w = 0) :
    intEquiv w (Formula.and
      (Formula.or (replaceUntl w A B (Formula.neg .bot)) (Formula.neg (.untl B A)))
      (Formula.or (.untl B A) (replaceUntl w A B .bot))) := by
  intro M t; constructor
  · intro hF
    apply int_truth_and_iff.mpr
    constructor
    · -- First clause: q_pos ∨ ¬U
      apply int_truth_or_iff.mpr
      by_cases hU : intTruth M t (.untl B A)
      · left; exact (single_U_eval_when_U_true w A B hsingle hexp hdepth M t hU).mp hF
      · right; exact int_truth_neg_iff.mpr hU
    · -- Second clause: U ∨ q_neg
      apply int_truth_or_iff.mpr
      by_cases hU : intTruth M t (.untl B A)
      · left; exact hU
      · right; exact (single_U_eval_when_U_false w A B hsingle hexp hdepth M t hU).mp hF
  · intro h
    have ⟨h1, h2⟩ := int_truth_and_iff.mp h
    by_cases hU : intTruth M t (.untl B A)
    · -- U true: from second clause, we have U ∨ q_neg. We need F.
      -- From first clause: q_pos ∨ ¬U. Since U, the ¬U branch is false, so q_pos.
      rcases int_truth_or_iff.mp h1 with hqp | hnotU
      · exact (single_U_eval_when_U_true w A B hsingle hexp hdepth M t hU).mpr hqp
      · exact absurd hU (int_truth_neg_iff.mp hnotU)
    · -- ¬U: from second clause: U ∨ q_neg. Since ¬U, we have q_neg.
      rcases int_truth_or_iff.mp h2 with hU' | hqn
      · exact absurd hU' hU
      · exact (single_U_eval_when_U_false w A B hsingle hexp hdepth M t hU).mpr hqn

/-- Guard conjunction distribution for Since (Lemma 10.2.1(ii)):
    S(ev, G₁ ∧ G₂) ↔ S(ev, G₁) ∧ S(ev, G₂).
    Re-export of `since_distrib_and_right` with the naming convention
    used in this file. -/
theorem snce_conj_guard_distribute (ev G1 G2 : Formula Atom) :
    intEquiv (.snce (Formula.and G1 G2) ev)
              (Formula.and (.snce G1 ev) (.snce G2 ev)) :=
  since_distrib_and_right ev G1 G2

/-- Congruence for untl: if a ≡ a' and b ≡ b' then untl a b ≡ untl a' b'. -/
theorem untl_congr {a a' b b' : Formula Atom}
    (ha : intEquiv a a') (hb : intEquiv b b') :
    intEquiv (.untl b a) (.untl b' a') := by
  intro M t; constructor
  · rintro ⟨s, hts, hφ, hψ⟩
    exact ⟨s, hts, (ha M s).mp hφ, fun r hr1 hr2 => (hb M r).mp (hψ r hr1 hr2)⟩
  · rintro ⟨s, hts, hφ, hψ⟩
    exact ⟨s, hts, (ha M s).mpr hφ, fun r hr1 hr2 => (hb M r).mpr (hψ r hr1 hr2)⟩

/-- Congruence for snce: if a ≡ a' and b ≡ b' then snce a b ≡ snce a' b'. -/
theorem snce_congr {a a' b b' : Formula Atom}
    (ha : intEquiv a a') (hb : intEquiv b b') :
    intEquiv (.snce b a) (.snce b' a') := by
  intro M t; constructor
  · rintro ⟨s, hst, hφ, hψ⟩
    exact ⟨s, hst, (ha M s).mp hφ, fun r hr1 hr2 => (hb M r).mp (hψ r hr1 hr2)⟩
  · rintro ⟨s, hst, hφ, hψ⟩
    exact ⟨s, hst, (ha M s).mpr hφ, fun r hr1 hr2 => (hb M r).mpr (hψ r hr1 hr2)⟩

/-- GHR94 Lemma 10.2.4 (general form -- the leaf case):
    `.snce F` C where C, F have `snceDepthOfU = 0` and `hasSingleUType`
    is separable. Non-recursive -- uses event-guard decomposition + Cases 1-8.

    Proof strategy:
    1. Event-split on U(A,B): S(C,F) <-> S(C^U,F) v S(C^-U,F)
    2. Simplify events: C^U <-> a^U, C^-U <-> a'^-U (a, a' U-free)
    3. Case-split guard F:
       - F U-free: Cases 1/2 directly
       - F not U-free: Guard 2-clause CNF: F <-> (q_pos v -U) ^ (U v q_neg)
         Then S(ev, F) <-> S(ev, q_pos v -U) ^ S(ev, U v q_neg) (Lemma 10.2.1(ii))
         Each term matches Cases 5-8. -/
theorem snce_single_U_depth_one_separable (C w A B : Formula Atom)
    (hA_sf : isSFree A = true) (hB_sf : isSFree B = true)
    (hA_uf : isUFree A = true) (hB_uf : isUFree B = true)
    (hsingle_C : hasSingleUType C A B)
    (hsingle_w : hasSingleUType w A B)
    (hdC : snceDepthOfU C = 0) (hdw : snceDepthOfU w = 0)
    (hexp_C : hasNoAllpastAllfuture C = true)
    (hexp_w : hasNoAllpastAllfuture w = true) :
    isSeparable (.snce w C) := by
  -- Step 1: Event-split on U(A,B)
  -- S(C,w) <-> S(C^U,w) v S(C^-U,w)
  apply since_event_split_separable C A B w
  -- Positive branch: S(C ^ U(A,B), w)
  · -- Step 2a: Simplify event C^U to a^U where a is U-free
    have h_simp_pos := single_U_and_conj_simplify C A B hsingle_C hexp_C hdC
    -- a = replaceUntl C A B (neg bot) is U-free
    let a_pos := replaceUntl C A B (Formula.neg .bot)
    have ha_uf : isUFree a_pos = true :=
      replace_untl_U_free C A B (Formula.neg .bot) hsingle_C (by simp [isUFree])
    -- S(C^U, w) is equiv to S(a^U, w)
    have h_equiv_pos : intEquiv (.snce w (Formula.and C (.untl B A)))
        (.snce w (Formula.and a_pos (.untl B A))) :=
      snce_congr h_simp_pos (int_equiv_refl w)
    apply is_separable_of_equiv h_equiv_pos
    -- Step 3: Case-split on whether w is U-free
    by_cases hwuf : isUFree w = true
    · -- w is U-free: Case 1
      exact case1_separable_gen a_pos w A B ha_uf hwuf hA_uf hB_uf hA_sf hB_sf
    · -- w not U-free: apply guard 2-clause CNF
      push Not at hwuf; simp [Bool.not_eq_true] at hwuf
      -- Guard CNF: w <-> (q_pos v -U) ^ (U v q_neg)
      have h_cnf := single_U_guard_cnf w A B hsingle_w hexp_w hdw
      let q_pos := replaceUntl w A B (Formula.neg .bot)
      let q_neg := replaceUntl w A B .bot
      have hqp_uf : isUFree q_pos = true :=
        replace_untl_U_free w A B (Formula.neg .bot) hsingle_w (by simp [isUFree])
      have hqn_uf : isUFree q_neg = true :=
        replace_untl_U_free w A B .bot hsingle_w (by simp [isUFree])
      -- S(a^U, w) equiv S(a^U, (q_pos v -U) ^ (U v q_neg))
      have h_guard_equiv : intEquiv (.snce w (Formula.and a_pos (.untl B A)))
          (.snce (Formula.and (Formula.or q_pos (Formula.neg (.untl B A)))
                         (Formula.or (.untl B A) q_neg))
            (Formula.and a_pos (.untl B A))) :=
        snce_congr (int_equiv_refl _) h_cnf
      apply is_separable_of_equiv h_guard_equiv
      -- Distribute S over guard conjunction (Lemma 10.2.1(ii))
      have h_distrib := snce_conj_guard_distribute
        (Formula.and a_pos (.untl B A))
        (Formula.or q_pos (Formula.neg (.untl B A)))
        (Formula.or (.untl B A) q_neg)
      apply is_separable_of_equiv h_distrib
      -- Now need: S(a^U, q_pos v -U) ^ S(a^U, U v q_neg) is separable
      apply and_separable
      · -- S(a^U, q_pos v -U): Case 7
        exact case7_separable_gen' a_pos q_pos A B ha_uf hqp_uf hA_uf hB_uf hA_sf hB_sf
      · -- S(a^U, U v q_neg): Case 5
        -- Need to rewrite (U v q_neg) as (q_neg v U)
        have h_comm : intEquiv (Formula.or (.untl B A) q_neg) (Formula.or q_neg (.untl B A)) := by
          intro M t; constructor
          · intro h; rcases int_truth_or_iff.mp h with hu | hq
            · exact int_truth_or_iff.mpr (Or.inr hu)
            · exact int_truth_or_iff.mpr (Or.inl hq)
          · intro h; rcases int_truth_or_iff.mp h with hq | hu
            · exact int_truth_or_iff.mpr (Or.inr hq)
            · exact int_truth_or_iff.mpr (Or.inl hu)
        have h_snce_comm : intEquiv
            (.snce (Formula.or (.untl B A) q_neg) (Formula.and a_pos (.untl B A)))
            (.snce (Formula.or q_neg (.untl B A)) (Formula.and a_pos (.untl B A))) :=
          snce_congr (int_equiv_refl _) h_comm
        apply is_separable_of_equiv h_snce_comm
        exact case5_separable_gen' a_pos q_neg A B ha_uf hqn_uf hA_uf hB_uf hA_sf hB_sf
  -- Negative branch: S(C ^ -U(A,B), w)
  · -- Step 2b: Simplify event C^-U to a'^-U where a' is U-free
    have h_simp_neg := single_U_and_conj_simplify_neg C A B hsingle_C hexp_C hdC
    let a_neg := replaceUntl C A B .bot
    have ha_neg_uf : isUFree a_neg = true :=
      replace_untl_U_free C A B .bot hsingle_C (by simp [isUFree])
    -- S(C^-U, w) equiv S(a'^-U, w)
    have h_equiv_neg : intEquiv (.snce w (Formula.and C (Formula.neg (.untl B A))))
        (.snce w (Formula.and a_neg (Formula.neg (.untl B A)))) :=
      snce_congr h_simp_neg (int_equiv_refl w)
    apply is_separable_of_equiv h_equiv_neg
    -- Case-split on whether w is U-free
    by_cases hwuf : isUFree w = true
    · -- w U-free: Case 2
      exact case2_separable_gen a_neg w A B ha_neg_uf hwuf hA_uf hB_uf hA_sf hB_sf
    · -- w not U-free: apply guard 2-clause CNF
      push Not at hwuf; simp [Bool.not_eq_true] at hwuf
      have h_cnf := single_U_guard_cnf w A B hsingle_w hexp_w hdw
      let q_pos := replaceUntl w A B (Formula.neg .bot)
      let q_neg := replaceUntl w A B .bot
      have hqp_uf : isUFree q_pos = true :=
        replace_untl_U_free w A B (Formula.neg .bot) hsingle_w (by simp [isUFree])
      have hqn_uf : isUFree q_neg = true :=
        replace_untl_U_free w A B .bot hsingle_w (by simp [isUFree])
      -- S(a'^-U, w) equiv S(a'^-U, (q_pos v -U) ^ (U v q_neg))
      have h_guard_equiv : intEquiv (.snce w (Formula.and a_neg (Formula.neg (.untl B A))))
          (.snce (Formula.and (Formula.or q_pos (Formula.neg (.untl B A)))
                         (Formula.or (.untl B A) q_neg))
            (Formula.and a_neg (Formula.neg (.untl B A)))) :=
        snce_congr (int_equiv_refl _) h_cnf
      apply is_separable_of_equiv h_guard_equiv
      -- Distribute S over guard conjunction
      have h_distrib := snce_conj_guard_distribute
        (Formula.and a_neg (Formula.neg (.untl B A)))
        (Formula.or q_pos (Formula.neg (.untl B A)))
        (Formula.or (.untl B A) q_neg)
      apply is_separable_of_equiv h_distrib
      apply and_separable
      · -- S(a'^-U, q_pos v -U): Case 8
        exact case8_separable_gen' a_neg q_pos A B ha_neg_uf hqp_uf hA_uf hB_uf hA_sf hB_sf
      · -- S(a'^-U, U v q_neg): Case 6
        have h_comm : intEquiv (Formula.or (.untl B A) q_neg) (Formula.or q_neg (.untl B A)) := by
          intro M t; constructor
          · intro h; rcases int_truth_or_iff.mp h with hu | hq
            · exact int_truth_or_iff.mpr (Or.inr hu)
            · exact int_truth_or_iff.mpr (Or.inl hq)
          · intro h; rcases int_truth_or_iff.mp h with hq | hu
            · exact int_truth_or_iff.mpr (Or.inr hq)
            · exact int_truth_or_iff.mpr (Or.inl hu)
        have h_snce_comm : intEquiv
            (.snce (Formula.or (.untl B A) q_neg) (Formula.and a_neg (Formula.neg (.untl B A))))
            (.snce (Formula.or q_neg (.untl B A)) (Formula.and a_neg (Formula.neg (.untl B A)))) :=
          snce_congr (int_equiv_refl _) h_comm
        apply is_separable_of_equiv h_snce_comm
        exact case6_separable_gen' a_neg q_neg A B ha_neg_uf hqn_uf hA_uf hB_uf hA_sf hB_sf

/-- GHR94 Lemma 10.2.4 with U-type preservation:
    `.snce w` C where C, w have `snceDepthOfU = 0` and `hasSingleUType`
    is `isSeparableWithUType`. Same structure as `snce_single_U_depth_one_separable`
    but returns the stronger `isSeparableWithUType` predicate. -/
theorem snce_single_U_depth_one_sep_with_U_type (C w A B : Formula Atom)
    (hA_sf : isSFree A = true) (hB_sf : isSFree B = true)
    (hA_uf : isUFree A = true) (hB_uf : isUFree B = true)
    (hsingle_C : hasSingleUType C A B)
    (hsingle_F : hasSingleUType w A B)
    (hdC : snceDepthOfU C = 0) (hdF : snceDepthOfU w = 0)
    (hexp_C : hasNoAllpastAllfuture C = true)
    (hexp_F : hasNoAllpastAllfuture w = true) :
    isSeparableWithUType (.snce w C) A B := by
  -- Step 1: Event-split on U(A,B)
  have hsplit := since_event_split C (.untl B A) w
  apply is_separable_with_U_type_of_equiv hsplit
  apply or_separable_with_U_type
  -- Positive branch: S(C ^ U(A,B), w)
  · have h_simp_pos := single_U_and_conj_simplify C A B hsingle_C hexp_C hdC
    let a_pos := replaceUntl C A B (Formula.neg .bot)
    have ha_uf : isUFree a_pos = true :=
      replace_untl_U_free C A B (Formula.neg .bot) hsingle_C (by simp [isUFree])
    have h_equiv_pos : intEquiv (.snce w (Formula.and C (.untl B A)))
        (.snce w (Formula.and a_pos (.untl B A))) :=
      snce_congr h_simp_pos (int_equiv_refl w)
    apply is_separable_with_U_type_of_equiv h_equiv_pos
    by_cases hFuf : isUFree w = true
    · exact case1_sep_with_U_type_gen a_pos w A B ha_uf hFuf hA_uf hB_uf hA_sf hB_sf
    · push Not at hFuf; simp [Bool.not_eq_true] at hFuf
      have h_cnf := single_U_guard_cnf w A B hsingle_F hexp_F hdF
      let q_pos := replaceUntl w A B (Formula.neg .bot)
      let q_neg := replaceUntl w A B .bot
      have hqp_uf : isUFree q_pos = true :=
        replace_untl_U_free w A B (Formula.neg .bot) hsingle_F (by simp [isUFree])
      have hqn_uf : isUFree q_neg = true :=
        replace_untl_U_free w A B .bot hsingle_F (by simp [isUFree])
      have h_guard_equiv : intEquiv (.snce w (Formula.and a_pos (.untl B A)))
          (.snce (Formula.and (Formula.or q_pos (Formula.neg (.untl B A)))
                         (Formula.or (.untl B A) q_neg))
            (Formula.and a_pos (.untl B A))) :=
        snce_congr (int_equiv_refl _) h_cnf
      apply is_separable_with_U_type_of_equiv h_guard_equiv
      have h_distrib := snce_conj_guard_distribute
        (Formula.and a_pos (.untl B A))
        (Formula.or q_pos (Formula.neg (.untl B A)))
        (Formula.or (.untl B A) q_neg)
      apply is_separable_with_U_type_of_equiv h_distrib
      apply and_separable_with_U_type
      · exact case7_sep_with_U_type_Z_gen a_pos q_pos A B ha_uf hqp_uf hA_uf hB_uf hA_sf hB_sf
      · have h_comm : intEquiv (Formula.or (.untl B A) q_neg) (Formula.or q_neg (.untl B A)) := by
          intro M t; constructor
          · intro h; rcases int_truth_or_iff.mp h with hu | hq
            · exact int_truth_or_iff.mpr (Or.inr hu)
            · exact int_truth_or_iff.mpr (Or.inl hq)
          · intro h; rcases int_truth_or_iff.mp h with hq | hu
            · exact int_truth_or_iff.mpr (Or.inr hq)
            · exact int_truth_or_iff.mpr (Or.inl hu)
        have h_snce_comm : intEquiv
            (.snce (Formula.or (.untl B A) q_neg) (Formula.and a_pos (.untl B A)))
            (.snce (Formula.or q_neg (.untl B A)) (Formula.and a_pos (.untl B A))) :=
          snce_congr (int_equiv_refl _) h_comm
        apply is_separable_with_U_type_of_equiv h_snce_comm
        exact case5_sep_with_U_type_Z_gen a_pos q_neg A B ha_uf hqn_uf hA_uf hB_uf hA_sf hB_sf
  -- Negative branch: S(C ^ -U(A,B), w)
  · have h_simp_neg := single_U_and_conj_simplify_neg C A B hsingle_C hexp_C hdC
    let a_neg := replaceUntl C A B .bot
    have ha_neg_uf : isUFree a_neg = true :=
      replace_untl_U_free C A B .bot hsingle_C (by simp [isUFree])
    have h_equiv_neg : intEquiv (.snce w (Formula.and C (Formula.neg (.untl B A))))
        (.snce w (Formula.and a_neg (Formula.neg (.untl B A)))) :=
      snce_congr h_simp_neg (int_equiv_refl w)
    apply is_separable_with_U_type_of_equiv h_equiv_neg
    by_cases hFuf : isUFree w = true
    · exact case2_sep_with_U_type_gen a_neg w A B ha_neg_uf hFuf hA_uf hB_uf hA_sf hB_sf
    · push Not at hFuf; simp [Bool.not_eq_true] at hFuf
      have h_cnf := single_U_guard_cnf w A B hsingle_F hexp_F hdF
      let q_pos := replaceUntl w A B (Formula.neg .bot)
      let q_neg := replaceUntl w A B .bot
      have hqp_uf : isUFree q_pos = true :=
        replace_untl_U_free w A B (Formula.neg .bot) hsingle_F (by simp [isUFree])
      have hqn_uf : isUFree q_neg = true :=
        replace_untl_U_free w A B .bot hsingle_F (by simp [isUFree])
      have h_guard_equiv : intEquiv (.snce w (Formula.and a_neg (Formula.neg (.untl B A))))
          (.snce (Formula.and (Formula.or q_pos (Formula.neg (.untl B A)))
                         (Formula.or (.untl B A) q_neg))
            (Formula.and a_neg (Formula.neg (.untl B A)))) :=
        snce_congr (int_equiv_refl _) h_cnf
      apply is_separable_with_U_type_of_equiv h_guard_equiv
      have h_distrib := snce_conj_guard_distribute
        (Formula.and a_neg (Formula.neg (.untl B A)))
        (Formula.or q_pos (Formula.neg (.untl B A)))
        (Formula.or (.untl B A) q_neg)
      apply is_separable_with_U_type_of_equiv h_distrib
      apply and_separable_with_U_type
      · exact case8_sep_with_U_type_Z_gen a_neg q_pos A B ha_neg_uf hqp_uf hA_uf hB_uf hA_sf hB_sf
      · have h_comm : intEquiv (Formula.or (.untl B A) q_neg) (Formula.or q_neg (.untl B A)) := by
          intro M t; constructor
          · intro h; rcases int_truth_or_iff.mp h with hu | hq
            · exact int_truth_or_iff.mpr (Or.inr hu)
            · exact int_truth_or_iff.mpr (Or.inl hq)
          · intro h; rcases int_truth_or_iff.mp h with hq | hu
            · exact int_truth_or_iff.mpr (Or.inr hq)
            · exact int_truth_or_iff.mpr (Or.inl hu)
        have h_snce_comm : intEquiv
            (.snce (Formula.or (.untl B A) q_neg) (Formula.and a_neg (Formula.neg (.untl B A))))
            (.snce (Formula.or q_neg (.untl B A)) (Formula.and a_neg (Formula.neg (.untl B A)))) :=
          snce_congr (int_equiv_refl _) h_comm
        apply is_separable_with_U_type_of_equiv h_snce_comm
        exact case6_sep_with_U_type_Z_gen a_neg q_neg A B ha_neg_uf hqn_uf hA_uf hB_uf hA_sf hB_sf


end Cslib.Logic.Bimodal.Metalogic.Separation
