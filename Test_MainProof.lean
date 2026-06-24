import Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion
import Cslib.Logics.Propositional.Semantics.Kripke

namespace Cslib.Logic.PL
open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]
variable {World : Type*} [Preorder World]

-- Helper: proposition BEq to Eq
private lemma prop_beq_eq6 :
    ∀ (a b : Proposition Atom), (a == b) = true → a = b := by
  intro a b h
  induction a generalizing b with
  | bot =>
    cases b <;> first
      | rfl
      | (simp [BEq.beq, instBEqProposition.beq] at h)
  | atom x => cases b with
    | atom y =>
      simp only [BEq.beq, instBEqProposition.beq] at h
      exact congrArg _ (eq_of_beq h)
    | _ => simp [BEq.beq, instBEqProposition.beq] at h
  | imp φ ψ ih_φ ih_ψ => cases b with
    | imp φ' ψ' =>
      change (instBEqProposition.beq (φ.imp ψ) (φ'.imp ψ')) = true at h
      rw [show instBEqProposition.beq (φ.imp ψ) (φ'.imp ψ') =
          (instBEqProposition.beq φ φ' && instBEqProposition.beq ψ ψ') from rfl] at h
      simp only [Bool.and_eq_true] at h
      exact congrArg₂ Proposition.imp (ih_φ φ' h.1) (ih_ψ ψ' h.2)
    | _ => simp [BEq.beq, instBEqProposition.beq] at h
  | and φ ψ ih_φ ih_ψ => cases b with
    | and φ' ψ' =>
      change (instBEqProposition.beq (φ.and ψ) (φ'.and ψ')) = true at h
      rw [show instBEqProposition.beq (φ.and ψ) (φ'.and ψ') =
          (instBEqProposition.beq φ φ' && instBEqProposition.beq ψ ψ') from rfl] at h
      simp only [Bool.and_eq_true] at h
      exact congrArg₂ Proposition.and (ih_φ φ' h.1) (ih_ψ ψ' h.2)
    | _ => simp [BEq.beq, instBEqProposition.beq] at h
  | or φ ψ ih_φ ih_ψ => cases b with
    | or φ' ψ' =>
      change (instBEqProposition.beq (φ.or ψ) (φ'.or ψ')) = true at h
      rw [show instBEqProposition.beq (φ.or ψ) (φ'.or ψ') =
          (instBEqProposition.beq φ φ' && instBEqProposition.beq ψ ψ') from rfl] at h
      simp only [Bool.and_eq_true] at h
      exact congrArg₂ Proposition.or (ih_φ φ' h.1) (ih_ψ ψ' h.2)
    | _ => simp [BEq.beq, instBEqProposition.beq] at h

-- Helper: elements of intTImpRule
private lemma mem_intTImpRule_form6 (φ ψ : Proposition Atom) (w : Nat) (b : IBranch Atom)
    (sf : ISF Atom) (h : sf ∈ intTImpRule φ ψ w b) :
    ∃ w', sf = ⟨.pos, ψ, w'⟩ ∧ w ≤ w' ∧
      (b.any fun sf_b => sf_b.sign == .pos && sf_b.formula == φ && sf_b.label == w') = true := by
  simp only [intTImpRule, List.mem_filterMap] at h
  obtain ⟨w', hmem_w', hcond⟩ := h
  simp only [List.mem_eraseDups, List.mem_filter, List.mem_map] at hmem_w'
  obtain ⟨⟨sf', _, hlab_eq⟩, hw_le⟩ := hmem_w'
  subst hlab_eq
  by_cases h1 : (b.any fun sf_b => sf_b.sign == .pos && sf_b.formula == φ && sf_b.label == sf'.label) = true
  · rw [if_pos h1] at hcond
    by_cases h2 : (b.any fun sf_b => sf_b.sign == .pos && sf_b.formula == ψ && sf_b.label == sf'.label) = true
    · rw [if_pos h2] at hcond; simp at hcond
    · rw [if_neg h2] at hcond
      simp only [Option.some.injEq] at hcond
      exact ⟨sf'.label, hcond.symm, by simpa using hw_le, h1⟩
  · rw [if_neg h1] at hcond; simp at hcond

-- Helper: applyAllTImpRules preserves satisfaction under monotone worldOf
private lemma applyAllTImpRules_preserves_sat6
    (val : World → Atom → Prop) (botForces : World → Prop)
    (worldOf : Nat → World)
    (h_mono : ∀ n m : Nat, n ≤ m → worldOf n ≤ worldOf m)
    (b : IBranch Atom)
    (hsat : ∀ sf ∈ b,
        (sf.sign = .pos → IForces val botForces (worldOf sf.label) sf.formula) ∧
        (sf.sign = .neg → ¬ IForces val botForces (worldOf sf.label) sf.formula)) :
    ∀ sf ∈ applyAllTImpRules b,
        (sf.sign = .pos → IForces val botForces (worldOf sf.label) sf.formula) ∧
        (sf.sign = .neg → ¬ IForces val botForces (worldOf sf.label) sf.formula) := by
  intro sf hmem
  simp only [applyAllTImpRules, List.mem_append, List.mem_flatten, List.mem_filterMap] at hmem
  rcases hmem with hmem | ⟨newForms, ⟨sf_orig, hsf_orig_mem, hsf_orig_match⟩, hmem_new⟩
  · exact hsat sf hmem
  · rcases sf_orig with ⟨(_ | _), (_ | _ | _ | _ | _ | _), l⟩ <;>
      simp only [SignedFormula.sign, SignedFormula.formula, SignedFormula.label] at hsf_orig_match hsf_orig_mem <;>
      (try simp at hsf_orig_match)
    rename_i φ ψ
    obtain ⟨_, hsf_orig_eq⟩ := hsf_orig_match
    subst hsf_orig_eq
    obtain ⟨w', sf_eq, hw'_ge, h_phi_at_w'⟩ := mem_intTImpRule_form6 φ ψ l b sf hmem_new
    subst sf_eq
    simp only [SignedFormula.sign, SignedFormula.formula, SignedFormula.label]
    refine ⟨fun _ => ?_, fun h => absurd h Sign.noConfusion⟩
    have h_orig := (hsat ⟨.pos, .imp φ ψ, l⟩ hsf_orig_mem).1 rfl
    rw [IForces_imp] at h_orig
    have h_phi : IForces val botForces (worldOf w') φ := by
      rw [List.any_eq_true] at h_phi_at_w'
      obtain ⟨sf_phi, hmem_phi, hcond_phi⟩ := h_phi_at_w'
      simp only [Bool.and_eq_true] at hcond_phi
      obtain ⟨⟨hsign, hform⟩, hlabel⟩ := hcond_phi
      have hφeq : sf_phi.formula = φ := prop_beq_eq6 _ _ hform
      have hlbl : sf_phi.label = w' := by simp [beq_iff_eq] at hlabel; exact hlabel
      have hsigneq : sf_phi.sign = .pos := by simp [beq_iff_eq] at hsign; exact hsign
      have hforces := (hsat sf_phi hmem_phi).1 hsigneq
      rwa [hφeq, hlbl] at hforces
    exact h_orig (worldOf w') (h_mono _ _ hw'_ge) h_phi

-- Helper: applyPersistenceFixpoint preserves satisfaction
private lemma applyPersistenceFixpoint_preserves_sat6
    (val : World → Atom → Prop) (botForces : World → Prop)
    (worldOf : Nat → World)
    (h_mono : ∀ n m : Nat, n ≤ m → worldOf n ≤ worldOf m)
    (fuel : Nat) (b : IBranch Atom)
    (hsat : ∀ sf ∈ b,
        (sf.sign = .pos → IForces val botForces (worldOf sf.label) sf.formula) ∧
        (sf.sign = .neg → ¬ IForces val botForces (worldOf sf.label) sf.formula)) :
    ∀ sf ∈ applyPersistenceFixpoint b fuel,
        (sf.sign = .pos → IForces val botForces (worldOf sf.label) sf.formula) ∧
        (sf.sign = .neg → ¬ IForces val botForces (worldOf sf.label) sf.formula) := by
  induction fuel generalizing b with
  | zero => simpa [applyPersistenceFixpoint]
  | succ n ih =>
    simp only [applyPersistenceFixpoint]
    by_cases heq : (applyAllTImpRules b).length == b.length
    · simp [heq]; exact hsat
    · simp only [heq, ite_false]
      apply ih
      exact applyAllTImpRules_preserves_sat6 val botForces worldOf h_mono b hsat

-- Helper: intStepBranch preserves sat (like classicalStepBranch)
-- Returns ∃ worldOf' monotone and sat for the new branches
private lemma intStepBranch_preserves_sat6
    (val : World → Atom → Prop) (botForces : World → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    (b : IBranch Atom)
    (e : List (ISF Atom))
    (nw : Nat)
    (newForms : List (ISF Atom))
    (nw' : Nat)
    (newExp : List (ISF Atom))
    (hstep : intStepBranch b e nw = some (.linearResult newForms nw', newExp))
    (worldOf : Nat → World)
    (h_mono : ∀ n m : Nat, n ≤ m → worldOf n ≤ worldOf m)
    (hsat : intBranchSatisfied val botForces worldOf b) :
    ∃ worldOf' : Nat → World,
      (∀ n m : Nat, n ≤ m → worldOf' n ≤ worldOf' m) ∧
      intBranchSatisfied val botForces worldOf' (Branch.extendMany b newForms) := by
  simp only [intStepBranch] at hstep
  obtain ⟨sf, hsfmem, hsf_cond⟩ := List.exists_of_findSome?_eq_some hstep
  simp only [List.any_eq_false_iff_forall, not_imp_not] at hsf_cond
  split at hsf_cond with h_expanded
  · exact absurd hsf_cond (by simp)
  · cases hca : intApplyRuleFull sf nw b with
    | notApplicable => simp [hca] at hsf_cond
    | linearResult newForms' nw'' =>
      simp only [hca, Option.some.injEq, Prod.mk.injEq] at hsf_cond
      obtain ⟨hnf, _, hnw', _⟩ := hsf_cond
      subst hnf hnw'
      -- Apply intRule_preserves_sat to get worldOf'
      have hnw_fresh : ∀ sf' ∈ b, sf'.label ≠ nw := by
        intro sf' hmem' heq
        -- sf is in b and not expanded; if nw = sf'.label, then something exists at nw
        -- Actually freshness comes from the nextWorld invariant; let's use sorry for now
        -- TODO: prove freshness from the invariant
        sorry
      have hpres := intRule_preserves_sat val botForces v_uc bf_uc worldOf b sf hsfmem hsat nw hnw_fresh
      rw [hca] at hpres
      obtain ⟨worldOf', h_agree, h_sat'⟩ := hpres
      -- Need to show worldOf' is monotone
      -- worldOf' = Function.update worldOf nw w' where worldOf(sf.label) ≤ w'
      -- For labels in new branch: old labels ∪ {nw}
      -- For old labels l ≠ nw: worldOf' l = worldOf l
      -- For nw: worldOf' nw = w'
      -- Monotonicity: for n ≤ m with n, m ∈ branch labels, need worldOf' n ≤ worldOf' m
      -- This requires additional work... use sorry for now
      exact ⟨worldOf', sorry, h_sat'⟩
    | branchingResult _ _ =>
      simp only [hca] at hsf_cond

#check @intStepBranch_preserves_sat6

end Cslib.Logic.PL
