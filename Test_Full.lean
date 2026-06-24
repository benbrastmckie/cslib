import Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion
import Cslib.Logics.Propositional.Semantics.Kripke

namespace Cslib.Logic.PL
open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]
variable {World : Type*} [Preorder World]

-- Helper: proposition BEq to Eq (reusing the proof from Minimal/Soundness.lean)
private lemma proposition_beq_eq2 :
    ∀ (a b : Proposition Atom), (a == b) = true → a = b := by
  intro a b h
  induction a generalizing b with
  | bot =>
    cases b <;> first
      | rfl
      | (change false = true at h; exact absurd h Bool.false_ne_true)
  | atom x => cases b with
    | atom y =>
      change (x == y) = true at h; exact congrArg _ (eq_of_beq h)
    | _ => change false = true at h; exact absurd h Bool.false_ne_true
  | imp φ ψ ih_φ ih_ψ => cases b with
    | imp φ' ψ' =>
      simp only [BEq.beq, instBEqProposition, Bool.and_eq_true] at h
      exact congrArg₂ (.imp) (ih_φ φ' h.1) (ih_ψ ψ' h.2)
    | _ => change false = true at h; exact absurd h Bool.false_ne_true
  | and φ ψ ih_φ ih_ψ => cases b with
    | and φ' ψ' =>
      simp only [BEq.beq, instBEqProposition, Bool.and_eq_true] at h
      exact congrArg₂ (.and) (ih_φ φ' h.1) (ih_ψ ψ' h.2)
    | _ => change false = true at h; exact absurd h Bool.false_ne_true
  | or φ ψ ih_φ ih_ψ => cases b with
    | or φ' ψ' =>
      simp only [BEq.beq, instBEqProposition, Bool.and_eq_true] at h
      exact congrArg₂ (.or) (ih_φ φ' h.1) (ih_ψ ψ' h.2)
    | _ => change false = true at h; exact absurd h Bool.false_ne_true

-- Helper: elements of intTImpRule
private lemma mem_intTImpRule_form2 (φ ψ : Proposition Atom) (w : Nat) (b : IBranch Atom)
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

-- Helper: applyAllTImpRules preserves branch satisfaction under monotone worldOf
private lemma applyAllTImpRules_preserves_sat2
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
    obtain ⟨w', sf_eq, hw'_ge, h_phi_at_w'⟩ := mem_intTImpRule_form2 φ ψ l b sf hmem_new
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
      have hφeq : sf_phi.formula = φ := proposition_beq_eq2 _ _ hform
      have hlbl : sf_phi.label = w' := by simp [beq_iff_eq] at hlabel; exact hlabel
      have hsigneq : sf_phi.sign = .pos := by simp [beq_iff_eq] at hsign; exact hsign
      have hforces := (hsat sf_phi hmem_phi).1 hsigneq
      rwa [hφeq, hlbl] at hforces
    exact h_orig (worldOf w') (h_mono _ _ hw'_ge) h_phi

-- Helper: applyPersistenceFixpoint preserves satisfaction
private lemma applyPersistenceFixpoint_preserves_sat2
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
      exact applyAllTImpRules_preserves_sat2 val botForces worldOf h_mono b hsat

-- Now the main loop invariant
-- First, we need intBranchSatisfied to be the same as the ∀ sf ∈ b predicate
-- Let's just use the sat predicate directly

end Cslib.Logic.PL
