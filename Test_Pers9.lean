import Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion
import Cslib.Logics.Propositional.Semantics.Kripke

namespace Cslib.Logic.PL
open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

lemma mem_intTImpRule_form (φ ψ : Proposition Atom) (w : Nat) (b : IBranch Atom)
    (sf : ISF Atom) (h : sf ∈ intTImpRule φ ψ w b) :
    ∃ w', sf = ⟨.pos, ψ, w'⟩ ∧ w ≤ w' ∧
      (b.any fun sf_b => sf_b.sign == .pos && sf_b.formula == φ && sf_b.label == w') = true := by
  simp only [intTImpRule, List.mem_filterMap] at h
  obtain ⟨w', hmem_w', hcond⟩ := h
  simp only [List.mem_eraseDups, List.mem_filter, List.mem_map] at hmem_w'
  obtain ⟨⟨sf', hmem_sf', hlab_eq⟩, hw_le⟩ := hmem_w'
  subst hlab_eq
  -- Check the case structure manually
  by_cases h1 : (b.any fun sf_b => sf_b.sign == .pos && sf_b.formula == φ && sf_b.label == sf'.label) = true
  · rw [if_pos h1] at hcond
    by_cases h2 : (b.any fun sf_b => sf_b.sign == .pos && sf_b.formula == ψ && sf_b.label == sf'.label) = true
    · rw [if_pos h2] at hcond; simp at hcond
    · rw [if_neg h2] at hcond
      simp only [Option.some.injEq] at hcond
      exact ⟨sf'.label, hcond.symm, by simpa using hw_le, h1⟩
  · rw [if_neg h1] at hcond; simp at hcond

end Cslib.Logic.PL
