import Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion
import Cslib.Logics.Propositional.Semantics.Kripke

namespace Cslib.Logic.PL
open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

-- What do elements of intTImpRule look like?
lemma mem_intTImpRule_form (φ ψ : Proposition Atom) (w : Nat) (b : IBranch Atom)
    (sf : ISF Atom) (h : sf ∈ intTImpRule φ ψ w b) :
    ∃ w', sf = ⟨.pos, ψ, w'⟩ ∧ w ≤ w' ∧
      (b.any fun sf_b => sf_b.sign == .pos && sf_b.formula == φ && sf_b.label == w') = true := by
  simp only [intTImpRule, List.mem_filterMap] at h
  obtain ⟨w', hmem_w', hcond⟩ := h
  -- check the condition
  revert hcond
  simp only [List.mem_filter]
  intro hmem_w'
  sorry

end Cslib.Logic.PL
