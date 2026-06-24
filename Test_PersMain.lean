import Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion
import Cslib.Logics.Propositional.Semantics.Kripke

namespace Cslib.Logic.PL
open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

-- Check how to extract equality from beq for Proposition
-- The key issue: we have (sf_phi.formula == φ) = true
-- where instBEqProposition uses decidableEq
-- Let's just see what's available

#check @instBEqProposition

-- Try using the fact that instBEqProposition uses decidable equality
example {Atom : Type*} [DecidableEq Atom] [Hashable Atom] (a b : Proposition Atom) 
    (h : (a == b) = true) : a = b := by
  -- instBEqProposition is derived via DecidableEq
  change instBEqProposition.beq a b = true at h
  -- The beq should unfold via decidable
  simp only [BEq.beq] at h
  -- h should now be about the decidable condition
  split at h with h_eq
  · exact h_eq
  · simp at h

end Cslib.Logic.PL
