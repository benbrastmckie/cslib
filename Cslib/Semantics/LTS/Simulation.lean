import Cslib.Semantics.LTS.Basic

def Simulation (lts : LTS State Label) (r : Rel State State) : Prop :=
  ∀ s1 s2, r s1 s2 → ∀ μ s1', lts.tr s1 μ s1' → ∃ s2', lts.tr s2 μ s2' ∧ r s1' s2'
