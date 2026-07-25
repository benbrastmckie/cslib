import Cslib.Logics.Modal.Metalogic.Constructive.CS5Completeness

namespace Cslib.Logic.Modal
open Cslib.Logic

universe u
variable {Atom : Type u}

/-- Probe 1: the left-tagged box is *syntactically* the box of the left tag. -/
theorem probe_tauL_box (A : Proposition Atom) :
    cs5PairTauL (Proposition.box A) = Proposition.box (cs5PairTauL A) := rfl

/-- Probe 2: `⊢ (τ_L (□A) ⊔ τ_R A) → τ_R A`, by `orE` against `cross1` and identity. -/
theorem probe_or_imp_right (A : Proposition Atom) :
    Deriv (@CS5PairAxiom Atom) []
      (((cs5PairTauL (Proposition.box A)).or (cs5PairTauR A)).imp (cs5PairTauR A)) := by
  have hcross : Deriv (@CS5PairAxiom Atom) []
      ((cs5PairTauL (Proposition.box A)).imp (cs5PairTauR A)) :=
    ⟨.ax [] _ (CS5PairAxiom.cross1 A)⟩
  have hid : Deriv (@CS5PairAxiom Atom) [] ((cs5PairTauR A).imp (cs5PairTauR A)) :=
    Metalogic.empty_imp_id (modalDerivationSystem CS5PairAxiom) cs5Pair_hCut _
  exact mp_deriv (mp_deriv (cs5Pair_hOrE _ _ _) hcross) hid

/-- Probe 3: the named open obligation follows from the right-hand exclusion alone. -/
theorem probe_dp_of_hR {H : Set (Proposition Atom)} {A : Proposition Atom}
    (hR : cs5PairTauR A ∉ modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H)) :
    CS5PairSeedDisjunctionProperty H A := by
  intro hor
  apply hR
  refine modalDeductiveClosure_closed cs5Pair_hImplyK cs5Pair_hImplyS
    [(cs5PairTauL (Proposition.box A)).or (cs5PairTauR A)] (cs5PairTauR A)
    (fun z hz => by rw [List.mem_singleton] at hz; rw [hz]; exact hor) ?_
  exact mp_deriv (weakening_deriv (probe_or_imp_right A) (by simp))
    (assumption_deriv (List.mem_singleton_self _))

/-- Probe 4: conversely, the obligation implies the right-hand exclusion (via `orI2`). -/
theorem probe_hR_of_dp {H : Set (Proposition Atom)} {A : Proposition Atom}
    (hOpen : CS5PairSeedDisjunctionProperty H A) :
    cs5PairTauR A ∉ modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H) := by
  intro hR
  apply hOpen
  refine modalDeductiveClosure_closed cs5Pair_hImplyK cs5Pair_hImplyS
    [cs5PairTauR A] ((cs5PairTauL (Proposition.box A)).or (cs5PairTauR A))
    (fun z hz => by rw [List.mem_singleton] at hz; rw [hz]; exact hR) ?_
  exact mp_deriv (weakening_deriv (cs5Pair_hOrI2 (cs5PairTauL (Proposition.box A))
    (cs5PairTauR A)) (by simp)) (assumption_deriv (List.mem_singleton_self _))

/-- Probe 5: the *left* exclusion `hL` also follows from `hR`, again via `cross1`. -/
theorem probe_hL_of_hR {H : Set (Proposition Atom)} {A : Proposition Atom}
    (hR : cs5PairTauR A ∉ modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H)) :
    cs5PairTauL (Proposition.box A) ∉
      modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H) := by
  intro hL
  apply hR
  refine modalDeductiveClosure_closed cs5Pair_hImplyK cs5Pair_hImplyS
    [cs5PairTauL (Proposition.box A)] (cs5PairTauR A)
    (fun z hz => by rw [List.mem_singleton] at hz; rw [hz]; exact hL) ?_
  exact mp_deriv (weakening_deriv (⟨.ax [] _ (CS5PairAxiom.cross1 A)⟩ :
      Deriv (@CS5PairAxiom Atom) [] ((cs5PairTauL (Proposition.box A)).imp (cs5PairTauR A)))
    (by simp)) (assumption_deriv (List.mem_singleton_self _))

/-- Probe 6 (payoff): `DerivExcludes` at the two-sided seed follows from `hR` **alone**. -/
theorem probe_derivExcludes_of_hR {H : Set (Proposition Atom)} {A : Proposition Atom}
    (hR : cs5PairTauR A ∉ modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H)) :
    Metalogic.DerivExcludes (modalDerivationSystem (@CS5PairAxiom Atom))
      {cs5PairTauL (Proposition.box A), cs5PairTauR A}
      (modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H)) :=
  cs5Pair_derivExcludes_of_disjunctionProperty (probe_hL_of_hR hR) hR (probe_dp_of_hR hR)

end Cslib.Logic.Modal
