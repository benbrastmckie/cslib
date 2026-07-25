import Cslib.Logics.Modal.Metalogic.Constructive.CS5Completeness

namespace Cslib.Logic.Modal
open Cslib.Logic

universe u
variable {Atom : Type u}

/-! # Round-2 Probe: the named obligation is REFUTABLE as literally stated

`CS5PairSeedDisjunctionProperty H A` carries **no hypothesis** relating `A` to `H`.  Round 1
established `hOpen ↔ hR` where `hR : cs5PairTauR A ∉ cl(cs5PairSeed H)`.  But the right component
of `cs5PairSeed H` is `cs5PairTauR '' (cl_{CS5} (boxInv H))`, and *every `CS5` theorem* lies in
`cl_{CS5} (boxInv H)` for **every** `H` (witness list `[]`).  So for any `CS5`-provable `A`, the
seed literally contains `τ_R A`, and both `hR` and `hOpen` fail — uniformly in `H`.

Concrete instance: `A := ⊥ → ⊥` (the `efq ⊥` axiom instance) and `H := ∅`.
-/

/-- `⊤ := ⊥ → ⊥` is a `CS5` axiom instance, hence lies in `cl_{CS5} S` for **every** `S`. -/
theorem probe_top_mem_closure (S : Set (Proposition Atom)) :
    (Proposition.bot.imp Proposition.bot) ∈ modalDeductiveClosure (@CS5ModalAxiom Atom) S := by
  refine ⟨[], ?_, ?_⟩
  · intro x hx; exact nomatch hx
  · exact ⟨.ax [] _ (CS5ModalAxiom.efq Proposition.bot)⟩

/-- Consequently `τ_R ⊤` is *already in the seed itself*, for every `H`. -/
theorem probe_tauR_top_mem_seed (H : Set (Proposition Atom)) :
    cs5PairTauR (Proposition.bot.imp Proposition.bot) ∈ (@cs5PairSeed Atom) H :=
  Set.mem_union_right _ (Set.mem_image_of_mem _ (probe_top_mem_closure _))

/-- **Refutation of the right exclusion.** `hR` fails at `A := ⊤`, for every `H`. -/
theorem probe_refute_hR (H : Set (Proposition Atom)) :
    cs5PairTauR (Proposition.bot.imp Proposition.bot) ∈
      modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H) :=
  modal_subset_deductive_closure _ _ (probe_tauR_top_mem_seed H)

/-- **Refutation of the named open obligation.** `CS5PairSeedDisjunctionProperty H ⊤` is FALSE
for every `H` — in particular for `H = ∅`.  Obtained from `probe_refute_hR` by `orI2` through
deductive closure, exactly the `hR → hOpen` direction round 1 machine-checked. -/
theorem probe_refute_disjunctionProperty (H : Set (Proposition Atom)) :
    ¬ CS5PairSeedDisjunctionProperty H (Proposition.bot.imp Proposition.bot) := by
  intro hOpen
  apply hOpen
  set A : Proposition Atom := Proposition.bot.imp Proposition.bot with hA
  have hR := probe_refute_hR (Atom := Atom) H
  have hd : (modalDerivationSystem (@CS5PairAxiom Atom)).Deriv [cs5PairTauR A]
      ((cs5PairTauL (Proposition.box A)).or (cs5PairTauR A)) :=
    mp_deriv (weakening_deriv (cs5Pair_hOrI2 (cs5PairTauL (Proposition.box A)) (cs5PairTauR A))
        (by simp)) (assumption_deriv (List.mem_singleton_self _))
  exact modalDeductiveClosure_closed cs5Pair_hImplyK cs5Pair_hImplyS [cs5PairTauR A]
    ((cs5PairTauL (Proposition.box A)).or (cs5PairTauR A))
    (fun z hz => by rw [List.mem_singleton] at hz; rw [hz]; exact hR) hd

/-- A second, `H`-specific refutation that does not rely on `A` being a theorem: whenever
`□A ∈ H`, the seed's right component already contains `τ_R A`, since `A ∈ boxInv H`. -/
theorem probe_refute_hR_of_boxMem {H : Set (Proposition Atom)} {A : Proposition Atom}
    (h : Proposition.box A ∈ H) :
    cs5PairTauR A ∈ modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H) :=
  modal_subset_deductive_closure _ _
    (Set.mem_union_right _
      (Set.mem_image_of_mem _ (modal_subset_deductive_closure _ _ h)))

end Cslib.Logic.Modal
