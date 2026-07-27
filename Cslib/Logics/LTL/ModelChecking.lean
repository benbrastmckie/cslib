/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Foundations.Semantics.LTS.NAProd
public import Cslib.Logics.LTL.Semantics.OmegaExecutionSatisfies
public import Cslib.Logics.LTL.Semantics.OmegaRegular
public import Cslib.Computability.Automata.NA.Emptiness

/-! # LTL Model Checking Reduction

This module proves the LTL model checking reduction theorem: a finite-state LTS satisfies an LTL
formula `phi` from all initial states if and only if the product of the LTS with the NBA for
`¬phi` has no reachable accepting cycle (equivalently, an empty language).

The key chain is:
1. `SatisfiesExec labeling ss phi` is equivalent to membership in `phi.omegaLanguage` (bridge)
2. `naProd_language_nonempty_iff_exec` connects product language non-emptiness to LTS executions
3. `gnba_language_eq` connects the GNBA NBA language to the LTL omega-language

## Main theorems

- `LTL.satisfiesExec_iff_satisfies_setWord` — congruence: `SatisfiesExec` with `labeling` on `ss`
  is equivalent to `Satisfies (fun p s => p ∈ s)` on the `Set Atom`-valued sequence
- `LTL.ltlModelChecking` — LTL model checking reduction: all executions satisfy `phi` iff the
  product with the GNBA for `¬phi` has no reachable accepting cycle

## References

* [C. Baier, J.-P. Katoen, *Principles of Model Checking*][BaierKatoen2008], Chapter 5
-/

@[expose] public section

namespace Cslib.Logic.LTL

open Set Filter ωSequence Automata Automata.NA LTS

variable {Atom State Label : Type*}

/-- Congruence lemma: `SatisfiesExec labeling ss phi` is equivalent to
`Satisfies (fun p s => p ∈ s) (ss.map (fun s => {p | labeling s p})) phi`.

The proof is by structural induction on `phi`. At each step, the key facts are:
- `head (ss.map f) = f ss.head`
- `tail (ss.map f) = ss.tail.map f`
- `drop n (ss.map f) = (ss.drop n).map f` -/
theorem satisfiesExec_iff_satisfies_setWord (labeling : State → (Atom → Prop))
    (ss : ωSequence State) (phi : Formula Atom) :
    SatisfiesExec labeling ss phi ↔
      Satisfies (fun p s => p ∈ s) (ss.map (fun s => {p | labeling s p})) phi := by
  induction phi generalizing ss with
  | atom p =>
    simp [SatisfiesExec, Satisfies]
  | bot =>
    simp [SatisfiesExec, Satisfies]
  | imp phi1 phi2 ih1 ih2 =>
    simp only [SatisfiesExec, Satisfies]
    constructor
    · intro h h1; exact (ih2 ss).mp (h ((ih1 ss).mpr h1))
    · intro h h1; exact (ih2 ss).mpr (h ((ih1 ss).mp h1))
  | next phi1 ih =>
    simp only [SatisfiesExec, Satisfies, tail_map]
    exact ih ss.tail
  | untl phi1 phi2 ih1 ih2 =>
    simp only [SatisfiesExec, Satisfies, drop_map]
    constructor
    · rintro ⟨j, hj, hguard⟩
      exact ⟨j, (ih2 (ss.drop j)).mp hj, fun k hk => (ih1 (ss.drop k)).mp (hguard k hk)⟩
    · rintro ⟨j, hj, hguard⟩
      exact ⟨j, (ih2 (ss.drop j)).mpr hj, fun k hk => (ih1 (ss.drop k)).mpr (hguard k hk)⟩

/-- Bridge lemma: `SatisfiesExec labeling ss phi` is equivalent to membership of the induced
`Set Atom`-valued sequence in `phi.omegaLanguage`. -/
theorem satisfiesExec_iff_mem_omegaLanguage {labeling : State → (Atom → Prop)}
    {ss : ωSequence State} {phi : Formula Atom} :
    SatisfiesExec labeling ss phi ↔
      ss.map (fun s => {p | labeling s p}) ∈ phi.omegaLanguage := by
  rw [mem_omegaLanguage]
  exact satisfiesExec_iff_satisfies_setWord labeling ss phi

/-- LTL model checking reduction theorem.

For a finite-state LTS with labeling `labeling : State → (Atom → Prop)` and initial states
`init`, the following are equivalent:
1. Every omega-execution from every initial state satisfies `phi`
2. The product of the LTS with the GNBA for `¬phi` has no reachable accepting cycle

This is the fundamental model checking algorithm reduction (Baier-Katoen Theorem 5.47).

Hypotheses:
- `[Finite State]` — required for the NBA emptiness check (finite product state space)
- `[Finite Atom]` — required for the GNBA tableau construction (finite closure) -/
theorem ltlModelChecking [Finite State] [Finite Atom]
    (lts : LTS State Label) (labeling : State → (Atom → Prop)) (init : Set State)
    (phi : Formula Atom) :
    (∀ s₀ ∈ init, ∀ (ss : ωSequence State) (mus : ωSequence Label),
      lts.OmegaExecution ss mus → ss 0 = s₀ → SatisfiesExec labeling ss phi) ↔
    ¬(naProd lts (fun s => {p | labeling s p}) init
        (Formula.gnbaNBA (Formula.neg phi))).HasReachableAcceptingCycle := by
  constructor
  · -- Forward: all executions satisfy phi → no reachable accepting cycle
    intro hall hrac
    -- hrac → product language is non-empty
    have hne : (ωAcceptor.language
        (naProd lts (fun s => {p | labeling s p}) init
          (Formula.gnbaNBA (Formula.neg phi)))).toSet.Nonempty :=
      Buchi.nonempty_of_hasReachableAcceptingCycle _ hrac
    -- Unpack: get product run witnessing the violation
    rw [naProd_language_nonempty_iff_exec] at hne
    obtain ⟨s₀, hs₀, ss_lts, mus, ss_nba, h_lts, h_ss0, h_start, h_tr, h_acc⟩ := hne
    -- The LTS execution from s₀ ∈ init satisfies phi (by assumption)
    have h_sat : SatisfiesExec labeling ss_lts phi :=
      hall s₀ hs₀ ss_lts mus h_lts h_ss0
    -- The labeling sequence violates phi (is in language of NBA for ¬phi)
    -- First, the NBA run is valid
    have h_nba_run : (Formula.gnbaNBA (Formula.neg phi)).Run
        (ss_lts.map (fun s => {p | labeling s p})) ss_nba :=
      ⟨h_start, h_tr⟩
    -- So the labeling sequence is in language(gnbaNBA (neg phi)) = (neg phi).gnbaOmegaLanguage
    have h_mem : ss_lts.map (fun s => {p | labeling s p}) ∈
        (ωAcceptor.language (Formula.gnbaNBA (Formula.neg phi))).toSet := by
      simp only [ωAcceptor.language, Set.mem_setOf_eq]
      exact ⟨ss_nba, h_nba_run, h_acc⟩
    -- By gnba_language_eq, the language = gnbaOmegaLanguage = omegaLanguage definitionally
    rw [Formula.gnba_language_eq] at h_mem
    -- h_mem : ... ∈ (neg phi).gnbaOmegaLanguage
    -- gnbaOmegaLanguage is definitionally omegaLanguage
    have h_negsat : SatisfiesExec labeling ss_lts (Formula.neg phi) :=
      satisfiesExec_iff_mem_omegaLanguage.mpr h_mem
    -- phi and ¬phi both satisfied — contradiction
    simp only [SatisfiesExec] at h_negsat
    exact h_negsat h_sat
  · -- Backward: no accepting cycle → all executions satisfy phi
    intro hno_cycle s₀ hs₀ ss mus h_exec h_ss0
    by_contra h_not_sat
    -- h_not_sat : ¬ SatisfiesExec labeling ss phi
    -- The labeling sequence violates phi, so satisfies neg phi
    have h_neg : SatisfiesExec labeling ss (Formula.neg phi) := by
      simp only [SatisfiesExec]; exact h_not_sat
    -- The labeling sequence is in (neg phi).omegaLanguage = language(gnbaNBA(neg phi))
    have h_neg_lang : ss.map (fun s => {p | labeling s p}) ∈
        (ωAcceptor.language (Formula.gnbaNBA (Formula.neg phi))).toSet := by
      rw [Formula.gnba_language_eq]
      exact satisfiesExec_iff_mem_omegaLanguage.mp h_neg
    rw [ωAcceptor.language] at h_neg_lang
    simp only [Set.mem_setOf_eq] at h_neg_lang
    obtain ⟨ss_nba, h_nba_run, h_nba_acc⟩ := h_neg_lang
    -- Build: there is a violating product run
    have h_prod_ne : (ωAcceptor.language (naProd lts (fun s => {p | labeling s p}) init
        (Formula.gnbaNBA (Formula.neg phi)))).toSet.Nonempty := by
      rw [naProd_language_nonempty_iff_exec]
      exact ⟨s₀, hs₀, ss, mus, ss_nba, h_exec, h_ss0,
        h_nba_run.start, h_nba_run.trans, h_nba_acc⟩
    -- Language non-empty → has reachable accepting cycle
    exact hno_cycle (Buchi.hasReachableAcceptingCycle_of_nonempty _ h_prod_ne)

end Cslib.Logic.LTL

end
