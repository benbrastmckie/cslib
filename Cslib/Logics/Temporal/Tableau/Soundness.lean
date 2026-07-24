/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Temporal.Tableau.Saturation
public import Cslib.Logics.Temporal.Semantics.Validity

/-! # Temporal Tableau Soundness

This module proves the soundness of the temporal tableau for the classically
closed case and documents the remaining proof obligations.

## Main Results (Proved)

- `branchSat`: Satisfiability of a temporal branch via a temporal model.
- `classicallyClosed_unsat`: A classically closed temporal branch is unsatisfiable.

## Blocked Obligations

The following results are required for the full soundness theorem but cannot
currently be proved without additional theory:

1. `temporalClosed_unsat` (eventuality-defect case): A branch closed by
   `findEventualityDefect` is unsatisfiable. This requires showing that
   time-subset blocking with unfulfilled eventualities implies unsatisfiability
   for **all** nontrivial linear orders. The argument requires either:
   - The Finite Model Property (FMP) for temporal logic over linear orders, or
   - A constructive loop-detection argument showing that the blocked branch
     cannot be satisfied in any infinite model either.

2. `temporalStepBranch_preserves_sat`: Each call to `temporalStepBranch`
   preserves branch satisfiability. The propositional and allFuture/allPast
   cases are straightforward. The key difficulty is the propagation of
   `F(U(χ,δ))@t → F(U(χ,δ))@t'` in `propagateToFuture`. Unlike the
   Modal K case (where `F(◇ψ)@w → F(ψ)@w'` is sound because `¬Sat(◇ψ)`
   means **no** accessible world satisfies ψ), the temporal case propagates
   the **full** Until formula, which requires a more nuanced argument: that
   in any model satisfying the branch, at least one of the branches produced
   by `temporalStepBranch` is also satisfiable.

3. `temporalExpandBranches_closed_unsat`: The loop invariant over fuel induction.
   Blocked by (1) and (2).

4. `temporalTableau_sound`: The main soundness theorem.
   Blocked by (1), (2), and (3).

## Phase Status

Phase 7 is [BLOCKED] pending resolution of the eventuality-defect soundness
gap and the F(U) propagation soundness argument.

## References

* Modal `Soundness.lean` (proof template)
* [R. Reynolds, *An axiomatization of prior's tense logic*][Reynolds1994]
* [I. Hodkinson and M. Reynolds, *Temporal Logic*][HodkinsonReynolds2006] (Handbook of Modal
  Logic, ch. 11, §5.4, §5.8: tableau soundness, filtration, and the FMP for discrete PTL)
* [C. Caleiro, L. Viganò, and M. Volpe, *On the Mosaic Method for Many-Dimensional Modal
  Logics*][CaleiroViganoVolpe2013] (§4.3: the mosaic-decidability route for `valid`, surveyed
  and rejected as non-transferable to the discrete case decided here)
* [D. Gabbay, I. Hodkinson, and M. Reynolds, *Temporal Expressive Completeness in the Presence
  of Gaps*][Gabbay1993]
-/

@[expose] public section

namespace Cslib.Logic.Temporal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Temporal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Branch Satisfiability -/

/-- A branch `b` with time ordering `ord` is satisfiable if there exists a temporal model
`M` over some discrete-serial time domain `D` (matching the frame class of
`Temporal.validDiscrete`/`Temporal.satisfiableDiscrete`: a nontrivial linear order with
`NoMaxOrder`, `NoMinOrder`, `SuccOrder`, `PredOrder`, `IsSuccArchimedean`), and a time
assignment `f : TimeIndex → D`, such that:
- The assignment is order-preserving: if `(t, t') ∈ ord.constraints` then `f t < f t'`.
- Every T(φ)@t on the branch satisfies `Satisfies M (f t) φ`.
- Every F(φ)@t on the branch satisfies `¬Satisfies M (f t) φ`.

The existential domain is restricted to the discrete-serial frame class (report 02 Finding
2.2) rather than the bare `[LinearOrder D] [Nontrivial D]` used in the earlier draft: the
tableau's `untlPos` rule (`Rules.lean`) places its Until witness at the immediate
integer successor of the current time, which is sound only under discreteness (the
discreteness axiom `G'⊥ ∧ H'⊥` separates `validDiscrete` from `valid`, `[Burgess1982I]`
§1.5, §2). -/
def branchSat
    (b : TBranch Atom)
    (ord : TimeOrdering) : Prop :=
  ∃ (D : Type) (_ : LinearOrder D) (_ : Nontrivial D)
    (_ : NoMaxOrder D) (_ : NoMinOrder D)
    (_ : SuccOrder D) (_ : PredOrder D) (_ : IsSuccArchimedean D)
    (M : TemporalModel D Atom)
    (f : TimeIndex → D),
    (∀ t t', (t, t') ∈ ord.constraints → f t < f t') ∧
    ∀ sf ∈ b,
      (sf.sign = .pos → Satisfies M (f sf.label) sf.formula) ∧
      (sf.sign = .neg → ¬Satisfies M (f sf.label) sf.formula)

/-! ## Classical Closure Implies Unsatisfiability -/

omit [Hashable Atom] in
/-- A classically closed temporal branch is unsatisfiable: no temporal model can
simultaneously satisfy all signed formulas on a classically closed branch.

Classical closure means T(⊥) is present at some time (never satisfiable) or
T(φ)/F(φ) coexist at the same time label (forcing simultaneous true and false). -/
lemma classicallyClosed_unsat
    (b : TBranch Atom)
    (ord : TimeOrdering)
    (hclosed : isClassicallyClosed b = true) :
    ¬branchSat b ord := by
  intro ⟨D, _, _, _, _, _, _, _, M, f, _, hb⟩
  simp only [isClassicallyClosed, ClosureCondition.isClosed] at hclosed
  have hsome : (ClosureCondition.findClosure b).isSome = true := hclosed
  rw [Option.isSome_iff_exists] at hsome
  obtain ⟨cr, hcr⟩ := hsome
  cases hfind : b.find? (fun sf => sf.isPos && sf.formula == (⊥ : Formula Atom)) with
  | some sf =>
    -- T(⊥) is on the branch
    have hmem := List.mem_of_find?_eq_some hfind
    have hpred := List.find?_some hfind
    simp only [Bool.and_eq_true, SignedFormula.isPos] at hpred
    obtain ⟨hpos, hbot⟩ := hpred
    have hsat := (hb sf hmem).1 (by
      cases h : sf.sign with
      | pos => rfl
      | neg => simp [h, Sign.isPos] at hpos)
    have hformbot : sf.formula = (⊥ : Formula Atom) :=
      LawfulBEq.eq_of_beq hbot
    rw [hformbot] at hsat
    exact Satisfies.bot_false M (f sf.label) hsat
  | none =>
    -- T(φ)/F(φ) contradiction at the same label
    simp only [ClosureCondition.findClosure] at hcr
    cases hcontra : Branch.findContradiction b with
    | none =>
        -- Both finds return none, but hcr says findClosure returned some cr.
        -- Reduce hcr using hcontra, then case-split on the bot-find to derive False.
        simp only [hcontra] at hcr
        cases hfindBot :
            List.find? (fun sf => sf.isPos && sf.formula == (HasBot.bot : Formula Atom)) b with
        | none => simp [hfindBot] at hcr
        | some sf =>
          -- hfindBot says bot-find returns some sf; hfind says the definitionally-equal
          -- expression returns none.  The rfl proof witnesses definitional equality.
          exact absurd hfind (by
            simp [show List.find? (fun sf => SignedFormula.isPos sf && sf.formula ==
                           (⊥ : Formula Atom)) b =
                       List.find? (fun sf => sf.isPos && sf.formula ==
                           (HasBot.bot : Formula Atom)) b from rfl,
                  hfindBot])
    | some pair =>
      obtain ⟨phi, l⟩ := pair
      simp only [Branch.findContradiction] at hcontra
      obtain ⟨sf, hsfmem, hsfcond⟩ := List.exists_of_findSome?_eq_some hcontra
      simp only [SignedFormula.isPos] at hsfcond
      by_cases hpos : sf.sign = .pos
      · simp only [hpos, Sign.isPos, ite_true, Option.ite_some_none_eq_some] at hsfcond
        obtain ⟨hany, _⟩ := hsfcond
        have htrue := (hb sf hsfmem).1 (by simp [hpos])
        obtain ⟨sf_neg, hmemneg, hsfneg⟩ := List.any_eq_true.mp hany
        simp only [Bool.and_eq_true] at hsfneg
        obtain ⟨⟨hsneg, hformEq⟩, hlabEq⟩ := hsfneg
        have hneg : sf_neg.sign = .neg := by
          cases h : sf_neg.sign with
          | pos => simp [h] at hsneg
          | neg => rfl
        have hformfeq : sf_neg.formula = sf.formula :=
          LawfulBEq.eq_of_beq hformEq
        have hlabfeq : sf_neg.label = sf.label :=
          LawfulBEq.eq_of_beq hlabEq
        have hfalse := (hb sf_neg hmemneg).2 (by simp [hneg])
        rw [hformfeq, hlabfeq] at hfalse
        exact absurd htrue hfalse
      · cases hsf : sf.sign with
        | pos => exact absurd hsf hpos
        | neg => simp [hsf, Sign.isPos] at hsfcond

/-! ## Proof Obligations for Full Soundness (BLOCKED)

The following section documents the proof obligations that remain blocked.
These are NOT proved in this module. See the module docstring for the
blockage explanation. -/

section BlockedObligations

/-! ### Eventuality-Defect Closure (BLOCKED)

A branch closed by eventuality-defect is unsatisfiable. The argument requires
showing that time-subset blocking with pending eventualities implies that no
model can satisfy all the branch formulas — in particular, that any Until
eventuality that is "blocked" (its time type cycles without witnessing the event)
cannot be satisfied even in an infinite model. This requires FMP or an explicit
loop-detection argument.

To complete this section, one needs a lemma of the form:

```lean
lemma eventualityDefect_unsat (b : TBranch Atom) (ord : TimeOrdering)
    (tracker : EventualityTracker Atom)
    (hblocked : findEventualityDefect b ord tracker = some t) :
    ¬branchSat b ord := ...
```

Once proved, `temporalClosed_unsat` follows by combining with `classicallyClosed_unsat`,
and `temporalTableau_sound` follows by the fuel-induction loop invariant. -/

end BlockedObligations

end Cslib.Logic.Temporal.Tableau

end
