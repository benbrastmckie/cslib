/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Init
import Cslib.Logics.Propositional.Tableau.Minimal.Completeness

/-! # IntMinScheme: Parameterized Interface for Intuitionistic/Minimal Tableau

This module introduces `IntMinScheme`, a structure bundling the two points where the
intuitionistic and minimal propositional tableau developments diverge:
- `closurePred : IBranch Atom → Bool`: the branch closure predicate.
- `modelBot : IBranch Atom → Nat → Prop`: the countermodel's `botForces`, built from
  an open saturated branch.

It also provides the two canonical data instances `intScheme` and `minScheme`.

## Design

The two divergence axes are value-level data on branches (not type-level), so a
bundling `structure` is the natural carrier; `instance` declarations are deliberately
avoided to prevent typeclass resolution ambiguity on `Bool`-valued data.

`closed_unsat` is stated for `botForces = fun _ => False`, matching the type of
`intClosed_unsatisfiable`. For minimal soundness with arbitrary `botForces`, pass
`minClosed_unsatisfiable` directly to `intExpandBranches_closed_unsat`.

`modelBot_uc` (upward-closure of `modelBot b`) is omitted from this interface because
it requires a saturation hypothesis for the minimal scheme; it is proved inline inside
the parametric truth lemma in `Scheme.lean` Phase 3.

## Main Definitions

- `IntMinScheme`: Structure with fields `closurePred`, `modelBot`, `closed_unsat`,
  `bot_truth`.
- `intScheme`: Intuitionistic instance (`isIntuitionisticallyClosed`, `fun _ _ => False`).
- `minScheme`: Minimal instance (`isMinimallyClosed`, `minBranchBotForces`).

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## IntMinScheme Structure -/

/-- A tableau scheme bundling the two divergence points between the intuitionistic and
minimal propositional tableau developments, together with per-logic proof obligations.

Use plain `def` instances (`intScheme`/`minScheme`) rather than `instance` declarations
to avoid typeclass resolution ambiguity on `Bool`-valued data. -/
structure IntMinScheme (Atom : Type*) [DecidableEq Atom] [Hashable Atom] where
  /-- Branch closure predicate. Determines when a branch is declared closed.
  - Intuitionistic: `isIntuitionisticallyClosed` (T(⊥) or complementary T(φ)/F(φ) pair).
  - Minimal: `isMinimallyClosed` (complementary T(φ)/F(φ) pair only). -/
  closurePred : IBranch Atom → Bool
  /-- The countermodel's `botForces` predicate, built from an open saturated branch.
  - Intuitionistic: `fun _ _ => False` (bot is never forced in intuitionistic models).
  - Minimal: `minBranchBotForces b` (T(⊥) is read directly from the branch). -/
  modelBot : IBranch Atom → Nat → Prop
  /-- Soundness obligation: a closed branch is unsatisfiable under `botForces = fun _ => False`.
  Used to instantiate `intExpandBranches_closed_unsat` in `tableau_sound`.
  For minimal soundness with arbitrary `botForces`, supply `minClosed_unsatisfiable`
  directly at call sites. -/
  closed_unsat : ∀ {World : Type*} [Preorder World]
      (val : World → Atom → Prop) (worldOf : Nat → World)
      (b : IBranch Atom),
      closurePred b = true → ¬ intBranchSatisfied val (fun _ => False) worldOf b
  /-- Completeness bot-case obligation: on an open branch, T(⊥) and F(⊥) are consistent
  with `modelBot`.
  - If T(⊥)@w is on the branch, then `modelBot b w` holds.
  - If F(⊥)@w is on the branch, then `¬ modelBot b w` holds (using openness). -/
  bot_truth : ∀ (b : IBranch Atom), closurePred b = false → ∀ (w : Nat),
      (b.any (fun sf =>
          sf.sign == .pos && sf.formula == (HasBot.bot : Proposition Atom)
          && sf.label == w) →
        modelBot b w) ∧
      (b.any (fun sf =>
          sf.sign == .neg && sf.formula == (HasBot.bot : Proposition Atom)
          && sf.label == w) →
        ¬ modelBot b w)

/-! ## Intuitionistic Scheme Instance -/

/-- The intuitionistic tableau scheme.

- `closurePred`: `isIntuitionisticallyClosed` (T(⊥) or complementary pair).
- `modelBot`: `fun _ _ => False` (intuitionistic models have bot always unforced).
- `closed_unsat`: `intClosed_unsatisfiable` directly.
- `bot_truth`: the T(⊥) case is vacuous (T(⊥) cannot appear on an open intuitionistic
  branch); the F(⊥) case is trivial since `¬ False = True`. -/
def intScheme : IntMinScheme Atom where
  closurePred := isIntuitionisticallyClosed
  modelBot    := fun _ _ => False
  closed_unsat := fun val worldOf b hclosed =>
    intClosed_unsatisfiable val worldOf b hclosed
  bot_truth := fun b hopen w => by
    -- isIntuitionisticallyClosed b = false means:
    --   ClosureCondition.isClosed b = false  (no T(⊥) on b)
    --   Branch.hasContradiction b = false
    simp only [isIntuitionisticallyClosed, Bool.or_eq_false_iff] at hopen
    obtain ⟨hnotbot, _⟩ := hopen
    constructor
    · -- T(⊥)@w ∈ b → False (contradicts ClosureCondition.isClosed b = false)
      intro hTbot
      exfalso
      -- Extract witness from hTbot
      rw [List.any_eq_true] at hTbot
      obtain ⟨sf, hmem, hcond⟩ := hTbot
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨⟨hsign, hform⟩, _⟩ := hcond
      -- sf.isPos = true (since sf.sign = .pos) and sf.formula = bot
      -- so ClosureCondition.isClosed b = true, contradicting hnotbot
      apply Bool.eq_false_iff.mp hnotbot
      simp only [ClosureCondition.isClosed, ClosureCondition.findClosure]
      cases hfind : b.find? (fun (sf' : ISF Atom) =>
          sf'.isPos && sf'.formula == (HasBot.bot : Proposition Atom)) with
      | some _ => rfl
      | none =>
        exfalso
        have hno := List.find?_eq_none.mp hfind sf hmem
        simp [SignedFormula.isPos, Sign.isPos, hsign, hform] at hno
    · -- F(⊥)@w ∈ b → ¬ (fun _ _ => False) b w = True (trivial)
      intro _
      exact id

/-! ## Minimal Scheme Instance -/

/-- The minimal tableau scheme.

- `closurePred`: `isMinimallyClosed` (complementary pair only, no T(⊥) closure).
- `modelBot`: `minBranchBotForces b` (T(⊥) read from the branch).
- `closed_unsat`: `minClosed_unsatisfiable` specialized to `botForces = fun _ => False`.
- `bot_truth`: first conjunct is definitional; second uses `minOpen_no_contradiction`. -/
def minScheme : IntMinScheme Atom where
  closurePred := isMinimallyClosed
  modelBot    := minBranchBotForces
  closed_unsat := fun val worldOf b hclosed =>
    minClosed_unsatisfiable val (fun _ => False) worldOf b hclosed
  bot_truth := fun b hopen w => by
    constructor
    · -- T(⊥)@w ∈ b → minBranchBotForces b w (definitionally the same)
      intro hTbot
      exact hTbot
    · -- F(⊥)@w ∈ b → ¬ minBranchBotForces b w
      -- Uses minOpen_no_contradiction: ¬ (T(⊥)@w ∈ b ∧ F(⊥)@w ∈ b)
      intro hFbot hTbot
      exact minOpen_no_contradiction b hopen (HasBot.bot : Proposition Atom) w ⟨hTbot, hFbot⟩

/-! ## Generic Tableau Soundness -/

/-- **Generic Tableau Soundness**: If the tableau with closure predicate `S.closurePred`
closes on `φ`, then `φ` is intuitionistically valid (`IValid φ`).

The proof instantiates `intExpandBranches_closed_unsat` with `S.closurePred` and
`S.closed_unsat`, giving a parametric wrap of `intuitionisticTableau_sound` that
ranges over all `IntMinScheme` instances.

The conclusion is `IValid φ` (validity with `botForces = fun _ => False`), matching the
`botForces = fun _ => False` specialization in `IntMinScheme.closed_unsat`.

- At `intScheme`: equivalent to `intuitionisticTableau_sound` (Phase 5 will repoint).
- At `minScheme`: proves the `botForces = fun _ => False` sub-case of minimal soundness.
  `minimalTableau_sound` (arbitrary `botForces`) stays in `Minimal/Soundness.lean`.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4 -/
theorem tableau_sound.{u_world} (S : IntMinScheme.{_, u_world} Atom) (φ : Proposition Atom)
    (h : intExpandBranches [[⟨.neg, φ, 0⟩]] [[]] [1] [[]]
        (2 ^ (2 * φ.complexity + 2)) S.closurePred = .closed) :
    IValid.{_, u_world} φ := by
  intro World _ val v_uc w₀
  by_contra hneg
  let worldOf : Nat → World := fun _ => w₀
  have hsat : intBranchSatisfied val (fun _ => False) worldOf [⟨.neg, φ, 0⟩] := by
    intro sf hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    subst hmem
    exact ⟨fun h' => absurd h' (Sign.noConfusion), fun _ => hneg⟩
  apply intExpandBranches_closed_unsat val (fun _ => False) v_uc
      (fun {_ _} _ hf => absurd hf id) _
      S.closurePred
      (fun (worldOf' : Nat → World) (b : IBranch Atom) hcl =>
          S.closed_unsat val worldOf' b hcl)
      [[⟨.neg, φ, 0⟩]] [[]] [1] [[]] (by rfl) (by rfl) (by rfl)
      (by
        intro b edges nw hmem
        simp only [List.zip_cons_cons, List.zip_nil_right,
          List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        obtain ⟨⟨hb, he⟩, hnw⟩ := hmem
        subst hb; subst he; subst hnw
        refine ⟨?_, ?_⟩
        · intro sf hsf
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hsf
          simp [hsf]
        · intro c p hcp
          simp only [List.not_mem_nil] at hcp) h
      [⟨.neg, φ, 0⟩] []
  · simp [List.zip_cons_cons, List.zip_nil_right]
  · exact fun w w' hacc => by
      simp only [isAccessible] at hacc
      split_ifs at hacc with heq
      · have hw : w = w' := by exact_mod_cast beq_iff_eq.mp heq
        exact le_of_eq (congrArg worldOf hw)
      · simp [isAccessible.go] at hacc
  · exact hsat

/-! ## Parametric Truth Lemma -/

/-- Parametric truth lemma (the single deferred completeness obligation, task 317).
Generalizes `intTruthLemma` over an `IntMinScheme`'s `closurePred`/`modelBot`. -/
lemma truthLemma (S : IntMinScheme Atom) (b : IBranch Atom)
    (hopen : S.closurePred b = false)
    (hsat : ∀ sf ∈ b, intStepBranch b [] 0 = none)
    (φ : Proposition Atom) (w : Nat) :
    (b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w) →
      IForces (intExtractValuation b) (S.modelBot b) w φ) ∧
    (b.any (fun sf => sf.sign == .neg && sf.formula == φ && sf.label == w) →
      ¬ IForces (intExtractValuation b) (S.modelBot b) w φ) := by
  sorry

/-! ## Parametric Open Branch Countermodel -/

/-- **Parametric Open Branch Countermodel**: An open branch returned by the parametric
expansion witnesses that `φ` is not forced in the branch-derived Kripke model.

If the expansion with `S.closurePred` returns `.openBranch b`, then the extracted
valuation `intExtractValuation b` with `botForces = S.modelBot b` falsifies `φ` at
world 0.

- At `intScheme`: specializes to `intuitionisticOpenBranch_countermodel` (Phase 3b).
- At `minScheme`: specializes to `minOpenBranch_countermodel` (Phase 3b).

## Proof structure

From `h : intExpandBranches ... S.closurePred = .openBranch b` we extract three
structural facts (each left as `sorry` pending `intExpandBranches_openBranch_*` structural
lemmas, which require induction on the expansion loop):
1. `hopen`: the returned branch is open (`S.closurePred b = false`).
2. `hsat`: the returned branch is saturated (`intStepBranch b [] 0 = none`).
3. `hFmem`: F(φ)@0 is on b (branch monotonicity: formulas are only added).
Then `(truthLemma S b hopen hsat φ 0).2 hFmem` closes the goal.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4 -/
lemma openBranch_countermodel (S : IntMinScheme Atom) (φ : Proposition Atom)
    (b : IBranch Atom)
    (h : intExpandBranches [[⟨.neg, φ, 0⟩]] [[]] [1] [[]]
        (2 ^ (2 * φ.complexity + 2)) S.closurePred = .openBranch b) :
    ¬ IForces (intExtractValuation b) (S.modelBot b) 0 φ := by
  -- Extract structural properties of b from the openBranch result.
  have hopen : S.closurePred b = false := by
    -- MISSING: `intExpandBranches_openBranch_closed`
    -- The expansion loop checks `closurePred b = false` before returning `.openBranch b`
    -- in both the fuel=0 case (via `findSome?`) and the fuel+1 inner loop.
    -- Formal proof requires induction on `intExpandBranches` and its `go` helper.
    sorry
  have hsat : ∀ sf ∈ b, intStepBranch b [] 0 = none := by
    -- MISSING: `intExpandBranches_openBranch_sat`
    -- In the fuel+1 case, `.openBranch bPers` is returned when
    -- `intStepBranch bPers e nw = none` for the accumulated expanded set `e` and
    -- next-world `nw`. Connecting this to `intStepBranch b [] 0 = none` (empty expanded
    -- set, world 0) requires showing the expanded set does not affect the none result
    -- for a fully saturated branch. Formal proof requires induction on the expansion loop.
    sorry
  have hFmem : b.any (fun sf => sf.sign == .neg && sf.formula == φ && sf.label == 0) := by
    -- MISSING: `intExpandBranches_openBranch_initial_mem`
    -- The initial branch `[[⟨.neg, φ, 0⟩]]` contains F(φ)@0.
    -- Under expansion, formulas are only added to branches (branch monotonicity via
    -- `applyPersistenceFixpoint` and `Branch.extendMany`). So F(φ)@0 remains in b.
    -- Formal proof requires a monotonicity lemma on `intExpandBranches`
    -- (analogous to `classicalExpandBranches_openBranch_initial_mem`).
    sorry
  -- Apply the truth lemma's F-branch direction.
  exact (truthLemma S b hopen hsat φ 0).2 hFmem

/-! ## Parametric Tableau Completeness -/

/-- **Parametric Tableau Completeness**: If `φ` is forced at world 0 in every
branch-derived Kripke model, then the parametric expansion closes on `φ`.

Proof: by contrapositive. If the expansion returns `.openBranch b`, then
`openBranch_countermodel S` gives `¬ IForces (intExtractValuation b) (S.modelBot b) 0 φ`,
contradicting `hvalid b`.

The hypothesis `hvalid` encodes the per-scheme validity notion:
- For `intScheme` (where `modelBot b = fun _ => False`): `hvalid b` follows from `IValid φ`
  applied at World `= ℕ`, `val = intExtractValuation b`, with the upward-closure of
  `intExtractValuation b`.
- For `minScheme` (where `modelBot b = minBranchBotForces b`): `hvalid b` follows from
  `MValid φ` applied with `botForces = minBranchBotForces b` and upward-closure of both
  `intExtractValuation b` and `minBranchBotForces b`.

This theorem is sorry-free given `openBranch_countermodel S`.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4 -/
theorem tableau_complete (S : IntMinScheme Atom) (φ : Proposition Atom)
    (hvalid : ∀ (b : IBranch Atom), IForces (intExtractValuation b) (S.modelBot b) 0 φ) :
    intExpandBranches [[⟨.neg, φ, 0⟩]] [[]] [1] [[]]
        (2 ^ (2 * φ.complexity + 2)) S.closurePred = .closed := by
  by_contra hne
  cases hresult : intExpandBranches [[⟨.neg, φ, 0⟩]] [[]] [1] [[]]
      (2 ^ (2 * φ.complexity + 2)) S.closurePred with
  | closed => exact hne hresult
  | openBranch b => exact absurd (hvalid b) (openBranch_countermodel S φ b hresult)

end Cslib.Logic.PL

end
