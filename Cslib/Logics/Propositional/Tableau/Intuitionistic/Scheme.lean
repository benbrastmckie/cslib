/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Tableau.Minimal.Soundness

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

/-! ## IBranchSaturation -/

/-- Saturation conditions for an open intuitionistic tableau branch.

A branch `b` is Hintikka-saturated if every compound formula on `b` has its rule outputs
also on `b`: alpha-rule formulas have BOTH outputs, beta-rule formulas have AT LEAST ONE
output (corresponding to the sub-branch taken), and the world-creating F(φ→ψ) rule has
T(φ) and F(ψ) at a fresh world.

These conditions are established structurally by `intExpandBranches_openBranch_sat` (task 317,
pending) via induction on the expansion loop. The key step: `intStepBranch b e nw = none`
implies every compound formula in `b` is in `e`, and formulas in `e` had their rule outputs
added to an ancestor branch; branch monotonicity carries them forward to `b`.

Note on `sat_fimp`: the new world `w'` satisfies `w ≤ w'` because the expansion assigns
strictly increasing world labels (nextWorld starts at 1 and only increments). -/
structure IBranchSaturation (Atom : Type*) [DecidableEq Atom] [Hashable Atom]
    (b : IBranch Atom) where
  /-- T(φ∧ψ)@w ∈ b → T(φ)@w ∈ b ∧ T(ψ)@w ∈ b (alpha-rule saturation) -/
  sat_tand : ∀ (φ ψ : Proposition Atom) (w : Nat),
      b.any (fun sf => sf.sign == .pos && sf.formula == .and φ ψ && sf.label == w) = true →
      b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w) = true ∧
      b.any (fun sf => sf.sign == .pos && sf.formula == ψ && sf.label == w) = true
  /-- F(φ∧ψ)@w ∈ b → F(φ)@w ∈ b ∨ F(ψ)@w ∈ b (beta-rule: one sub-branch taken) -/
  sat_fand : ∀ (φ ψ : Proposition Atom) (w : Nat),
      b.any (fun sf => sf.sign == .neg && sf.formula == .and φ ψ && sf.label == w) = true →
      b.any (fun sf => sf.sign == .neg && sf.formula == φ && sf.label == w) = true ∨
      b.any (fun sf => sf.sign == .neg && sf.formula == ψ && sf.label == w) = true
  /-- T(φ∨ψ)@w ∈ b → T(φ)@w ∈ b ∨ T(ψ)@w ∈ b (beta-rule: one sub-branch taken) -/
  sat_tor : ∀ (φ ψ : Proposition Atom) (w : Nat),
      b.any (fun sf => sf.sign == .pos && sf.formula == .or φ ψ && sf.label == w) = true →
      b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w) = true ∨
      b.any (fun sf => sf.sign == .pos && sf.formula == ψ && sf.label == w) = true
  /-- F(φ∨ψ)@w ∈ b → F(φ)@w ∈ b ∧ F(ψ)@w ∈ b (alpha-rule saturation) -/
  sat_for_ : ∀ (φ ψ : Proposition Atom) (w : Nat),
      b.any (fun sf => sf.sign == .neg && sf.formula == .or φ ψ && sf.label == w) = true →
      b.any (fun sf => sf.sign == .neg && sf.formula == φ && sf.label == w) = true ∧
      b.any (fun sf => sf.sign == .neg && sf.formula == ψ && sf.label == w) = true
  /-- F(φ→ψ)@w ∈ b → ∃ w' ≥ w, T(φ)@w' ∈ b ∧ F(ψ)@w' ∈ b (world-creating rule) -/
  sat_fimp : ∀ (φ ψ : Proposition Atom) (w : Nat),
      b.any (fun sf => sf.sign == .neg && sf.formula == .imp φ ψ && sf.label == w) = true →
      ∃ (w' : Nat), w ≤ w' ∧
        b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w') = true ∧
        b.any (fun sf => sf.sign == .neg && sf.formula == ψ && sf.label == w') = true

/-! ## IntMinScheme Structure -/

/-- A tableau scheme bundling the two divergence points between the intuitionistic and
minimal propositional tableau developments: the branch closure predicate and the
countermodel's `botForces` predicate, together with the completeness bot-case obligation.

Use plain `def` instances (`intScheme`/`minScheme`) rather than `instance` declarations
to avoid typeclass resolution ambiguity on `Bool`-valued data.

The soundness obligation (`closed_unsat`) is NOT a field here because it is
universe-polymorphic (`∀ {World : Type*} ...`) while the completeness theorems use
`World = Nat`. Carrying `closed_unsat` as a field would make `IntMinScheme` universe-polymorphic
and cause universe metavariables in `truthLemma`, `openBranch_countermodel`, and
`tableau_complete`. Instead, `closed_unsat` is passed as a separate parameter to
`tableau_sound`. -/
structure IntMinScheme (Atom : Type*) [DecidableEq Atom] [Hashable Atom] where
  /-- Branch closure predicate. Determines when a branch is declared closed.
  - Intuitionistic: `isIntuitionisticallyClosed` (T(⊥) or complementary T(φ)/F(φ) pair).
  - Minimal: `isMinimallyClosed` (complementary T(φ)/F(φ) pair only). -/
  closurePred : IBranch Atom → Bool
  /-- The countermodel's `botForces` predicate, built from an open saturated branch.
  - Intuitionistic: `fun _ _ => False` (bot is never forced in intuitionistic models).
  - Minimal: `minBranchBotForces b` (T(⊥) is read directly from the branch). -/
  modelBot : IBranch Atom → Nat → Prop
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
  /-- No-contradiction: an open branch cannot contain both T(φ)@w and F(φ)@w.
  Follows from the closure predicate checking complementary pairs (`Branch.hasContradiction`).
  Needed for the atom F-direction in `truthLemma`. -/
  no_contradiction : ∀ (b : IBranch Atom), closurePred b = false →
      ∀ (φ : Proposition Atom) (w : Nat),
        ¬ (b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w) = true ∧
           b.any (fun sf => sf.sign == .neg && sf.formula == φ && sf.label == w) = true)

/-! ## Intuitionistic Scheme Instance -/

/-- The intuitionistic tableau scheme.

- `closurePred`: `isIntuitionisticallyClosed` (T(⊥) or complementary pair).
- `modelBot`: `fun _ _ => False` (intuitionistic models have bot always unforced).
- `bot_truth`: the T(⊥) case is vacuous (T(⊥) cannot appear on an open intuitionistic
  branch); the F(⊥) case is trivial since `¬ False = True`.

The soundness obligation `intClosed_unsatisfiable` is passed directly to `tableau_sound`
as a separate parameter (not stored in the scheme). -/
def intScheme : IntMinScheme Atom where
  closurePred := isIntuitionisticallyClosed
  modelBot    := fun _ _ => False
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
  no_contradiction := fun b hopen φ w => by
    -- isIntuitionisticallyClosed b = false → Branch.hasContradiction b = false
    simp only [isIntuitionisticallyClosed, Bool.or_eq_false_iff] at hopen
    obtain ⟨_, hnocontra⟩ := hopen
    -- Branch.hasContradiction = isMinimallyClosed (definitional)
    exact minOpen_no_contradiction b hnocontra φ w

/-! ## Minimal Scheme Instance -/

/-- The minimal tableau scheme.

- `closurePred`: `isMinimallyClosed` (complementary pair only, no T(⊥) closure).
- `modelBot`: `minBranchBotForces b` (T(⊥) read from the branch).
- `bot_truth`: first conjunct is definitional; second uses `minOpen_no_contradiction`.

The soundness obligation `minClosed_unsatisfiable` is passed directly to `tableau_sound`
as a separate parameter (not stored in the scheme). -/
def minScheme : IntMinScheme Atom where
  closurePred := isMinimallyClosed
  modelBot    := minBranchBotForces
  bot_truth := fun b hopen w => by
    constructor
    · -- T(⊥)@w ∈ b → minBranchBotForces b w (definitionally the same)
      intro hTbot
      exact hTbot
    · -- F(⊥)@w ∈ b → ¬ minBranchBotForces b w
      -- Uses minOpen_no_contradiction: ¬ (T(⊥)@w ∈ b ∧ F(⊥)@w ∈ b)
      intro hFbot hTbot
      exact minOpen_no_contradiction b hopen (HasBot.bot : Proposition Atom) w ⟨hTbot, hFbot⟩
  no_contradiction := fun b hopen φ w =>
    minOpen_no_contradiction b hopen φ w

/-! ## Generic Tableau Soundness -/

/-- **Generic Tableau Soundness**: If the tableau with closure predicate `S.closurePred`
closes on `φ`, then `φ` is intuitionistically valid (`IValid φ`).

The proof instantiates `intExpandBranches_closed_unsat` with `S.closurePred` and the
provided `closed_unsat` argument. This gives a parametric wrap of
`intuitionisticTableau_sound` that ranges over all `IntMinScheme` instances.

The `closed_unsat` parameter is passed separately (not stored in `IntMinScheme`) because
it is universe-polymorphic (`∀ {World : Type*} ...`) while the completeness theorems in
`IntMinScheme` use `World = Nat`. Storing `closed_unsat` in the struct would make
`IntMinScheme` universe-polymorphic and cause universe metavariables in the completeness
theorems. See the `IntMinScheme` docstring.

The conclusion is `IValid φ` (validity with `botForces = fun _ => False`), matching
the `botForces = fun _ => False` specialization typically used with this function.

- At `intScheme`/`intClosed_unsatisfiable`: equivalent to `intuitionisticTableau_sound`.
- At `minScheme`/`minClosed_unsatisfiable (fun _ => False)`: minimal soundness sub-case.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4 -/
theorem tableau_sound.{u_world} (S : IntMinScheme Atom)
    (closed_unsat : ∀ {World : Type u_world} [Preorder World]
        (val : World → Atom → Prop) (worldOf : Nat → World)
        (b : IBranch Atom),
        S.closurePred b = true → ¬ intBranchSatisfied val (fun _ => False) worldOf b)
    (φ : Proposition Atom)
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
          closed_unsat val worldOf' b hcl)
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
Generalizes `intTruthLemma` over an `IntMinScheme`'s `closurePred`/`modelBot`.

**Infrastructure cross-reference** (task 422): The FMP routes in `Metalogic/IntDecidability.lean`
and `Metalogic/MinDecidability.lean` prove analogous "forcing ↔ membership" statements
(`int_fin_truth_lemma`, `min_fin_truth_lemma`) over finite `Σ`-bounded worlds. Those lemmas
rest on the `IntLindenbaum.lean`/minimal Lindenbaum substrate and are sorry-free. This
parametric `truthLemma` operates over Nat-labelled branch worlds (disjoint carrier type).
Factoring a common abstraction across the two carrier systems is explicitly deferred; see
the module headers in `Metalogic/IntDecidability.lean` and `Metalogic/MinDecidability.lean`
for the full rationale. -/
lemma truthLemma (S : IntMinScheme Atom) (b : IBranch Atom)
    (hopen : S.closurePred b = false)
    (hsat : IBranchSaturation Atom b)
    (φ : Proposition Atom) (w : Nat) :
    (b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w) →
      IForces (intExtractValuation b) (S.modelBot b) w φ) ∧
    (b.any (fun sf => sf.sign == .neg && sf.formula == φ && sf.label == w) →
      ¬ IForces (intExtractValuation b) (S.modelBot b) w φ) := by
  induction φ generalizing w with
  | atom p =>
    simp only [IForces_atom, intExtractValuation]
    constructor
    · exact id
    · intro hneg hpos
      exact S.no_contradiction b hopen (.atom p) w ⟨hpos, hneg⟩
  | bot =>
    simp only [IForces_bot]
    exact S.bot_truth b hopen w
  | imp φ' ψ' ih_φ' ih_ψ' =>
    simp only [IForces_imp]
    constructor
    · -- T(φ'→ψ')@w ∈ b → ∀ w' ≥ w, IForces val w' φ' → IForces val w' ψ'.
      -- Requires a T-modus ponens saturation (sat_timp) together with backward reasoning
      -- from IForces to branch membership, neither of which is available without branch
      -- completeness. Deferred: task 317 phase-6 blocker (intStepBranch internals +
      -- completeness of branch labelling).
      intro _
      sorry
    · -- F(φ'→ψ')@w ∈ b → ¬∀ w' ≥ w, IForces val w' φ' → IForces val w' ψ'.
      -- sat_fimp witnesses w', T(φ')@w', F(ψ')@w'; IH closes each membership-to-forcing step.
      intro h hcontra
      obtain ⟨w', hw', ht_φ', hf_ψ'⟩ := hsat.sat_fimp φ' ψ' w h
      exact (ih_ψ' w').2 hf_ψ' (hcontra w' hw' ((ih_φ' w').1 ht_φ'))
  | and φ' ψ' ih_φ' ih_ψ' =>
    simp only [IForces_and]
    constructor
    · -- T(φ'∧ψ')@w ∈ b → IForces val w φ' ∧ IForces val w ψ'.
      -- sat_tand splits alpha-rule; both sub-membership facts close via T-direction of IH.
      intro h
      obtain ⟨ht_φ', ht_ψ'⟩ := hsat.sat_tand φ' ψ' w h
      exact ⟨(ih_φ' w).1 ht_φ', (ih_ψ' w).1 ht_ψ'⟩
    · -- F(φ'∧ψ')@w ∈ b → ¬(IForces val w φ' ∧ IForces val w ψ').
      -- sat_fand gives F(φ')@w or F(ψ')@w; F-direction of IH gives a contradiction.
      intro h hcontra
      rcases hsat.sat_fand φ' ψ' w h with hf | hf
      · exact (ih_φ' w).2 hf hcontra.1
      · exact (ih_ψ' w).2 hf hcontra.2
  | or φ' ψ' ih_φ' ih_ψ' =>
    simp only [IForces_or]
    constructor
    · -- T(φ'∨ψ')@w ∈ b → IForces val w φ' ∨ IForces val w ψ'.
      -- sat_tor gives T(φ')@w or T(ψ')@w; T-direction of IH closes each.
      intro h
      rcases hsat.sat_tor φ' ψ' w h with ht | ht
      · exact Or.inl ((ih_φ' w).1 ht)
      · exact Or.inr ((ih_ψ' w).1 ht)
    · -- F(φ'∨ψ')@w ∈ b → ¬(IForces val w φ' ∨ IForces val w ψ').
      -- sat_for_ gives F(φ')@w and F(ψ')@w; F-direction of IH refutes each disjunct.
      intro h hcontra
      obtain ⟨hf_φ', hf_ψ'⟩ := hsat.sat_for_ φ' ψ' w h
      rcases hcontra with hpos | hpos
      · exact (ih_φ' w).2 hf_φ' hpos
      · exact (ih_ψ' w).2 hf_ψ' hpos

/-! ## Structural Lemmas for `openBranch_countermodel` -/

omit [Hashable Atom] in
/-- Formulas are preserved under `applyPersistenceFixpoint`:
`applyAllTImpRules` only appends to `b`, so `sf ∈ b` is maintained across fixpoint
iterations. -/
private lemma applyPersistenceFixpoint_mem_preserved
    (b : IBranch Atom) (edges : IEdges) (fuel : Nat)
    (sf : ISF Atom) (h : sf ∈ b) :
    sf ∈ applyPersistenceFixpoint b edges fuel := by
  induction fuel generalizing b with
  | zero => simpa [applyPersistenceFixpoint] using h
  | succ k ih =>
    simp only [applyPersistenceFixpoint]
    split_ifs
    · exact h
    · apply ih; simp only [applyAllTImpRules, List.mem_append]; exact Or.inl h

omit [Hashable Atom] in
/-- If the expansion loop returns `.openBranch b`, then `closurePred b = false`.

In the fuel=0 case, `findSome?` only yields a branch when `closurePred b = false`.
In the fuel+1 case, the inner go returns `.openBranch bPers` only inside the `else`
branch of `if closurePred bPers`, so `closurePred bPers = false`. When a rule fires
it recurses to `intExpandBranches` with fuel', and the outer IH applies. -/
private lemma intExpandBranches_openBranch_closed (fuel : Nat)
    (branches : List (IBranch Atom))
    (expandedSets : List (List (ISF Atom)))
    (nextWorlds : List Nat)
    (edgeSets : List IEdges)
    (closurePred : IBranch Atom → Bool)
    (b : IBranch Atom)
    (h : intExpandBranches branches expandedSets nextWorlds edgeSets fuel closurePred
        = .openBranch b) :
    closurePred b = false := by
  induction fuel generalizing branches expandedSets nextWorlds edgeSets with
  | zero =>
    simp only [intExpandBranches] at h
    cases hfs : branches.findSome? (fun b' => if closurePred b' then none else some b') with
    | none => simp [hfs] at h
    | some b' =>
      simp only [hfs] at h; injection h with heq; subst heq
      obtain ⟨b₀, _, hcond⟩ := List.exists_of_findSome?_eq_some hfs
      cases heq : closurePred b₀ with
      | true => simp [heq] at hcond
      | false =>
        simp only [heq, Bool.false_eq_true, if_false, Option.some.injEq] at hcond
        exact hcond ▸ heq
  | succ fuel' ih =>
    simp only [intExpandBranches] at h
    suffices key : ∀ (pending : List (IBranch Atom))
        (pendingExp : List (List (ISF Atom)))
        (pendingNW : List Nat)
        (pendingEdges : List IEdges)
        (done : List (IBranch Atom))
        (doneExp : List (List (ISF Atom)))
        (doneNW : List Nat)
        (doneEdges : List IEdges),
        intExpandBranches.go closurePred fuel' pending pendingExp pendingNW pendingEdges
            done doneExp doneNW doneEdges = .openBranch b →
        closurePred b = false from
      key branches expandedSets nextWorlds edgeSets [] [] [] [] h
    intro pending
    induction pending with
    | nil =>
      intro _ _ _ _ _ _ _ hgo
      simp only [intExpandBranches.go] at hgo
      simp at hgo
    | cons bh bt ih_inner =>
      intro pendingExp pendingNW pendingEdges done doneExp doneNW doneEdges hgo
      cases hpE : pendingExp with
      | nil =>
        rw [hpE] at hgo; simp only [intExpandBranches.go] at hgo
        exact ih_inner [] [] [] done doneExp doneNW doneEdges hgo
      | cons eH eT =>
        cases hpNW : pendingNW with
        | nil =>
          rw [hpE, hpNW] at hgo; simp only [intExpandBranches.go] at hgo
          exact ih_inner [] [] [] done doneExp doneNW doneEdges hgo
        | cons nwH nwT =>
          cases hpEdges : pendingEdges with
          | nil =>
            rw [hpE, hpNW, hpEdges] at hgo; simp only [intExpandBranches.go] at hgo
            exact ih_inner [] [] [] done doneExp doneNW doneEdges hgo
          | cons edgesH edgesT =>
            rw [hpE, hpNW, hpEdges] at hgo
            set bPers := applyPersistenceFixpoint bh edgesH (fuel' + 1) with hbPers_def
            simp only [intExpandBranches.go] at hgo
            by_cases hcl : closurePred bPers = true
            · rw [if_pos hcl] at hgo
              exact ih_inner eT nwT edgesT
                  (done ++ [bPers]) (doneExp ++ [eH]) (doneNW ++ [nwH]) (doneEdges ++ [edgesH])
                  hgo
            · simp only [Bool.not_eq_true] at hcl
              rw [if_neg (by simp [← hbPers_def, hcl])] at hgo
              cases hstep : intStepBranch bPers eH nwH with
              | none =>
                rw [hstep] at hgo; injection hgo with heq; subst heq; exact hcl
              | some step =>
                obtain ⟨result, newExp⟩ := step
                rw [hstep] at hgo
                cases result with
                | linearResult newForms nw' newEdge =>
                  simp only at hgo; exact ih _ _ _ _ hgo
                | branchingResult branches' nw' =>
                  simp only at hgo; exact ih _ _ _ _ hgo
                | notApplicable =>
                  simp only at hgo; injection hgo with heq; subst heq; exact hcl

/-- If `intExpandBranches` returns `.openBranch b`, then `b` is Hintikka-saturated:
every compound formula on `b` has its rule-outputs also on `b` (see `IBranchSaturation`).

The proof mirrors `intExpandBranches_openBranch_closed`: induction on `fuel`, with inner
induction on the `pending` list in the `go` helper. In the recursive cases (`linearResult`,
`branchingResult`), the fuel IH closes the goal. In the leaf cases (`none`, `notApplicable`),
the returned branch equals `bPers` directly; saturation of `bPers` requires analysing
`intStepBranch`'s internal invariants and is left as `sorry` (task 317 phase-6 blocker).
The fuel-0 base case has the same gap. -/
private lemma intExpandBranches_openBranch_sat (fuel : Nat)
    (branches : List (IBranch Atom))
    (expandedSets : List (List (ISF Atom)))
    (nextWorlds : List Nat)
    (edgeSets : List IEdges)
    (closurePred : IBranch Atom → Bool)
    (b : IBranch Atom)
    (h : intExpandBranches branches expandedSets nextWorlds edgeSets fuel closurePred
        = .openBranch b) :
    IBranchSaturation Atom b := by
  induction fuel generalizing branches expandedSets nextWorlds edgeSets with
  | zero =>
    simp only [intExpandBranches] at h
    cases hfs : branches.findSome? (fun b' => if closurePred b' then none else some b') with
    | none => simp [hfs] at h
    | some b' =>
      simp only [hfs] at h; injection h with heq; subst heq
      obtain ⟨b₀, _, hcond⟩ := List.exists_of_findSome?_eq_some hfs
      cases heq : closurePred b₀ with
      | true => simp [heq] at hcond
      | false =>
        simp only [heq, Bool.false_eq_true, if_false, Option.some.injEq] at hcond
        -- b = b₀ from the initial branch list; saturation of b₀ requires that
        -- intStepBranch b₀ eH nwH = none for the appropriate eH and nwH, which
        -- in turn requires analysing intStepBranch's internals.
        -- Left as sorry (task 317 phase-6 blocker: intStepBranch internals).
        sorry
  | succ fuel' ih =>
    simp only [intExpandBranches] at h
    suffices key : ∀ (pending : List (IBranch Atom))
        (pendingExp : List (List (ISF Atom)))
        (pendingNW : List Nat)
        (pendingEdges : List IEdges)
        (done : List (IBranch Atom))
        (doneExp : List (List (ISF Atom)))
        (doneNW : List Nat)
        (doneEdges : List IEdges),
        intExpandBranches.go closurePred fuel' pending pendingExp pendingNW pendingEdges
            done doneExp doneNW doneEdges = .openBranch b →
        IBranchSaturation Atom b from
      key branches expandedSets nextWorlds edgeSets [] [] [] [] h
    intro pending
    induction pending with
    | nil =>
      intro _ _ _ _ _ _ _ hgo
      simp only [intExpandBranches.go] at hgo
      simp at hgo
    | cons bh bt ih_inner =>
      intro pendingExp pendingNW pendingEdges done doneExp doneNW doneEdges hgo
      cases hpE : pendingExp with
      | nil =>
        rw [hpE] at hgo; simp only [intExpandBranches.go] at hgo
        exact ih_inner [] [] [] done doneExp doneNW doneEdges hgo
      | cons eH eT =>
        cases hpNW : pendingNW with
        | nil =>
          rw [hpE, hpNW] at hgo; simp only [intExpandBranches.go] at hgo
          exact ih_inner [] [] [] done doneExp doneNW doneEdges hgo
        | cons nwH nwT =>
          cases hpEdges : pendingEdges with
          | nil =>
            rw [hpE, hpNW, hpEdges] at hgo; simp only [intExpandBranches.go] at hgo
            exact ih_inner [] [] [] done doneExp doneNW doneEdges hgo
          | cons edgesH edgesT =>
            rw [hpE, hpNW, hpEdges] at hgo
            set bPers := applyPersistenceFixpoint bh edgesH (fuel' + 1) with hbPers_def
            simp only [intExpandBranches.go] at hgo
            by_cases hcl : closurePred bPers = true
            · rw [if_pos hcl] at hgo
              exact ih_inner eT nwT edgesT
                  (done ++ [bPers]) (doneExp ++ [eH]) (doneNW ++ [nwH]) (doneEdges ++ [edgesH])
                  hgo
            · simp only [Bool.not_eq_true] at hcl
              rw [if_neg (by simp [← hbPers_def, hcl])] at hgo
              cases hstep : intStepBranch bPers eH nwH with
              | none =>
                rw [hstep] at hgo; injection hgo with heq; subst heq
                -- b = bPers; intStepBranch returned none, meaning all compound
                -- formulas in bPers have been expanded. Proving IBranchSaturation
                -- requires analysing intStepBranch's none-condition internals.
                -- Left as sorry (task 317 phase-6 blocker).
                sorry
              | some step =>
                obtain ⟨result, newExp⟩ := step
                rw [hstep] at hgo
                cases result with
                | linearResult newForms nw' newEdge =>
                  simp only at hgo; exact ih _ _ _ _ hgo
                | branchingResult branches' nw' =>
                  simp only at hgo; exact ih _ _ _ _ hgo
                | notApplicable =>
                  simp only at hgo; injection hgo with heq; subst heq
                  -- b = bPers; notApplicable means no tableau rule is applicable
                  -- to bPers, implying saturation. Requires intStepBranch analysis.
                  -- Left as sorry (task 317 phase-6 blocker).
                  sorry

omit [Hashable Atom] in
/-- Every formula in every initial branch appears in the open branch returned by
`intExpandBranches`. This shows that F(φ)@0, present in the initial branch, is still
on the open countermodel branch.

Both `applyPersistenceFixpoint` and `Branch.extendMany` only prepend/append formulas,
so membership is monotone throughout the expansion. -/
private lemma intExpandBranches_openBranch_initial_mem (fuel : Nat)
    (sf : ISF Atom) :
    ∀ (branches : List (IBranch Atom))
      (expandedSets : List (List (ISF Atom)))
      (nextWorlds : List Nat)
      (edgeSets : List IEdges)
      (closurePred : IBranch Atom → Bool),
      (∀ b₀ ∈ branches, sf ∈ b₀) →
      ∀ b, intExpandBranches branches expandedSets nextWorlds edgeSets fuel closurePred
          = .openBranch b →
        sf ∈ b := by
  induction fuel with
  | zero =>
    intro branches expandedSets nextWorlds edgeSets closurePred hAll b h
    simp only [intExpandBranches] at h
    cases hfs : branches.findSome? (fun b' => if closurePred b' then none else some b') with
    | none => simp [hfs] at h
    | some b' =>
      simp only [hfs] at h; injection h with heq; subst heq
      obtain ⟨b₀, hb₀_mem, hcond⟩ := List.exists_of_findSome?_eq_some hfs
      cases heq : closurePred b₀ with
      | true => simp [heq] at hcond
      | false =>
        simp only [heq, Bool.false_eq_true, if_false, Option.some.injEq] at hcond
        exact hcond ▸ hAll b₀ hb₀_mem
  | succ fuel' ih =>
    intro branches expandedSets nextWorlds edgeSets closurePred hAll b h
    simp only [intExpandBranches] at h
    suffices key : ∀ (pending : List (IBranch Atom))
        (pendingExp : List (List (ISF Atom)))
        (pendingNW : List Nat)
        (pendingEdges : List IEdges)
        (done : List (IBranch Atom))
        (doneExp : List (List (ISF Atom)))
        (doneNW : List Nat)
        (doneEdges : List IEdges),
        (∀ bp ∈ pending, sf ∈ bp) →
        (∀ bd ∈ done, sf ∈ bd) →
        intExpandBranches.go closurePred fuel' pending pendingExp pendingNW pendingEdges
            done doneExp doneNW doneEdges = .openBranch b →
        sf ∈ b from
      key branches expandedSets nextWorlds edgeSets [] [] [] []
          (fun b₀ hb₀ => hAll b₀ hb₀) (by simp) h
    intro pending
    induction pending with
    | nil =>
      intro _ _ _ _ _ _ _ _ _ hgo
      simp only [intExpandBranches.go] at hgo
      simp at hgo
    | cons bh bt ih_inner =>
      intro pendingExp pendingNW pendingEdges done doneExp doneNW doneEdges hPend hDone hgo
      cases hpE : pendingExp with
      | nil =>
        rw [hpE] at hgo; simp only [intExpandBranches.go] at hgo
        exact ih_inner [] [] [] done doneExp doneNW doneEdges
            (fun bp hbp => hPend bp (List.mem_cons_of_mem _ hbp)) hDone hgo
      | cons eH eT =>
        cases hpNW : pendingNW with
        | nil =>
          rw [hpE, hpNW] at hgo; simp only [intExpandBranches.go] at hgo
          exact ih_inner [] [] [] done doneExp doneNW doneEdges
              (fun bp hbp => hPend bp (List.mem_cons_of_mem _ hbp)) hDone hgo
        | cons nwH nwT =>
          cases hpEdges : pendingEdges with
          | nil =>
            rw [hpE, hpNW, hpEdges] at hgo; simp only [intExpandBranches.go] at hgo
            exact ih_inner [] [] [] done doneExp doneNW doneEdges
                (fun bp hbp => hPend bp (List.mem_cons_of_mem _ hbp)) hDone hgo
          | cons edgesH edgesT =>
            rw [hpE, hpNW, hpEdges] at hgo
            set bPers := applyPersistenceFixpoint bh edgesH (fuel' + 1) with hbPers_def
            have hbh_sf : sf ∈ bh := hPend bh List.mem_cons_self
            have hbPers_sf : sf ∈ bPers :=
              applyPersistenceFixpoint_mem_preserved bh edgesH (fuel' + 1) sf hbh_sf
            simp only [intExpandBranches.go] at hgo
            by_cases hcl : closurePred bPers = true
            · rw [if_pos hcl] at hgo
              exact ih_inner eT nwT edgesT
                  (done ++ [bPers]) (doneExp ++ [eH]) (doneNW ++ [nwH]) (doneEdges ++ [edgesH])
                  (fun bp hbp => hPend bp (List.mem_cons_of_mem _ hbp))
                  (by intro bd hbd
                      simp only [List.mem_append, List.mem_singleton] at hbd
                      rcases hbd with h1 | rfl
                      · exact hDone bd h1
                      · exact hbPers_sf)
                  hgo
            · simp only [Bool.not_eq_true] at hcl
              rw [if_neg (by simp [← hbPers_def, hcl])] at hgo
              cases hstep : intStepBranch bPers eH nwH with
              | none =>
                rw [hstep] at hgo; injection hgo with heq; subst heq; exact hbPers_sf
              | some step =>
                obtain ⟨result, newExp⟩ := step
                rw [hstep] at hgo
                cases result with
                | linearResult newForms nw' newEdge =>
                  simp only at hgo
                  refine ih _ _ _ _ _ ?_ b hgo
                  intro b₀ hb₀
                  simp only [List.mem_append, List.mem_singleton] at hb₀
                  rcases hb₀ with ((hd | rfl) | hbt)
                  · exact hDone b₀ hd
                  · simp only [Branch.extendMany, List.mem_append]; exact Or.inr hbPers_sf
                  · exact hPend b₀ (List.mem_cons_of_mem _ hbt)
                | branchingResult branches' nw' =>
                  simp only at hgo
                  refine ih _ _ _ _ _ ?_ b hgo
                  intro b₀ hb₀
                  simp only [List.mem_append, List.mem_map] at hb₀
                  rcases hb₀ with ((hd | ⟨x, _, rfl⟩) | hbt)
                  · exact hDone b₀ hd
                  · simp only [Branch.extendMany, List.mem_append]; exact Or.inr hbPers_sf
                  · exact hPend b₀ (List.mem_cons_of_mem _ hbt)
                | notApplicable =>
                  simp only at hgo; injection hgo with heq; subst heq; exact hbPers_sf

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
  have hopen : S.closurePred b = false :=
    intExpandBranches_openBranch_closed _ _ _ _ _ _ _ h
  have hFmem : b.any (fun sf => sf.sign == .neg && sf.formula == φ && sf.label == 0) := by
    have hmem : (⟨.neg, φ, 0⟩ : ISF Atom) ∈ b :=
      intExpandBranches_openBranch_initial_mem _ _ _ _ _ _ _
          (fun b₀ hb₀ => by
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb₀
              subst hb₀
              exact List.mem_cons_self)
          b h
    exact List.any_eq_true.mpr ⟨_, hmem, by simp⟩
  -- Obtain saturation witness from the expansion structure.
  have hsat : IBranchSaturation Atom b :=
    intExpandBranches_openBranch_sat _ _ _ _ _ _ _ h
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
