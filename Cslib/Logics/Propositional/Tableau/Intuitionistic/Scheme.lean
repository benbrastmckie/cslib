/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
import Cslib.Foundations.Logic.Tableau.Measure
import Mathlib.Tactic.Ring
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
the parametric truth lemma in `Scheme.lean`.

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

These conditions are established structurally by `intExpandBranches_openBranch_sat`
(pending) via induction on the expansion loop. The key step: `intStepBranch b e nw = none`
implies every compound formula in `b` is in `e`, and formulas in `e` had their rule outputs
added to an ancestor branch; branch monotonicity carries them forward to `b`.

Note on `sat_fimp`: the numeric ordering conjunct `w ≤ w'` was dropped (see the field's own
doc comment for the D8 rationale). It was a raw-`Nat` proxy for accessibility, sound only under
descendant-directed world creation where labels increase monotonically; under ancestor-directed
blocking the witness `w'` can carry a *smaller* label than `w`. The genuine accessibility
content — that the witness is reachable from `w` — is carried in strictly stronger form by
`IFimpAccess`, which the F-imp case of `truthLemma` reads from directly. -/
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
  /-- F(φ→ψ)@w ∈ b → ∃ w', T(φ)@w' ∈ b ∧ F(ψ)@w' ∈ b (world-creating rule). The numeric
  ordering conjunct `w ≤ w'` is dropped (D8): it was a raw-`Nat` proxy for accessibility that
  held only because the original descendant-directed expansion assigned strictly increasing
  world labels. Under ancestor-directed blocking the reuse witness can sit at a *smaller* label
  than `w`, so the conjunct is false in general — and it is never consumed downstream (verified:
  `truthLemma`'s F-imp case reads its witness from `IFimpAccess`, never from this field), so
  dropping it loses no content. -/
  sat_fimp : ∀ (φ ψ : Proposition Atom) (w : Nat),
      b.any (fun sf => sf.sign == .neg && sf.formula == .imp φ ψ && sf.label == w) = true →
      ∃ (w' : Nat),
        b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w') = true ∧
        b.any (fun sf => sf.sign == .neg && sf.formula == ψ && sf.label == w') = true
  /-- T(φ→ψ)@w ∈ b → F(φ)@w ∈ b ∨ T(ψ)@w ∈ b (Fitting Ch. 4 split, beta-rule, reflexive at the
  same world `w` this copy of T(φ→ψ) is labeled at — realized by `intApplyRuleFull`'s `.pos, .imp`
  branching arm, `Rules.lean:274-275`). -/
  sat_timp : ∀ (φ ψ : Proposition Atom) (w : Nat),
      b.any (fun sf => sf.sign == .pos && sf.formula == .imp φ ψ && sf.label == w) = true →
      b.any (fun sf => sf.sign == .neg && sf.formula == φ && sf.label == w) = true ∨
      b.any (fun sf => sf.sign == .pos && sf.formula == ψ && sf.label == w) = true

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
        (intFuel φ) S.closurePred = .closed) :
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

/-! ## Edge-Accessibility Preorder

`isAccessible edges` (`Rules.lean:87-102`) already computes multi-hop reachability over the
parent-child `edges` list (a fuel-bounded DFS). Rather than re-proving `isAccessible` itself is
transitive (a nontrivial graph-reachability fact about its fuel-bounded implementation), the
completeness frame is defined as `Relation.ReflTransGen (isAccessible edges · · = true)`:
Mathlib's reflexive-transitive closure of `isAccessible edges` treated as a base step relation.
This is sound regardless of whether `isAccessible edges` is "already" transitive (it gives AT
LEAST as much accessibility as needed, and `Relation.ReflTransGen.single` lifts any ONE
`isAccessible edges w w' = true` fact — which is all `sat_fimp`/`sat_timp` witnesses ever
supply — directly into the closure). This replaces the ambient numeric `≤` (a known finding:
the ambient `(ℕ,≤)` frame admits "phantom" worlds not on the branch, falsifying the T(→)
truth-lemma case; edge-reachability restricts `≤` to worlds the expansion actually
constructed). -/

/-- The edge-accessibility `Preorder Nat` for a fixed edge set: `w ≤ w'` iff `w'` is reachable
from `w` via the reflexive-transitive closure of `isAccessible edges`. This is the completeness
countermodel's frame, installed locally (via `letI`/an explicit instance argument at use sites)
rather than as a global instance, since `Preorder Nat` varies per branch's edge set. -/
@[reducible] def intAccessPreorder (edges : IEdges) : Preorder Nat where
  le w w' := Relation.ReflTransGen (fun x y => isAccessible edges x y = true) w w'
  lt w w' := Relation.ReflTransGen (fun x y => isAccessible edges x y = true) w w' ∧
    ¬ Relation.ReflTransGen (fun x y => isAccessible edges x y = true) w' w
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  lt_iff_le_not_ge _ _ := Iff.rfl

/-- Any direct `isAccessible` fact lifts into the `intAccessPreorder` order. This is the
single bridging fact `sat_fimp`/`sat_timp` witnesses need: both only ever supply a raw
`isAccessible edges w w' = true` fact (never an explicit multi-hop chain), and this lemma
lifts it to the `Preorder`'s `≤` directly via `Relation.ReflTransGen.single`. -/
lemma intAccessPreorder_le_of_isAccessible {edges : IEdges} {w w' : Nat}
    (h : isAccessible edges w w' = true) :
    @LE.le Nat (intAccessPreorder edges).toLE w w' :=
  Relation.ReflTransGen.single h

/-! ### Edge-list monotonicity

The expansion loop only ever APPENDS to `edges` (world-creation adds one parent-child pair;
persistence/alpha/beta steps leave it unchanged), so any accessibility fact established at an
earlier step must survive as `edges` grows into the final accumulated list. These two lemmas
supply that survival fact: `isAccessible_one_step` (mirrors the identically-named private
lemma in `Soundness.lean`, re-derived here since `private` declarations are file-local) gives
a direct edge its one-hop accessibility; `isAccessible_append_mono` shows appending a new edge
never loses an existing accessibility witness (the DFS's candidate-children list and fuel
bound can only grow). Together with `Relation.ReflTransGen.mono`, these let
`intAccessPreorder`-accessibility survive edge-list growth without needing to touch
`Soundness.lean`'s (read-only) internal machinery. -/

/-- A direct parent-child edge `(w', w) ∈ edges` gives one-hop accessibility `w ⤳ w'`. -/
private lemma isAccessible_one_step {edges : IEdges} {w w' : Nat}
    (hmem : (w', w) ∈ edges) : isAccessible edges w w' = true := by
  simp only [isAccessible]
  by_cases heq : w == w'
  · simp [heq]
  · simp only [heq, Bool.false_eq_true, ite_false]
    have hne : edges ≠ [] := List.ne_nil_of_mem hmem
    have hpos : 0 < edges.length := by rwa [List.length_pos_iff_ne_nil]
    cases hn : edges.length with
    | zero => omega
    | succ m =>
      rw [isAccessible.go, List.any_eq_true]
      exact ⟨w', by simp only [List.mem_filterMap]; exact ⟨(w', w), hmem, by simp⟩, by simp⟩

/-- `isAccessible.go` is monotone under appending a new edge: any reachability witness found
using `edges` survives when `edges` grows to `edges ++ [newEdge]` (the DFS's per-step
candidate-children list can only gain entries, never lose them). -/
private lemma isAccessible_go_append_mono
    (edges : IEdges) (newEdge : Nat × Nat) (target : Nat) :
    ∀ (current fuel : Nat), isAccessible.go edges target current fuel = true →
      isAccessible.go (edges ++ [newEdge]) target current fuel = true := by
  intro current fuel
  induction fuel generalizing current with
  | zero => simp [isAccessible.go]
  | succ k ih =>
    simp only [isAccessible.go]
    intro h
    rw [List.any_eq_true] at h ⊢
    obtain ⟨child, hchild, hcond⟩ := h
    simp only [List.mem_filterMap] at hchild
    obtain ⟨⟨c, p⟩, hedges, hfilt⟩ := hchild
    by_cases hp : p == current
    · simp only [hp, ite_true, Option.some.injEq] at hfilt
      refine ⟨child, ?_, ?_⟩
      · simp only [List.mem_filterMap]
        refine ⟨(c, p), List.mem_append_left _ hedges, ?_⟩
        simp [hp, hfilt]
      · by_cases hce : child == target
        · simp [hce]
        · simp only [hce, Bool.false_eq_true, ite_false] at hcond ⊢
          exact ih child hcond
    · simp only [Bool.not_eq_true] at hp
      simp [hp] at hfilt

/-- `isAccessible.go` is monotone in its fuel argument: extra fuel never turns a `true`
result into `false` (the DFS just has slack left over). -/
private lemma isAccessible_go_fuel_mono
    (edges : IEdges) (target : Nat) :
    ∀ (current fuel : Nat), isAccessible.go edges target current fuel = true →
      isAccessible.go edges target current (fuel + 1) = true := by
  intro current fuel
  induction fuel generalizing current with
  | zero => simp [isAccessible.go]
  | succ k ih =>
    simp only [isAccessible.go]
    intro h
    rw [List.any_eq_true] at h ⊢
    obtain ⟨child, hchild, hcond⟩ := h
    refine ⟨child, hchild, ?_⟩
    by_cases hce : child == target
    · simp [hce]
    · simp only [hce, Bool.false_eq_true, ite_false] at hcond ⊢
      exact ih child hcond

/-- `isAccessible` is monotone under appending a new edge (the top-level wrapper combining
`isAccessible_go_append_mono` with `isAccessible_go_fuel_mono`, since `isAccessible`'s fuel
bound `edges.length` also grows by one when a new edge is appended; also handles the
`w == w'` short-circuit case). -/
private lemma isAccessible_append_mono {edges : IEdges} (newEdge : Nat × Nat) {w w' : Nat}
    (h : isAccessible edges w w' = true) :
    isAccessible (edges ++ [newEdge]) w w' = true := by
  simp only [isAccessible] at h ⊢
  by_cases heq : w == w'
  · simp [heq]
  · simp only [heq, Bool.false_eq_true, ite_false] at h ⊢
    have h1 := isAccessible_go_append_mono edges newEdge w' w edges.length h
    have h2 := isAccessible_go_fuel_mono (edges ++ [newEdge]) w' w edges.length h1
    simpa [List.length_append] using h2

/-- `intAccessPreorder`'s `≤` is monotone under appending a new edge: any accessibility fact
established relative to `edges` remains true relative to `edges ++ [newEdge]`. Lifts
`isAccessible_append_mono` through `Relation.ReflTransGen.mono`. -/
lemma intAccessPreorder_mono_append {edges : IEdges} (newEdge : Nat × Nat) {w w' : Nat}
    (h : @LE.le Nat (intAccessPreorder edges).toLE w w') :
    @LE.le Nat (intAccessPreorder (edges ++ [newEdge])).toLE w w' :=
  Relation.ReflTransGen.mono (fun _ _ hxy => isAccessible_append_mono newEdge hxy) _ _ h

/-- The final edge-accessibility payoff: every `F(φ→ψ)@w` on the
saturated branch `b` has a genuinely edge-accessible witness under `edges`, upgrading
`sat_fimp`'s numeric proxy to the real `intAccessPreorder` frame. Declared early (ahead of
the invariant-threading machinery below) since `truthLemma` consumes it directly. NOT
`private`: it appears in the public `truthLemma`/`openBranch_countermodel` signatures, and a
`private` declaration cannot appear in a `public` lemma's stated type in this module. -/
def IFimpAccess (edges : IEdges) (b : IBranch Atom) : Prop :=
  ∀ (φ ψ : Proposition Atom) (w : Nat),
    b.any (fun sf => sf.sign == .neg && sf.formula == .imp φ ψ && sf.label == w) = true →
    ∃ w' : Nat, isAccessible edges w w' = true ∧
      b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w') = true ∧
      b.any (fun sf => sf.sign == .neg && sf.formula == ψ && sf.label == w') = true

/-! ### `intExtractValuation` monotonicity — STOP-gate finding

**Blocker (documented, not a `sorry`; no lemma is stated below).** The remaining monotonicity
task —
"prove `intExtractValuation` monotone along `intAccessPreorder edges`" (needed both for a
genuine `KripkeModel.v_upward_closed` field AND for instantiating `IValid`'s
`∀{w w'} p, w≤w' → val w p → val w' p` hypothesis, `Kripke.lean:145-148`, which is exactly the
`sorry` at `Completeness.lean:113`/`Minimal/Completeness.lean:110`) is **entangled with the B2
fuel-sufficiency argument, not completable from completeness-side machinery alone**.

Evidence (verified against source, not assumed):
- `intApplyRuleFull` (`Rules.lean:245-268`) maps EVERY `.pos, .imp` signed formula (i.e. every
  `T(φ→ψ)`) to `.notApplicable` — `T(φ→ψ)` is NEVER processed by `intStepBranch`. It is handled
  EXCLUSIVELY by `applyPersistenceFixpoint`/`applyAllTImpRules` (`Expansion.lean:118-139`), run
  BEFORE each `intStepBranch` check, bounded by a fuel parameter (`fuel'+1`, the OUTER
  expansion's remaining fuel budget at that step).
- Consequently `intStepBranch b e nw = none` (the "none leaf" structural fact used to produce
  the FINAL returned branch, `intExpandBranches_openBranch_sat`'s only saturation witness)
  provides NO guarantee that `applyPersistenceFixpoint` reached a TRUE fixpoint of
  `applyAllTImpRules` — only that no alpha/beta/world-creation rule remains applicable.
- `T(atom p)@w` monotonicity along edges requires, for `T(atom p)` introduced via a
  `T(φ→atom p)`-triggered `intTImpRule` application at an accessible descendant, that the
  ANTECEDENT `φ`'s OWN monotonicity has ALREADY propagated to that descendant — a
  co-inductive dependency on formula complexity resolved only by REPEATED
  `applyPersistenceFixpoint` passes, i.e. by fuel. This is not a completeness-side gap fixable
  by a `Soundness.lean` edit (Postmortem 4 does not apply); it is a genuine WAVE-ORDERING
  inversion: the monotonicity task (Wave 2) becomes logically dependent on the
  `intExpMeasure`/fuel-sufficiency machinery (Wave 6), which does not exist yet.

**What IS complete and unconditionally true** (committed above, `lake build` green,
zero new sorries): `intAccessPreorder` (a genuine `Preorder Nat` from edge-reachability, via
`Relation.ReflTransGen (isAccessible edges · · = true)`, sidestepping the need to prove
`isAccessible` itself transitive) and `intAccessPreorder_le_of_isAccessible` (lifting any raw
`sat_fimp`/future-`sat_timp` witness into that order). `sat_fimp`'s numeric `w ≤ w'` clause
(R8) is UNCHANGED here per the plan's own allowance ("or note it will be restated over the edge
relation in Phase 4") — deferred to the edge-relation restatement, not a monotonicity-task
blocker.

**Recommendation for continuation**: either (a) reorder so Phase 2's monotonicity discharge is
FOLDED INTO Phase 10 (mirroring R3's own anticipated fold for `sat_timp`'s succ-case, generalized
to Phase 2's atom-monotonicity too — i.e. state monotonicity as a NEW field/hypothesis threaded
alongside `sat_timp`, discharged only once `measure ≤ fuel` is available), or (b) have the
orchestrator re-plan Phase 2/4/10's dependency edges to reflect this inversion before further
dispatch. Do NOT attempt to force monotonicity via a weakened/vacuous statement or a `sorry`. -/

/-! ## Blocking-Quotient Frame (task 574, Phase 5)

`intFImpReuseWitnessAnc?`'s ancestor-directed reuse (Phase 3/4) lets an `F(φ→ψ)@l`
obligation be discharged by an ancestor `x` (`x < l`, `isAccessible edges x l`) that already
carries `T(φ)@x` and an explicit `F(ψ)@x` entry, instead of by a freshly-created descendant
`w' ≥ l`. `sfSatisfied`'s `.neg, .imp` clause and `sfAccessSat`'s `.neg, .imp` clause both
demand a witness in the DESCENDANT direction (`l ≤ w'`, `isAccessible edges l w'`), so an
ancestor witness cannot discharge them directly — this is D5 of the task's implementation
plan (`specs/574_tableau_calculus_repair_ancestor_blocking/plans/`).

This section builds the **blocking-quotient frame**: identify every blocked world `l` with
its blocking ancestor `x` under a representative map `rep`, so `rep l = rep x` makes the
reversed conjuncts hold **reflexively** on the quotient. The construction follows the
filtration method of [ChagrovZakharyaschev1997] Part II §5.3 (`p02_kripke-semantics.md`
lines 397-463, Theorem 5.23 and surrounding discussion): points of
a model are grouped into equivalence classes `[x]`, and the quotient's accessibility relation
is built from the (transitive closure of the) finest filtration relation `S`, where `[x]S[y]`
holds whenever the original points satisfy `xRy` (`p02_kripke-semantics.md:409`, condition
(iii)) — read `intBlockRep` as computing the equivalence-class representative and
`intAccessPreorderQ` (5.2, below) as the `rep`-pulled-back accessibility relation, mirroring
the theorem's own use of the transitive closure `S_` (`p02_kripke-semantics.md:445-457`) to
obtain a well-behaved quotient order — `intAccessPreorder` is already exactly that closure
over `isAccessible`. `GargGenoveseNegri2012`/`Fitting1983` remain cited only as design
provenance for the underlying ancestor-directed blocking check itself (see
`intFImpReuseWitnessAnc?`'s docstring and the plan's H3 honesty rule); this quotient
construction is grounded in the one readable source, `ChagrovZakharyaschev1997`. -/

/-! ### 5.1 — The blocking-ancestor representative map -/

omit [Hashable Atom] in
/-- The `F(φ→ψ)` obligation (if any) recorded at label `w` on `b`, read off directly as a
`(φ, ψ)` pair. `none` when `w` carries no `.neg`-signed implication. -/
def negImpAt (b : IBranch Atom) (w : Nat) :
    Option (Proposition Atom × Proposition Atom) :=
  b.findSome? fun sf =>
    if sf.sign == .neg && sf.label == w then
      match sf.formula with
      | .imp φ ψ => some (φ, ψ)
      | _ => none
    else none

omit [Hashable Atom] in
/-- One step of the blocking-ancestor search: if `b` carries an `F(φ→ψ)@w` formula
(`negImpAt`), look for a STRICTLY smaller-labeled ancestor `x < w` (accessible *to* `w`,
`isAccessible edges x w`) whose forced-set already contains `φ` and lacks `ψ`, with an
explicit `F(ψ)@x` entry (Option-A, never merely "not forced"). This is the same
`Sfor`-containment test `intFImpReuseWitnessAnc?` performs during expansion
(`Expansion.lean:260-284`), replayed post hoc against the finished branch's own `F(φ→ψ)@w`
entry rather than against a would-be fresh world's `newForms` — so `intBlockRep` and
`intFImpReuseWitnessAnc?` agree by construction: the label `w` that a reuse event never
assigned a fresh child to is exactly the label whose `F(φ→ψ)` this step re-discharges against
the same ancestor `x`. Returns `none` when `w` carries no `F(→)` formula, or when no ancestor
discharges the one it carries (a fresh world was genuinely created at `w`). -/
def intBlockRepStep (b : IBranch Atom) (edges : IEdges) (w : Nat) : Option Nat :=
  match negImpAt b w with
  | none => none
  | some φψ =>
    let candidates := (b.map (·.label)).eraseDups
    candidates.findSome? fun x =>
      if x < w
          && isAccessible edges x w
          && (posFormulasAt b x).contains φψ.1
          && !(posFormulasAt b x).contains φψ.2
          && b.any (fun y => y.sign == .neg && y.formula == φψ.2 && y.label == x) then
        some x
      else none

omit [Hashable Atom] in
/-- `intBlockRepStep` only ever returns a STRICTLY smaller label than its input — the
termination measure for `intBlockRep`'s well-founded recursion below. -/
lemma intBlockRepStep_lt {b : IBranch Atom} {edges : IEdges} {w x : Nat}
    (h : intBlockRepStep b edges w = some x) : x < w := by
  unfold intBlockRepStep at h
  cases hn : negImpAt b w with
  | none => rw [hn] at h; simp at h
  | some φψ =>
    rw [hn] at h
    obtain ⟨x', _hx'mem, hif⟩ := List.exists_of_findSome?_eq_some h
    by_cases hcond : (x' < w && isAccessible edges x' w
        && (posFormulasAt b x').contains φψ.1 && !(posFormulasAt b x').contains φψ.2
        && b.any (fun y => y.sign == .neg && y.formula == φψ.2 && y.label == x')) = true
    · simp only [hcond, if_true] at hif
      injection hif with hif; subst hif
      simp only [Bool.and_eq_true] at hcond
      obtain ⟨⟨⟨⟨h1, _h2⟩, _h3⟩, _h4⟩, _h5⟩ := hcond
      exact of_decide_eq_true h1
    · simp only [Bool.not_eq_true] at hcond
      simp only [hcond] at hif
      simp at hif

/-- The blocking-ancestor representative: `intBlockRep b edges w` chases `intBlockRepStep`
to a fixed point — a world no longer subject to further blocking — returning `w` itself when
no blocking applies at all. Well-founded on `intBlockRepStep_lt`'s strict label decrease.
Iterating to a fixed point (rather than stopping after one step) is what makes `rep` a genuine
representative map (`intBlockRep_idempotent` below): it sends every world to the canonical
member of its blocking-equivalence class, matching the filtration method's
representative-per-class role ([ChagrovZakharyaschev1997] §5.3). -/
def intBlockRep (b : IBranch Atom) (edges : IEdges) : Nat → Nat
  | w =>
    match h : intBlockRepStep b edges w with
    | none => w
    | some x => intBlockRep b edges x
termination_by w => w
decreasing_by exact intBlockRepStep_lt h

omit [Hashable Atom] in
/-- Unfolding equation for `intBlockRep` at a fixed point (`intBlockRepStep` returns `none`):
`intBlockRep` returns the world itself. -/
lemma intBlockRep_eq_none {b : IBranch Atom} {edges : IEdges} {w : Nat}
    (h : intBlockRepStep b edges w = none) : intBlockRep b edges w = w := by
  rw [intBlockRep, h]

omit [Hashable Atom] in
/-- Unfolding equation for `intBlockRep` at a blocking step (`intBlockRepStep` returns
`some x`): `intBlockRep` recurses on the ancestor `x`. -/
lemma intBlockRep_eq_some {b : IBranch Atom} {edges : IEdges} {w x : Nat}
    (h : intBlockRepStep b edges w = some x) :
    intBlockRep b edges w = intBlockRep b edges x := by
  rw [intBlockRep, h]

omit [Hashable Atom] in
/-- `intBlockRep` never increases a world's label: ancestors carry strictly smaller labels
(`intBlockRepStep_lt`), and this survives the chase-to-fixed-point closure. -/
lemma intBlockRep_le (b : IBranch Atom) (edges : IEdges) (w : Nat) :
    intBlockRep b edges w ≤ w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    cases h : intBlockRepStep b edges w with
    | none => exact le_of_eq (intBlockRep_eq_none h)
    | some x =>
      rw [intBlockRep_eq_some h]
      exact le_trans (ih x (intBlockRepStep_lt h)) (le_of_lt (intBlockRepStep_lt h))

omit [Hashable Atom] in
/-- `intBlockRep` is idempotent: re-applying it to its own output is a no-op. This is the
representative-map property the quotient frame (5.2) needs — `rep` picks out one canonical
member per blocking-equivalence class, and idempotence is exactly "the representative of a
representative is itself". Follows for free from `intBlockRep`'s well-founded chase-to-a-
fixed-point definition: at the point the recursion stops (`intBlockRepStep` returns `none`),
re-running the same deterministic one-step search on that same fixed value reproduces `none`
again. -/
lemma intBlockRep_idempotent (b : IBranch Atom) (edges : IEdges) (w : Nat) :
    intBlockRep b edges (intBlockRep b edges w) = intBlockRep b edges w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    cases h : intBlockRepStep b edges w with
    | none => simp only [intBlockRep_eq_none h]
    | some x =>
      rw [intBlockRep_eq_some h]
      exact ih x (intBlockRepStep_lt h)

/-! ### 5.2 — The quotient preorder -/

/-- The `rep`-pullback of `intAccessPreorder edges`: `w ≤ w'` on the quotient iff `rep w ≤
rep w'` in the original edge-accessibility order. Mirrors `intAccessPreorder`'s own
`Relation.ReflTransGen` construction (`:318-324`) pointwise through `rep`, so the same `letI`
installation idiom works at use sites. This is the filtration method's quotient accessibility
relation ([ChagrovZakharyaschev1997] §5.3, condition (iii): `xRy` implies `[x]S[y]`) —
`intAccessPreorder` is already the reflexive-transitive closure the theorem's own construction
needs, so pulling it back through `rep` suffices without re-deriving transitivity. -/
@[reducible] def intAccessPreorderQ (edges : IEdges) (rep : Nat → Nat) : Preorder Nat where
  le w w' := Relation.ReflTransGen (fun x y => isAccessible edges x y = true) (rep w) (rep w')
  lt w w' := Relation.ReflTransGen (fun x y => isAccessible edges x y = true) (rep w) (rep w') ∧
    ¬ Relation.ReflTransGen (fun x y => isAccessible edges x y = true) (rep w') (rep w)
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  lt_iff_le_not_ge _ _ := Iff.rfl

/-- Any direct `isAccessible` fact between two worlds' representatives lifts into the
`intAccessPreorderQ` order. The Q-analogue of `intAccessPreorder_le_of_isAccessible`
(`:326-333`) — the single bridging fact every Q-level witness needs. -/
lemma intAccessPreorderQ_le_of_isAccessible {edges : IEdges} {rep : Nat → Nat} {w w' : Nat}
    (h : isAccessible edges (rep w) (rep w') = true) :
    @LE.le Nat (intAccessPreorderQ edges rep).toLE w w' :=
  Relation.ReflTransGen.single h

/-- Two worlds with the same representative are `intAccessPreorderQ`-related in BOTH
directions — reflexively, since their images under `rep` coincide. This is what makes an
ancestor witness admissible on the quotient (D5): `rep w = rep x` gives both `w ≤ x` and
`x ≤ w`. -/
lemma intAccessPreorderQ_le_of_rep_eq {edges : IEdges} {rep : Nat → Nat} {w w' : Nat}
    (h : rep w = rep w') :
    @LE.le Nat (intAccessPreorderQ edges rep).toLE w w' := by
  change Relation.ReflTransGen (fun x y => isAccessible edges x y = true) (rep w) (rep w')
  rw [h]

/-! ### `sat_timp` discharge — STOP-gate finding, UPDATED (Deliverable 6
branching-rule redesign)

**Gap 2 (determinacy) is RESOLVED as of the `.pos, .imp` branching arm added to
`intApplyRuleFull` (`Rules.lean:245-268`).** The STOP-gate below was written
against the OLD design, where `intTImpRule` was the ONLY `T(φ→ψ)` rule and only ever ADDED
`T(ψ)@w'` under `T(φ)@w' ∈ b` — never planting `F(φ)@w'`, so the needed disjunction
`F(φ)@w' ∈ b ∨ T(ψ)@w' ∈ b` was unreachable without an independent determinacy/bivalence fact
(Gap 2, below). The new design instead adds a genuine branching rule, `T(φ→ψ)@w' →
[F(φ)@w'] | [T(ψ)@w']`, firing reflexively at whatever label its own signed-formula copy
carries; `sfSatisfied`'s new `.pos, .imp` case (above `IExpandedConsistent`) states exactly this
disjunction, and `IExpandedConsistent_sat` (`:897-967`) discharges it the same mechanical way as
every other field (`sat_tand`/`sat_fand`/`sat_tor`/`sat_for_`) — via `intStepBranch b e nw = none`
plus `IExpandedConsistent b e`, **with no determinacy/bivalence argument needed at all**. This is
exactly the "restate as a branching rule" move Finding 6c / Decision D2 of the calculus-repair
task recommend, and it is now landed.

**Gap 1 (fuel entanglement) is UNCHANGED and remains the sole blocker.** The disjunction above
only holds for a world `w'` that actually carries its OWN `⟨.pos, φ → ψ, w'⟩` copy on the
branch. `applyAllTImpRules` (`Expansion.lean:118-…`) now ALSO copies `T(φ→ψ)` itself to every
world accessible from its source that lacks a copy — but this copying, like the original
`T(ψ)`-consequence propagation, runs inside `applyPersistenceFixpoint`'s fuel-bounded fixpoint
loop (`Expansion.lean:133-139`), reusing the OUTER expansion loop's remaining step-count
(`fuel'+1` at the `intExpandBranches_openBranch_sat` call site). If that fuel is exhausted
before a GENUINE fixpoint of `applyAllTImpRules` is reached, some accessible world may never
receive its copy, and the `sat_timp` disjunction is then genuinely FALSE for that world on that
specific (low-fuel) branch — not merely unproved, but false as a fact about the branch.
Establishing "fuel is always sufficient for persistence's OWN recursion to reach a genuine
fixpoint" needs a NEW step-lt-style measure lemma for `applyPersistenceFixpoint`'s recursion
(distinct from `intExpMeasure_step_lt`, which bounds the OUTER alpha/beta/world-creation loop and
says nothing about inner persistence rounds) threaded through `intExpandBranches_openBranch_sat`'s
own fuel-0 `sorry` (the SAME gap, one level up — see that lemma's docstring and in-proof note for
the current status of that obligation). This measure has not been built. Note also that the
world bound any such fuel-sufficiency measure would ultimately be sized against is itself
refuted: see the *Divergence witness* note in `Expansion.lean` (this does NOT by itself refute
Gap 1 — the witness bears on world-boundedness, not on persistence fuel-sufficiency directly —
but any future attempt at this measure must not lean on `intUniverse`'s linear world range as a
genuine invariant of produced branches).

**`sat_timp` IS an `IBranchSaturation` field** (`:105-108`), realized by `intApplyRuleFull`'s
`.pos, .imp` branching arm (`Rules.lean:245-268`, `:274-275`), which fires reflexively at the
label of the specific signed-formula copy it is given. No converse of the induction hypothesis
is needed to use it: in `truthLemma`'s T-imp case, the `F(φ')@w'` arm of the disjunction
contradicts `IForces val w' φ'` via `ih_φ'.2`, and the `T(ψ')@w'` arm yields the goal directly
via `ih_ψ'.1`. The case nonetheless stays `sorry`, not because `sat_timp` is missing or because
a converse is needed, but because the disjunction is only available at `w'` once `w'` carries
its own `T(φ'→ψ')` copy — Gap 1 above, which is not yet established. `intRule_preserves_sat`'s
`.pos, .imp` case (`Soundness.lean`) is already landed and sorry-free — that lemma reasons about
a real Kripke model's forcing relation directly (classical excluded middle on `IForces`), not
about branch-syntactic saturation, so it does not depend on Gap 1 at all. Recommendation for
continuation: build the persistence fuel-sufficiency measure (Gap 1) as its own effort, then
revisit `truthLemma`'s T-imp case together with `intExpandBranches_openBranch_sat`'s fuel-0
`sorry` in one pass, since both bottom out in the same missing invariant. Do NOT attempt to
force either `sorry` via a weakened/vacuous statement. -/

/-! ## Parametric Truth Lemma -/

/-- Parametric truth lemma (the single deferred completeness obligation).
Generalizes `intTruthLemma` over an `IntMinScheme`'s `closurePred`/`modelBot`.

**Infrastructure cross-reference**: The FMP routes in `Metalogic/IntDecidability.lean`
and `Metalogic/MinDecidability.lean` prove analogous "forcing ↔ membership" statements
(`int_fin_truth_lemma`, `min_fin_truth_lemma`) over finite `Σ`-bounded worlds. Those lemmas
rest on the `IntLindenbaum.lean`/minimal Lindenbaum substrate and are sorry-free. This
parametric `truthLemma` operates over Nat-labelled branch worlds (disjoint carrier type).
Factoring a common abstraction across the two carrier systems is explicitly deferred; see
the module headers in `Metalogic/IntDecidability.lean` and `Metalogic/MinDecidability.lean`
for the full rationale.

**Route (a) frame**: the completeness countermodel's `[Preorder Nat]`
instance is `intAccessPreorder edges` (edge-reachability over the branch's accumulated
parent-child edges), installed locally via `letI` (per `intAccessPreorder`'s own docstring),
NOT the ambient global `Nat` order — the latter admits "phantom" worlds not on the branch,
falsifying the T(→) case. `hfimp : IFimpAccess edges b` upgrades `sat_fimp`'s
witness from the numeric `w ≤ w'` proxy to a genuine `isAccessible edges w w'` fact, which
the F-imp case below needs to instantiate `IForces_imp`'s `∀ w', w ≤ w' → …` over this frame. -/
lemma truthLemma (S : IntMinScheme Atom) (b : IBranch Atom) (edges : IEdges)
    (hopen : S.closurePred b = false)
    (hsat : IBranchSaturation Atom b)
    (hfimp : IFimpAccess edges b)
    (φ : Proposition Atom) (w : Nat) :
    letI : Preorder Nat := intAccessPreorder edges
    (b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w) →
      IForces (intExtractValuation b) (S.modelBot b) w φ) ∧
    (b.any (fun sf => sf.sign == .neg && sf.formula == φ && sf.label == w) →
      ¬ IForces (intExtractValuation b) (S.modelBot b) w φ) := by
  letI : Preorder Nat := intAccessPreorder edges
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
    · -- T(φ'→ψ')@w ∈ b → ∀ w' accessible from w, IForces val w' φ' → IForces val w' ψ'.
      -- `sat_timp` (a live `IBranchSaturation` field, `:105-108`) supplies exactly
      -- `∀ w' accessible from w, F(φ')@w' ∈ b ∨ T(ψ')@w' ∈ b` at any world `w'` carrying its
      -- own `T(φ'→ψ')` copy: the `F(φ')@w'` arm contradicts `IForces val w' φ'` via `ih_φ'.2`,
      -- and the `T(ψ')@w'` arm yields the goal via `ih_ψ'.1` -- see the updated
      -- "`sat_timp` discharge" STOP-gate note above this lemma. What remains, UNCHANGED, is
      -- Gap 1: the disjunction is only available at `w'` once `w'` actually carries its own
      -- `T(φ'→ψ')` copy, which `applyAllTImpRules`'s copy-propagation only guarantees at a
      -- GENUINE fixpoint of the fuel-bounded persistence loop -- an invariant not yet built
      -- (see the STOP-gate note for the exact call-site analysis). This case stays `sorry`
      -- because that copy-propagation invariant is not established, not because `sat_timp` is
      -- missing or because a converse of the induction hypothesis is needed.
      intro _
      sorry
    · -- F(φ'→ψ')@w ∈ b → ¬∀ w' accessible from w, IForces val w' φ' → IForces val w' ψ'.
      -- hfimp (Route (a)) witnesses a genuinely edge-accessible w' with
      -- T(φ')@w', F(ψ')@w'; lift to the `intAccessPreorder` order, IH closes each
      -- membership-to-forcing step.
      intro h hcontra
      obtain ⟨w', hacc, ht_φ', hf_ψ'⟩ := hfimp φ' ψ' w h
      exact (ih_ψ' w').2 hf_ψ'
        (hcontra w' (intAccessPreorder_le_of_isAccessible hacc) ((ih_φ' w').1 ht_φ'))
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
                  simp only at hgo
                  split at hgo <;> (try split at hgo) <;> exact ih _ _ _ _ hgo
                | branchingResult branches' nw' =>
                  simp only at hgo; exact ih _ _ _ _ hgo
                | notApplicable =>
                  simp only at hgo; injection hgo with heq; subst heq; exact hcl

/-! ## Expansion Invariant Helpers -/

/-- Output condition for a single signed formula on branch `b`: asserts that the
rule outputs are present on `b`. For non-compound formulas (atoms, T(imp), bot), the
condition is vacuously `True`. -/
private def sfSatisfied (b : IBranch Atom) (sf : ISF Atom) : Prop :=
  match sf.sign, sf.formula with
  | .pos, .and φ ψ =>
    b.any (fun x => x.sign == .pos && x.formula == φ && x.label == sf.label) = true ∧
    b.any (fun x => x.sign == .pos && x.formula == ψ && x.label == sf.label) = true
  | .neg, .and φ ψ =>
    b.any (fun x => x.sign == .neg && x.formula == φ && x.label == sf.label) = true ∨
    b.any (fun x => x.sign == .neg && x.formula == ψ && x.label == sf.label) = true
  | .pos, .or φ ψ =>
    b.any (fun x => x.sign == .pos && x.formula == φ && x.label == sf.label) = true ∨
    b.any (fun x => x.sign == .pos && x.formula == ψ && x.label == sf.label) = true
  | .neg, .or φ ψ =>
    b.any (fun x => x.sign == .neg && x.formula == φ && x.label == sf.label) = true ∧
    b.any (fun x => x.sign == .neg && x.formula == ψ && x.label == sf.label) = true
  | .neg, .imp φ ψ =>
    ∃ w' : Nat,
      b.any (fun x => x.sign == .pos && x.formula == φ && x.label == w') = true ∧
      b.any (fun x => x.sign == .neg && x.formula == ψ && x.label == w') = true
  | .pos, .imp φ ψ =>
    -- Deliverable 6, Fitting `T(→)` split: `intApplyRuleFull`'s `.pos, .imp` branching arm
    -- resolves reflexively at `sf.label`, so the output condition is the same-label
    -- disjunction `sat_timp` needs (this is the loop-invariant analogue of `IBranchSaturation`'s
    -- `sat_timp` field added below for the global saturation certificate).
    b.any (fun x => x.sign == .neg && x.formula == φ && x.label == sf.label) = true ∨
    b.any (fun x => x.sign == .pos && x.formula == ψ && x.label == sf.label) = true
  | _, _ => True

/-- The expanded-set invariant: every formula in `e` has its rule outputs present on `b`. -/
private def IExpandedConsistent (b : IBranch Atom) (e : List (ISF Atom)) : Prop :=
  ∀ sf ∈ e, sfSatisfied b sf

/-- `List.any` is monotone under branch inclusion. -/
private lemma any_mono_sub {α : Type*} {p : α → Bool} {l l' : List α}
    (hsub : ∀ x ∈ l, x ∈ l') (h : l.any p = true) : l'.any p = true := by
  rw [List.any_eq_true] at h ⊢
  obtain ⟨x, hx, hpx⟩ := h
  exact ⟨x, hsub x hx, hpx⟩

omit [Hashable Atom] in
/-- `sfSatisfied` is monotone under branch inclusion: if outputs are in `b`, they are in `b'`
whenever `b ⊆ b'`. -/
private lemma sfSatisfied_mono {b b' : IBranch Atom} {sf : ISF Atom}
    (hmono : ∀ x ∈ b, x ∈ b') (h : sfSatisfied b sf) : sfSatisfied b' sf := by
  simp only [sfSatisfied] at *
  rcases sf with ⟨s, f, l⟩
  cases s <;> cases f <;> simp only [] at * <;>
    first
    | exact h
    | exact ⟨any_mono_sub hmono h.1, any_mono_sub hmono h.2⟩
    | (rcases h with h | h
       · exact Or.inl (any_mono_sub hmono h)
       · exact Or.inr (any_mono_sub hmono h))
    | (obtain ⟨w', h1, h2⟩ := h
       exact ⟨w', any_mono_sub hmono h1, any_mono_sub hmono h2⟩)

omit [Hashable Atom] in
/-- `IExpandedConsistent` is monotone under branch inclusion. -/
private lemma IExpandedConsistent_mono {b b' : IBranch Atom} {e : List (ISF Atom)}
    (hmono : ∀ x ∈ b, x ∈ b') (h : IExpandedConsistent b e) : IExpandedConsistent b' e :=
  fun sf hsfin => sfSatisfied_mono hmono (h sf hsfin)

/-! ### Edge-accessibility companion invariant (Route (a))

`sfSatisfied`'s `.neg, .imp` clause records the numeric proxy `sf.label ≤ w'`. The "kept
as-is — no reformulation, per the Preserved Assets table" directive this note used to state is
now SUPERSEDED by task 574's Phase 5: `sfSatisfiedQ`/`sfAccessSatQ` (defined further below,
after `IExpandedAccessConsistent`'s block) restate that proxy over a representative map `rep`
(`rep sf.label ≤ rep w'` / `isAccessible edges (rep sf.label) (rep w')`), landed ADDITIVELY
alongside the originals — neither `sfSatisfied` nor `sfAccessSat` is modified in place, and
`grep -c IBranchSaturation Soundness.lean` stays `0` throughout (the spike's H2 evidence).

This still leaves the "phantom worlds" gap this note originally flagged: the plain (non-Q)
proxy is NOT strong enough to instantiate `truthLemma`'s F-imp case over `intAccessPreorder
edges` (which needs genuine edge-reachability of the witness, not merely a numeric bound).
`sfAccessSat`/`IExpandedAccessConsistent` remains the companion invariant threaded ALONGSIDE
`sfSatisfied`/`IExpandedConsistent` for that upgrade. The D5 rationale (Phase 5) is that an
ANCESTOR witness — reachable in the REVERSE direction from what these two demand — is made
admissible not by editing these definitions in place, but by rep-identifying the blocked world
with its blocking ancestor (`intBlockRep`) so the Q-restated clauses hold reflexively via
`intAccessPreorderQ_le_of_rep_eq`. Both the fresh-world-creation site (`intFImpRule`'s new edge
`(w', w)`, one-hop via `isAccessible_one_step`) and the Option-A dedup reuse site
(`intFImpReuseWitnessAnc?_spec`'s `isAccessible` conjunct) already establish the underlying
fact at construction time; this invariant (and its Q-restatement) only threads it forward. -/

/-- The `.neg, .imp` edge-accessibility obligation: vacuously `True` for every other
sign/formula pair (mirrors `sfSatisfied`'s shape, restricted to the one case that needs
upgrading). -/
private def sfAccessSat (edges : IEdges) (b : IBranch Atom) (sf : ISF Atom) : Prop :=
  match sf.sign, sf.formula with
  | .neg, .imp φ ψ =>
    ∃ w' : Nat, isAccessible edges sf.label w' = true ∧
      b.any (fun x => x.sign == .pos && x.formula == φ && x.label == w') = true ∧
      b.any (fun x => x.sign == .neg && x.formula == ψ && x.label == w') = true
  | _, _ => True

/-- The edge-accessibility companion of `IExpandedConsistent`: every formula in `e` has its
F(φ→ψ) witness (if any) genuinely edge-accessible under `edges`. -/
private def IExpandedAccessConsistent (edges : IEdges) (b : IBranch Atom)
    (e : List (ISF Atom)) : Prop :=
  ∀ sf ∈ e, sfAccessSat edges b sf

omit [Hashable Atom] in
/-- `sfAccessSat` is monotone under branch inclusion. -/
private lemma sfAccessSat_mono {edges : IEdges} {b b' : IBranch Atom} {sf : ISF Atom}
    (hmono : ∀ x ∈ b, x ∈ b') (h : sfAccessSat edges b sf) : sfAccessSat edges b' sf := by
  rcases sf with ⟨s, f, l⟩
  cases s <;> cases f <;> simp only [sfAccessSat] at *
  first
  | exact h
  | (obtain ⟨w', hacc, h1, h2⟩ := h
     exact ⟨w', hacc, any_mono_sub hmono h1, any_mono_sub hmono h2⟩)

omit [Hashable Atom] in
/-- `sfAccessSat` is monotone under appending a new edge to `edges` (the accessibility
witness survives, per `isAccessible_append_mono`). -/
private lemma sfAccessSat_edges_mono {edges : IEdges} (newEdge : Nat × Nat) {b : IBranch Atom}
    {sf : ISF Atom} (h : sfAccessSat edges b sf) : sfAccessSat (edges ++ [newEdge]) b sf := by
  rcases sf with ⟨s, f, l⟩
  cases s <;> cases f <;> simp only [sfAccessSat] at *
  first
  | exact h
  | (obtain ⟨w', hacc, h1, h2⟩ := h
     exact ⟨w', isAccessible_append_mono newEdge hacc, h1, h2⟩)

omit [Hashable Atom] in
/-- `IExpandedAccessConsistent` is monotone under branch inclusion. -/
private lemma IExpandedAccessConsistent_mono {edges : IEdges} {b b' : IBranch Atom}
    {e : List (ISF Atom)} (hmono : ∀ x ∈ b, x ∈ b')
    (h : IExpandedAccessConsistent edges b e) : IExpandedAccessConsistent edges b' e :=
  fun sf hsfin => sfAccessSat_mono hmono (h sf hsfin)

omit [Hashable Atom] in
/-- `IExpandedAccessConsistent` is monotone under appending a new edge. -/
private lemma IExpandedAccessConsistent_edges_mono {edges : IEdges} (newEdge : Nat × Nat)
    {b : IBranch Atom} {e : List (ISF Atom)}
    (h : IExpandedAccessConsistent edges b e) :
    IExpandedAccessConsistent (edges ++ [newEdge]) b e :=
  fun sf hsfin => sfAccessSat_edges_mono newEdge (h sf hsfin)

/-! ### 5.3 — Quotient-restated `sf`-level predicates -/

/-- `sfSatisfied`, restated over a representative map `rep`: identical to `sfSatisfied` in
every case EXCEPT `.neg, .imp`, where the ordering witness is required on the QUOTIENT
(`rep sf.label ≤ rep w'`) rather than on the raw numeric label order. This is what lets an
ancestor witness `x` (with `rep sf.label = rep x` per D5) discharge the obligation
reflexively via `intAccessPreorderQ_le_of_rep_eq`. The `.pos, .imp` case (Deliverable 6's
reflexive `sat_timp` split) is copied UNCHANGED — `sat_timp` is not in scope (D2). -/
private def sfSatisfiedQ (rep : Nat → Nat) (b : IBranch Atom) (sf : ISF Atom) : Prop :=
  match sf.sign, sf.formula with
  | .pos, .and φ ψ =>
    b.any (fun x => x.sign == .pos && x.formula == φ && x.label == sf.label) = true ∧
    b.any (fun x => x.sign == .pos && x.formula == ψ && x.label == sf.label) = true
  | .neg, .and φ ψ =>
    b.any (fun x => x.sign == .neg && x.formula == φ && x.label == sf.label) = true ∨
    b.any (fun x => x.sign == .neg && x.formula == ψ && x.label == sf.label) = true
  | .pos, .or φ ψ =>
    b.any (fun x => x.sign == .pos && x.formula == φ && x.label == sf.label) = true ∨
    b.any (fun x => x.sign == .pos && x.formula == ψ && x.label == sf.label) = true
  | .neg, .or φ ψ =>
    b.any (fun x => x.sign == .neg && x.formula == φ && x.label == sf.label) = true ∧
    b.any (fun x => x.sign == .neg && x.formula == ψ && x.label == sf.label) = true
  | .neg, .imp φ ψ =>
    ∃ w' : Nat, rep sf.label ≤ rep w' ∧
      b.any (fun x => x.sign == .pos && x.formula == φ && x.label == w') = true ∧
      b.any (fun x => x.sign == .neg && x.formula == ψ && x.label == w') = true
  | .pos, .imp φ ψ =>
    b.any (fun x => x.sign == .neg && x.formula == φ && x.label == sf.label) = true ∨
    b.any (fun x => x.sign == .pos && x.formula == ψ && x.label == sf.label) = true
  | _, _ => True

/-- The expanded-set invariant, restated over `rep`: every formula in `e` has its rule
outputs present on `b`, with the `.neg, .imp` witness ordered on the quotient. -/
private def IExpandedConsistentQ (rep : Nat → Nat) (b : IBranch Atom)
    (e : List (ISF Atom)) : Prop :=
  ∀ sf ∈ e, sfSatisfiedQ rep b sf

omit [Hashable Atom] in
/-- `sfSatisfiedQ` is monotone under branch inclusion. Mirrors `sfSatisfied_mono`'s proof
verbatim — the `.neg, .imp` witness's ORDER fact (`rep sf.label ≤ rep w'`) is carried through
unchanged; only the two membership facts need `any_mono_sub`. -/
private lemma sfSatisfiedQ_mono {rep : Nat → Nat} {b b' : IBranch Atom} {sf : ISF Atom}
    (hmono : ∀ x ∈ b, x ∈ b') (h : sfSatisfiedQ rep b sf) : sfSatisfiedQ rep b' sf := by
  simp only [sfSatisfiedQ] at *
  rcases sf with ⟨s, f, l⟩
  cases s <;> cases f <;> simp only [] at * <;>
    first
    | exact h
    | exact ⟨any_mono_sub hmono h.1, any_mono_sub hmono h.2⟩
    | (rcases h with h | h
       · exact Or.inl (any_mono_sub hmono h)
       · exact Or.inr (any_mono_sub hmono h))
    | (obtain ⟨w', hw', h1, h2⟩ := h
       exact ⟨w', hw', any_mono_sub hmono h1, any_mono_sub hmono h2⟩)

omit [Hashable Atom] in
/-- `IExpandedConsistentQ` is monotone under branch inclusion. -/
private lemma IExpandedConsistentQ_mono {rep : Nat → Nat} {b b' : IBranch Atom}
    {e : List (ISF Atom)} (hmono : ∀ x ∈ b, x ∈ b') (h : IExpandedConsistentQ rep b e) :
    IExpandedConsistentQ rep b' e :=
  fun sf hsfin => sfSatisfiedQ_mono hmono (h sf hsfin)

/-- `sfAccessSat`, restated over a representative map `rep`: the `.neg, .imp` edge-accessibility
witness is required between REPRESENTATIVES (`isAccessible edges (rep sf.label) (rep w')`)
rather than between the raw labels. Mirrors `sfAccessSat`'s shape exactly otherwise. -/
private def sfAccessSatQ (edges : IEdges) (rep : Nat → Nat) (b : IBranch Atom)
    (sf : ISF Atom) : Prop :=
  match sf.sign, sf.formula with
  | .neg, .imp φ ψ =>
    ∃ w' : Nat, isAccessible edges (rep sf.label) (rep w') = true ∧
      b.any (fun x => x.sign == .pos && x.formula == φ && x.label == w') = true ∧
      b.any (fun x => x.sign == .neg && x.formula == ψ && x.label == w') = true
  | _, _ => True

/-- The edge-accessibility companion of `IExpandedConsistentQ`: every formula in `e` has its
F(φ→ψ) witness (if any) genuinely edge-accessible BETWEEN REPRESENTATIVES under `edges`. -/
private def IExpandedAccessConsistentQ (edges : IEdges) (rep : Nat → Nat) (b : IBranch Atom)
    (e : List (ISF Atom)) : Prop :=
  ∀ sf ∈ e, sfAccessSatQ edges rep b sf

/-! ### 5.4 — Quotient-restated branch-level predicates -/

/-- Saturation conditions for an open intuitionistic tableau branch, restated over a
representative map `rep`: identical to `IBranchSaturation` (`:74-108`) in EVERY field except
`sat_fimp`, whose ordering witness is required on the QUOTIENT (`rep w ≤ rep w'`) rather than
on the raw label order — the D5 restatement that makes an ancestor witness admissible. The
spike prototyped this exact shape (`specs/574_.../handoffs/01_quotient-soundness-spike-decision.md`)
and confirmed it elaborates with zero diagnostics. -/
structure IBranchSaturationQ (Atom : Type*) [DecidableEq Atom] [Hashable Atom]
    (b : IBranch Atom) (rep : Nat → Nat) where
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
  /-- F(φ→ψ)@w ∈ b → ∃ w', rep w ≤ rep w' ∧ T(φ)@w' ∈ b ∧ F(ψ)@w' ∈ b (world-creating rule,
  QUOTIENT-ordered — the sole field that differs from `IBranchSaturation`). -/
  sat_fimp : ∀ (φ ψ : Proposition Atom) (w : Nat),
      b.any (fun sf => sf.sign == .neg && sf.formula == .imp φ ψ && sf.label == w) = true →
      ∃ (w' : Nat), rep w ≤ rep w' ∧
        b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w') = true ∧
        b.any (fun sf => sf.sign == .neg && sf.formula == ψ && sf.label == w') = true
  /-- T(φ→ψ)@w ∈ b → F(φ)@w ∈ b ∨ T(ψ)@w ∈ b (Fitting Ch. 4 split, reflexive at `w`; copied
  UNCHANGED from `IBranchSaturation` — `sat_timp` is not in scope, D2). -/
  sat_timp : ∀ (φ ψ : Proposition Atom) (w : Nat),
      b.any (fun sf => sf.sign == .pos && sf.formula == .imp φ ψ && sf.label == w) = true →
      b.any (fun sf => sf.sign == .neg && sf.formula == φ && sf.label == w) = true ∨
      b.any (fun sf => sf.sign == .pos && sf.formula == ψ && sf.label == w) = true

/-- The edge-accessibility payoff, restated over `rep`: every `F(φ→ψ)@w` on the saturated
branch `b` has a genuinely edge-accessible witness BETWEEN REPRESENTATIVES under `edges`.
Mirrors `IFimpAccess` (`:442-447`) with `isAccessible edges w w'` replaced by
`isAccessible edges (rep w) (rep w')`. -/
def IFimpAccessQ (edges : IEdges) (rep : Nat → Nat) (b : IBranch Atom) : Prop :=
  ∀ (φ ψ : Proposition Atom) (w : Nat),
    b.any (fun sf => sf.sign == .neg && sf.formula == .imp φ ψ && sf.label == w) = true →
    ∃ w' : Nat, isAccessible edges (rep w) (rep w') = true ∧
      b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w') = true ∧
      b.any (fun sf => sf.sign == .neg && sf.formula == ψ && sf.label == w') = true

omit [Hashable Atom] in
/-- When `intStepBranch b e nw = none` and `sf ∈ b` with `intApplyRuleFull sf nw b ≠ .notApplicable`
(i.e., `sf` is a compound formula), then `sf ∈ e`. -/
private lemma intStepBranch_none_compound_mem
    {b : IBranch Atom} {e : List (ISF Atom)} {nw : Nat}
    (hstep : intStepBranch b e nw = none)
    (sf : ISF Atom) (hsfb : sf ∈ b)
    (hcomp : intApplyRuleFull sf nw b ≠ .notApplicable) :
    sf ∈ e := by
  simp only [intStepBranch, List.findSome?_eq_none_iff] at hstep
  have hbody := hstep sf hsfb
  by_cases hany : e.any (· == sf) = true
  · simp only [List.any_eq_true, beq_iff_eq] at hany
    obtain ⟨x, hxe, rfl⟩ := hany
    exact hxe
  · rw [Bool.not_eq_true] at hany
    simp only [hany] at hbody
    cases hca : intApplyRuleFull sf nw b with
    | linearResult fs nw' edge => simp only [hca] at hbody; exact absurd hbody (by simp)
    | branchingResult brs nw' => simp only [hca] at hbody; exact absurd hbody (by simp)
    | notApplicable => exact absurd hca hcomp

/-- Given `intStepBranch b e nw = none` and `IExpandedConsistent b e`,
every saturation condition of `IBranchSaturation Atom b` holds.

This is the bridge lemma connecting the expansion invariant to the Hintikka saturation
structure required by `truthLemma`. -/
private lemma IExpandedConsistent_sat
    {b : IBranch Atom} {e : List (ISF Atom)} {nw : Nat}
    (hstep : intStepBranch b e nw = none)
    (hIC : IExpandedConsistent b e) :
    IBranchSaturation Atom b := by
  -- Helper: given a compound sf ∈ b (via any condition), return its IExpandedConsistent witness.
  have compound_sat : ∀ (sf : ISF Atom),
      sf ∈ b → intApplyRuleFull sf nw b ≠ .notApplicable → sfSatisfied b sf := by
    intro sf hsfb hcomp
    exact hIC sf (intStepBranch_none_compound_mem hstep sf hsfb hcomp)
  constructor
  · -- sat_tand: T(φ∧ψ)@w ∈ b → T(φ)@w ∈ b ∧ T(ψ)@w ∈ b
    intro φ ψ w hmem
    rw [List.any_eq_true] at hmem
    obtain ⟨sf, hsfb, hsfp⟩ := hmem
    simp only [Bool.and_eq_true, beq_iff_eq] at hsfp
    obtain ⟨⟨hs, hf⟩, hl⟩ := hsfp
    have hsfeq : sf = ⟨.pos, .and φ ψ, w⟩ := by cases sf; simp_all
    have hcomp : intApplyRuleFull sf nw b ≠ .notApplicable := by
      rw [hsfeq]; simp [intApplyRuleFull]
    have hsat := compound_sat sf hsfb hcomp
    rw [hsfeq] at hsat; simp only [sfSatisfied] at hsat
    exact hsat
  · -- sat_fand: F(φ∧ψ)@w ∈ b → F(φ)@w ∈ b ∨ F(ψ)@w ∈ b
    intro φ ψ w hmem
    rw [List.any_eq_true] at hmem
    obtain ⟨sf, hsfb, hsfp⟩ := hmem
    simp only [Bool.and_eq_true, beq_iff_eq] at hsfp
    obtain ⟨⟨hs, hf⟩, hl⟩ := hsfp
    have hsfeq : sf = ⟨.neg, .and φ ψ, w⟩ := by cases sf; simp_all
    have hcomp : intApplyRuleFull sf nw b ≠ .notApplicable := by
      rw [hsfeq]; simp [intApplyRuleFull]
    have hsat := compound_sat sf hsfb hcomp
    rw [hsfeq] at hsat; simp only [sfSatisfied] at hsat
    exact hsat
  · -- sat_tor: T(φ∨ψ)@w ∈ b → T(φ)@w ∈ b ∨ T(ψ)@w ∈ b
    intro φ ψ w hmem
    rw [List.any_eq_true] at hmem
    obtain ⟨sf, hsfb, hsfp⟩ := hmem
    simp only [Bool.and_eq_true, beq_iff_eq] at hsfp
    obtain ⟨⟨hs, hf⟩, hl⟩ := hsfp
    have hsfeq : sf = ⟨.pos, .or φ ψ, w⟩ := by cases sf; simp_all
    have hcomp : intApplyRuleFull sf nw b ≠ .notApplicable := by
      rw [hsfeq]; simp [intApplyRuleFull]
    have hsat := compound_sat sf hsfb hcomp
    rw [hsfeq] at hsat; simp only [sfSatisfied] at hsat
    exact hsat
  · -- sat_for_: F(φ∨ψ)@w ∈ b → F(φ)@w ∈ b ∧ F(ψ)@w ∈ b
    intro φ ψ w hmem
    rw [List.any_eq_true] at hmem
    obtain ⟨sf, hsfb, hsfp⟩ := hmem
    simp only [Bool.and_eq_true, beq_iff_eq] at hsfp
    obtain ⟨⟨hs, hf⟩, hl⟩ := hsfp
    have hsfeq : sf = ⟨.neg, .or φ ψ, w⟩ := by cases sf; simp_all
    have hcomp : intApplyRuleFull sf nw b ≠ .notApplicable := by
      rw [hsfeq]; simp [intApplyRuleFull]
    have hsat := compound_sat sf hsfb hcomp
    rw [hsfeq] at hsat; simp only [sfSatisfied] at hsat
    exact hsat
  · -- sat_fimp: F(φ→ψ)@w ∈ b → ∃ w' ≥ w, T(φ)@w' ∈ b ∧ F(ψ)@w' ∈ b
    intro φ ψ w hmem
    rw [List.any_eq_true] at hmem
    obtain ⟨sf, hsfb, hsfp⟩ := hmem
    simp only [Bool.and_eq_true, beq_iff_eq] at hsfp
    obtain ⟨⟨hs, hf⟩, hl⟩ := hsfp
    have hsfeq : sf = ⟨.neg, .imp φ ψ, w⟩ := by cases sf; simp_all
    have hcomp : intApplyRuleFull sf nw b ≠ .notApplicable := by
      rw [hsfeq]; simp [intApplyRuleFull]
    have hsat := compound_sat sf hsfb hcomp
    rw [hsfeq] at hsat; simp only [sfSatisfied] at hsat
    exact hsat
  · -- sat_timp: T(φ→ψ)@w ∈ b → F(φ)@w ∈ b ∨ T(ψ)@w ∈ b
    intro φ ψ w hmem
    rw [List.any_eq_true] at hmem
    obtain ⟨sf, hsfb, hsfp⟩ := hmem
    simp only [Bool.and_eq_true, beq_iff_eq] at hsfp
    obtain ⟨⟨hs, hf⟩, hl⟩ := hsfp
    have hsfeq : sf = ⟨.pos, .imp φ ψ, w⟩ := by cases sf; simp_all
    have hcomp : intApplyRuleFull sf nw b ≠ .notApplicable := by
      rw [hsfeq]; simp [intApplyRuleFull]
    have hsat := compound_sat sf hsfb hcomp
    rw [hsfeq] at hsat; simp only [sfSatisfied] at hsat
    exact hsat

/-- Given `intStepBranch b e nw = none` and `IExpandedConsistentQ rep b e`, every saturation
condition of `IBranchSaturationQ Atom b rep` holds. Mirrors `IExpandedConsistent_sat`'s proof
verbatim, `sf`-case by `sf`-case: `sfSatisfiedQ`'s cases have the exact same shape as
`sfSatisfied`'s, so the same `hsfeq`/`intApplyRuleFull`-unfolding pattern applies; the
`sat_fimp` bullet closes by `exact hsat` because `sfSatisfiedQ`'s `.neg, .imp` clause and the
field are definitionally identical (both `∃ w', rep w ≤ rep w' ∧ …`), the same property
`IExpandedConsistent_sat`'s own `sat_fimp` bullet relies on. -/
private lemma IExpandedConsistentQ_sat
    {rep : Nat → Nat} {b : IBranch Atom} {e : List (ISF Atom)} {nw : Nat}
    (hstep : intStepBranch b e nw = none)
    (hIC : IExpandedConsistentQ rep b e) :
    IBranchSaturationQ Atom b rep := by
  have compound_sat : ∀ (sf : ISF Atom),
      sf ∈ b → intApplyRuleFull sf nw b ≠ .notApplicable → sfSatisfiedQ rep b sf := by
    intro sf hsfb hcomp
    exact hIC sf (intStepBranch_none_compound_mem hstep sf hsfb hcomp)
  constructor
  · -- sat_tand: T(φ∧ψ)@w ∈ b → T(φ)@w ∈ b ∧ T(ψ)@w ∈ b
    intro φ ψ w hmem
    rw [List.any_eq_true] at hmem
    obtain ⟨sf, hsfb, hsfp⟩ := hmem
    simp only [Bool.and_eq_true, beq_iff_eq] at hsfp
    obtain ⟨⟨hs, hf⟩, hl⟩ := hsfp
    have hsfeq : sf = ⟨.pos, .and φ ψ, w⟩ := by cases sf; simp_all
    have hcomp : intApplyRuleFull sf nw b ≠ .notApplicable := by
      rw [hsfeq]; simp [intApplyRuleFull]
    have hsat := compound_sat sf hsfb hcomp
    rw [hsfeq] at hsat; simp only [sfSatisfiedQ] at hsat
    exact hsat
  · -- sat_fand: F(φ∧ψ)@w ∈ b → F(φ)@w ∈ b ∨ F(ψ)@w ∈ b
    intro φ ψ w hmem
    rw [List.any_eq_true] at hmem
    obtain ⟨sf, hsfb, hsfp⟩ := hmem
    simp only [Bool.and_eq_true, beq_iff_eq] at hsfp
    obtain ⟨⟨hs, hf⟩, hl⟩ := hsfp
    have hsfeq : sf = ⟨.neg, .and φ ψ, w⟩ := by cases sf; simp_all
    have hcomp : intApplyRuleFull sf nw b ≠ .notApplicable := by
      rw [hsfeq]; simp [intApplyRuleFull]
    have hsat := compound_sat sf hsfb hcomp
    rw [hsfeq] at hsat; simp only [sfSatisfiedQ] at hsat
    exact hsat
  · -- sat_tor: T(φ∨ψ)@w ∈ b → T(φ)@w ∈ b ∨ T(ψ)@w ∈ b
    intro φ ψ w hmem
    rw [List.any_eq_true] at hmem
    obtain ⟨sf, hsfb, hsfp⟩ := hmem
    simp only [Bool.and_eq_true, beq_iff_eq] at hsfp
    obtain ⟨⟨hs, hf⟩, hl⟩ := hsfp
    have hsfeq : sf = ⟨.pos, .or φ ψ, w⟩ := by cases sf; simp_all
    have hcomp : intApplyRuleFull sf nw b ≠ .notApplicable := by
      rw [hsfeq]; simp [intApplyRuleFull]
    have hsat := compound_sat sf hsfb hcomp
    rw [hsfeq] at hsat; simp only [sfSatisfiedQ] at hsat
    exact hsat
  · -- sat_for_: F(φ∨ψ)@w ∈ b → F(φ)@w ∈ b ∧ F(ψ)@w ∈ b
    intro φ ψ w hmem
    rw [List.any_eq_true] at hmem
    obtain ⟨sf, hsfb, hsfp⟩ := hmem
    simp only [Bool.and_eq_true, beq_iff_eq] at hsfp
    obtain ⟨⟨hs, hf⟩, hl⟩ := hsfp
    have hsfeq : sf = ⟨.neg, .or φ ψ, w⟩ := by cases sf; simp_all
    have hcomp : intApplyRuleFull sf nw b ≠ .notApplicable := by
      rw [hsfeq]; simp [intApplyRuleFull]
    have hsat := compound_sat sf hsfb hcomp
    rw [hsfeq] at hsat; simp only [sfSatisfiedQ] at hsat
    exact hsat
  · -- sat_fimp: F(φ→ψ)@w ∈ b → ∃ w', rep w ≤ rep w' ∧ T(φ)@w' ∈ b ∧ F(ψ)@w' ∈ b
    intro φ ψ w hmem
    rw [List.any_eq_true] at hmem
    obtain ⟨sf, hsfb, hsfp⟩ := hmem
    simp only [Bool.and_eq_true, beq_iff_eq] at hsfp
    obtain ⟨⟨hs, hf⟩, hl⟩ := hsfp
    have hsfeq : sf = ⟨.neg, .imp φ ψ, w⟩ := by cases sf; simp_all
    have hcomp : intApplyRuleFull sf nw b ≠ .notApplicable := by
      rw [hsfeq]; simp [intApplyRuleFull]
    have hsat := compound_sat sf hsfb hcomp
    rw [hsfeq] at hsat; simp only [sfSatisfiedQ] at hsat
    exact hsat
  · -- sat_timp: T(φ→ψ)@w ∈ b → F(φ)@w ∈ b ∨ T(ψ)@w ∈ b
    intro φ ψ w hmem
    rw [List.any_eq_true] at hmem
    obtain ⟨sf, hsfb, hsfp⟩ := hmem
    simp only [Bool.and_eq_true, beq_iff_eq] at hsfp
    obtain ⟨⟨hs, hf⟩, hl⟩ := hsfp
    have hsfeq : sf = ⟨.pos, .imp φ ψ, w⟩ := by cases sf; simp_all
    have hcomp : intApplyRuleFull sf nw b ≠ .notApplicable := by
      rw [hsfeq]; simp [intApplyRuleFull]
    have hsat := compound_sat sf hsfb hcomp
    rw [hsfeq] at hsat; simp only [sfSatisfiedQ] at hsat
    exact hsat

/-- Label-boundedness invariant: every formula on `b` has a label at most `nw`, the
current next-world counter. Threaded alongside `IExpandedConsistent` to justify the
`w ≤ w'` witness ordering required by `sat_fimp` when discharging the `F(φ→ψ)` case. -/
private def ILabelBound (b : IBranch Atom) (nw : Nat) : Prop :=
  ∀ sf ∈ b, sf.label ≤ nw

omit [Hashable Atom] [DecidableEq Atom] in
/-- `ILabelBound` extends across `Branch.extendMany` when the new formulas' labels are
bounded by the (possibly larger) new counter and the old counter only grows. -/
private lemma ILabelBound_extendMany {b : IBranch Atom} {nw nw' : Nat}
    {newForms : List (ISF Atom)}
    (hle : nw ≤ nw') (h : ILabelBound b nw)
    (hnew : ∀ sf ∈ newForms, sf.label ≤ nw') :
    ILabelBound (Branch.extendMany b newForms) nw' := by
  intro sf hsf
  simp only [Branch.extendMany, List.mem_append] at hsf
  rcases hsf with hsf | hsf
  · exact hnew sf hsf
  · exact (h sf hsf).trans hle

omit [Hashable Atom] in
/-- Extracts the processed formula from a `some` result of `intStepBranch`: some
`sf ∈ b` had `intApplyRuleFull sf nw b = result` and `newExp = e ++ [sf]`. -/
private lemma intStepBranch_some_exists
    {b : IBranch Atom} {e : List (ISF Atom)} {nw : Nat}
    {result : IntRuleResult Atom} {newExp : List (ISF Atom)}
    (hstep : intStepBranch b e nw = some (result, newExp)) :
    ∃ sf, sf ∈ b ∧ intApplyRuleFull sf nw b = result ∧ newExp = e ++ [sf] := by
  simp only [intStepBranch] at hstep
  obtain ⟨sf, hsfb, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  by_cases hexp : (e.any (· == sf)) = true
  · simp [hexp] at hsf
  · simp only [Bool.not_eq_true] at hexp
    simp only [hexp, Bool.false_eq_true, if_false] at hsf
    cases hint : intApplyRuleFull sf nw b with
    | notApplicable => simp [hint] at hsf
    | linearResult fs nw' ed =>
      simp only [hint, Option.some.injEq, Prod.mk.injEq] at hsf
      exact ⟨sf, hsfb, hint.trans hsf.1, hsf.2.symm⟩
    | branchingResult bs nw' =>
      simp only [hint, Option.some.injEq, Prod.mk.injEq] at hsf
      exact ⟨sf, hsfb, hint.trans hsf.1, hsf.2.symm⟩

omit [Hashable Atom] in
/-- A `linearResult` step preserves `IExpandedConsistent`, `ILabelBound`, and the
edge-accessibility companion `IExpandedAccessConsistent`: the processed
formula's rule outputs are exactly the new formulas added to the branch, so `sfSatisfied`
(and, for the world-creating `.neg, .imp` case, `sfAccessSat` over the freshly-appended edge)
holds for it, and old formulas persist their satisfaction/bound/access facts since
`Branch.extendMany` only prepends and `edges` only grows by the one new edge (if any). -/
private lemma intStepBranch_linear_preserves
    {b : IBranch Atom} {e : List (ISF Atom)} {nw : Nat} {edges : IEdges}
    {newForms : List (ISF Atom)} {nw' : Nat} {newEdge : Option (Nat × Nat)}
    {newExp : List (ISF Atom)}
    (hIC : IExpandedConsistent b e) (hLB : ILabelBound b nw)
    (hACC : IExpandedAccessConsistent edges b e)
    (hstep : intStepBranch b e nw = some (.linearResult newForms nw' newEdge, newExp)) :
    IExpandedConsistent (Branch.extendMany b newForms) newExp ∧
      ILabelBound (Branch.extendMany b newForms) nw' ∧
      IExpandedAccessConsistent (newEdge.elim edges (fun ed => edges ++ [ed]))
        (Branch.extendMany b newForms) newExp := by
  obtain ⟨sf, hsfb, hint, hnewExp⟩ := intStepBranch_some_exists hstep
  have hsfl : sf.label ≤ nw := hLB sf hsfb
  obtain ⟨s, ff, l⟩ := sf
  simp only at hsfl hint
  have hmemOld : ∀ sf₀ ∈ b, sf₀ ∈ Branch.extendMany b newForms := fun sf₀ hsf₀ => by
    simp only [Branch.extendMany, List.mem_append]; exact Or.inr hsf₀
  have hmemNew : ∀ sf₀ ∈ newForms, sf₀ ∈ Branch.extendMany b newForms := fun sf₀ hsf₀ => by
    simp only [Branch.extendMany, List.mem_append]; exact Or.inl hsf₀
  cases s with
  | pos =>
    cases ff with
    | atom x => simp [intApplyRuleFull] at hint
    | bot => simp [intApplyRuleFull] at hint
    | imp φ ψ => simp [intApplyRuleFull] at hint
    | or φ ψ => simp [intApplyRuleFull] at hint
    | and φ ψ =>
      simp only [intApplyRuleFull, IntRuleResult.linearResult.injEq] at hint
      obtain ⟨hnf, hnw', hed⟩ := hint
      subst hnw'; subst hnewExp; subst hed
      refine ⟨?_, ILabelBound_extendMany (le_refl nw) hLB ?_, ?_⟩
      · intro sf' hsf'
        rw [List.mem_append, List.mem_singleton] at hsf'
        rcases hsf' with hsf' | rfl
        · exact sfSatisfied_mono hmemOld (hIC sf' hsf')
        · show sfSatisfied (Branch.extendMany b newForms) ⟨.pos, .and φ ψ, l⟩
          simp only [sfSatisfied]
          refine ⟨List.any_eq_true.mpr ⟨⟨.pos, φ, l⟩, hmemNew _ ?_, by simp⟩,
                  List.any_eq_true.mpr ⟨⟨.pos, ψ, l⟩, hmemNew _ ?_, by simp⟩⟩ <;>
            rw [← hnf] <;> simp
      · intro sf' hsf'
        rw [← hnf] at hsf'
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hsf'
        rcases hsf' with rfl | rfl <;> simpa using hsfl
      · intro sf' hsf'
        rw [List.mem_append, List.mem_singleton] at hsf'
        rcases hsf' with hsf' | rfl
        · exact sfAccessSat_mono hmemOld (hACC sf' hsf')
        · change sfAccessSat edges (Branch.extendMany b newForms) ⟨.pos, .and φ ψ, l⟩
          simp [sfAccessSat]
  | neg =>
    cases ff with
    | atom x => simp [intApplyRuleFull] at hint
    | bot => simp [intApplyRuleFull] at hint
    | and φ ψ => simp [intApplyRuleFull] at hint
    | or φ ψ =>
      simp only [intApplyRuleFull, IntRuleResult.linearResult.injEq] at hint
      obtain ⟨hnf, hnw', hed⟩ := hint
      subst hnw'; subst hnewExp; subst hed
      refine ⟨?_, ILabelBound_extendMany (le_refl nw) hLB ?_, ?_⟩
      · intro sf' hsf'
        rw [List.mem_append, List.mem_singleton] at hsf'
        rcases hsf' with hsf' | rfl
        · exact sfSatisfied_mono hmemOld (hIC sf' hsf')
        · show sfSatisfied (Branch.extendMany b newForms) ⟨.neg, .or φ ψ, l⟩
          simp only [sfSatisfied]
          refine ⟨List.any_eq_true.mpr ⟨⟨.neg, φ, l⟩, hmemNew _ ?_, by simp⟩,
                  List.any_eq_true.mpr ⟨⟨.neg, ψ, l⟩, hmemNew _ ?_, by simp⟩⟩ <;>
            rw [← hnf] <;> simp
      · intro sf' hsf'
        rw [← hnf] at hsf'
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hsf'
        rcases hsf' with rfl | rfl <;> simpa using hsfl
      · intro sf' hsf'
        rw [List.mem_append, List.mem_singleton] at hsf'
        rcases hsf' with hsf' | rfl
        · exact sfAccessSat_mono hmemOld (hACC sf' hsf')
        · change sfAccessSat edges (Branch.extendMany b newForms) ⟨.neg, .or φ ψ, l⟩
          simp [sfAccessSat]
    | imp φ ψ =>
      simp only [intApplyRuleFull, intFImpRule, IntRuleResult.linearResult.injEq] at hint
      obtain ⟨hnf, hnw', hed⟩ := hint
      subst hnw'; subst hnewExp; subst hed
      refine ⟨?_, ILabelBound_extendMany (Nat.le_succ nw) hLB ?_, ?_⟩
      · intro sf' hsf'
        rw [List.mem_append, List.mem_singleton] at hsf'
        rcases hsf' with hsf' | rfl
        · exact sfSatisfied_mono hmemOld (hIC sf' hsf')
        · show sfSatisfied (Branch.extendMany b newForms) ⟨.neg, .imp φ ψ, l⟩
          simp only [sfSatisfied]
          refine ⟨nw, List.any_eq_true.mpr ⟨⟨.pos, φ, nw⟩, hmemNew _ ?_, by simp⟩,
                  List.any_eq_true.mpr ⟨⟨.neg, ψ, nw⟩, hmemNew _ ?_, by simp⟩⟩ <;>
            rw [← hnf] <;> simp
      · intro sf' hsf'
        rw [← hnf] at hsf'
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hsf'
        rcases hsf' with (rfl | rfl) | hpers
        · exact Nat.le_succ nw
        · exact Nat.le_succ nw
        · simp only [propagatePersistence, List.mem_map] at hpers
          obtain ⟨a, -, rfl⟩ := hpers
          exact Nat.le_succ nw
      · intro sf' hsf'
        rw [List.mem_append, List.mem_singleton] at hsf'
        rcases hsf' with hsf' | rfl
        · change sfAccessSat (edges ++ [(nw, l)]) (Branch.extendMany b newForms) sf'
          exact sfAccessSat_edges_mono (nw, l) (sfAccessSat_mono hmemOld (hACC sf' hsf'))
        · change sfAccessSat (edges ++ [(nw, l)]) (Branch.extendMany b newForms) ⟨.neg, .imp φ ψ, l⟩
          simp only [sfAccessSat]
          refine ⟨nw, isAccessible_one_step (by simp),
                  List.any_eq_true.mpr ⟨⟨.pos, φ, nw⟩, hmemNew _ ?_, by simp⟩,
                  List.any_eq_true.mpr ⟨⟨.neg, ψ, nw⟩, hmemNew _ ?_, by simp⟩⟩ <;>
            rw [← hnf] <;> simp

omit [Hashable Atom] in
/-- A `branchingResult` step preserves `IExpandedConsistent`, `ILabelBound`, and
`IExpandedAccessConsistent` on every sub-branch: each sub-branch receives one disjunct of the
processed formula's rule output, which is exactly what `sfSatisfied`'s disjunctive case
requires. Branching (`.pos, .or`/`.neg, .and`) never creates a world, so `edges` is unchanged
and the new disjunct formulas are never `.neg, .imp`, making the access obligation trivial. -/
private lemma intStepBranch_branch_preserves
    {b : IBranch Atom} {e : List (ISF Atom)} {nw : Nat} {edges : IEdges}
    {branches' : List (List (ISF Atom))} {nw' : Nat} {newExp : List (ISF Atom)}
    (hIC : IExpandedConsistent b e) (hLB : ILabelBound b nw)
    (hACC : IExpandedAccessConsistent edges b e)
    (hstep : intStepBranch b e nw = some (.branchingResult branches' nw', newExp)) :
    ∀ br ∈ branches',
      IExpandedConsistent (Branch.extendMany b br) newExp ∧
        ILabelBound (Branch.extendMany b br) nw' ∧
        IExpandedAccessConsistent edges (Branch.extendMany b br) newExp := by
  obtain ⟨sf, hsfb, hint, hnewExp⟩ := intStepBranch_some_exists hstep
  have hsfl : sf.label ≤ nw := hLB sf hsfb
  obtain ⟨s, ff, l⟩ := sf
  simp only at hsfl hint
  intro br hbr
  have hmemOld : ∀ sf₀ ∈ b, sf₀ ∈ Branch.extendMany b br := fun sf₀ hsf₀ => by
    simp only [Branch.extendMany, List.mem_append]; exact Or.inr hsf₀
  cases s with
  | pos =>
    cases ff with
    | atom x => simp [intApplyRuleFull] at hint
    | bot => simp [intApplyRuleFull] at hint
    | imp φ ψ =>
      -- Deliverable 6: T(φ → ψ) → [F(φ)@l] | [T(ψ)@l], reflexively at `l`. Same shape as the
      -- `.pos, .or` case below, with mixed signs on the two disjuncts.
      simp only [intApplyRuleFull, IntRuleResult.branchingResult.injEq] at hint
      obtain ⟨hbrs, hnw'⟩ := hint
      subst hnw'; subst hnewExp
      rw [← hbrs] at hbr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr
      refine ⟨?_, ?_, ?_⟩
      · intro sf' hsf'
        rw [List.mem_append, List.mem_singleton] at hsf'
        rcases hsf' with hsf' | rfl
        · exact sfSatisfied_mono hmemOld (hIC sf' hsf')
        · rcases hbr with rfl | rfl
          · exact Or.inl (List.any_eq_true.mpr
              ⟨⟨.neg, φ, l⟩, by simp [Branch.extendMany], by simp⟩)
          · exact Or.inr (List.any_eq_true.mpr
              ⟨⟨.pos, ψ, l⟩, by simp [Branch.extendMany], by simp⟩)
      · intro sf' hsf'
        rcases hbr with rfl | rfl <;>
          simp only [Branch.extendMany, List.mem_cons, List.mem_nil_iff, List.mem_append,
            or_false] at hsf' <;>
          rcases hsf' with rfl | hsf' <;> first | exact hsfl | exact hLB sf' hsf'
      · intro sf' hsf'
        rw [List.mem_append, List.mem_singleton] at hsf'
        rcases hsf' with hsf' | rfl
        · exact sfAccessSat_mono hmemOld (hACC sf' hsf')
        · rcases hbr with rfl | rfl <;> simp [sfAccessSat]
    | and φ ψ => simp [intApplyRuleFull] at hint
    | or φ ψ =>
      simp only [intApplyRuleFull, IntRuleResult.branchingResult.injEq] at hint
      obtain ⟨hbrs, hnw'⟩ := hint
      subst hnw'; subst hnewExp
      rw [← hbrs] at hbr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr
      refine ⟨?_, ?_, ?_⟩
      · intro sf' hsf'
        rw [List.mem_append, List.mem_singleton] at hsf'
        rcases hsf' with hsf' | rfl
        · exact sfSatisfied_mono hmemOld (hIC sf' hsf')
        · rcases hbr with rfl | rfl
          · exact Or.inl (List.any_eq_true.mpr
              ⟨⟨.pos, φ, l⟩, by simp [Branch.extendMany], by simp⟩)
          · exact Or.inr (List.any_eq_true.mpr
              ⟨⟨.pos, ψ, l⟩, by simp [Branch.extendMany], by simp⟩)
      · intro sf' hsf'
        rcases hbr with rfl | rfl <;>
          simp only [Branch.extendMany, List.mem_cons, List.mem_nil_iff, List.mem_append,
            or_false] at hsf' <;>
          rcases hsf' with rfl | hsf' <;> first | exact hsfl | exact hLB sf' hsf'
      · intro sf' hsf'
        rw [List.mem_append, List.mem_singleton] at hsf'
        rcases hsf' with hsf' | rfl
        · exact sfAccessSat_mono hmemOld (hACC sf' hsf')
        · rcases hbr with rfl | rfl <;> simp [sfAccessSat]
  | neg =>
    cases ff with
    | atom x => simp [intApplyRuleFull] at hint
    | bot => simp [intApplyRuleFull] at hint
    | imp φ ψ => simp [intApplyRuleFull] at hint
    | or φ ψ => simp [intApplyRuleFull] at hint
    | and φ ψ =>
      simp only [intApplyRuleFull, IntRuleResult.branchingResult.injEq] at hint
      obtain ⟨hbrs, hnw'⟩ := hint
      subst hnw'; subst hnewExp
      rw [← hbrs] at hbr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr
      refine ⟨?_, ?_, ?_⟩
      · intro sf' hsf'
        rw [List.mem_append, List.mem_singleton] at hsf'
        rcases hsf' with hsf' | rfl
        · exact sfSatisfied_mono hmemOld (hIC sf' hsf')
        · rcases hbr with rfl | rfl
          · exact Or.inl (List.any_eq_true.mpr
              ⟨⟨.neg, φ, l⟩, by simp [Branch.extendMany], by simp⟩)
          · exact Or.inr (List.any_eq_true.mpr
              ⟨⟨.neg, ψ, l⟩, by simp [Branch.extendMany], by simp⟩)
      · intro sf' hsf'
        rcases hbr with rfl | rfl <;>
          simp only [Branch.extendMany, List.mem_cons, List.mem_nil_iff, List.mem_append,
            or_false] at hsf' <;>
          rcases hsf' with rfl | hsf' <;> first | exact hsfl | exact hLB sf' hsf'
      · intro sf' hsf'
        rw [List.mem_append, List.mem_singleton] at hsf'
        rcases hsf' with hsf' | rfl
        · exact sfAccessSat_mono hmemOld (hACC sf' hsf')
        · rcases hbr with rfl | rfl <;> simp [sfAccessSat]

omit [Hashable Atom] in
/-- `applyAllTImpRules` only introduces new formulas whose label already appears on `b`
(drawn from `intTImpRule`'s `accessibleWorlds`, itself a subset of `b.map (·.label)`), so a
single persistence-propagation step preserves `ILabelBound`. Mirrors the structural pattern of
the (private, non-reusable) `intTImpRules_sat`-style proofs in `Soundness.lean`. -/
private lemma ILabelBound_applyAllTImpRules {b : IBranch Atom} {edges : IEdges} {nw : Nat}
    (h : ILabelBound b nw) : ILabelBound (applyAllTImpRules b edges) nw := by
  intro sf hmem
  simp only [applyAllTImpRules, List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · exact h sf hmem
  · simp only [List.mem_flatten, List.mem_filterMap] at hmem
    obtain ⟨newForms, ⟨⟨sign_o, form_o, label_o⟩, hmem_outer, houter⟩, hmem_inner⟩ := hmem
    cases sign_o with
    | neg => simp only at houter; exact absurd houter (by simp)
    | pos =>
      cases form_o with
      | atom _ => simp only at houter; exact absurd houter (by simp)
      | bot => simp only at houter; exact absurd houter (by simp)
      | and _ _ => simp only at houter; exact absurd houter (by simp)
      | or _ _ => simp only at houter; exact absurd houter (by simp)
      | imp φ ψ =>
        simp only [] at houter
        by_cases hemp : (intTImpRule φ ψ label_o edges b).isEmpty = true
        · simp only [hemp, ite_true] at houter; exact absurd houter (by simp)
        · simp only [Bool.false_eq_true, hemp, ite_false, Option.some.injEq] at houter
          -- STEP 1, task 574: `hmem_inner` ranges only over `intTImpRule`'s output; the
          -- self-copy branch (`hmem_copy`) no longer exists.
          rw [← houter] at hmem_inner
          simp only [intTImpRule, List.mem_filterMap] at hmem_inner
          obtain ⟨w', hw'_acc, hw'_sf⟩ := hmem_inner
          simp only [List.mem_filter, List.mem_eraseDups, List.mem_map] at hw'_acc
          obtain ⟨⟨x, hxb, hxeq⟩, -⟩ := hw'_acc
          by_cases hphi : (b.any fun sf =>
              sf.sign == .pos && sf.formula == φ && sf.label == w') = true
          · by_cases hpsi : (b.any fun sf =>
                sf.sign == .pos && sf.formula == ψ && sf.label == w') = true
            · simp [hphi, hpsi] at hw'_sf
            · simp only [hphi, ↓reduceIte, hpsi, Bool.false_eq_true, Option.some.injEq]
                at hw'_sf
              rw [← hw'_sf]
              simpa [← hxeq] using h x hxb
          · simp [hphi] at hw'_sf

omit [Hashable Atom] in
/-- `ILabelBound` is preserved by `applyPersistenceFixpoint` (any number of fixpoint
iterations of `applyAllTImpRules`), by induction on the fuel counter. -/
private lemma ILabelBound_applyPersistenceFixpoint {b : IBranch Atom} {edges : IEdges}
    {nw : Nat} (fuel : Nat) (h : ILabelBound b nw) :
    ILabelBound (applyPersistenceFixpoint b edges fuel) nw := by
  induction fuel generalizing b with
  | zero => simpa [applyPersistenceFixpoint] using h
  | succ k ih =>
    simp only [applyPersistenceFixpoint]
    split_ifs with hlen
    · exact h
    · exact ih (ILabelBound_applyAllTImpRules h)

/-- Combined per-branch invariant carrier: `IExpandedConsistent` and `ILabelBound` hold for
every corresponding triple in three parallel lists (branches, expanded-sets, next-world
counters). Defined by simultaneous recursion so any shape mismatch between the lists is
automatically `False` (closeable via `simp [IAllConsistent] at h`), avoiding the need for a
`List.Forall₃`-style combinator. -/
private def IAllConsistent (bs : List (IBranch Atom)) (es : List (List (ISF Atom)))
    (nws : List Nat) : Prop :=
  match bs, es, nws with
  | [], [], [] => True
  | b :: bs', e :: es', nw :: nws' =>
      IExpandedConsistent b e ∧ ILabelBound b nw ∧ IAllConsistent bs' es' nws'
  | _, _, _ => False

omit [Hashable Atom] in
/-- `IAllConsistent` combines under list append (used to extend `done`/`doneExp`/`doneNW`
with the just-processed branch, and to combine `done` with the still-`pending` tail). -/
private lemma IAllConsistent_append {bs1 bs2 : List (IBranch Atom)}
    {es1 es2 : List (List (ISF Atom))} {nws1 nws2 : List Nat}
    (h1 : IAllConsistent bs1 es1 nws1) (h2 : IAllConsistent bs2 es2 nws2) :
    IAllConsistent (bs1 ++ bs2) (es1 ++ es2) (nws1 ++ nws2) := by
  induction bs1 generalizing es1 nws1 with
  | nil =>
    cases es1 with
    | nil =>
      cases nws1 with
      | nil => simpa using h2
      | cons nwh nwt => simp [IAllConsistent] at h1
    | cons eh et => simp [IAllConsistent] at h1
  | cons bh bt ih =>
    cases es1 with
    | nil => simp [IAllConsistent] at h1
    | cons eh et =>
      cases nws1 with
      | nil => simp [IAllConsistent] at h1
      | cons nwh nwt =>
        simp only [IAllConsistent] at h1
        obtain ⟨hIC, hLB, hrest⟩ := h1
        simp only [List.cons_append]
        exact ⟨hIC, hLB, ih hrest⟩

omit [Hashable Atom] in
/-- `IAllConsistent` holds along a uniform `map`: if every branch obtained by applying `f`
to an element of `branches'` satisfies the same `IExpandedConsistent`/`ILabelBound` facts
(the shape produced by a branching-rule step, where every sub-branch shares one `newExp`,
`nw'`), then `IAllConsistent` holds of the mapped/replicated triple of lists. -/
private lemma IAllConsistent_map {branches' : List (IBranch Atom)} (f : IBranch Atom → IBranch Atom)
    {newExp : List (ISF Atom)} {nw' : Nat}
    (h : ∀ br ∈ branches', IExpandedConsistent (f br) newExp ∧ ILabelBound (f br) nw') :
    IAllConsistent (branches'.map f) (branches'.map (fun _ => newExp))
      (branches'.map (fun _ => nw')) := by
  induction branches' with
  | nil => simp [IAllConsistent]
  | cons bh bt ih =>
    simp only [List.map_cons, IAllConsistent]
    exact ⟨(h bh (List.mem_cons_self ..)).1, (h bh (List.mem_cons_self ..)).2,
      ih fun br hbr => h br (List.mem_cons_of_mem _ hbr)⟩

/-- The edge-accessibility companion of `IAllConsistent`: threaded
ALONGSIDE it (not merged into it, to avoid touching `IAllConsistent`'s already-green call
sites) through the same `branches`/`expandedSets`/`edgeSets` triple. -/
private def IAllAccessConsistent (bs : List (IBranch Atom)) (es : List (List (ISF Atom)))
    (edgeSets : List IEdges) : Prop :=
  match bs, es, edgeSets with
  | [], [], [] => True
  | b :: bs', e :: es', edges :: edgeSets' =>
      IExpandedAccessConsistent edges b e ∧ IAllAccessConsistent bs' es' edgeSets'
  | _, _, _ => False

omit [Hashable Atom] in
/-- `IAllAccessConsistent` combines under list append (mirrors `IAllConsistent_append`). -/
private lemma IAllAccessConsistent_append {bs1 bs2 : List (IBranch Atom)}
    {es1 es2 : List (List (ISF Atom))} {edgeSets1 edgeSets2 : List IEdges}
    (h1 : IAllAccessConsistent bs1 es1 edgeSets1) (h2 : IAllAccessConsistent bs2 es2 edgeSets2) :
    IAllAccessConsistent (bs1 ++ bs2) (es1 ++ es2) (edgeSets1 ++ edgeSets2) := by
  induction bs1 generalizing es1 edgeSets1 with
  | nil =>
    cases es1 with
    | nil =>
      cases edgeSets1 with
      | nil => simpa using h2
      | cons eh et => simp [IAllAccessConsistent] at h1
    | cons eh et => simp [IAllAccessConsistent] at h1
  | cons bh bt ih =>
    cases es1 with
    | nil => simp [IAllAccessConsistent] at h1
    | cons eh et =>
      cases edgeSets1 with
      | nil => simp [IAllAccessConsistent] at h1
      | cons edgesh edgest =>
        simp only [IAllAccessConsistent] at h1
        obtain ⟨hACC, hrest⟩ := h1
        simp only [List.cons_append]
        exact ⟨hACC, ih hrest⟩

omit [Hashable Atom] in
/-- `IAllAccessConsistent` holds along a uniform `map` (mirrors `IAllConsistent_map`; used
for the branching-rule case, which never creates a world so `edges` is unchanged). -/
private lemma IAllAccessConsistent_map {branches' : List (IBranch Atom)}
    (f : IBranch Atom → IBranch Atom) {newExp : List (ISF Atom)} {edges : IEdges}
    (h : ∀ br ∈ branches', IExpandedAccessConsistent edges (f br) newExp) :
    IAllAccessConsistent (branches'.map f) (branches'.map (fun _ => newExp))
      (branches'.map (fun _ => edges)) := by
  induction branches' with
  | nil => simp [IAllAccessConsistent]
  | cons bh bt ih =>
    simp only [List.map_cons, IAllAccessConsistent]
    exact ⟨h bh (List.mem_cons_self ..), ih fun br hbr => h br (List.mem_cons_of_mem _ hbr)⟩

omit [Hashable Atom] in
/-- Given `intStepBranch b e nw = none` and `IExpandedAccessConsistent edges b e`,
`IFimpAccess edges b` holds. Mirrors `IExpandedConsistent_sat`'s extraction pattern,
restricted to the one `.neg, .imp` case `sfAccessSat` covers. -/
private lemma IExpandedAccessConsistent_sat
    {b : IBranch Atom} {e : List (ISF Atom)} {nw : Nat} {edges : IEdges}
    (hstep : intStepBranch b e nw = none)
    (hACC : IExpandedAccessConsistent edges b e) :
    IFimpAccess edges b := by
  intro φ ψ w hmem
  rw [List.any_eq_true] at hmem
  obtain ⟨sf, hsfb, hsfp⟩ := hmem
  simp only [Bool.and_eq_true, beq_iff_eq] at hsfp
  obtain ⟨⟨hs, hf⟩, hl⟩ := hsfp
  have hsfeq : sf = ⟨.neg, .imp φ ψ, w⟩ := by cases sf; simp_all
  have hcomp : intApplyRuleFull sf nw b ≠ .notApplicable := by
    rw [hsfeq]; simp [intApplyRuleFull]
  have hsat := hACC sf (intStepBranch_none_compound_mem hstep sf hsfb hcomp)
  rw [hsfeq] at hsat; simp only [sfAccessSat] at hsat
  exact hsat

omit [Hashable Atom] in
/-- Given `intStepBranch b e nw = none` and `IExpandedAccessConsistentQ edges rep b e`,
`IFimpAccessQ edges rep b` holds. Mirrors `IExpandedAccessConsistent_sat`'s extraction
pattern verbatim, restricted to the one `.neg, .imp` case `sfAccessSatQ` covers; the two
definitions are shaped identically modulo the `rep`-wrapping on the accessibility witness, so
the same `hsfeq`-based rewriting closes it. -/
private lemma IExpandedAccessConsistentQ_sat
    {rep : Nat → Nat} {b : IBranch Atom} {e : List (ISF Atom)} {nw : Nat} {edges : IEdges}
    (hstep : intStepBranch b e nw = none)
    (hACC : IExpandedAccessConsistentQ edges rep b e) :
    IFimpAccessQ edges rep b := by
  intro φ ψ w hmem
  rw [List.any_eq_true] at hmem
  obtain ⟨sf, hsfb, hsfp⟩ := hmem
  simp only [Bool.and_eq_true, beq_iff_eq] at hsfp
  obtain ⟨⟨hs, hf⟩, hl⟩ := hsfp
  have hsfeq : sf = ⟨.neg, .imp φ ψ, w⟩ := by cases sf; simp_all
  have hcomp : intApplyRuleFull sf nw b ≠ .notApplicable := by
    rw [hsfeq]; simp [intApplyRuleFull]
  have hsat := hACC sf (intStepBranch_none_compound_mem hstep sf hsfb hcomp)
  rw [hsfeq] at hsat; simp only [sfAccessSatQ] at hsat
  exact hsat

/-! ## Fixed Finite Universe and Counting Work

This section defines the fixed finite `(sign, subformula, world)` cell universe
`intUniverse φ` and the per-branch counting measure `intWork`, mirroring the proven
Modal-K `FmpMeasure` pattern (`Cslib/Logics/Modal/Tableau/FmpMeasure.lean`: `modalSubfmls`,
`modalUniverse`, `modalWork`). These are the building blocks for the base-3 damped worklist
measure `intExpMeasure` (not yet defined) that will certify `intFuel φ`
is sufficient for the expansion loop to reach a Hintikka set before fuel is exhausted.

The intuitionistic/minimal calculus differs from Modal K in its connective set (`imp`/
`and`/`or`, no `box`/`diamond`), so `intSubfmls`/`intUniverse` are fresh List-recursive
definitions (mirroring `modalSubfmls`/`modalUniverse`'s *shape*, not literal reuse) rather
than reusing `Proposition.subformulas` (`Subformula.lean`), which is `Finset`-valued and
the wrong shape for the counting-measure machinery below. `intUniverse`'s size bound
(`intUniverse_length_le`) is exactly the quantity `intFuel φ := 3 ^ (2 * (2 * φ.complexity
+ 1) * (φ.complexity + 2))` (`Expansion.lean:462-463`) was pre-sized
against.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4
-/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Structural subformula list of a `Proposition Atom` (mirrors `modalSubfmls`,
`FmpMeasure.lean:73-80`, restricted to the propositional connective set: `atom`/`bot`/`imp`/
`and`/`or`, no `box`/`diamond`). Every node of `φ`'s syntax tree contributes exactly one
entry. -/
def intSubfmls : Proposition Atom → List (Proposition Atom)
  | .atom p => [.atom p]
  | .bot => [.bot]
  | .imp a b => .imp a b :: intSubfmls a ++ intSubfmls b
  | .and a b => .and a b :: intSubfmls a ++ intSubfmls b
  | .or a b => .or a b :: intSubfmls a ++ intSubfmls b

omit [DecidableEq Atom] [Hashable Atom] in
/-- The subformula list has length at most `2 * φ.complexity + 1` (mirrors
`modalSubfmls_length_le`, `FmpMeasure.lean:82-102`). -/
lemma intSubfmls_length_le (φ : Proposition Atom) :
    (intSubfmls φ).length ≤ 2 * φ.complexity + 1 := by
  induction φ with
  | atom p => simp [intSubfmls]
  | bot => simp [intSubfmls]
  | imp a b iha ihb =>
    simp only [intSubfmls, List.length_cons, List.length_append, complexity_imp]
    omega
  | and a b iha ihb =>
    simp only [intSubfmls, List.length_cons, List.length_append, complexity_and]
    omega
  | or a b iha ihb =>
    simp only [intSubfmls, List.length_cons, List.length_append, complexity_or]
    omega

/-- Whether a `Proposition Atom` is `.imp`-shaped at its root (used to count `.imp`-node
*positions*, not distinct values, in a subformula list -- `intSubfmls` is a raw,
non-deduplicating list, so `List.countP isImpShaped (intSubfmls φ)` counts every syntactic
`.imp` tree-node occurrence of `φ`, even when two occurrences share the same formula value
(e.g. `(a→b) ∧ (a→b)` has two distinct `.imp`-node positions with identical value `a→b`). -/
def isImpShaped : Proposition Atom → Bool
  | .imp _ _ => true
  | _ => false

omit [DecidableEq Atom] [Hashable Atom] in
/-- The number of `.imp`-node positions in `φ`'s subformula list is at most `φ.complexity`
(mirrors `intSubfmls_length_le`'s induction shape, tracking a per-connective `imp`-count
instead of total length). This is the key combinatorial fact underlying the linear world
bound `intExpandBranches_world_bound`: world-creation
fires *only* on a `.neg`-signed `.imp` formula (`Rules.lean:262-264`), and (per the
occurrence-tracking argument recorded in the Branch-Universe Containment section below) each
world created
during expansion can be injected into a DISTINCT `.imp`-node position of `φ0`'s own parse
tree -- since F-signed formulas never propagate via persistence (`posFormulasAt`/
`propagatePersistence`/`intTImpRule` are `.pos`-only, `Rules.lean:126,139-141,174-186`), a
given `.imp` position's negative instance can only ever exist in the ONE world where its own
decomposition lineage placed it. Combined with this bound, that injection gives
`(number of worlds created) ≤ φ0.complexity`, hence `(distinct labels).length ≤
φ0.complexity + 1` (the `+1` for the initial world `0`) -- the target bound. -/
lemma intSubfmls_impCount_le (φ : Proposition Atom) :
    (intSubfmls φ).countP isImpShaped ≤ φ.complexity := by
  induction φ with
  | atom p => simp [intSubfmls, isImpShaped]
  | bot => simp [intSubfmls, isImpShaped]
  | imp a b iha ihb =>
    simp [intSubfmls, List.countP_cons, List.countP_append, isImpShaped, complexity_imp]
    omega
  | and a b iha ihb =>
    simp [intSubfmls, List.countP_append, isImpShaped, complexity_and]
    omega
  | or a b iha ihb =>
    simp [intSubfmls, List.countP_append, isImpShaped, complexity_or]
    omega

omit [DecidableEq Atom] [Hashable Atom] in
/-- The fixed finite universe of `(sign, subformula, world)` cells for `φ`: both signs,
every subformula of `φ`, at every world label `0 .. φ.complexity + 1` (mirrors `modalUniverse`,
`FmpMeasure.lean:149-152`, using the linear world range `φ.complexity + 1` in place of the
Modal-K `modalWorldBound`).

**This linear world bound is REFUTED as an invariant of branches actually produced by
`intExpandBranches`** -- see the *Divergence witness* note in `Expansion.lean` (immediately
before its `## Decision Procedures` section) for the counterexample: on a complexity-9 witness
formula, world labels grow linearly and unboundedly in fuel, with no saturation. `intUniverse`
is retained here only as the *measure domain* `intExpMeasure` is built over (a finite-cell
bookkeeping convenience for the fuel-sufficiency argument), NOT as a containment guarantee that
every world an actual expansion run visits lies within `0 .. φ.complexity + 1`. Do not read
`∀ x ∈ b, x ∈ intUniverse φ` as an established invariant of `intExpandBranches`; the *Divergence
witness* note shows a direct counterexample. -/
def intUniverse (φ : Proposition Atom) : List (ISF Atom) :=
  (List.range (φ.complexity + 2)).flatMap (fun w =>
    (intSubfmls φ).flatMap (fun ψ => [(⟨.pos, ψ, w⟩ : ISF Atom), ⟨.neg, ψ, w⟩]))

omit [DecidableEq Atom] [Hashable Atom] in
/-- The universe has length at most `2 * (2 * φ.complexity + 1) * (φ.complexity + 2)` --
exactly the exponent `intFuel φ := 3 ^ (2 * (2 * φ.complexity + 1) * (φ.complexity + 2))`
(`Expansion.lean:462-463`) was pre-sized against (mirrors
`modalUniverse_length_le`, `FmpMeasure.lean:154-186`). -/
lemma intUniverse_length_le (φ : Proposition Atom) :
    (intUniverse φ).length ≤
      2 * (2 * φ.complexity + 1) * (φ.complexity + 2) := by
  have hinner : ∀ w : Nat,
      ((intSubfmls φ).flatMap
        (fun ψ => [(⟨.pos, ψ, w⟩ : ISF Atom), ⟨.neg, ψ, w⟩])).length
        ≤ 2 * (2 * φ.complexity + 1) := by
    intro w
    rw [List.length_flatMap]
    have hb : (List.map (fun ψ =>
        ([(⟨.pos, ψ, w⟩ : ISF Atom), ⟨.neg, ψ, w⟩]).length)
        (intSubfmls φ)).sum ≤ (intSubfmls φ).length * 2 :=
      sum_map_le_length_mul (intSubfmls φ) _ 2 (fun ψ _ => by simp)
    have hlen := intSubfmls_length_le φ
    omega
  unfold intUniverse
  rw [List.length_flatMap]
  have houter : (List.map (fun w =>
      ((intSubfmls φ).flatMap
        (fun ψ => [(⟨.pos, ψ, w⟩ : ISF Atom), ⟨.neg, ψ, w⟩])).length)
      (List.range (φ.complexity + 2))).sum
      ≤ (List.range (φ.complexity + 2)).length * (2 * (2 * φ.complexity + 1)) :=
    sum_map_le_length_mul (List.range (φ.complexity + 2)) _
      (2 * (2 * φ.complexity + 1)) (fun w _ => hinner w)
  rw [List.length_range] at houter
  calc (List.map (fun w =>
        ((intSubfmls φ).flatMap
          (fun ψ => [(⟨.pos, ψ, w⟩ : ISF Atom), ⟨.neg, ψ, w⟩])).length)
        (List.range (φ.complexity + 2))).sum
      ≤ (φ.complexity + 2) * (2 * (2 * φ.complexity + 1)) := houter
    _ = 2 * (2 * φ.complexity + 1) * (φ.complexity + 2) := by ring

/-! ## Branch-Universe Containment

This section proves that every signed formula added to a branch by any intuitionistic
tableau rule (ALPHA, BETA, world-creating F(φ→ψ), or the persistent T(φ→ψ) rule) stays
inside the fixed finite `intUniverse φ0` -- the load-bearing "universe-containment" fact
`intExpMeasure_step_lt`/`_branch` (above) take as the `hb` hypothesis. Mirrors the Modal-K
`FmpMeasure.lean` subformula-closure development (`modalSubfmls_self_mem`,
`modalSubfmls_trans`, `mem_modalUniverse_of[']`, `modalUniverse_mem_formula/label`,
`modalApplyOne_outputs_subset`, `FmpMeasure.lean:266-754`), simplified for the propositional
connective set (`imp`/`and`/`or`, no `box`/`diamond`) and the single world-creating rule
(F(φ→ψ), vs. Modal-K's two: `diamondPos`/`boxNeg`). -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Every `Proposition Atom` is a member of its own structural subformula list (mirrors
`modalSubfmls_self_mem`, `FmpMeasure.lean:266`). -/
@[simp]
lemma intSubfmls_self_mem (φ : Proposition Atom) : φ ∈ intSubfmls φ := by
  cases φ <;> simp [intSubfmls]

omit [DecidableEq Atom] [Hashable Atom] in
/-- Transitivity of `intSubfmls`: a subformula of a subformula is a subformula (mirrors
`modalSubfmls_trans`, `FmpMeasure.lean:393-427`). Needed because the world-creating
`F(φ → ψ)` rule's persistence group derives its subformula bound from *other* branch
members via the branch invariant, not from the source formula directly, so a two-step
subformula chain must be composed. -/
private lemma intSubfmls_trans {a b c : Proposition Atom}
    (hab : a ∈ intSubfmls b) (hbc : b ∈ intSubfmls c) : a ∈ intSubfmls c := by
  induction c with
  | atom p =>
    simp only [intSubfmls, List.mem_singleton] at hbc; subst hbc; exact hab
  | bot =>
    simp only [intSubfmls, List.mem_singleton] at hbc; subst hbc; exact hab
  | imp x y ihx ihy =>
    simp only [intSubfmls, List.mem_cons, List.mem_append] at hbc
    rcases hbc with (rfl | hx) | hy
    · exact hab
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihx hx))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihy hy))
  | and x y ihx ihy =>
    simp only [intSubfmls, List.mem_cons, List.mem_append] at hbc
    rcases hbc with (rfl | hx) | hy
    · exact hab
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihx hx))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihy hy))
  | or x y ihx ihy =>
    simp only [intSubfmls, List.mem_cons, List.mem_append] at hbc
    rcases hbc with (rfl | hx) | hy
    · exact hab
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihx hx))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihy hy))

omit [DecidableEq Atom] [Hashable Atom] in
/-- Constructor direction for `intUniverse` membership: a signed formula with any sign, a
subformula of `φ0`, at a world label within the linear bound, is in `U(φ0)` (mirrors
`mem_modalUniverse_of`, `FmpMeasure.lean:432-437`). -/
private lemma mem_intUniverse_of {φ0 : Proposition Atom} {s : Sign} {φ : Proposition Atom}
    {w : Nat} (hw : w ≤ φ0.complexity + 1) (hφ : φ ∈ intSubfmls φ0) :
    (⟨s, φ, w⟩ : ISF Atom) ∈ intUniverse φ0 := by
  have hlt : w < φ0.complexity + 2 := by omega
  simp only [intUniverse, List.mem_flatMap, List.mem_range]
  exact ⟨w, hlt, φ, hφ, by cases s <;> simp⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- Generic form of `mem_intUniverse_of`, stated for an arbitrary signed formula `z` (mirrors
`mem_modalUniverse_of'`, `FmpMeasure.lean:443-448`). -/
private lemma mem_intUniverse_of' {φ0 : Proposition Atom} {z : ISF Atom}
    (hw : z.label ≤ φ0.complexity + 1) (hφ : z.formula ∈ intSubfmls φ0) :
    z ∈ intUniverse φ0 := by
  obtain ⟨s, φ, w⟩ := z
  exact mem_intUniverse_of hw hφ

omit [DecidableEq Atom] [Hashable Atom] in
/-- Extraction: the formula-component of any `intUniverse φ0` member is a subformula of
`φ0` (mirrors `modalUniverse_mem_formula`, `FmpMeasure.lean:453-458`). -/
private lemma intUniverse_mem_formula {φ0 : Proposition Atom} {x : ISF Atom}
    (hx : x ∈ intUniverse φ0) : x.formula ∈ intSubfmls φ0 := by
  simp only [intUniverse, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  obtain ⟨w, -, ψ, hψ, heq | heq⟩ := hx <;> (subst heq; exact hψ)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Extraction: the label-component of any `intUniverse φ0` member is bounded by
`φ0.complexity + 1` (mirrors `modalUniverse_mem_label`, `FmpMeasure.lean:463-468`). -/
private lemma intUniverse_mem_label {φ0 : Proposition Atom} {x : ISF Atom}
    (hx : x ∈ intUniverse φ0) : x.label ≤ φ0.complexity + 1 := by
  simp only [intUniverse, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  obtain ⟨w, hw, ψ, -, heq | heq⟩ := hx <;>
    (subst heq; change w ≤ φ0.complexity + 1; omega)

omit [Hashable Atom] in
/-- Containment for the persistent `T(φ → ψ)` rule (`Rules.lean:174-186`): every formula it
emits stays inside `U(φ0)`, given the branch invariant `hb` and the source membership `hsf`
(the exact `⟨.pos, .imp φ ψ, w⟩ ∈ b` the rule is fired from). The emitted label `w'` is always
an EXISTING label already appearing on `b` (read off via `b.map (·.label)`, no fresh label is
minted), so no world-bound hypothesis is needed here -- this mirrors the Modal-K "world-
preserving rules" P1a pattern (`boxPos`/`diamondNeg`, `FmpMeasure.lean:253-260`), which also
consume no world-bound hypothesis. -/
private lemma intTImpRule_outputs_subset {φ0 : Proposition Atom} {b : IBranch Atom}
    {edges : IEdges} {φ ψ : Proposition Atom} {w : Nat}
    (hb : ∀ x ∈ b, x ∈ intUniverse φ0)
    (hsf : (⟨.pos, .imp φ ψ, w⟩ : ISF Atom) ∈ b) :
    ∀ x ∈ intTImpRule φ ψ w edges b, x ∈ intUniverse φ0 := by
  have hψsub : ψ ∈ intSubfmls φ0 := by
    have himp : (Proposition.imp φ ψ) ∈ intSubfmls φ0 := intUniverse_mem_formula (hb _ hsf)
    have hψmem : ψ ∈ intSubfmls (Proposition.imp φ ψ) := by simp [intSubfmls]
    exact intSubfmls_trans hψmem himp
  intro x hx
  simp only [intTImpRule, List.mem_filterMap, List.mem_filter, List.mem_eraseDups,
    List.mem_map] at hx
  obtain ⟨w', ⟨⟨y, hymem, hyeq⟩, -⟩, hxeq⟩ := hx
  have hwle : w' ≤ φ0.complexity + 1 := by
    subst hyeq; exact intUniverse_mem_label (hb y hymem)
  split at hxeq
  · split at hxeq
    · simp at hxeq
    · simp only [Option.some.injEq] at hxeq
      exact hxeq ▸ mem_intUniverse_of hwle hψsub
  · simp at hxeq

omit [Hashable Atom] in
/-- Containment for one full round of `applyAllTImpRules` (`Expansion.lean:118-127`): the
new formulas it appends stay inside `U(φ0)`, given the branch invariant `hb`. Dispatches to
`intTImpRule_outputs_subset` for each `T(φ → ψ)`-shaped branch member that fires; all other
members contribute nothing (the `match sf.sign, sf.formula with | .pos, .imp φ ψ => … | _, _
=> none` filter). -/
private lemma applyAllTImpRules_subset {φ0 : Proposition Atom} {b : IBranch Atom}
    {edges : IEdges} (hb : ∀ x ∈ b, x ∈ intUniverse φ0) :
    ∀ x ∈ applyAllTImpRules b edges, x ∈ intUniverse φ0 := by
  intro x hx
  simp only [applyAllTImpRules, List.mem_append] at hx
  rcases hx with hxb | hxnew
  · exact hb x hxb
  · simp only [List.mem_flatten, List.mem_filterMap] at hxnew
    obtain ⟨toAdd, ⟨sf, hsfmem, hsfeq⟩, hxmem⟩ := hxnew
    obtain ⟨s, ff, l⟩ := sf
    cases s with
    | neg => simp at hsfeq
    | pos =>
      cases ff with
      | atom p => simp at hsfeq
      | bot => simp at hsfeq
      | and a c => simp at hsfeq
      | or a c => simp at hsfeq
      | imp φ ψ =>
        simp only at hsfeq
        split at hsfeq
        · simp at hsfeq
        · simp only [Option.some.injEq] at hsfeq
          rw [← hsfeq] at hxmem
          -- STEP 1, task 574: `toAdd` is the whole result (no self-copy branch anymore).
          exact intTImpRule_outputs_subset hb hsfmem x hxmem

omit [Hashable Atom] in
/-- Containment is a loop invariant of `applyPersistenceFixpoint` (`Expansion.lean:133-139`):
iterating `applyAllTImpRules` to fixpoint never breaches `U(φ0)`, given the branch invariant
holds at entry. Proved by induction on the fuel counter, re-applying
`applyAllTImpRules_subset` at each non-fixpoint iteration. -/
private lemma applyPersistenceFixpoint_subset {φ0 : Proposition Atom} (b : IBranch Atom)
    (edges : IEdges) (fuel : Nat) (hb : ∀ x ∈ b, x ∈ intUniverse φ0) :
    ∀ x ∈ applyPersistenceFixpoint b edges fuel, x ∈ intUniverse φ0 := by
  induction fuel generalizing b with
  | zero => simpa [applyPersistenceFixpoint] using hb
  | succ fuel' ih =>
    simp only [applyPersistenceFixpoint]
    split
    · exact hb
    · exact ih _ (applyAllTImpRules_subset hb)

omit [Hashable Atom] [DecidableEq Atom] in
/-- **Step-level containment dispatch**: every signed formula emitted by
`intApplyRuleFull sf nextWorld b` stays inside `U(φ0)`, given the branch invariant `hb`, the
source membership `hsf`, and the world-bound hypothesis `hnw` (consumed only by the
world-creating `F(φ → ψ)` case, to show the freshly minted world label `nextWorld` stays inside
`U(φ0)`'s label range). Mirrors `modalApplyOne_outputs_subset`, `FmpMeasure.lean:669-754`,
simplified for the propositional connective set (2 ALPHA + 2 BETA rules, one world-creating
rule) versus Modal-K's box/diamond rule set (2 persistent + 2 fresh-world-minting rules).

**`hnw` is FALSE for branches `intExpandBranches` actually produces** -- refuted by direct
counterexample, not merely unproven. See the *Divergence witness* note in `Expansion.lean`
(immediately before its `## Decision Procedures` section): on the witness formula there, the
expansion loop mints worlds with unboundedly growing labels, so `nextWorld ≤ φ0.complexity + 1`
fails at the actual call sites reached during expansion. The lemma below remains
conditionally TRUE (its conclusion follows validly from its hypotheses), but `hnw` is not
dischargeable at those call sites -- so this lemma cannot, by itself, establish the
step-invariant an outer induction over `intExpandBranches` would need. The hypothesis is left
in place deliberately: removing it would be a statement change, out of scope here. -/
lemma intApplyRuleFull_outputs_subset {φ0 : Proposition Atom} {sf : ISF Atom}
    {nextWorld : Nat} {b : IBranch Atom}
    (hb : ∀ x ∈ b, x ∈ intUniverse φ0) (hsf : sf ∈ b)
    (hnw : nextWorld ≤ φ0.complexity + 1) :
    (match intApplyRuleFull sf nextWorld b with
      | .linearResult formulas _ _ => ∀ x ∈ formulas, x ∈ intUniverse φ0
      | .branchingResult branches _ => ∀ x ∈ branches.flatten, x ∈ intUniverse φ0
      | .notApplicable => True) := by
  have hsfU : sf ∈ intUniverse φ0 := hb sf hsf
  obtain ⟨s, ff, l⟩ := sf
  unfold intApplyRuleFull
  cases s with
  | pos =>
    cases ff with
    | atom p => trivial
    | bot => trivial
    | imp φ ψ =>
      -- Deliverable 6, branching arm: same shape as `.pos, .or` below (both φ and ψ are
      -- subformulas of `φ → ψ`, labels stay at `l`).
      have hsub : (Proposition.imp φ ψ) ∈ intSubfmls φ0 := intUniverse_mem_formula hsfU
      have hlab : l ≤ φ0.complexity + 1 := intUniverse_mem_label hsfU
      intro x hx
      simp only [List.mem_flatten, List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨t, (rfl | rfl), hxt⟩ := hx <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxt <;>
        (subst hxt
         exact mem_intUniverse_of hlab (intSubfmls_trans (by simp [intSubfmls]) hsub))
    | and φ ψ =>
      have hsub : (Proposition.and φ ψ) ∈ intSubfmls φ0 := intUniverse_mem_formula hsfU
      have hlab : l ≤ φ0.complexity + 1 := intUniverse_mem_label hsfU
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact mem_intUniverse_of hlab (intSubfmls_trans (by simp [intSubfmls]) hsub)
      · exact mem_intUniverse_of hlab (intSubfmls_trans (by simp [intSubfmls]) hsub)
    | or φ ψ =>
      have hsub : (Proposition.or φ ψ) ∈ intSubfmls φ0 := intUniverse_mem_formula hsfU
      have hlab : l ≤ φ0.complexity + 1 := intUniverse_mem_label hsfU
      intro x hx
      simp only [List.mem_flatten, List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨t, (rfl | rfl), hxt⟩ := hx <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxt <;>
        (subst hxt
         exact mem_intUniverse_of hlab (intSubfmls_trans (by simp [intSubfmls]) hsub))
  | neg =>
    cases ff with
    | atom p => trivial
    | bot => trivial
    | and φ ψ =>
      have hsub : (Proposition.and φ ψ) ∈ intSubfmls φ0 := intUniverse_mem_formula hsfU
      have hlab : l ≤ φ0.complexity + 1 := intUniverse_mem_label hsfU
      intro x hx
      simp only [List.mem_flatten, List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨t, (rfl | rfl), hxt⟩ := hx <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxt <;>
        (subst hxt
         exact mem_intUniverse_of hlab (intSubfmls_trans (by simp [intSubfmls]) hsub))
    | or φ ψ =>
      have hsub : (Proposition.or φ ψ) ∈ intSubfmls φ0 := intUniverse_mem_formula hsfU
      have hlab : l ≤ φ0.complexity + 1 := intUniverse_mem_label hsfU
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact mem_intUniverse_of hlab (intSubfmls_trans (by simp [intSubfmls]) hsub)
      · exact mem_intUniverse_of hlab (intSubfmls_trans (by simp [intSubfmls]) hsub)
    | imp φ ψ =>
      have himp : (Proposition.imp φ ψ) ∈ intSubfmls φ0 := intUniverse_mem_formula hsfU
      simp only [intFImpRule, propagatePersistence, posFormulasAt]
      intro x hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_map, List.mem_filterMap] at hx
      rcases hx with (rfl | rfl) | ⟨ψ', ⟨sf', hsf'mem, hsf'eq⟩, hxeq⟩
      · exact mem_intUniverse_of hnw (intSubfmls_trans (by simp [intSubfmls]) himp)
      · exact mem_intUniverse_of hnw (intSubfmls_trans (by simp [intSubfmls]) himp)
      · split at hsf'eq
        · simp only [Option.some.injEq] at hsf'eq
          have hsf'U : sf' ∈ intUniverse φ0 := hb sf' hsf'mem
          exact hxeq ▸ mem_intUniverse_of hnw (hsf'eq ▸ intUniverse_mem_formula hsf'U)
        · simp at hsf'eq

omit [Hashable Atom] in
/-- The per-branch counting measure `R(b, e) := |U \ b| + |U \ e|` (mirrors `modalWork`,
`FmpMeasure.lean:190-193`): the number of universe elements not yet on the branch, plus
the number not yet expanded. Strictly decreases per expansion step despite persistence
(`intExpMeasure_step_lt`, not yet proved). -/
def intWork (U b e : List (ISF Atom)) : Nat :=
  U.countP (fun sf => !(b.any (· == sf))) + U.countP (fun sf => !(e.any (· == sf)))

omit [Hashable Atom] in
/-- The base-3 damped worklist measure `Σ 3^(intWork U bᵢ eᵢ)` over the zipped
branch/expanded-set worklist (mirrors `modalExpMeasure`, `FmpMeasure.lean:197-200`). -/
def intExpMeasure (U : List (ISF Atom))
    (branches expandedSets : List (List (ISF Atom))) : Nat :=
  ((branches.zip expandedSets).map (fun p => 3 ^ intWork U p.1 p.2)).sum

/-! ## Strict-Decrease Engine -/

omit [Hashable Atom] in
/-- **Combinatorial core** (mirrors `modalCount_notMem_append_drop`, `FmpMeasure.lean:2440`):
appending `x` (a member of `U`, not yet in `l`) to the exclusion list `l` strictly drops, by at
least one, the count of `U`-members excluded by `l`. -/
private lemma intCount_notMem_append_drop
    {α : Type*} [BEq α] [LawfulBEq α]
    (U l : List α) (x : α)
    (hxU : x ∈ U) (hxl : l.any (· == x) = false) :
    U.countP (fun y => !((l ++ [x]).any (· == y))) + 1 ≤
      U.countP (fun y => !(l.any (· == y))) := by
  induction U with
  | nil => simp at hxU
  | cons u us ih =>
    rcases List.mem_cons.mp hxU with rfl | hxU'
    · have h1 : (x :: us).countP (fun y => !(l.any (· == y))) =
          us.countP (fun y => !(l.any (· == y))) + 1 := by
        rw [List.countP_cons]; simp [hxl]
      have h2 : (x :: us).countP (fun y => !((l ++ [x]).any (· == y))) =
          us.countP (fun y => !((l ++ [x]).any (· == y))) := by
        rw [List.countP_cons]; simp [List.any_append]
      have hmono : us.countP (fun y => !((l ++ [x]).any (· == y))) ≤
          us.countP (fun y => !(l.any (· == y))) := by
        have hsub : List.Sublist (us.filter (fun y => !((l ++ [x]).any (· == y))))
            (us.filter (fun y => !(l.any (· == y)))) := by
          apply List.monotone_filter_right
          intro y hy
          simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false,
            Bool.not_or, Bool.and_eq_true] at hy
          exact hy.1
        simpa [List.countP_eq_length_filter] using hsub.length_le
      omega
    · by_cases hlu : l.any (· == u)
      · have h1 : (u :: us).countP (fun y => !(l.any (· == y))) =
            us.countP (fun y => !(l.any (· == y))) := by
          rw [List.countP_cons]; simp [hlu]
        have hlu' : (l ++ [x]).any (· == u) = true := by
          rw [List.any_append, hlu, Bool.true_or]
        have h2 : (u :: us).countP (fun y => !((l ++ [x]).any (· == y))) =
            us.countP (fun y => !((l ++ [x]).any (· == y))) := by
          rw [List.countP_cons, hlu']; simp
        have := ih hxU'
        omega
      · by_cases hux : u == x
        · have hux' : u = x := LawfulBEq.eq_of_beq hux
          subst hux'
          have h1 : (u :: us).countP (fun y => !(l.any (· == y))) =
              us.countP (fun y => !(l.any (· == y))) + 1 := by
            rw [List.countP_cons]; simp [hlu]
          have h2 : (u :: us).countP (fun y => !((l ++ [u]).any (· == y))) =
              us.countP (fun y => !((l ++ [u]).any (· == y))) := by
            rw [List.countP_cons]; simp [List.any_append]
          have hmono : us.countP (fun y => !((l ++ [u]).any (· == y))) ≤
              us.countP (fun y => !(l.any (· == y))) := by
            have hsub : List.Sublist (us.filter (fun y => !((l ++ [u]).any (· == y))))
                (us.filter (fun y => !(l.any (· == y)))) := by
              apply List.monotone_filter_right
              intro y hy
              simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false,
                Bool.not_or, Bool.and_eq_true] at hy
              exact hy.1
            simpa [List.countP_eq_length_filter] using hsub.length_le
          omega
        · simp only [Bool.not_eq_true] at hlu
          have h1 : (u :: us).countP (fun y => !(l.any (· == y))) =
              us.countP (fun y => !(l.any (· == y))) + 1 := by
            rw [List.countP_cons]; simp [hlu]
          have hlux' : (l ++ [x]).any (· == u) = false := by
            rw [List.any_append, hlu, Bool.false_or, List.any_cons, List.any_nil,
              Bool.or_false, beq_eq_false_iff_ne]
            simp only [beq_iff_eq] at hux
            exact fun h => hux h.symm
          have h2 : (u :: us).countP (fun y => !((l ++ [x]).any (· == y))) =
              us.countP (fun y => !((l ++ [x]).any (· == y))) + 1 := by
            rw [List.countP_cons]; simp [hlux']
          have := ih hxU'
          omega

omit [Hashable Atom] in
/-- **Weak monotonicity** (mirrors `modalCount_notMem_mono`, `FmpMeasure.lean:2517`): growing
the exclusion list's underlying membership set (`b ⊆ b'`) can only decrease (never increase)
the count of `U`-members excluded by it. -/
private lemma intCount_notMem_mono
    {α : Type*} [BEq α] [LawfulBEq α]
    (U b b' : List α)
    (hsub : ∀ z ∈ b, z ∈ b') :
    U.countP (fun y => !(b'.any (· == y))) ≤ U.countP (fun y => !(b.any (· == y))) := by
  have hsubf : List.Sublist (U.filter (fun y => !(b'.any (· == y))))
      (U.filter (fun y => !(b.any (· == y)))) := by
    apply List.monotone_filter_right
    intro y hy
    rw [Bool.not_eq_true'] at hy ⊢
    rw [List.any_eq_false] at hy ⊢
    intro z hz
    exact hy z (hsub z hz)
  simpa [List.countP_eq_length_filter] using hsubf.length_le

omit [Hashable Atom] in
/-- **`R`-drop** (mirrors `modalWork_drop_linear`, `FmpMeasure.lean:2539`): when the fired
formula `sf` is added to the expanded set (`e' = e ++ [sf]`) and the child branch `b'` weakly
extends `b`, the counting measure strictly drops by at least one. Unlike the Modal-K template,
the intuitionistic calculus has no separate "persistent" step kind (persistence is exhausted to
fixpoint via `applyPersistenceFixpoint` BEFORE `intStepBranch` runs), so this single lemma covers
every arm of `intExpandBranches`'s `go` -- ALPHA (`newEdge = none`), world-creation
(`newEdge = some _`, no `Sfor`-reuse), and the `Sfor`-containment reuse case (`b' = b`, `hsub`
trivial by reflexivity) -- as well as each BETA sub-branch. -/
private lemma intWork_drop
    (U b b' e : List (ISF Atom)) (sf : ISF Atom)
    (hsfU : sf ∈ U) (hsfe : e.any (· == sf) = false) (hsub : ∀ z ∈ b, z ∈ b') :
    intWork U b' (e ++ [sf]) + 1 ≤ intWork U b e := by
  unfold intWork
  have hb := intCount_notMem_mono U b b' hsub
  have he := intCount_notMem_append_drop U e sf hsfU hsfe
  omega

omit [Hashable Atom] in
/-- `intExpMeasure` splits over a single distinguished position, given length-aligned prefixes
(mirrors `modalExpMeasure_split`, `FmpMeasure.lean:2826`). -/
private lemma intExpMeasure_split
    (U : List (ISF Atom))
    (done : List (List (ISF Atom))) (doneExp : List (List (ISF Atom)))
    (bh e : List (ISF Atom))
    (rest : List (List (ISF Atom))) (restEs : List (List (ISF Atom)))
    (hlen : done.length = doneExp.length) :
    intExpMeasure U (done ++ bh :: rest) (doneExp ++ e :: restEs)
      = intExpMeasure U done doneExp + 3 ^ intWork U bh e
        + intExpMeasure U rest restEs := by
  simp only [intExpMeasure, List.zip_append hlen, List.zip_cons_cons,
             List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  omega

omit [Hashable Atom] in
/-- Additivity of `intExpMeasure` over list append (mirrors `modalExpMeasure_append`,
`FmpMeasure.lean:2843`). -/
private lemma intExpMeasure_append
    (U : List (ISF Atom))
    (l1 l2 : List (List (ISF Atom))) (e1 e2 : List (List (ISF Atom)))
    (h : l1.length = e1.length) :
    intExpMeasure U (l1 ++ l2) (e1 ++ e2)
      = intExpMeasure U l1 e1 + intExpMeasure U l2 e2 := by
  simp only [intExpMeasure, List.zip_append h, List.map_append, List.sum_append]

omit [Hashable Atom] in
/-- **The strict-decrease engine** (mirrors `modalExpMeasure_step_lt`'s linear
case, `FmpMeasure.lean:2873`): one `intExpandBranches`'s `go` step that replaces the single
active branch `bh` by a single successor `b'` -- covering the ALPHA arm (`newEdge = none`,
`b' = Branch.extendMany bh newForms`), the world-creating arm with no `Sfor`-reuse
(`newEdge = some _`, `b' = Branch.extendMany bh newForms`), and the `Sfor`-containment reuse arm
(`b' = bh` unchanged, `hsub` trivially reflexive) -- strictly decreases `intExpMeasure`. Takes the
branch-containment invariant `hb` as a hypothesis (as the Modal-K template does for its own `hb`),
NOT `intExpandBranches_world_bound` (a distinct, harder distinct-label-count fact this lemma does
not need): only `sf ∈ intUniverse φ0` is required, obtained directly from `hb` together with
`sf ∈ bh` (read off `intStepBranch`'s internal `findSome?` witness). -/
lemma intExpMeasure_step_lt
    (φ0 : Proposition Atom)
    (done bt : List (List (ISF Atom)))
    (doneExp es : List (List (ISF Atom)))
    (newExp : List (ISF Atom))
    (bh e : List (ISF Atom)) (nw nw' : Nat) (newForms : List (ISF Atom))
    (newEdge : Option (Nat × Nat)) (b' : List (ISF Atom))
    (hdlen : done.length = doneExp.length)
    (hb : ∀ x ∈ bh, x ∈ intUniverse φ0)
    (hsub : ∀ z ∈ bh, z ∈ b')
    (hstep : intStepBranch bh e nw = some (.linearResult newForms nw' newEdge, newExp)) :
    intExpMeasure (intUniverse φ0) (done ++ [b'] ++ bt) (doneExp ++ [newExp] ++ es) + 1
      ≤ intExpMeasure (intUniverse φ0) (done ++ bh :: bt) (doneExp ++ e :: es) := by
  set U := intUniverse φ0 with hUdef
  have hrhs := intExpMeasure_split U done doneExp bh e bt es hdlen
  have hlhs : intExpMeasure U (done ++ [b'] ++ bt) (doneExp ++ [newExp] ++ es) =
      intExpMeasure U done doneExp + 3 ^ intWork U b' newExp + intExpMeasure U bt es := by
    have hlen1 : (done ++ [b']).length = (doneExp ++ [newExp]).length := by simp [hdlen]
    rw [intExpMeasure_append U (done ++ [b']) bt (doneExp ++ [newExp]) es hlen1,
        intExpMeasure_append U done [b'] doneExp [newExp] hdlen]
    simp [intExpMeasure]
  rw [hrhs, hlhs]
  suffices h : 3 ^ intWork U b' newExp + 1 ≤ 3 ^ intWork U bh e by omega
  simp only [intStepBranch] at hstep
  obtain ⟨sf, hsfmem, hfound⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hfound with hany
  simp only [Bool.not_eq_true] at hany
  have hsfU : sf ∈ U := hb sf hsfmem
  cases hint : intApplyRuleFull sf nw bh with
  | notApplicable => simp [hint] at hfound
  | linearResult fs nw2 ne =>
    simp only [hint, Option.some.injEq, Prod.mk.injEq] at hfound
    obtain ⟨hfs, hexp⟩ := hfound
    injection hfs with hfseq hnweq hneeq
    subst hfseq; subst hexp
    have hdrop : intWork U b' (e ++ [sf]) + 1 ≤ intWork U bh e :=
      intWork_drop U bh b' e sf hsfU hany hsub
    have hC : 1 ≤ intWork U bh e := by omega
    have h0 : intWork U b' (e ++ [sf]) ≤ intWork U bh e - 1 := by omega
    exact pow3_add_one_le hC h0
  | branchingResult bs nw2 =>
    simp only [hint, Option.some.injEq, Prod.mk.injEq] at hfound
    exact absurd hfound.1 (by simp)

omit [Hashable Atom] in
/-- `intExpMeasure` over a worklist of the form `newBs` zipped with a CONSTANT expanded set
`newExp` collapses to a plain sum over `newBs` (mirrors `modalExpMeasure_const_exp`,
`FmpMeasure.lean:2856`): needed by `intExpMeasure_step_lt_branch` to unfold the branching arm's
`branches'.map (fun _ => newExp)` expanded-set shape. -/
private lemma intExpMeasure_const_exp
    (U : List (ISF Atom))
    (newBs : List (List (ISF Atom)))
    (newExp : List (ISF Atom)) :
    intExpMeasure U newBs (newBs.map (fun _ => newExp))
      = (newBs.map (fun child => 3 ^ intWork U child newExp)).sum := by
  simp only [intExpMeasure, ← List.map_prod_left_eq_zip, List.map_map, Function.comp_def]

omit [Hashable Atom] in
/-- **The BETA-arm strict-decrease lemma** (mirrors
`modalExpMeasure_step_lt`'s branching case, `FmpMeasure.lean:2921-2937`): completes
`intExpMeasure_step_lt`'s coverage of `intStepBranch`'s `.branchingResult` arm -- the two
branching rules, `.pos, .or` (F-or) and `.neg, .and` (T-and), both producing a literal
2-element list of singleton sub-branches directly in `intApplyRuleFull` (`Rules.lean:254,260`),
with the next-world counter unchanged (`nw' = nw`, since branching never creates a world).
Applies `intWork_drop` twice (once per sub-branch, each `hsub` trivial since every sub-branch is
`bh` extended by exactly one new formula) and combines via `pow3_two_add_one_le`
(`Cslib/Foundations/Logic/Tableau/Measure.lean:117`), exactly mirroring the Modal-K template's
own branching case. -/
lemma intExpMeasure_step_lt_branch
    (φ0 : Proposition Atom)
    (done bt : List (List (ISF Atom)))
    (doneExp es : List (List (ISF Atom)))
    (newExp : List (ISF Atom))
    (bh e : List (ISF Atom)) (nw nw' : Nat)
    (branches' : List (List (ISF Atom)))
    (hdlen : done.length = doneExp.length)
    (hb : ∀ x ∈ bh, x ∈ intUniverse φ0)
    (hstep : intStepBranch bh e nw = some (.branchingResult branches' nw', newExp)) :
    intExpMeasure (intUniverse φ0)
        (done ++ branches'.map (Branch.extendMany bh ·) ++ bt)
        (doneExp ++ branches'.map (fun _ => newExp) ++ es) + 1
      ≤ intExpMeasure (intUniverse φ0) (done ++ bh :: bt) (doneExp ++ e :: es) := by
  set U := intUniverse φ0 with hUdef
  have hrhs := intExpMeasure_split U done doneExp bh e bt es hdlen
  have hlhs : intExpMeasure U (done ++ branches'.map (Branch.extendMany bh ·) ++ bt)
        (doneExp ++ branches'.map (fun _ => newExp) ++ es) =
      intExpMeasure U done doneExp +
        (branches'.map (fun br => 3 ^ intWork U (Branch.extendMany bh br) newExp)).sum +
        intExpMeasure U bt es := by
    have hlen1 : (done ++ branches'.map (Branch.extendMany bh ·)).length
        = (doneExp ++ branches'.map (fun _ => newExp)).length := by
      simp [List.length_append, hdlen]
    rw [intExpMeasure_append U (done ++ branches'.map (Branch.extendMany bh ·)) bt
          (doneExp ++ branches'.map (fun _ => newExp)) es hlen1,
        intExpMeasure_append U done (branches'.map (Branch.extendMany bh ·))
          doneExp (branches'.map (fun _ => newExp)) hdlen,
        show branches'.map (fun (_ : List (ISF Atom)) => newExp)
            = (branches'.map (Branch.extendMany bh ·)).map (fun _ => newExp) by
          simp [Function.comp_def],
        intExpMeasure_const_exp]
    simp only [List.map_map, Function.comp_def]
  rw [hrhs, hlhs]
  suffices h : (branches'.map (fun br => 3 ^ intWork U (Branch.extendMany bh br) newExp)).sum + 1 ≤
      3 ^ intWork U bh e by omega
  simp only [intStepBranch] at hstep
  obtain ⟨sf, hsfmem, hfound⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hfound with hany
  simp only [Bool.not_eq_true] at hany
  have hsfU : sf ∈ U := hb sf hsfmem
  cases hint : intApplyRuleFull sf nw bh with
  | notApplicable => simp [hint] at hfound
  | linearResult fs nw2 ne =>
    simp only [hint, Option.some.injEq, Prod.mk.injEq] at hfound
    exact absurd hfound.1 (by simp)
  | branchingResult bs nw2 =>
    simp only [hint, Option.some.injEq, Prod.mk.injEq] at hfound
    obtain ⟨hbs, hexp⟩ := hfound
    injection hbs with hbseq hnweq
    subst hbseq; subst hexp
    obtain ⟨s, ff, l⟩ := sf
    cases s with
    | pos =>
      cases ff with
      | atom x => simp [intApplyRuleFull] at hint
      | bot => simp [intApplyRuleFull] at hint
      | imp φ ψ =>
        -- Deliverable 6, branching arm: same shape as `.pos, .or` below, mixed signs.
        simp only [intApplyRuleFull, IntRuleResult.branchingResult.injEq] at hint
        obtain ⟨hbrs, hnw'eq⟩ := hint
        subst hbrs
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        have hdrop0 : intWork U (Branch.extendMany bh [⟨.neg, φ, l⟩])
            (e ++ [⟨.pos, .imp φ ψ, l⟩]) + 1 ≤ intWork U bh e :=
          intWork_drop U bh (Branch.extendMany bh [⟨.neg, φ, l⟩]) e ⟨.pos, .imp φ ψ, l⟩ hsfU hany
            (fun z hz => by simp only [Branch.extendMany, List.mem_append]; exact Or.inr hz)
        have hdrop1 : intWork U (Branch.extendMany bh [⟨.pos, ψ, l⟩])
            (e ++ [⟨.pos, .imp φ ψ, l⟩]) + 1 ≤ intWork U bh e :=
          intWork_drop U bh (Branch.extendMany bh [⟨.pos, ψ, l⟩]) e ⟨.pos, .imp φ ψ, l⟩ hsfU hany
            (fun z hz => by simp only [Branch.extendMany, List.mem_append]; exact Or.inr hz)
        have hC : 1 ≤ intWork U bh e := by omega
        have h0 : intWork U (Branch.extendMany bh [⟨.neg, φ, l⟩])
            (e ++ [⟨.pos, .imp φ ψ, l⟩]) ≤ intWork U bh e - 1 := by omega
        have h1 : intWork U (Branch.extendMany bh [⟨.pos, ψ, l⟩])
            (e ++ [⟨.pos, .imp φ ψ, l⟩]) ≤ intWork U bh e - 1 := by omega
        exact pow3_two_add_one_le hC h0 h1
      | and φ ψ => simp [intApplyRuleFull] at hint
      | or φ ψ =>
        simp only [intApplyRuleFull, IntRuleResult.branchingResult.injEq] at hint
        obtain ⟨hbrs, hnw'eq⟩ := hint
        subst hbrs
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        have hdrop0 : intWork U (Branch.extendMany bh [⟨.pos, φ, l⟩])
            (e ++ [⟨.pos, .or φ ψ, l⟩]) + 1 ≤ intWork U bh e :=
          intWork_drop U bh (Branch.extendMany bh [⟨.pos, φ, l⟩]) e ⟨.pos, .or φ ψ, l⟩ hsfU hany
            (fun z hz => by simp only [Branch.extendMany, List.mem_append]; exact Or.inr hz)
        have hdrop1 : intWork U (Branch.extendMany bh [⟨.pos, ψ, l⟩])
            (e ++ [⟨.pos, .or φ ψ, l⟩]) + 1 ≤ intWork U bh e :=
          intWork_drop U bh (Branch.extendMany bh [⟨.pos, ψ, l⟩]) e ⟨.pos, .or φ ψ, l⟩ hsfU hany
            (fun z hz => by simp only [Branch.extendMany, List.mem_append]; exact Or.inr hz)
        have hC : 1 ≤ intWork U bh e := by omega
        have h0 : intWork U (Branch.extendMany bh [⟨.pos, φ, l⟩])
            (e ++ [⟨.pos, .or φ ψ, l⟩]) ≤ intWork U bh e - 1 := by omega
        have h1 : intWork U (Branch.extendMany bh [⟨.pos, ψ, l⟩])
            (e ++ [⟨.pos, .or φ ψ, l⟩]) ≤ intWork U bh e - 1 := by omega
        exact pow3_two_add_one_le hC h0 h1
    | neg =>
      cases ff with
      | atom x => simp [intApplyRuleFull] at hint
      | bot => simp [intApplyRuleFull] at hint
      | imp φ ψ => simp [intApplyRuleFull] at hint
      | or φ ψ => simp [intApplyRuleFull] at hint
      | and φ ψ =>
        simp only [intApplyRuleFull, IntRuleResult.branchingResult.injEq] at hint
        obtain ⟨hbrs, hnw'eq⟩ := hint
        subst hbrs
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        have hdrop0 : intWork U (Branch.extendMany bh [⟨.neg, φ, l⟩])
            (e ++ [⟨.neg, .and φ ψ, l⟩]) + 1 ≤ intWork U bh e :=
          intWork_drop U bh (Branch.extendMany bh [⟨.neg, φ, l⟩]) e ⟨.neg, .and φ ψ, l⟩ hsfU hany
            (fun z hz => by simp only [Branch.extendMany, List.mem_append]; exact Or.inr hz)
        have hdrop1 : intWork U (Branch.extendMany bh [⟨.neg, ψ, l⟩])
            (e ++ [⟨.neg, .and φ ψ, l⟩]) + 1 ≤ intWork U bh e :=
          intWork_drop U bh (Branch.extendMany bh [⟨.neg, ψ, l⟩]) e ⟨.neg, .and φ ψ, l⟩ hsfU hany
            (fun z hz => by simp only [Branch.extendMany, List.mem_append]; exact Or.inr hz)
        have hC : 1 ≤ intWork U bh e := by omega
        have h0 : intWork U (Branch.extendMany bh [⟨.neg, φ, l⟩])
            (e ++ [⟨.neg, .and φ ψ, l⟩]) ≤ intWork U bh e - 1 := by omega
        have h1 : intWork U (Branch.extendMany bh [⟨.neg, ψ, l⟩])
            (e ++ [⟨.neg, .and φ ψ, l⟩]) ≤ intWork U bh e - 1 := by omega
        exact pow3_two_add_one_le hC h0 h1

omit [Hashable Atom] in
/-- At the tableau entry point, the worklist measure over the universe `intUniverse φ` is
bounded by `intFuel φ` (mirrors `modalExpMeasure_entry_le_fuel`,
`FmpMeasure.lean:208-251`). The initial singleton branch `[⟨.neg, φ, 0⟩]` with empty
expanded-set `[]` gives `intWork (intUniverse φ) [⟨.neg, φ, 0⟩] [] ≤ 2 * |intUniverse φ|`
(the branch-exclusion term is bounded by `List.countP_le_length`, the expanded-set term is
exactly the full length since `e = []` excludes nothing); `intUniverse_length_le` then bounds
`|intUniverse φ|` by `2 * (2 * φ.complexity + 1) * (φ.complexity + 2)`, so `2 * |intUniverse φ|`
is bounded by `4 * (2 * φ.complexity + 1) * (φ.complexity + 2)` -- exactly the doubled exponent
`intFuel φ` was raised to (`Expansion.lean`), closing with equality (no slack
needed, unlike the modal analogue's messier world-bound formula). -/
lemma intExpMeasure_init_le_fuel (φ : Proposition Atom) :
    intExpMeasure (intUniverse φ) [[(⟨.neg, φ, 0⟩ : ISF Atom)]] [[]] ≤ intFuel φ := by
  have hmeas : intExpMeasure (intUniverse φ) [[(⟨.neg, φ, 0⟩ : ISF Atom)]] [[]]
      = 3 ^ intWork (intUniverse φ) [(⟨.neg, φ, 0⟩ : ISF Atom)] [] := by
    simp [intExpMeasure]
  rw [hmeas]
  have hwork : intWork (intUniverse φ) [(⟨.neg, φ, 0⟩ : ISF Atom)] [] ≤
      2 * (intUniverse φ).length := by
    have heq : intWork (intUniverse φ) [(⟨.neg, φ, 0⟩ : ISF Atom)] [] =
        (intUniverse φ).countP
          (fun sf => !(([(⟨.neg, φ, 0⟩ : ISF Atom)]).any (· == sf))) +
        (intUniverse φ).countP
          (fun sf => !((([] : List (ISF Atom))).any (· == sf))) := rfl
    rw [heq]
    have h2 : (intUniverse φ).countP
        (fun sf => !((([] : List (ISF Atom))).any (· == sf))) = (intUniverse φ).length := by
      simp
    rw [h2]
    have h1 : (intUniverse φ).countP
        (fun sf => !(([(⟨.neg, φ, 0⟩ : ISF Atom)]).any (· == sf))) ≤
        (intUniverse φ).length :=
      List.countP_le_length
    omega
  have hUlen := intUniverse_length_le φ
  have hfinal : intWork (intUniverse φ) [(⟨.neg, φ, 0⟩ : ISF Atom)] [] ≤
      4 * (2 * φ.complexity + 1) * (φ.complexity + 2) := by
    have h2U : 2 * (intUniverse φ).length ≤
        2 * (2 * (2 * φ.complexity + 1) * (φ.complexity + 2)) :=
      Nat.mul_le_mul_left 2 hUlen
    have heq : 2 * (2 * (2 * φ.complexity + 1) * (φ.complexity + 2)) =
        4 * (2 * φ.complexity + 1) * (φ.complexity + 2) := by ring
    omega
  calc 3 ^ intWork (intUniverse φ) [(⟨.neg, φ, 0⟩ : ISF Atom)] []
      ≤ 3 ^ (4 * (2 * φ.complexity + 1) * (φ.complexity + 2)) :=
        Nat.pow_le_pow_right (by norm_num) hfinal
    _ = intFuel φ := rfl

/-! ## Persistence-loop fuel-sufficiency (`sat_timp` STOP-gate gap 1 continuation,
`Scheme.lean:485-533`)

Closes GAP 1 of the `sat_timp` STOP-gate above: a genuine termination bound for
`applyPersistenceFixpoint`'s OWN recursion, distinct from `intExpMeasure_step_lt` (which bounds
the OUTER alpha/beta/world-creation loop only). The key fact: each non-fixpoint round of
`applyAllTImpRules` strictly drops the count of `intUniverse φ0`-cells not yet on the branch
(mirrors the `intWork`/`intCount_notMem_append_drop` engine above, restricted to the
branch-membership term alone, since persistence has no separate `e` "expanded" set). Since this
count is bounded above by `|intUniverse φ0|` (a fixed polynomial in `φ0.complexity`), fuel at
least this count suffices for a genuine fixpoint. GAP 2 (determinacy) is NOT addressed here — see
the investigation note after `applyPersistenceFixpoint_genuine_of_count_le_fuel` below. -/

omit [Hashable Atom] in
/-- Every output of `intTImpRule` is, by construction, NOT already on the branch it fires from
(the rule's inner guard `if b.any (… ψ …) then none else some …` only ever fires on the `else`
branch, i.e. exactly when `ψ@w'` is absent). -/
private lemma intTImpRule_output_notMem {φ ψ : Proposition Atom} {w : Nat} {edges : IEdges}
    {b : IBranch Atom} {x : ISF Atom} (hx : x ∈ intTImpRule φ ψ w edges b) :
    b.any (· == x) = false := by
  simp only [intTImpRule, List.mem_filterMap] at hx
  obtain ⟨w', -, hxeq⟩ := hx
  split at hxeq
  · split at hxeq
    · simp at hxeq
    · rename_i hnotψ
      simp only [Option.some.injEq] at hxeq
      rw [← hxeq, Bool.eq_false_iff]
      intro hcon
      apply hnotψ
      rw [List.any_eq_true] at hcon ⊢
      obtain ⟨sf, hsfmem, hsfeq⟩ := hcon
      refine ⟨sf, hsfmem, ?_⟩
      rw [beq_iff_eq] at hsfeq
      simp [hsfeq]
  · simp at hxeq

omit [Hashable Atom] in
/-- One non-fixpoint round of `applyAllTImpRules` strictly drops the count of `intUniverse φ0`
cells not yet on the branch, given branch-containment `hb` (the fuel-sufficiency gap 1
continuation; mirrors `intWork_drop`'s combinatorial core, restricted to the branch-membership
term since persistence tracks no separate expanded set). -/
private lemma applyAllTImpRules_count_drop
    {φ0 : Proposition Atom} {b : IBranch Atom} {edges : IEdges}
    (hb : ∀ x ∈ b, x ∈ intUniverse φ0)
    (hne : (applyAllTImpRules b edges).length ≠ b.length) :
    (intUniverse φ0).countP (fun sf => !((applyAllTImpRules b edges).any (· == sf))) + 1 ≤
      (intUniverse φ0).countP (fun sf => !(b.any (· == sf))) := by
  have happend : applyAllTImpRules b edges =
      b ++ (b.filterMap fun sf =>
        match sf.sign, sf.formula with
        | .pos, .imp φ ψ =>
          let toAdd := intTImpRule φ ψ sf.label edges b
          if toAdd.isEmpty then none else some toAdd
        | _, _ => none).flatten := rfl
  set nf := (b.filterMap fun sf =>
        match sf.sign, sf.formula with
        | .pos, .imp φ ψ =>
          let toAdd := intTImpRule φ ψ sf.label edges b
          if toAdd.isEmpty then none else some toAdd
        | _, _ => none) with hnf_def
  have hne' : nf.flatten ≠ [] := by
    intro hcontra
    apply hne
    rw [happend, hcontra, List.append_nil]
  obtain ⟨x, hxmem⟩ := List.exists_mem_of_ne_nil _ hne'
  have hxU : x ∈ intUniverse φ0 := by
    have hsub := applyAllTImpRules_subset (φ0 := φ0) (edges := edges) hb (x := x)
    apply hsub
    rw [happend]
    exact List.mem_append_right b hxmem
  have hxnotb : b.any (· == x) = false := by
    simp only [hnf_def, List.mem_flatten, List.mem_filterMap] at hxmem
    obtain ⟨toAdd, ⟨sf, hsfmem, hsfeq⟩, hxmem⟩ := hxmem
    obtain ⟨s, ff, l⟩ := sf
    cases s with
    | neg => simp at hsfeq
    | pos =>
      cases ff with
      | atom p => simp at hsfeq
      | bot => simp at hsfeq
      | and a c => simp at hsfeq
      | or a c => simp at hsfeq
      | imp φ ψ =>
        simp only at hsfeq
        split at hsfeq
        · simp at hsfeq
        · simp only [Option.some.injEq] at hsfeq
          rw [← hsfeq] at hxmem
          -- STEP 1, task 574: `toAdd` is the whole result (no self-copy branch anymore).
          exact intTImpRule_output_notMem hxmem
  have hdrop := intCount_notMem_append_drop (intUniverse φ0) b x hxU hxnotb
  have hmono := intCount_notMem_mono (intUniverse φ0) (b ++ [x]) (applyAllTImpRules b edges)
    (by
      rw [happend]
      intro z hz
      rw [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact List.mem_append_left _ hz
      · exact List.mem_append_right _ hxmem)
  omega

omit [Hashable Atom] in
/-- **Genuine-fixpoint sufficiency** (closes `sat_timp` STOP-gate GAP 1):
`applyPersistenceFixpoint b edges fuel` is a genuine fixpoint of `applyAllTImpRules` — applying
one more round changes nothing — whenever the fuel is at least the count of `intUniverse φ0`
cells not yet claimed by `b`. Combined with `intUniverse_length_le` (a fixed polynomial bound in
`φ0.complexity`), any fuel `≥ |intUniverse φ0|` suffices regardless of `b`'s shape. -/
private lemma applyPersistenceFixpoint_genuine_of_count_le_fuel
    {φ0 : Proposition Atom} {edges : IEdges} (b : IBranch Atom) (fuel : Nat)
    (hb : ∀ x ∈ b, x ∈ intUniverse φ0)
    (hfuel : (intUniverse φ0).countP (fun sf => !(b.any (· == sf))) ≤ fuel) :
    applyAllTImpRules (applyPersistenceFixpoint b edges fuel) edges
      = applyPersistenceFixpoint b edges fuel := by
  induction fuel generalizing b with
  | zero =>
    have hlen : (applyAllTImpRules b edges).length = b.length := by
      by_contra hne
      have := applyAllTImpRules_count_drop (φ0 := φ0) hb hne
      omega
    have hval : applyAllTImpRules b edges = b := by
      have happend : applyAllTImpRules b edges = b ++
          (b.filterMap fun sf =>
            match sf.sign, sf.formula with
            | .pos, .imp φ ψ =>
              let toAdd := intTImpRule φ ψ sf.label edges b
              if toAdd.isEmpty then none else some toAdd
            | _, _ => none).flatten := rfl
      rw [happend] at hlen ⊢
      have hflat : (b.filterMap fun sf =>
            match sf.sign, sf.formula with
            | .pos, .imp φ ψ =>
              let toAdd := intTImpRule φ ψ sf.label edges b
              if toAdd.isEmpty then none else some toAdd
            | _, _ => none).flatten = [] := by
        have hlen2 := hlen
        rw [List.length_append] at hlen2
        exact List.length_eq_zero_iff.mp (by omega)
      rw [hflat, List.append_nil]
    simpa [applyPersistenceFixpoint] using hval
  | succ fuel' ih =>
    simp only [applyPersistenceFixpoint]
    split
    · rename_i hlenb
      rw [beq_iff_eq] at hlenb
      have happend : applyAllTImpRules b edges = b ++
          (b.filterMap fun sf =>
            match sf.sign, sf.formula with
            | .pos, .imp φ ψ =>
              let toAdd := intTImpRule φ ψ sf.label edges b
              if toAdd.isEmpty then none else some toAdd
            | _, _ => none).flatten := rfl
      rw [happend] at hlenb
      have hflat : (b.filterMap fun sf =>
            match sf.sign, sf.formula with
            | .pos, .imp φ ψ =>
              let toAdd := intTImpRule φ ψ sf.label edges b
              if toAdd.isEmpty then none else some toAdd
            | _, _ => none).flatten = [] := by
        have hlen2 := hlenb
        rw [List.length_append] at hlen2
        exact List.length_eq_zero_iff.mp (by omega)
      rw [happend, hflat, List.append_nil]
    · rename_i hlenb
      rw [Bool.not_eq_true, beq_eq_false_iff_ne] at hlenb
      have hb' : ∀ x ∈ applyAllTImpRules b edges, x ∈ intUniverse φ0 :=
        applyAllTImpRules_subset hb
      have hfuel' : (intUniverse φ0).countP
          (fun sf => !((applyAllTImpRules b edges).any (· == sf))) ≤ fuel' := by
        have := applyAllTImpRules_count_drop (φ0 := φ0) hb hlenb
        omega
      exact ih (applyAllTImpRules b edges) hb' hfuel'

/-- If `intExpandBranches` returns `.openBranch b`, then `b` is Hintikka-saturated:
every compound formula on `b` has its rule-outputs also on `b` (see `IBranchSaturation`).
Additionally exposes the accumulated `IEdges` active for `b` at the point of saturation
(plumbing), so the completeness side can install edge-accessibility as the
countermodel frame instead of the ambient numeric `≤`. The conclusion also
carries `IFimpAccess edges b`: every `F(φ→ψ)@w ∈ b` has a genuinely edge-accessible witness
(not merely the numeric `sat_fimp` proxy), the fact `truthLemma`'s F-imp case needs to
instantiate over `intAccessPreorder edges` (Route (a)).

The proof mirrors `intExpandBranches_openBranch_closed`: induction on `fuel`, with inner
induction on the `pending` list in the `go` helper, threading the combined `IAllConsistent`
invariant AND its edge-accessibility companion `IAllAccessConsistent`. In
the recursive cases (`linearResult`, `branchingResult`), the fuel IH closes the goal once both
invariants are re-established for the extended/branched state via
`intStepBranch_linear_preserves`/`intStepBranch_branch_preserves` (the exposed `edges` witness
passes through the IH, growing by one edge exactly at world-creation). In the `none` leaf
case, the returned branch equals `bPers` directly, `edgesH` (the edge list active at that
point) is the exposed witness, and `IExpandedConsistent_sat`/`IExpandedAccessConsistent_sat`
discharge both conjuncts directly from the threaded invariants. The fuel-0 base case's goal is
REFUTED at its current statement, not merely gapped: see the in-proof note at the `sorry`
below for the Lean-verified counter-instance and why no proof can close it as written. -/
private lemma intExpandBranches_openBranch_sat (fuel : Nat)
    (branches : List (IBranch Atom))
    (expandedSets : List (List (ISF Atom)))
    (nextWorlds : List Nat)
    (edgeSets : List IEdges)
    (closurePred : IBranch Atom → Bool)
    (b : IBranch Atom)
    (hAC : IAllConsistent branches expandedSets nextWorlds)
    (hLen0 : branches.length = edgeSets.length)
    (hACC : IAllAccessConsistent branches expandedSets edgeSets)
    (h : intExpandBranches branches expandedSets nextWorlds edgeSets fuel closurePred
        = .openBranch b) :
    ∃ edges : IEdges, IBranchSaturation Atom b ∧ IFimpAccess edges b := by
  induction fuel generalizing branches expandedSets nextWorlds edgeSets hAC hLen0 hACC with
  | zero =>
    -- fuel=0 base case: THE GOAL IS FALSE AT ITS CURRENT STATEMENT, refuted by a
    -- Lean-verified counter-instance, not merely unproven.
    --
    -- Counter-instance: `branches = [[⟨.neg, p ∧ q, 0⟩]]`, `expandedSets = [[]]`,
    -- `nextWorlds = [1]`, `edgeSets = [[]]`.
    --
    -- Every hypothesis of this lemma holds at that instance: `ILabelBound` holds trivially
    -- (the single branch's one formula sits at label `0 < 1`); `IExpandedConsistent` and
    -- `IAllAccessConsistent` are vacuous, since `expandedSets = [[]]` supplies the empty
    -- expanded-set `e = []` and `edgeSets = [[]]` supplies the empty edge list; the length
    -- hypotheses `hLen0` (`branches.length = edgeSets.length`) and the analogous
    -- `expandedSets`/`nextWorlds` lengths are all `(1, 1)`.
    --
    -- With `fuel = 0`, `intExpandBranches` returns `.openBranch b` for `b` = the branch
    -- itself, `[⟨.neg, p ∧ q, 0⟩]`, unmodified -- it is never saturated. But
    -- `IBranchSaturation.sat_fand`'s premise (`F(p ∧ q)@0` present) evaluates `true` while
    -- BOTH disjuncts it requires (`F(p)@0` or `F(q)@0` present) evaluate `false`: neither is
    -- on the branch. So `IBranchSaturation Atom b` is false at this `b`, and the existential
    -- goal (`∃ edges, IBranchSaturation Atom b ∧ IFimpAccess edges b`) is unsatisfiable at
    -- this instance despite every hypothesis holding.
    --
    -- Consequence: no proof can close this `sorry` at the lemma's current statement. Closing
    -- it requires RESTATING the lemma (e.g. with a saturation-establishing precondition on
    -- the initial worklist, ruling out the counter-instance above) -- out of scope here. This
    -- note only records the refutation so no future attempt re-derives it from scratch.
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
        IAllConsistent pending pendingExp pendingNW →
        pending.length = pendingEdges.length →
        IAllConsistent done doneExp doneNW →
        done.length = doneEdges.length →
        IAllAccessConsistent pending pendingExp pendingEdges →
        IAllAccessConsistent done doneExp doneEdges →
        intExpandBranches.go closurePred fuel' pending pendingExp pendingNW pendingEdges
            done doneExp doneNW doneEdges = .openBranch b →
        ∃ edges : IEdges, IBranchSaturation Atom b ∧ IFimpAccess edges b from
      key branches expandedSets nextWorlds edgeSets [] [] [] []
        hAC hLen0 (by trivial) rfl hACC (by trivial) h
    intro pending
    induction pending with
    | nil =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hgo
      simp only [intExpandBranches.go] at hgo
      simp at hgo
    | cons bh bt ih_inner =>
      intro pendingExp pendingNW pendingEdges done doneExp doneNW doneEdges
        hPending hLenP hDone hLenD hPendingACC hDoneACC hgo
      cases hpE : pendingExp with
      | nil =>
        simp only [hpE, IAllConsistent] at hPending
      | cons eH eT =>
        cases hpNW : pendingNW with
        | nil =>
          simp only [hpE, hpNW, IAllConsistent] at hPending
        | cons nwH nwT =>
          cases hpEdges : pendingEdges with
          | nil =>
            simp only [hpEdges, List.length_cons, List.length_nil] at hLenP
            omega
          | cons edgesH edgesT =>
            rw [hpE, hpNW, hpEdges] at hgo
            simp only [hpE, hpNW, IAllConsistent] at hPending
            obtain ⟨hIC_bh_eH, hLB_bh_nwH, hPendingTail⟩ := hPending
            simp only [hpE, hpEdges, IAllAccessConsistent] at hPendingACC
            obtain ⟨hACC_bh_eH, hPendingACCTail⟩ := hPendingACC
            simp only [hpEdges, List.length_cons, Nat.add_right_cancel_iff] at hLenP
            set bPers := applyPersistenceFixpoint bh edgesH (fuel' + 1) with hbPers_def
            have hIC_bPers : IExpandedConsistent bPers eH :=
              IExpandedConsistent_mono
                (fun x hx => applyPersistenceFixpoint_mem_preserved bh edgesH (fuel' + 1) x hx)
                hIC_bh_eH
            have hLB_bPers : ILabelBound bPers nwH :=
              ILabelBound_applyPersistenceFixpoint (fuel' + 1) hLB_bh_nwH
            have hACC_bPers : IExpandedAccessConsistent edgesH bPers eH :=
              IExpandedAccessConsistent_mono
                (fun x hx => applyPersistenceFixpoint_mem_preserved bh edgesH (fuel' + 1) x hx)
                hACC_bh_eH
            simp only [intExpandBranches.go] at hgo
            by_cases hcl : closurePred bPers = true
            · rw [if_pos hcl] at hgo
              refine ih_inner eT nwT edgesT
                  (done ++ [bPers]) (doneExp ++ [eH]) (doneNW ++ [nwH]) (doneEdges ++ [edgesH])
                  hPendingTail hLenP
                  (IAllConsistent_append hDone ⟨hIC_bPers, hLB_bPers, by trivial⟩)
                  (by simp [hLenD]) hPendingACCTail
                  (IAllAccessConsistent_append hDoneACC ⟨hACC_bPers, by trivial⟩) hgo
            · simp only [Bool.not_eq_true] at hcl
              rw [if_neg (by simp [← hbPers_def, hcl])] at hgo
              cases hstep : intStepBranch bPers eH nwH with
              | none =>
                rw [hstep] at hgo; injection hgo with heq; subst heq
                -- b = bPers; intStepBranch returned none, so every compound formula in
                -- bPers is already recorded in eH (`intStepBranch_none_compound_mem`), and
                -- `hIC_bPers`/`hACC_bPers` give its rule-outputs / edge-access witnesses on
                -- bPers -- exactly `IBranchSaturation` + `IFimpAccess`.
                exact ⟨edgesH, IExpandedConsistent_sat hstep hIC_bPers,
                  IExpandedAccessConsistent_sat hstep hACC_bPers⟩
              | some step =>
                obtain ⟨result, newExp⟩ := step
                rw [hstep] at hgo
                cases result with
                | linearResult newForms nw' newEdge =>
                  simp only at hgo
                  obtain ⟨hIC_ext, hLB_ext, hACC_ext⟩ :=
                    intStepBranch_linear_preserves hIC_bPers hLB_bPers hACC_bPers hstep
                  have hAC' :
                      IAllConsistent
                        (done ++ [Branch.extendMany bPers newForms] ++ bt)
                        (doneExp ++ [newExp] ++ eT) (doneNW ++ [nw'] ++ nwT) :=
                    IAllConsistent_append
                      (IAllConsistent_append hDone ⟨hIC_ext, hLB_ext, by trivial⟩) hPendingTail
                  have hLen0' :
                      (done ++ [Branch.extendMany bPers newForms] ++ bt).length =
                        (doneEdges ++ [newEdge.elim edgesH (fun e => edgesH ++ [e])]
                          ++ edgesT).length := by
                    cases newEdge <;> simp <;> omega
                  have hACC' :
                      IAllAccessConsistent
                        (done ++ [Branch.extendMany bPers newForms] ++ bt)
                        (doneExp ++ [newExp] ++ eT)
                        (doneEdges ++ [newEdge.elim edgesH (fun e => edgesH ++ [e])] ++ edgesT) :=
                    IAllAccessConsistent_append
                      (IAllAccessConsistent_append hDoneACC ⟨hACC_ext, by trivial⟩)
                      hPendingACCTail
                  split at hgo <;> (try split at hgo) <;>
                    first
                    | exact ih _ _ _ _ hAC' hLen0' hACC' hgo
                    | (rename_i newEdgeVar edgeVar deadVar x heq
                       obtain ⟨sf, hsfb, hint, hnewExp⟩ := intStepBranch_some_exists hstep
                       obtain ⟨s, ff, l⟩ := sf
                       cases s with
                       | pos =>
                         cases ff with
                         | atom _ => simp [intApplyRuleFull] at hint
                         | bot => simp [intApplyRuleFull] at hint
                         | imp _ _ => simp [intApplyRuleFull] at hint
                         | or _ _ => simp [intApplyRuleFull] at hint
                         | and _ _ => simp [intApplyRuleFull] at hint
                       | neg =>
                         cases ff with
                         | atom _ => simp [intApplyRuleFull] at hint
                         | bot => simp [intApplyRuleFull] at hint
                         | and _ _ => simp [intApplyRuleFull] at hint
                         | or _ _ => simp [intApplyRuleFull] at hint
                         | imp φ ψ₀ =>
                           simp only [intApplyRuleFull, intFImpRule,
                             IntRuleResult.linearResult.injEq, Option.some.injEq] at hint
                           obtain ⟨hnf, hnw', hed⟩ := hint
                           obtain rfl := hed.symm
                           have hψ : newForms.findSome?
                               (fun sf => if sf.sign == .neg then some sf.formula else none)
                               = some ψ₀ := by rw [← hnf]; simp [propagatePersistence]
                           -- Phase 4: repointed to the ancestor-directed spec. Under ancestor
                           -- direction `hacc`/`hle` now witness `isAccessible edges x l` /
                           -- `x ≤ l` (x is an *ancestor* of l) — the reverse of what
                           -- `sfSatisfied`/`sfAccessSat`'s `.neg,.imp` clauses below require
                           -- (`l ≤ w'`, `isAccessible edges l w'`); see D5/D6 in the plan.
                           obtain ⟨hacc, hle, hcont, hnotmem, hFpsi⟩ :=
                             intFImpReuseWitnessAnc?_spec hψ heq
                           have hmemsfor : φ ∈ (newForms.filterMap fun sf =>
                               if sf.sign == .pos then some sf.formula else none) := by
                             rw [← hnf]; simp [propagatePersistence]
                           have hphi : (posFormulasAt bPers x).contains φ = true :=
                             List.all_eq_true.mp hcont φ hmemsfor
                           have houtPhi : bPers.any
                               (fun y => y.sign == .pos && y.formula == φ && y.label == x)
                               = true := by
                             rw [List.contains_iff_mem] at hphi
                             simp only [posFormulasAt, List.mem_filterMap] at hphi
                             obtain ⟨y, hy_mem, hy_cond⟩ := hphi
                             rw [List.any_eq_true]
                             refine ⟨y, hy_mem, ?_⟩
                             by_cases hs : y.sign == .pos && y.label == x
                             · simp only [hs, if_true, Option.some.injEq] at hy_cond
                               simp only [Bool.and_eq_true] at hs
                               simp [hs.1, hs.2, hy_cond]
                             · simp [hs] at hy_cond
                           have hreuse_sat : IExpandedConsistent bPers newExp ∧
                               IExpandedAccessConsistent edgesH bPers newExp := by
                             -- TEMPORARY (task phase 4 -> phase 6): reuse-site discharge is
                             -- restated over the blocking quotient in Phase 6. Under
                             -- ancestor-direction blocking `x ≤ l` / `isAccessible edges x l`
                             -- hold (D5: x is an ancestor of l), not the `l ≤ w'` /
                             -- `isAccessible edges l w'` that `sfSatisfied`/`sfAccessSat`
                             -- demand directly. Phase 5's `intBlockRep`/`intAccessPreorderQ`
                             -- identify `rep l = rep x`, so both conjuncts hold reflexively on
                             -- the quotient (D5); Phase 6 restates this lemma's conclusion over
                             -- `IBranchSaturationQ`/`IFimpAccessQ` and re-closes this site.
                             -- Closed before task completion.
                             sorry
                           have hIC_reuse : IExpandedConsistent bPers newExp := hreuse_sat.1
                           have hACC_reuse : IExpandedAccessConsistent edgesH bPers newExp :=
                             hreuse_sat.2
                           have hAC'' : IAllConsistent (done ++ [bPers] ++ bt)
                               (doneExp ++ [newExp] ++ eT) (doneNW ++ [nwH] ++ nwT) :=
                             IAllConsistent_append
                               (IAllConsistent_append hDone ⟨hIC_reuse, hLB_bPers, trivial⟩)
                               hPendingTail
                           have hLen0'' : (done ++ [bPers] ++ bt).length =
                               (doneEdges ++ [edgesH] ++ edgesT).length := by simp; omega
                           have hACC'' : IAllAccessConsistent (done ++ [bPers] ++ bt)
                               (doneExp ++ [newExp] ++ eT) (doneEdges ++ [edgesH] ++ edgesT) :=
                             IAllAccessConsistent_append
                               (IAllAccessConsistent_append hDoneACC ⟨hACC_reuse, trivial⟩)
                               hPendingACCTail
                           exact ih _ _ _ _ hAC'' hLen0'' hACC'' hgo)
                | branchingResult branches' nw' =>
                  simp only at hgo
                  have hbr := intStepBranch_branch_preserves hIC_bPers hLB_bPers hACC_bPers hstep
                  have hAC' :
                      IAllConsistent
                        (done ++ branches'.map (Branch.extendMany bPers ·) ++ bt)
                        (doneExp ++ branches'.map (fun _ => newExp) ++ eT)
                        (doneNW ++ branches'.map (fun _ => nw') ++ nwT) :=
                    IAllConsistent_append
                      (IAllConsistent_append hDone
                        (IAllConsistent_map (Branch.extendMany bPers ·)
                          (fun br hbr' => ⟨(hbr br hbr').1, (hbr br hbr').2.1⟩))) hPendingTail
                  have hLen0' :
                      (done ++ branches'.map (Branch.extendMany bPers ·) ++ bt).length =
                        (doneEdges ++ branches'.map (fun _ => edgesH) ++ edgesT).length := by
                    simp; omega
                  have hACC' :
                      IAllAccessConsistent
                        (done ++ branches'.map (Branch.extendMany bPers ·) ++ bt)
                        (doneExp ++ branches'.map (fun _ => newExp) ++ eT)
                        (doneEdges ++ branches'.map (fun _ => edgesH) ++ edgesT) :=
                    IAllAccessConsistent_append
                      (IAllAccessConsistent_append hDoneACC
                        (IAllAccessConsistent_map (Branch.extendMany bPers ·)
                          (fun br hbr' => (hbr br hbr').2.2))) hPendingACCTail
                  exact ih _ _ _ _ hAC' hLen0' hACC' hgo
                | notApplicable =>
                  simp only at hgo; injection hgo with heq; subst heq
                  -- hstep : intStepBranch bPers eH nwH = some (.notApplicable, newExp)
                  -- This contradicts intStepBranch_result_ne_notApplicable.
                  exact absurd rfl (intStepBranch_result_ne_notApplicable hstep)

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
                  split at hgo <;> (try split at hgo) <;>
                    (refine ih _ _ _ _ _ ?_ b hgo
                     intro b₀ hb₀
                     simp only [List.mem_append, List.mem_singleton] at hb₀
                     rcases hb₀ with ((hd | rfl) | hbt)
                     · exact hDone b₀ hd
                     · first
                       | exact hbPers_sf
                       | (simp only [Branch.extendMany, List.mem_append]
                          exact Or.inr hbPers_sf)
                     · exact hPend b₀ (List.mem_cons_of_mem _ hbt))
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

- At `intScheme`: specializes to `intuitionisticOpenBranch_countermodel`.
- At `minScheme`: specializes to `minOpenBranch_countermodel`.

## Proof structure

From `h : intExpandBranches ... S.closurePred = .openBranch b` we extract structural facts:
1. `hopen`: the returned branch is open (`S.closurePred b = false`).
2. `hsat`/`hfimp`: the returned branch is saturated, together with the edge-accessibility
   upgrade of its F(φ→ψ) witnesses (Route (a)).
3. `hFmem`: F(φ)@0 is on b (branch monotonicity: formulas are only added).
Then `(truthLemma S b edges hopen hsat hfimp φ 0).2 hFmem` closes the goal, existentially
packaging the `edges` the countermodel frame (`intAccessPreorder edges`) is installed over
(Postmortem-5 revision: this internal conclusion MAY expose `edges`; the stable public
`tableau_complete`/`Decidable` contract, discharged elsewhere, does not).

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4 -/
lemma openBranch_countermodel (S : IntMinScheme Atom) (φ : Proposition Atom)
    (b : IBranch Atom)
    (h : intExpandBranches [[⟨.neg, φ, 0⟩]] [[]] [1] [[]]
        (intFuel φ) S.closurePred = .openBranch b) :
    ∃ edges : IEdges,
      ¬ @IForces Atom Nat (intAccessPreorder edges) (intExtractValuation b) (S.modelBot b) 0 φ
      := by
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
  -- Obtain the saturation witness and its accumulated edges, together
  -- with the edge-accessibility upgrade `hfimp` of its F(φ→ψ) witnesses.
  obtain ⟨edges, hsat, hfimp⟩ :=
    intExpandBranches_openBranch_sat _ _ _ _ _ _ _
      (by simp [IAllConsistent, IExpandedConsistent, ILabelBound]) rfl
      (by simp [IAllAccessConsistent, IExpandedAccessConsistent]) h
  -- Apply the truth lemma's F-branch direction over the `intAccessPreorder edges` frame.
  exact ⟨edges, (truthLemma S b edges hopen hsat hfimp φ 0).2 hFmem⟩

/-! ## Parametric Tableau Completeness -/

/-- **Parametric Tableau Completeness**: If `φ` is forced at world 0 in every
branch-derived Kripke model, then the parametric expansion closes on `φ`.

Proof: by contrapositive. If the expansion returns `.openBranch b`, then
`openBranch_countermodel S` gives `∃ edges, ¬ @IForces Atom Nat (intAccessPreorder edges)
(intExtractValuation b) (S.modelBot b) 0 φ` (Route (a)), contradicting
`hvalid edges b`.

The hypothesis `hvalid` encodes the per-scheme validity notion, now quantified over the
`edges`-parameterized `intAccessPreorder` frame rather than a single ambient instance (Route
(a): `edges` is only discovered inside `openBranch_countermodel`'s own proof, so `hvalid` must
accept it as an argument):
- For `intScheme` (where `modelBot b = fun _ => False`): `hvalid edges b` follows from
  `IValid φ` applied at World `= ℕ` with the `intAccessPreorder edges` instance,
  `val = intExtractValuation b`, with the upward-closure of `intExtractValuation b` along that
  frame (the deferred-monotonicity bridge).
- For `minScheme` (where `modelBot b = minBranchBotForces b`): `hvalid edges b` follows from
  `MValid φ` applied analogously, with upward-closure of both `intExtractValuation b` and
  `minBranchBotForces b` along `intAccessPreorder edges`.

This theorem is sorry-free given `openBranch_countermodel S`; the deferred-monotonicity
obligation lives entirely in `hvalid`'s callers.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4 -/
theorem tableau_complete (S : IntMinScheme Atom) (φ : Proposition Atom)
    (hvalid : ∀ (edges : IEdges) (b : IBranch Atom),
      @IForces Atom Nat (intAccessPreorder edges) (intExtractValuation b) (S.modelBot b) 0 φ) :
    intExpandBranches [[⟨.neg, φ, 0⟩]] [[]] [1] [[]]
        (intFuel φ) S.closurePred = .closed := by
  by_contra hne
  cases hresult : intExpandBranches [[⟨.neg, φ, 0⟩]] [[]] [1] [[]]
      (intFuel φ) S.closurePred with
  | closed => exact hne hresult
  | openBranch b =>
    obtain ⟨edges, hcm⟩ := openBranch_countermodel S φ b hresult
    exact absurd (hvalid edges b) hcm

end Cslib.Logic.PL

end
