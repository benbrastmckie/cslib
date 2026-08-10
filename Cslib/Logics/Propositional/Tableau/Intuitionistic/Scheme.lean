/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
import Cslib.Foundations.Logic.Tableau.Measure
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Logic.Function.Iterate
public import Cslib.Foundations.Logic.Tableau.Blocking
public import Mathlib.Data.Finset.Prod
public import Cslib.Logics.Propositional.Tableau.Minimal.Soundness
public import Cslib.Logics.Propositional.Subformula

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

/-! ### Reverse-direction append monotonicity (fresh-target case)

`isAccessible_append_mono` gives only ONE direction: appending an edge never LOSES an existing
accessibility witness. The converse -- appending a FRESH edge `(nw, l)` (where `nw` is a brand
new node, never previously a parent-slot member of `edges`) never GAINS a witness for any target
OTHER than `nw` itself -- is not implied by `isAccessible_append_mono` and needs its own
induction. Intuition: any DFS path that ever routes through the new edge `(nw, l)` must, to make
further progress, treat `nw` as an intermediate `current` node and look for `nw`'s own outgoing
edges; since `nw` is fresh, it has none (the only edge mentioning `nw` at all, `(nw, l)`, has
`nw` in the CHILD slot, not the parent slot), so any such path is a dead end. Consequently every
genuine reachability witness for a target `≠ nw` in the extended list avoids the new edge
entirely and is already a witness in the original list. -/

/-- Dead end: from `nw` itself, the extended edge list `edges ++ [(nw, l)]` has NO outgoing
candidates at all (regardless of fuel), given `nw` is fresh (never a parent-slot member of
`edges`) and `l ≠ nw` (the freshly-appended edge's own parent slot is not `nw`, which holds
since `l` is an existing label and `nw` is a brand new one). This is the key dead-end fact
`isAccessible_go_append_eq_of_fresh` uses to rule out the "routed through the new edge" case. -/
private lemma isAccessible_go_fresh_dead_end
    (edges : IEdges) (nw l : Nat) (hfresh : ∀ c, (c, nw) ∉ edges) (hne : l ≠ nw)
    (target fuel : Nat) :
    isAccessible.go (edges ++ [(nw, l)]) target nw fuel = false := by
  match fuel with
  | 0 => simp [isAccessible.go]
  | fuel' + 1 =>
    simp only [isAccessible.go, List.any_eq_false]
    intro child hchild
    simp only [List.mem_filterMap] at hchild
    obtain ⟨⟨c, p⟩, hmem, hfilt⟩ := hchild
    by_cases hp : p == nw
    · exfalso
      have hp' : p = nw := by simpa using hp
      subst hp'
      rw [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hold | hnewedge
      · exact hfresh c hold
      · exact hne (congrArg Prod.snd hnewedge).symm
    · simp [hp] at hfilt

/-- `isAccessible.go` reverse-direction append monotonicity: given `nw` is fresh (never a
parent-slot member of `edges`, `l ≠ nw`), any reachability witness for a target `≠ nw` found
using the extended list `edges ++ [(nw, l)]` already existed using the original `edges` list, at
the SAME fuel. Proved by induction on fuel, splitting on whether the candidate child at each step
came from an old edge (immediate transfer) or is the new edge itself (only possible when
`current = l`, giving candidate `child = nw`; since `target ≠ nw` this forces the recursive call
`go (edges ++ [(nw, l)]) target nw fuel' = true`, which `isAccessible_go_fresh_dead_end` refutes
outright, so this branch never occurs). Counterpart to `isAccessible_go_append_mono` (`:316`). -/
private lemma isAccessible_go_append_eq_of_fresh
    (edges : IEdges) (nw l : Nat) (hfresh : ∀ c, (c, nw) ∉ edges) (hne : l ≠ nw)
    (target : Nat) (htarget : target ≠ nw) :
    ∀ (current fuel : Nat), isAccessible.go (edges ++ [(nw, l)]) target current fuel = true →
      isAccessible.go edges target current fuel = true := by
  intro current fuel
  induction fuel generalizing current with
  | zero => simp [isAccessible.go]
  | succ k ih =>
    simp only [isAccessible.go]
    intro h
    rw [List.any_eq_true] at h ⊢
    obtain ⟨child, hchild, hcond⟩ := h
    simp only [List.mem_filterMap] at hchild
    obtain ⟨⟨c, p⟩, hmem, hfilt⟩ := hchild
    by_cases hp : p == current
    · simp only [hp, ite_true, Option.some.injEq] at hfilt
      rw [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hold | hnewedge
      · -- (c, p) ∈ edges: a genuine candidate in the un-extended list too.
        refine ⟨child, ?_, ?_⟩
        · simp only [List.mem_filterMap]
          exact ⟨(c, p), hold, by simp [hp, hfilt]⟩
        · by_cases hce : child == target
          · simp [hce]
          · simp only [hce, Bool.false_eq_true, ite_false] at hcond ⊢
            exact ih child hcond
      · -- (c, p) = (nw, l): child = nw, so this branch is a dead end.
        have hcnw : child = nw := by
          simp only [Prod.mk.injEq] at hnewedge
          rw [← hfilt]
          exact hnewedge.1
        exfalso
        by_cases hce : child == target
        · have hchildtarget : child = target := by simpa using hce
          exact htarget (hcnw.symm.trans hchildtarget).symm
        · simp only [hce, Bool.false_eq_true, ite_false] at hcond
          rw [hcnw] at hcond
          have hdead := isAccessible_go_fresh_dead_end edges nw l hfresh hne target k
          rw [hdead] at hcond
          exact absurd hcond (by simp)
    · simp [hp] at hfilt

/-! ### Sub-frame monotonicity

Upward closure is *anti-monotone* in the edge set: growing `edges` to any superset `edges'`
(not just a single-edge append) can only add reachability, never remove it, so any
accessibility fact established relative to `edges` survives relative to `edges'`. This is the
subset-general form of the append-monotonicity lemmas above, modelled verbatim on their proof
shape. It is what lets both of `openBranch_rawEdges_upward_closed`'s upward-closure conjuncts
(and, via `openBranch_rawEdges_both_upward_closed`, `minBranchBotForces`'s `⊥`-shape instance)
transfer to any sub-frame of `rawEdges`, not just to `rawEdges` itself. -/

/-- `isAccessible.go` is monotone under passing to a superset edge list: any reachability
witness found using `edges` survives when `edges` is replaced by any `edges'` containing all of
`edges`'s entries (the DFS's per-step candidate-children list can only gain entries, never lose
them, under such an inclusion). Subset-general counterpart of `isAccessible_go_append_mono`. -/
private lemma isAccessible_go_subset_mono
    (edges edges' : IEdges) (hsub : ∀ e ∈ edges, e ∈ edges') (target : Nat) :
    ∀ (current fuel : Nat), isAccessible.go edges target current fuel = true →
      isAccessible.go edges' target current fuel = true := by
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
        refine ⟨(c, p), hsub _ hedges, ?_⟩
        simp [hp, hfilt]
      · by_cases hce : child == target
        · simp [hce]
        · simp only [hce, Bool.false_eq_true, ite_false] at hcond ⊢
          exact ih child hcond
    · simp only [Bool.not_eq_true] at hp
      simp [hp] at hfilt

/-- `isAccessible` is monotone under passing to a superset edge list of at least the same
length (the top-level wrapper combining `isAccessible_go_subset_mono` with
`isAccessible_go_fuel_mono`, mirroring `isAccessible_append_mono`'s structure; also handles the
`w == w'` short-circuit case). The length hypothesis supplies the extra fuel `isAccessible`'s
fuel bound `edges.length` needs when `edges'` is longer than `edges`. -/
private lemma isAccessible_subset_mono {edges edges' : IEdges}
    (hsub : ∀ e ∈ edges, e ∈ edges') (hlen : edges.length ≤ edges'.length) {w w' : Nat}
    (h : isAccessible edges w w' = true) : isAccessible edges' w w' = true := by
  simp only [isAccessible] at h ⊢
  by_cases heq : w == w'
  · simp [heq]
  · simp only [heq, Bool.false_eq_true, ite_false] at h ⊢
    have h1 := isAccessible_go_subset_mono edges edges' hsub w' w edges.length h
    have hgen : ∀ d : Nat, isAccessible.go edges' w' w (edges.length + d) = true := by
      intro d
      induction d with
      | zero => simpa using h1
      | succ m ih => exact isAccessible_go_fuel_mono edges' w' w _ ih
    obtain ⟨d, hd⟩ := Nat.le.dest hlen
    rw [← hd]
    exact hgen d

/-- `intAccessPreorder`'s `≤` is monotone under passing to a superset edge list: any
accessibility fact established relative to `edges` remains true relative to any `edges'`
containing `edges`'s entries (of at least the same length). Lifts `isAccessible_subset_mono`
through `Relation.ReflTransGen.mono`. -/
lemma intAccessPreorder_mono_subset {edges edges' : IEdges}
    (hsub : ∀ e ∈ edges, e ∈ edges') (hlen : edges.length ≤ edges'.length) {w w' : Nat}
    (h : @LE.le Nat (intAccessPreorder edges).toLE w w') :
    @LE.le Nat (intAccessPreorder edges').toLE w w' :=
  Relation.ReflTransGen.mono (fun _ _ hxy => isAccessible_subset_mono hsub hlen hxy) _ _ h

/-! ### One-hop ancestry extension (DP-2 support)

`isAccessible edges · ·` does not need full transitivity for the mint-time argument used by
`IWorldHist` (see the docstring above at line 250): only a ONE-HOP extension is needed, converting
`par`-ancestry (a direct parent-child edge freshly appended) plus an existing accessibility fact
into a new accessibility fact for the freshly-minted world. `isAccessible_go_one_hop_ext` is the
raw fuel-indexed statement (any direct edge `(c, p)` extends a `go`-reachability witness to `p` by
exactly one hop, using one more unit of fuel); `isAccessible_one_hop_ext` specializes it to the
EXACT shape needed at a mint site, where `c` is fresh and `(c, p)` is the edge being appended: the
fuel arithmetic then closes exactly, since `(edges ++ [(c, p)]).length = edges.length + 1` matches
the one extra hop precisely. Full transitivity of `isAccessible` is deliberately NOT proved here
(`Scheme.lean:250` explains why the weaker one-hop form suffices and is sound). -/

/-- A direct edge `(c, p) ∈ edges` gives `go`-reachability of `c` from `p` at ANY positive fuel
(the DFS finds `c` as an immediate child of `p` in a single unfold, regardless of how much fuel
remains afterward). This is the `go`-level analogue of `isAccessible_one_step`. -/
private lemma isAccessible_go_direct {edges : IEdges} {p c : Nat} (hmem : (c, p) ∈ edges)
    (fuel : Nat) : isAccessible.go edges c p (fuel + 1) = true := by
  rw [isAccessible.go, List.any_eq_true]
  exact ⟨c, by simp only [List.mem_filterMap]; exact ⟨(c, p), hmem, by simp⟩, by simp⟩

/-- Raw one-hop extension at the `isAccessible.go` level: if `go` can reach `p` from `current`
within `fuel` steps, and `(c, p)` is a direct edge, then `go` can reach `c` from `current` within
`fuel + 1` steps. Proved by induction on `fuel`: either the last step before reaching `p` was
itself the direct edge into `p` (in which case `c` is reached via the extra hop through `p`, by
`isAccessible_go_direct`), or the induction hypothesis applies one level down. -/
private lemma isAccessible_go_one_hop_ext (edges : IEdges) {p c : Nat} (hmem : (c, p) ∈ edges) :
    ∀ (current fuel : Nat), isAccessible.go edges p current fuel = true →
      isAccessible.go edges c current (fuel + 1) = true := by
  intro current fuel
  induction fuel generalizing current with
  | zero => simp [isAccessible.go]
  | succ k ih =>
    simp only [isAccessible.go]
    intro h
    rw [List.any_eq_true] at h
    obtain ⟨d, hd, hcond⟩ := h
    simp only [List.mem_filterMap] at hd
    obtain ⟨⟨d', parent⟩, hedges', hfilt⟩ := hd
    by_cases hpar : parent == current
    · simp only [hpar, ite_true, Option.some.injEq] at hfilt
      rw [List.any_eq_true]
      by_cases hdp : d == p
      · -- d = p: (p, current) ∈ edges directly, so current →(1 hop)→ p →(1 hop, via hmem)→ c
        have hdp' : d = p := by simpa using hdp
        refine ⟨d, ?_, ?_⟩
        · simp only [List.mem_filterMap]
          exact ⟨(d', parent), hedges', by simp [hpar, hfilt]⟩
        · by_cases hpc : d == c
          · simp [hpc]
          · simp only [hpc, Bool.false_eq_true, ite_false]
            rw [hdp']
            exact isAccessible_go_direct hmem k
      · -- d ≠ p: recurse via the induction hypothesis
        simp only [hdp, Bool.false_eq_true, ite_false] at hcond
        refine ⟨d, ?_, ?_⟩
        · simp only [List.mem_filterMap]
          exact ⟨(d', parent), hedges', by simp [hpar, hfilt]⟩
        · by_cases hdc : d == c
          · simp [hdc]
          · simp only [hdc, Bool.false_eq_true, ite_false]
            exact ih d hcond
    · simp only [Bool.not_eq_true] at hpar
      simp [hpar] at hfilt

/-- The specialized one-hop extension used at every mint site: if `x` accesses `p` under the
CURRENT edge list, then after appending the fresh edge `(c, p)` (as the mint arm always does,
`Scheme.lean:3272`), `x` accesses the newly-minted `c` under the extended edge list. This is the
exact shape needed to discharge (H1)'s accessibility half of `IWorldHist` at a mint: the fuel
arithmetic closes precisely because `(edges ++ [(c, p)]).length = edges.length + 1`, i.e. the one
extra hop uses exactly the one unit of fuel gained by the append. -/
private lemma isAccessible_one_hop_ext {edges : IEdges} {x p c : Nat}
    (hacc : isAccessible edges x p = true) :
    isAccessible (edges ++ [(c, p)]) x c = true := by
  by_cases hxc : x == c
  · simp [isAccessible, hxc]
  · simp only [isAccessible, hxc, Bool.false_eq_true, ite_false]
    rw [List.length_append, List.length_singleton]
    by_cases hxp : x == p
    · -- x = p: (c, p) ∈ edges ++ [(c,p)] gives the one direct hop, for any fuel ≥ 1
      have hxp' : x = p := by simpa using hxp
      have hmem : (c, p) ∈ edges ++ [(c, p)] :=
        List.mem_append_right _ (List.mem_singleton_self _)
      rw [hxp']
      exact isAccessible_go_direct hmem edges.length
    · simp only [isAccessible, hxp, Bool.false_eq_true, ite_false] at hacc
      have h1 : isAccessible.go (edges ++ [(c, p)]) p x edges.length = true :=
        isAccessible_go_append_mono edges (c, p) p x edges.length hacc
      have hmem : (c, p) ∈ edges ++ [(c, p)] :=
        List.mem_append_right _ (List.mem_singleton_self _)
      exact isAccessible_go_one_hop_ext (edges ++ [(c, p)]) hmem x edges.length h1

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

/-! ### `sat_timp` discharge — STOP-gate finding, CLOSED (DP-5 discharged via `hpers`)

**DISCHARGED (supersedes the "Gap 1" analysis below).** `truthLemma` now takes an explicit
`hpers` hypothesis — positive-formula persistence along `edges`
(`∀ χ x y, isAccessible edges x y = true → T(χ)@x ∈ b → T(χ)@y ∈ b`) — and the T-imp case is
proved unconditionally from it plus `sat_timp` (see the proof at this lemma's T-imp case below:
lift `T(φ'→ψ')@w ∈ b` to membership, chain `hpers` along `Relation.ReflTransGen` by
`induction hle` to get `T(φ'→ψ')@w' ∈ b`, then close by `sat_timp` exactly as this note
anticipated). This sidesteps Gap 1 rather than closing it via the originally-anticipated
self-copy channel: `hpers` transfers the SOURCE world's `T(φ'→ψ')` membership to `w'` directly,
so `w'` ends up carrying its own copy without any `Expansion.lean` self-copy machinery. The
obstruction the note below diagnoses is real only at the AUGMENTED frame, where `hpers` is
itself REFUTED (`CslibTests/BetaSplitRefutation.lean`) — it is an artefact of that frame
CHOICE, not of the T-imp goal: `truthLemma`'s frame is a parameter, and over the raw frame or
any sub-raw frame carrying `hpers` (`IPosPersistRaw`/`IWorldsPlanted`, `:6782`/`:3568`, both
sorry-free) the case is unconditionally provable, which is exactly the DISCHARGED state
`truthLemma` is in now. The remainder of this note (the self-copy-channel investigation
below) is retained as the historical record of the route this file no longer takes; do not
re-derive its "open"/"blocked" conclusions about Gap 1 as current.

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
the current status of that obligation). Note also that the world bound any such fuel-sufficiency
measure would ultimately be sized against is itself refuted: see the *Divergence witness* note in
`Expansion.lean` (this does NOT by itself refute Gap 1 — the witness bears on world-boundedness,
not on persistence fuel-sufficiency directly — but any future attempt at this measure must not
lean on `intUniverse`'s linear world range as a genuine invariant of produced branches).

**CORRECTION (annotation-and-docstring close-out): the "this measure has not been built" claim
above is STALE.** The measure has been built, sorry-free: `applyAllTImpRules b edges =
b ++ newForms.flatten ++ genCopies.flatten` (`Expansion.lean`) is purely additive, so the
length-equality exit of `applyPersistenceFixpoint` genuinely IS fixpoint-ness
(`applyAllTImpRules_eq_self_of_length_eq`, `Scheme.lean:5335`) — the only non-genuine exit is
`fuel = 0` — and `applyPersistenceFixpoint_genuine_of_count_le_fuel` (`Scheme.lean:5386`)
discharges exactly that remaining case, stated for arbitrary `b` and `fuel`, with both its
hypotheses already in scope at every arm of the `key` induction below, including the reuse arm
(`case6`). Gap 1's fuel-sufficiency side is therefore closed. This does **not** discharge the
`sorry` immediately below (DP-5's augmented-frame instantiation), which genuinely depends on the
AUGMENTED-frame positive-formula persistence invariant and is refuted at `phiRef1` (see that
`sorry`'s own annotation, and `CslibTests/BetaSplitRefutation.lean`). **Correction**: it does
NOT, however, bear on DP-3/DP-4 the way an earlier note here claimed. Those consume
`openBranch_countermodel`'s conjunct 1, which — per that lemma's docstring — needs no algorithm
invariant at all, so the claim that all three depended on this refuted invariant was itself
wrong for DP-3/DP-4; only DP-5's augmented-frame instantiation genuinely does. Retained here,
uncorrected in place except for that one dependency claim, as a historical record of the earlier
(mistaken) blocker analysis; do not re-derive the "not been built" claim or its correction.

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
about branch-syntactic saturation, so it does not depend on Gap 1 at all.

**GAP 1 UPDATE (post-ancestor-blocking calculus repair): the anticipated closure route no
longer exists in this codebase; this is a confirmed structural blocker, not an unattempted
proof.** A later dispatch's task list proposed closing Gap 1 by threading
`applyPersistenceFixpoint_genuine_of_count_le_fuel` (below, `:3444` at time of writing) so the
returned branch is a genuine fixpoint of `applyAllTImpRules`, on the premise that "every world
accessible from a `T(φ'→ψ')` source carries its own copy (the `applyAllTImpRules` copy channel
at a fixpoint)". **That copy channel ("Deliverable 6") was deliberately removed**, commit
`a70187dd` ("bound the T-implication self-copy channel (STEP 1)"), which deleted exactly the
`copies`/`combined` block of `applyAllTImpRules` that used to copy `T(φ → ψ)` itself to every
accessible world lacking one — verified by direct diff inspection, not inference. That commit's
own docstring on `applyAllTImpRules` (`Expansion.lean`, "STEP 1" note) states explicitly:
*"Whether `sat_timp` can additionally be established at accessible worlds (not just reflexively)
is Gap 1 and remains out of scope for this task; `truthLemma`'s T-imp `sorry` … is untouched by
this change."* The removal happened because a companion divergence probe (variant V3) measured
the channel as termination-irrelevant hygiene once ancestor-directed blocking is active — a
correct and well-evidenced call for that repair's own goal — but it leaves the `sat_timp`
discharge below without the mechanism the later task list named.

**What survives, and where the remaining gap actually sits (partial progress, recorded for the
next attempt).** `applyAllTImpRules`'s ψ-CONSEQUENCE propagation (`intTImpRule`, unaffected by
the self-copy removal) still fires FROM the source world, not needing any copy AT `w'`: at a
genuine fixpoint, for `T(φ→ψ)@w ∈ b` and `w'` accessible from `w`, `T(φ)@w' ∈ b → T(ψ)@w' ∈ b`
(else `intTImpRule φ ψ w edges b` would be non-empty, contradicting fixpoint-ness — a
straightforward `filterMap`/`countP` argument mirroring `applyAllTImpRules_count_drop` above).
This is *stronger* than what a copy-then-reflexive-branch route gives, in that it needs no copy
of `T(φ→ψ)` at `w'` at all. But it is not sufficient to close the `sorry` below: the goal after
`intro w' hacc hforce_φ'` needs `IForces … w' ψ'` from `IForces … w' φ'` (semantic forcing), and
the ψ-consequence fact above only fires from *branch membership* `T(φ)@w' ∈ b`, not from
semantic `IForces`. `truthLemma`'s own induction hypotheses (`ih_φ'`/`ih_ψ'`) give
`T(_)@w'∈b → Force` and `F(_)@w'∈b → ¬Force`, never the converse `Force → T(_)@w'∈b` — so there
is no way to recover membership from `hforce_φ'` alone without an independent
bivalence/totality fact (`T(φ')@w'∈b ∨ F(φ')@w'∈b`) that nothing in this file currently
establishes. This is the same totality gap the original copy-then-branch route existed to
sidestep (a copy at `w'` lets `intApplyRuleFull`'s `.pos,.imp` arm supply the disjunction
directly, without needing prior membership of `φ'` itself) — removing the copy channel removed
that sidestep, not the underlying need for it.

**Recommendation for continuation (revised after dedicated continuation-options research).**
Do not re-add the self-copy channel in this file — doing so is calculus-level work outside a
`Scheme.lean`-only dispatch (`Expansion.lean` is out of scope here) and remains a decision for a
dedicated follow-up, not a call to make unilaterally mid-dispatch. Two corrections to the
options above, established by that research and recorded here so a future attempt does not
re-derive them:

(i) **Reinstating the self-copy channel does not reopen the divergence the calculus repair
fixed — this is already measured, not merely plausible.** The repair's own variant-selection
probe compared "ancestor blocking with the self-copy channel retained" against "ancestor
blocking with it removed": both terminate and reach the *identical* saturated branch across
every fuel value tested, and all conformance rows match under either. Option (a)'s "would need
its own divergence probe before being trusted" is therefore over-cautious: the retained-channel
variant of that very probe already stands as the trust evidence: only a re-confirmation against
the current tree is outstanding, not a fresh probe from scratch.

(ii) **But a bare reinstatement of the channel would NOT by itself close Gap 1 — a fact no
earlier note here recorded.** `intExpandBranches_openBranch_sat`'s conclusion existentially
quantifies over an edge list built from `augSets`, decoupled from the algorithm's own edge
list and carrying the calculus repair's loop-back edges. `truthLemma`'s frame above installs
`intAccessPreorder` over exactly that AUGMENTED list, so the T-imp goal ranges over strictly
more worlds than any copy channel — which only ever copies along the algorithm's RAW edges —
can reach. The gate is therefore a loop-back transfer lemma (`T(φ)@x ∈ b → T(φ)@l ∈ b` across a
recorded loop-back edge `(x, l)`, using the `Sfor`-containment established at the blocking
site), not the copy channel alone; a bounded self-copy variant is still one route to supplying
`T(φ'→ψ')`'s own copy at directly-accessible worlds, but the augmented-frame gap must close
first for either a bounded self-copy variant (a) or the quotient/blocking-frame reconstruction
(b) to actually discharge this case. This whole self-copy-channel analysis (i)-(ii) is now
historical: DP-5 was discharged via the `hpers` route at the top of this note instead, which
needs neither a self-copy channel nor a loop-back transfer lemma — it takes persistence as an
explicit hypothesis and lets the CALLER supply it (refuted at the augmented frame, provable at
the raw/sub-raw frame). The augmented-frame gap this paragraph names is real and still open, but
it now blocks a DIFFERENT goal: `openBranch_countermodel`'s own surviving existential
(`Scheme.lean`, further below), not this lemma's T-imp case. -/

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
    (hpers : ∀ (χ : Proposition Atom) (x y : Nat), isAccessible edges x y = true →
      (⟨.pos, χ, x⟩ : ISF Atom) ∈ b → (⟨.pos, χ, y⟩ : ISF Atom) ∈ b)
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
      -- DISCHARGED (DP-5). `hpers` transfers `T(φ'→ψ')`'s membership from the source world `w`
      -- to the accessible world `w'` directly (chained along `Relation.ReflTransGen` by
      -- `induction hle`), so `w'` carries its own `T(φ'→ψ')` copy without any self-copy channel
      -- in `Expansion.lean`. `sat_timp` (a live `IBranchSaturation` field, `:105-108`) then
      -- supplies `F(φ')@w' ∈ b ∨ T(ψ')@w' ∈ b`: the `F(φ')@w'` arm contradicts `IForces val w'
      -- φ'` via `ih_φ'.2`, and the `T(ψ')@w'` arm yields the goal via `ih_ψ'.1`. See the
      -- "`sat_timp` discharge" STOP-gate note above this lemma for the full history (the
      -- originally-anticipated self-copy-channel route was superseded by this `hpers` route).
      --
      -- `hpers` is REFUTED at the AUGMENTED frame (`CslibTests/BetaSplitRefutation.lean`, zero
      -- errors, zero sorries: `phiRef1 := ((pr ∨ ps) ∧ ((ps → (ps → pr)) → pb)) → pr` has
      -- augmented-preorder-equivalent worlds `1`/`2` -- joined by a loop-back edge
      -- `intFImpReuseWitnessAnc?` never re-validates once recorded, see that declaration's
      -- docstring in `Expansion.lean` -- that disagree on `pr`), so this case is
      -- unconditionally true only when the CALLER supplies `hpers` -- provable over the raw
      -- frame (`IPosPersistRaw`/`IWorldsPlanted`, sorry-free) or any sub-raw frame, refuted over
      -- the augmented frame. That caller-side obligation is `openBranch_countermodel`'s concern
      -- (further below in this file), not this lemma's: `truthLemma` itself is now
      -- unconditionally true over any frame carrying `hpers`.
      intro hT w' hle
      have hmem : (⟨.pos, .imp φ' ψ', w⟩ : ISF Atom) ∈ b := by
        obtain ⟨sf, hsfb, hsfp⟩ := List.any_eq_true.mp hT
        simp only [Bool.and_eq_true, beq_iff_eq] at hsfp
        obtain ⟨⟨hs, hf⟩, hl⟩ := hsfp
        cases sf; simp_all
      have hmem' : (⟨.pos, .imp φ' ψ', w'⟩ : ISF Atom) ∈ b := by
        induction hle with
        | refl => exact hmem
        | @tail y w2 _hchain hstep ih => exact hpers _ y w2 hstep ih
      have hany' : b.any
          (fun sf => sf.sign == .pos && sf.formula == .imp φ' ψ' && sf.label == w') = true :=
        List.any_eq_true.mpr ⟨_, hmem', by simp⟩
      intro hforce_φ'
      rcases hsat.sat_timp φ' ψ' w' hany' with hF | hT2
      · exact absurd hforce_φ' ((ih_φ' w').2 hF)
      · exact (ih_ψ' w').1 hT2
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
    · apply ih; simp only [applyAllTImpRules, List.mem_append]; exact Or.inl (Or.inl h)

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

`sfSatisfied`'s `.neg, .imp` clause originally recorded a numeric proxy `sf.label ≤ w'` for
accessibility; that conjunct has since been DROPPED (it held only under descendant-directed
label growth and is false under ancestor blocking, where the reuse witness carries a *smaller*
label — see the definitions above). `sfAccessSat`/`IExpandedAccessConsistent`, defined below,
carry the genuine content in strictly stronger form: `isAccessible edges sf.label w'` rather
than a raw `Nat` comparison, needed to instantiate `truthLemma`'s F-imp case over
`intAccessPreorder edges` (which requires genuine edge-reachability of the witness, not merely
a numeric bound).

An ancestor witness `x` — reachable in the REVERSE direction from what `sfAccessSat`'s
`.neg, .imp` clause demands (`l ≤ w'` shape) — is made admissible not by identifying `x` with
the blocked world `l` under a representative map, but by recording the blocking event itself as
an explicit loop-back edge `(x, l)` in an invariant-side augmented edge list (`augSets`,
threaded through `intExpandBranches_openBranch_sat`'s induction), at the moment each block
happens. `Sfor`-containment (`hcont : posFormulasAt bPers l ⊆ posFormulasAt bPers x`) together
with ancestor persistence gives the converse containment, so `x` and `l` force the same positive
formulas; `IForces` (`Semantics/Kripke.lean`) is defined over `[Preorder World]` with no
antisymmetry requirement, so the resulting cycle in the enlarged accessibility relation is
admissible. This is `GargGenoveseNegri2012`'s published countermodel construction
`M ∪ C` with `C = {x ≤ y | Sfor(x) ⊆ Sfor(y)}` — cited as provenance only; the source is not
readable in-repo and the design rests on the verified construction here, not on the paper text.
Both the fresh-world-creation site (`intFImpRule`'s new edge `(w', w)`, one-hop via
`isAccessible_one_step`) and the reuse-site discharge (which appends `(x, l)` to `augSets`)
establish the underlying fact at construction time; this invariant only threads it forward. -/

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

/-- **Phase 4** (strict label bound; report section 5.4): every formula on `b` has a label
STRICTLY less than the current next-world counter `nw`. Strictly stronger than `ILabelBound`
(which the DP-2 route already threads and which stays unmodified -- this is a companion, not a
replacement). The strict form is what justifies `par c < c` at the mint arm: the world that
mints `c = nw` records its parent's label `par c`, and `par c < nw` (strict) is exactly what
this invariant supplies at the moment of minting. -/
private def ILabelBoundStrict (b : IBranch Atom) (nw : Nat) : Prop :=
  ∀ sf ∈ b, sf.label < nw

omit [Hashable Atom] [DecidableEq Atom] in
/-- `ILabelBoundStrict` extends across `Branch.extendMany` when the new formulas' labels are
strictly bounded by the (possibly larger) new counter and the old counter only grows (mirrors
`ILabelBound_extendMany`). -/
private lemma ILabelBoundStrict_extendMany {b : IBranch Atom} {nw nw' : Nat}
    {newForms : List (ISF Atom)}
    (hle : nw ≤ nw') (h : ILabelBoundStrict b nw)
    (hnew : ∀ sf ∈ newForms, sf.label < nw') :
    ILabelBoundStrict (Branch.extendMany b newForms) nw' := by
  intro sf hsf
  simp only [Branch.extendMany, List.mem_append] at hsf
  rcases hsf with hsf | hsf
  · exact hnew sf hsf
  · exact lt_of_lt_of_le (h sf hsf) hle

/-- The shape a `some` result of either stepper (`intStepBranch` or `intStepBranchPrio`)
extracts from the branch: some `sf ∈ b`, not already in the `expanded` set `e`, whose rule
application is exactly `result`, with `newExp` the `expanded` set extended by `sf`.

Naming this once (Phase 2 of the beta-priority repair, report §5.1) lets every downstream
`intStepBranch_*` lemma that currently unfolds `intStepBranch` directly instead take a single
`IStepShape` hypothesis that a `some` result of *either* stepper satisfies -- the abstraction
the Phase 3 call-site swap needs to be a small, local edit: `go`'s proof obligations move from
"derived from `intStepBranch b e nw = some (...)`" to "derived from `IStepShape b e nw ...`",
supplied by `intStepBranch_some_shape` today and by `intStepBranchPrio_some_exists` after the
swap, with no change to the obligation lemmas themselves. -/
def IStepShape (b : IBranch Atom) (e : List (ISF Atom)) (nw : Nat)
    (result : IntRuleResult Atom) (newExp : List (ISF Atom)) : Prop :=
  ∃ sf, sf ∈ b ∧ sf ∉ e ∧ intApplyRuleFull sf nw b = result ∧ newExp = e ++ [sf]

omit [Hashable Atom] in
/-- `intStepBranch`'s `some` result satisfies `IStepShape`. Strengthens the un-named extraction
this file previously performed inline (and which `intStepBranch_some_exists_fuel` below used to
duplicate under a different name) with the `sf ∉ e` conjunct in one place. -/
lemma intStepBranch_some_shape
    {b : IBranch Atom} {e : List (ISF Atom)} {nw : Nat}
    {result : IntRuleResult Atom} {newExp : List (ISF Atom)}
    (hstep : intStepBranch b e nw = some (result, newExp)) :
    IStepShape b e nw result newExp := by
  simp only [intStepBranch] at hstep
  obtain ⟨sf, hsfb, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  by_cases hexp : (e.any (· == sf)) = true
  · simp [hexp] at hsf
  · simp only [Bool.not_eq_true] at hexp
    simp only [hexp, Bool.false_eq_true, if_false] at hsf
    have hsfne : sf ∉ e := fun hmem => by
      have hcontra : e.any (· == sf) = true := List.any_eq_true.mpr ⟨sf, hmem, by simp⟩
      simp [hexp] at hcontra
    cases hint : intApplyRuleFull sf nw b with
    | notApplicable => simp [hint] at hsf
    | linearResult fs nw' ed =>
      simp only [hint, Option.some.injEq, Prod.mk.injEq] at hsf
      exact ⟨sf, hsfb, hsfne, hint.trans hsf.1, hsf.2.symm⟩
    | branchingResult bs nw' =>
      simp only [hint, Option.some.injEq, Prod.mk.injEq] at hsf
      exact ⟨sf, hsfb, hsfne, hint.trans hsf.1, hsf.2.symm⟩

omit [Hashable Atom] in
/-- Converts `IStepShape`'s `sf ∉ e` (Prop) negation to the `List.any`-Bool-false form that
`intWork_drop` and (below) `intStepBranch_some_exists_fuel` expect. -/
private lemma any_beq_eq_false_of_not_mem {e : List (ISF Atom)} {sf : ISF Atom}
    (hne : sf ∉ e) : e.any (· == sf) = false := by
  cases hcase : e.any (· == sf) with
  | false => rfl
  | true =>
    obtain ⟨x, hx, hxeq⟩ := List.any_eq_true.mp hcase
    exact absurd ((beq_iff_eq.mp hxeq) ▸ hx) hne

omit [Hashable Atom] [DecidableEq Atom] in
/-- Extracts the processed formula from a `some` result of `intStepBranch`: some
`sf ∈ b` had `intApplyRuleFull sf nw b = result` and `newExp = e ++ [sf]`. Now a thin
weakening of `intStepBranch_some_shape` (drops the `sf ∉ e` conjunct), rather than its own
direct unfold, per Phase 2's re-basing. -/
private lemma intStepBranch_some_exists
    {b : IBranch Atom} {e : List (ISF Atom)} {nw : Nat}
    {result : IntRuleResult Atom} {newExp : List (ISF Atom)}
    (hshape : IStepShape b e nw result newExp) :
    ∃ sf, sf ∈ b ∧ intApplyRuleFull sf nw b = result ∧ newExp = e ++ [sf] := by
  obtain ⟨sf, hsfb, -, hint, hnewExp⟩ := hshape
  exact ⟨sf, hsfb, hint, hnewExp⟩

omit [Hashable Atom] in
/-- `intStepBranchPrio` returns `none` in exactly the same circumstances as `intStepBranch`
(Phase 1 of the beta-priority repair, report §5.2).

Forward: if `intStepBranchPrio` is `none`, the first pass must have been `none` (else
`intStepBranchPrio` would return `some`), so `intStepBranchPrio` reduces definitionally to
`intStepBranch b e nw`, which is therefore `none`.

Reverse: if `intStepBranch b e nw = none`, then by `List.findSome?_eq_none_iff`, no `sf ∈ b`
satisfies `intStepBranch`'s guard-and-apply predicate. The first pass's predicate is strictly
more restrictive (same predicate, plus `¬ isWorldCreating sf`), so no `sf ∈ b` satisfies it
either; hence the first pass is also `none`, and `intStepBranchPrio` reduces to
`intStepBranch b e nw = none`. Every `none`-keyed downstream fact -- saturation,
`IBranchSaturation`, `intExpandBranches_openBranch_sat`'s open-branch leaf -- transfers across
the swap via this bridge alone, with no reproof needed (Phase 3). -/
lemma intStepBranchPrio_none_iff
    {b : IBranch Atom} {e : List (ISF Atom)} {nw : Nat} :
    intStepBranchPrio b e nw = none ↔ intStepBranch b e nw = none := by
  constructor
  · intro h
    simp only [intStepBranchPrio] at h
    cases hfp : intStepBranchPrioFirstPass b e nw with
    | none => simp only [hfp] at h; exact h
    | some rp => simp only [hfp] at h; exact absurd h (by simp)
  · intro h
    have hfpNone : intStepBranchPrioFirstPass b e nw = none := by
      simp only [intStepBranchPrioFirstPass]
      rw [List.findSome?_eq_none_iff]
      intro sf hsfb
      simp only [intStepBranch, List.findSome?_eq_none_iff] at h
      have hbody := h sf hsfb
      by_cases hguard : (e.any (· == sf) || isWorldCreating sf) = true
      · simp [hguard]
      · simp only [Bool.not_eq_true] at hguard
        rw [Bool.or_eq_false_iff] at hguard
        simp only [hguard.1, Bool.false_eq_true, if_false] at hbody
        simp only [hguard.1, hguard.2, Bool.or_self, Bool.false_eq_true, if_false]
        exact hbody
    simp only [intStepBranchPrio, hfpNone]
    exact h

omit [Hashable Atom] in
/-- Extraction bridge for `intStepBranchPrio`: its `some` result also satisfies `IStepShape`
(Phase 2 re-point of the Phase 1 bridge onto the shared predicate). The `none`-first-pass case
reduces directly to `intStepBranch_some_shape`; the `some`-first-pass case repeats the same
`findSome?`/`if`-unfold shape one level up, over `intStepBranchPrioFirstPass`'s extra
`isWorldCreating` guard disjunct. -/
lemma intStepBranchPrio_some_exists
    {b : IBranch Atom} {e : List (ISF Atom)} {nw : Nat}
    {result : IntRuleResult Atom} {newExp : List (ISF Atom)}
    (hstep : intStepBranchPrio b e nw = some (result, newExp)) :
    IStepShape b e nw result newExp := by
  simp only [intStepBranchPrio] at hstep
  cases hfp : intStepBranchPrioFirstPass b e nw with
  | none =>
    simp only [hfp] at hstep
    exact intStepBranch_some_shape hstep
  | some rp =>
    obtain ⟨result', newExp'⟩ := rp
    simp only [hfp, Option.some.injEq, Prod.mk.injEq] at hstep
    obtain ⟨hresEq, hnewExpEq⟩ := hstep
    subst hresEq; subst hnewExpEq
    simp only [intStepBranchPrioFirstPass] at hfp
    obtain ⟨sf, hsfb, hsf⟩ := List.exists_of_findSome?_eq_some hfp
    by_cases hguard : (e.any (· == sf) || isWorldCreating sf) = true
    · simp [hguard] at hsf
    · simp only [Bool.not_eq_true] at hguard
      rw [Bool.or_eq_false_iff] at hguard
      simp only [hguard.1, hguard.2, Bool.or_self, Bool.false_eq_true, if_false] at hsf
      have hsfne : sf ∉ e := fun hmem => by
        have hcontra : e.any (· == sf) = true := List.any_eq_true.mpr ⟨sf, hmem, by simp⟩
        simp [hguard.1] at hcontra
      cases hint : intApplyRuleFull sf nw b with
      | notApplicable => simp [hint] at hsf
      | linearResult fs nw' ed =>
        simp only [hint, Option.some.injEq, Prod.mk.injEq] at hsf
        exact ⟨sf, hsfb, hsfne, hint.trans hsf.1, hsf.2.symm⟩
      | branchingResult bs nw' =>
        simp only [hint, Option.some.injEq, Prod.mk.injEq] at hsf
        exact ⟨sf, hsfb, hsfne, hint.trans hsf.1, hsf.2.symm⟩

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
    (hshape : IStepShape b e nw (.linearResult newForms nw' newEdge) newExp) :
    IExpandedConsistent (Branch.extendMany b newForms) newExp ∧
      ILabelBound (Branch.extendMany b newForms) nw' ∧
      IExpandedAccessConsistent (newEdge.elim edges (fun ed => edges ++ [ed]))
        (Branch.extendMany b newForms) newExp := by
  obtain ⟨sf, hsfb, hint, hnewExp⟩ := intStepBranch_some_exists hshape
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

omit [Hashable Atom] [DecidableEq Atom] in
/-- **Phase 4**: a `linearResult` step of `intStepBranch` preserves the strict label-bound
companion `ILabelBoundStrict`: the ALPHA arms (`.pos,.and` / `.neg,.or`) only ever emit
formulas at the processed formula's own label `l`, and `l < nw` is exactly the head fact
`hLBS` already supplies (so `l < nw'` since `nw' = nw` there); the world-creating `.neg,.imp`
arm (the mint case) emits every new formula at exactly the CURRENT counter `nw`, and
`nw < nw' = nw + 1` is immediate. Companion of `intStepBranch_linear_preserves`, mirroring the
existing `hUniv`/`hNW`/`hFuel` companion-lemma pattern (`intStepBranch_linear_preserves_univ`
etc.) for this new invariant. -/
private lemma intStepBranch_linear_preserves_labelStrict
    {b : IBranch Atom} {e : List (ISF Atom)} {nw : Nat}
    {newForms : List (ISF Atom)} {nw' : Nat} {newEdge : Option (Nat × Nat)}
    {newExp : List (ISF Atom)}
    (hLBS : ILabelBoundStrict b nw)
    (hshape : IStepShape b e nw (.linearResult newForms nw' newEdge) newExp) :
    ILabelBoundStrict (Branch.extendMany b newForms) nw' := by
  obtain ⟨sf, hsfb, hint, -⟩ := intStepBranch_some_exists hshape
  have hsfl : sf.label < nw := hLBS sf hsfb
  obtain ⟨s, ff, l⟩ := sf
  simp only at hsfl hint
  cases s with
  | pos =>
    cases ff with
    | atom x => simp [intApplyRuleFull] at hint
    | bot => simp [intApplyRuleFull] at hint
    | imp φ ψ => simp [intApplyRuleFull] at hint
    | or φ ψ => simp [intApplyRuleFull] at hint
    | and φ ψ =>
      simp only [intApplyRuleFull, IntRuleResult.linearResult.injEq] at hint
      obtain ⟨hnf, hnw', -⟩ := hint
      subst hnw'
      refine ILabelBoundStrict_extendMany (le_refl nw) hLBS ?_
      intro sf' hsf'
      rw [← hnf] at hsf'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hsf'
      rcases hsf' with rfl | rfl <;> simpa using hsfl
  | neg =>
    cases ff with
    | atom x => simp [intApplyRuleFull] at hint
    | bot => simp [intApplyRuleFull] at hint
    | and φ ψ => simp [intApplyRuleFull] at hint
    | or φ ψ =>
      simp only [intApplyRuleFull, IntRuleResult.linearResult.injEq] at hint
      obtain ⟨hnf, hnw', -⟩ := hint
      subst hnw'
      refine ILabelBoundStrict_extendMany (le_refl nw) hLBS ?_
      intro sf' hsf'
      rw [← hnf] at hsf'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hsf'
      rcases hsf' with rfl | rfl <;> simpa using hsfl
    | imp φ ψ =>
      simp only [intApplyRuleFull, intFImpRule, IntRuleResult.linearResult.injEq] at hint
      obtain ⟨hnf, hnw', -⟩ := hint
      subst hnw'
      refine ILabelBoundStrict_extendMany (Nat.le_succ nw) hLBS ?_
      intro sf' hsf'
      rw [← hnf] at hsf'
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hsf'
      rcases hsf' with (rfl | rfl) | hpers
      · exact Nat.lt_succ_self nw
      · exact Nat.lt_succ_self nw
      · simp only [propagatePersistence, List.mem_map] at hpers
        obtain ⟨a, -, rfl⟩ := hpers
        exact Nat.lt_succ_self nw

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
    (hshape : IStepShape b e nw (.branchingResult branches' nw') newExp) :
    ∀ br ∈ branches',
      IExpandedConsistent (Branch.extendMany b br) newExp ∧
        ILabelBound (Branch.extendMany b br) nw' ∧
        IExpandedAccessConsistent edges (Branch.extendMany b br) newExp := by
  obtain ⟨sf, hsfb, hint, hnewExp⟩ := intStepBranch_some_exists hshape
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

omit [Hashable Atom] [DecidableEq Atom] in
/-- **Phase 4**: a `branchingResult` step of `intStepBranch` preserves the strict label-bound
companion `ILabelBoundStrict` on every sub-branch: branching arms (`.pos,.or` / `.pos,.imp`
Deliverable 6 / `.neg,.and`) never mint a world (`nw' = nw`) and every disjunct formula is
emitted at the processed formula's own label `l`, so the same head fact `hLBS sf hsfb : l < nw`
transfers directly. Companion of `intStepBranch_branch_preserves`. -/
private lemma intStepBranch_branch_preserves_labelStrict
    {b : IBranch Atom} {e : List (ISF Atom)} {nw : Nat}
    {branches' : List (List (ISF Atom))} {nw' : Nat} {newExp : List (ISF Atom)}
    (hLBS : ILabelBoundStrict b nw)
    (hshape : IStepShape b e nw (.branchingResult branches' nw') newExp) :
    ∀ br ∈ branches', ILabelBoundStrict (Branch.extendMany b br) nw' := by
  obtain ⟨sf, hsfb, hint, -⟩ := intStepBranch_some_exists hshape
  have hsfl : sf.label < nw := hLBS sf hsfb
  obtain ⟨s, ff, l⟩ := sf
  simp only at hsfl hint
  intro br hbr
  cases s with
  | pos =>
    cases ff with
    | atom x => simp [intApplyRuleFull] at hint
    | bot => simp [intApplyRuleFull] at hint
    | imp φ ψ =>
      simp only [intApplyRuleFull, IntRuleResult.branchingResult.injEq] at hint
      obtain ⟨hbrs, hnw'⟩ := hint
      subst hnw'
      rw [← hbrs] at hbr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr
      intro sf' hsf'
      rcases hbr with rfl | rfl <;>
        simp only [Branch.extendMany, List.mem_cons, List.mem_nil_iff, List.mem_append,
          or_false] at hsf' <;>
        rcases hsf' with rfl | hsf' <;> first | exact hsfl | exact hLBS sf' hsf'
    | and φ ψ => simp [intApplyRuleFull] at hint
    | or φ ψ =>
      simp only [intApplyRuleFull, IntRuleResult.branchingResult.injEq] at hint
      obtain ⟨hbrs, hnw'⟩ := hint
      subst hnw'
      rw [← hbrs] at hbr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr
      intro sf' hsf'
      rcases hbr with rfl | rfl <;>
        simp only [Branch.extendMany, List.mem_cons, List.mem_nil_iff, List.mem_append,
          or_false] at hsf' <;>
        rcases hsf' with rfl | hsf' <;> first | exact hsfl | exact hLBS sf' hsf'
  | neg =>
    cases ff with
    | atom x => simp [intApplyRuleFull] at hint
    | bot => simp [intApplyRuleFull] at hint
    | imp φ ψ => simp [intApplyRuleFull] at hint
    | or φ ψ => simp [intApplyRuleFull] at hint
    | and φ ψ =>
      simp only [intApplyRuleFull, IntRuleResult.branchingResult.injEq] at hint
      obtain ⟨hbrs, hnw'⟩ := hint
      subst hnw'
      rw [← hbrs] at hbr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr
      intro sf' hsf'
      rcases hbr with rfl | rfl <;>
        simp only [Branch.extendMany, List.mem_cons, List.mem_nil_iff, List.mem_append,
          or_false] at hsf' <;>
        rcases hsf' with rfl | hsf' <;> first | exact hsfl | exact hLBS sf' hsf'

omit [Hashable Atom] in
/-- `applyAllTImpRules` only introduces new formulas whose label already appears on `b`
(drawn from `intTImpRule`'s `accessibleWorlds`, itself a subset of `b.map (·.label)`), so a
single persistence-propagation step preserves `ILabelBound`. Mirrors the structural pattern of
the (private, non-reusable) `intTImpRules_sat`-style proofs in `Soundness.lean`. -/
private lemma ILabelBound_applyAllTImpRules {b : IBranch Atom} {edges : IEdges} {nw : Nat}
    (h : ILabelBound b nw) : ILabelBound (applyAllTImpRules b edges) nw := by
  intro sf hmem
  simp only [applyAllTImpRules, List.mem_append] at hmem
  rcases hmem with (hmem | hmem) | hmem
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
  · -- Generalized copy channel: the copy's label `w'` is drawn from `b.map (·.label)`
    -- directly, bounded exactly like any other pre-existing label.
    simp only [List.mem_flatten, List.mem_filterMap] at hmem
    obtain ⟨cs, ⟨⟨sign_o, form_o, label_o⟩, hmem_outer, hmatch⟩, hmem_cs⟩ := hmem
    cases sign_o with
    | neg => simp only at hmatch; exact absurd hmatch (by simp)
    | pos =>
      simp only at hmatch
      by_cases hemp : (List.filterMap
          (fun w' =>
            if b.any (fun y => y.sign == .pos && y.formula == form_o && y.label == w') then none
            else some (⟨.pos, form_o, w'⟩ : ISF Atom))
          (List.filter (isAccessible edges label_o ·) (b.map (·.label)).eraseDups)).isEmpty
          = true
      · simp only [hemp, ite_true] at hmatch; exact absurd hmatch (by simp)
      · simp only [Bool.false_eq_true, hemp, ite_false, Option.some.injEq] at hmatch
        rw [← hmatch] at hmem_cs
        simp only [List.mem_filterMap, List.mem_filter, List.mem_eraseDups,
          List.mem_map] at hmem_cs
        obtain ⟨w', ⟨⟨x, hxb, hxeq⟩, -⟩, hcopy⟩ := hmem_cs
        split_ifs at hcopy with hcond
        simp only [Option.some.injEq] at hcopy
        rw [← hcopy]
        simpa [← hxeq] using h x hxb

omit [Hashable Atom] in
/-- **Phase 4**: `applyAllTImpRules` only introduces new formulas whose label already appears
on `b` (mirrors `ILabelBound_applyAllTImpRules`; the persistence-propagation rule never mints
a world, so it preserves the strict companion too). -/
private lemma ILabelBoundStrict_applyAllTImpRules {b : IBranch Atom} {edges : IEdges} {nw : Nat}
    (h : ILabelBoundStrict b nw) : ILabelBoundStrict (applyAllTImpRules b edges) nw := by
  intro sf hmem
  simp only [applyAllTImpRules, List.mem_append] at hmem
  rcases hmem with (hmem | hmem) | hmem
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
  · simp only [List.mem_flatten, List.mem_filterMap] at hmem
    obtain ⟨cs, ⟨⟨sign_o, form_o, label_o⟩, hmem_outer, hmatch⟩, hmem_cs⟩ := hmem
    cases sign_o with
    | neg => simp only at hmatch; exact absurd hmatch (by simp)
    | pos =>
      simp only at hmatch
      by_cases hemp : (List.filterMap
          (fun w' =>
            if b.any (fun y => y.sign == .pos && y.formula == form_o && y.label == w') then none
            else some (⟨.pos, form_o, w'⟩ : ISF Atom))
          (List.filter (isAccessible edges label_o ·) (b.map (·.label)).eraseDups)).isEmpty
          = true
      · simp only [hemp, ite_true] at hmatch; exact absurd hmatch (by simp)
      · simp only [Bool.false_eq_true, hemp, ite_false, Option.some.injEq] at hmatch
        rw [← hmatch] at hmem_cs
        simp only [List.mem_filterMap, List.mem_filter, List.mem_eraseDups,
          List.mem_map] at hmem_cs
        obtain ⟨w', ⟨⟨x, hxb, hxeq⟩, -⟩, hcopy⟩ := hmem_cs
        split_ifs at hcopy with hcond
        simp only [Option.some.injEq] at hcopy
        rw [← hcopy]
        simpa [← hxeq] using h x hxb

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

omit [Hashable Atom] in
/-- **Phase 4**: `ILabelBoundStrict` is preserved by `applyPersistenceFixpoint` (mirrors
`ILabelBound_applyPersistenceFixpoint`). -/
private lemma ILabelBoundStrict_applyPersistenceFixpoint {b : IBranch Atom} {edges : IEdges}
    {nw : Nat} (fuel : Nat) (h : ILabelBoundStrict b nw) :
    ILabelBoundStrict (applyPersistenceFixpoint b edges fuel) nw := by
  induction fuel generalizing b with
  | zero => simpa [applyPersistenceFixpoint] using h
  | succ k ih =>
    simp only [applyPersistenceFixpoint]
    split_ifs with hlen
    · exact h
    · exact ih (ILabelBoundStrict_applyAllTImpRules h)

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

/-- **Phase 4**: the strict-label-bound companion of `IAllConsistent`, threaded ALONGSIDE it
(not merged in, to avoid touching `IAllConsistent`'s already-green call sites) through the same
`branches`/`nextWorlds` pair. A 2-list zip (only `bs` and `nws` are needed, since
`ILabelBoundStrict` does not depend on an expanded-set component), defined by simultaneous
recursion so a length mismatch is automatically `False`, mirroring `IAllConsistent`'s own shape
one list narrower. -/
private def IAllLabelBoundStrict (bs : List (IBranch Atom)) (nws : List Nat) : Prop :=
  match bs, nws with
  | [], [] => True
  | b :: bs', nw :: nws' => ILabelBoundStrict b nw ∧ IAllLabelBoundStrict bs' nws'
  | _, _ => False

omit [Hashable Atom] [DecidableEq Atom] in
/-- `IAllLabelBoundStrict` combines under list append (mirrors `IAllConsistent_append`). -/
private lemma IAllLabelBoundStrict_append {bs1 bs2 : List (IBranch Atom)}
    {nws1 nws2 : List Nat}
    (h1 : IAllLabelBoundStrict bs1 nws1) (h2 : IAllLabelBoundStrict bs2 nws2) :
    IAllLabelBoundStrict (bs1 ++ bs2) (nws1 ++ nws2) := by
  induction bs1 generalizing nws1 with
  | nil =>
    cases nws1 with
    | nil => simpa using h2
    | cons nwh nwt => simp [IAllLabelBoundStrict] at h1
  | cons bh bt ih =>
    cases nws1 with
    | nil => simp [IAllLabelBoundStrict] at h1
    | cons nwh nwt =>
      simp only [IAllLabelBoundStrict] at h1
      obtain ⟨hLBS, hrest⟩ := h1
      simp only [List.cons_append]
      exact ⟨hLBS, ih hrest⟩

omit [Hashable Atom] [DecidableEq Atom] in
/-- `IAllLabelBoundStrict` holds along a constant-valued `map` (mirrors `IAllConsistent_map`
narrowed to one list; used by the BETA arm, where every sub-branch shares one `nw'`). -/
private lemma IAllLabelBoundStrict_map {branches' : List (IBranch Atom)}
    (f : IBranch Atom → IBranch Atom) {nw' : Nat}
    (h : ∀ br ∈ branches', ILabelBoundStrict (f br) nw') :
    IAllLabelBoundStrict (branches'.map f) (branches'.map (fun _ => nw')) := by
  induction branches' with
  | nil => simp [IAllLabelBoundStrict]
  | cons bh bt ih =>
    simp only [List.map_cons, IAllLabelBoundStrict]
    exact ⟨h bh (List.mem_cons_self ..), ih fun br hbr => h br (List.mem_cons_of_mem _ hbr)⟩

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
bookkeeping convenience for the now retained-but-unconsumed sum-measure engine below), NOT as a
containment guarantee that every world an actual expansion run visits lies within
`0 .. φ.complexity + 1`. Do not read `∀ x ∈ b, x ∈ intUniverse φ` as an established invariant of
`intExpandBranches`; the *Divergence witness* note shows a direct counterexample.

**Live development**: the per-branch-fuel expansion engine's own containment/fuel-sufficiency
argument does NOT use `intUniverse`/`intExpMeasure` -- it uses the enlarged, post-blocking-aware
universe `intUniverseExt` (below) sized against `WBound`, the world bound the ancestor-blocking
calculus repair's saturation actually respects. `intUniverse`/`intExpMeasure`/
`intExpMeasure_step_lt`(+`_branch`) remain in the file, build-green, but unconsumed by any
current statement; treat `intUniverseExt`/`WBound` as the live account of the world bound, and
this section as a retained, superseded alternative. -/
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

/-! ## Containment-Blocking Bridge

This section consumes the shared containment-blocking module
(`Cslib/Foundations/Logic/Tableau/Blocking.lean`) at the intuitionistic propositional
types. `IBranch Atom` is definitionally `Branch (Proposition Atom) Nat` (`Rules.lean` vs
`Branch.lean`), so the signed counting layer (`distinctTypes_le_pow`,
`exists_typeAt_eq_of_card_lt`, `strictChain_le_card`) applies to intuitionistic branches
without any coercion. The only content gap is between the local persistence projection
`posFormulasAt` (a raw `filterMap`, `Rules.lean`) and the blocking module's deduplicated
positive type `Branch.posTypeAt`: the two lists differ by an `eraseDups`, so they agree on
membership (`posFormulasAt_mem_iff`).

The signed universe is `intSignedUniverse φ := {pos, neg} ×ˢ (intSubfmls φ).toFinset`,
a `Finset (Sign × Proposition Atom)`, giving the *signed* `2 ^ V.card` type-count bound
of `distinctTypes_le_pow`. The sign pairing is load-bearing: an unsigned count over the
bare subformula universe undercounts (two labels can agree on positive formulas while
differing on negative ones and still have distinct types), which is why the counting layer
is instantiated only in this signed form. See [GargGenoveseNegri2012], §III, for the
corresponding count of distinct forced sets. -/

omit [Hashable Atom] in
/-- Membership bridge between the local persistence projection `posFormulasAt`
(`Rules.lean`) and the blocking module's deduplicated positive type `Branch.posTypeAt`
(`Blocking.lean`): the two lists differ only by an `eraseDups`, hence agree on
membership. `IBranch Atom` is definitionally `Branch (Proposition Atom) Nat`, so no
coercion is involved. -/
lemma posFormulasAt_mem_iff {b : IBranch Atom} {w : Nat} {φ : Proposition Atom} :
    φ ∈ posFormulasAt b w ↔ φ ∈ Branch.posTypeAt b w := by
  simp only [posFormulasAt, Branch.posTypeAt, List.mem_filterMap, List.mem_eraseDups,
    List.mem_map, List.mem_filter, Option.ite_none_right_eq_some, Option.some.injEq]
  constructor
  · rintro ⟨sf, hmem, hcond, hform⟩
    exact ⟨sf, ⟨hmem, hcond⟩, hform⟩
  · rintro ⟨sf, ⟨hmem, hcond⟩, hform⟩
    exact ⟨sf, hmem, hcond, hform⟩

omit [Hashable Atom] in
/-- The signed subformula universe for `φ`: both signs paired with every structural
subformula of `φ`. This is the universe `V : Finset (Sign × Proposition Atom)` at which
the blocking module's signed counting layer is instantiated for the intuitionistic
tableau. -/
def intSignedUniverse (φ : Proposition Atom) : Finset (Sign × Proposition Atom) :=
  ({.pos, .neg} : Finset Sign) ×ˢ (intSubfmls φ).toFinset

omit [Hashable Atom] in
/-- Membership in the signed universe ignores the sign: `(s, ψ)` lies in
`intSignedUniverse φ` exactly when `ψ` is a structural subformula of `φ`. -/
@[simp]
lemma mem_intSignedUniverse {φ ψ : Proposition Atom} {s : Sign} :
    (s, ψ) ∈ intSignedUniverse φ ↔ ψ ∈ intSubfmls φ := by
  cases s <;> simp [intSignedUniverse]

omit [Hashable Atom] in
/-- Signed type-count bound at the propositional instantiation: a branch whose formulas
all lie in `intSubfmls φ` exhibits at most `2 ^ (intSignedUniverse φ).card` distinct
signed types. Instantiates `distinctTypes_le_pow` at `V := intSignedUniverse φ`. -/
lemma intDistinctTypes_le_pow (φ : Proposition Atom) (b : IBranch Atom)
    (hb : ∀ sf ∈ b, sf.formula ∈ intSubfmls φ) :
    ((Branch.labels b).toFinset.image fun l => (Branch.typeAt b l).toFinset).card
      ≤ 2 ^ (intSignedUniverse φ).card :=
  distinctTypes_le_pow b (intSignedUniverse φ) fun sf hsf =>
    mem_intSignedUniverse.mpr (hb sf hsf)

omit [Hashable Atom] in
/-- Pigeonhole at the propositional instantiation: a branch whose formulas all lie in
`intSubfmls φ` and which carries more than `2 ^ (intSignedUniverse φ).card` distinct
world labels has two distinct labels with the same signed type. Instantiates
`exists_typeAt_eq_of_card_lt`; this is the loop-detection core the ancestor-blocking
termination argument consumes. -/
lemma intExists_typeAt_eq_of_card_lt (φ : Proposition Atom) (b : IBranch Atom)
    (hb : ∀ sf ∈ b, sf.formula ∈ intSubfmls φ)
    (hcard : 2 ^ (intSignedUniverse φ).card < (Branch.labels b).toFinset.card) :
    ∃ l₁ ∈ Branch.labels b, ∃ l₂ ∈ Branch.labels b, l₁ ≠ l₂ ∧
      (Branch.typeAt b l₁).toFinset = (Branch.typeAt b l₂).toFinset :=
  exists_typeAt_eq_of_card_lt b (intSignedUniverse φ)
    (fun sf hsf => mem_intSignedUniverse.mpr (hb sf hsf)) hcard

/- `strictChain_le_card` is already fully generic in the finset element type, so it
applies at the propositional instantiation with no wrapper: a chain of positive-type
finsets growing strictly at each of `k` steps and ending inside a subformula universe
`U` has at most `U.card` steps. Recorded as an `example` to keep the build checking
direct applicability without adding a redundant declaration. -/
example {k : Nat} (f : Nat → Finset (Proposition Atom)) (U : Finset (Proposition Atom))
    (hchain : ∀ i, i < k → f i ⊂ f (i + 1)) (hU : f k ⊆ U) : k ≤ U.card :=
  strictChain_le_card f U hchain hU

/-! ## Post-Blocking World Bound

`WBound` is the post-blocking world bound directed by the divergence-witness record
(`Expansion.lean`): finiteness of the created-world tree comes from the *blocking
combinatorics* — the ψ-conditioned ancestor check `intFImpReuseWitnessAnc?` — never
from `intUniverse`'s linear world range (refuted; see the warning on `intUniverse`).

The chain bound counts `(posTypeAt, ψ)` pairs: along an edge chain of created worlds,
each created world carries its positive type (a subset of the subformula universe of
`φ`, the positive projection of the counting layer above) and its creation obligation
ψ (a subformula), so an over-long chain repeats a pair, and the repeat contradicts
unblockedness of the later creation site — the earlier created world is an ancestor
with containment-equal forced set, an explicit `F(ψ)` entry, and ψ not yet forced,
i.e. exactly a reuse witness the ancestor check would have returned. See
[GargGenoveseNegri2012], §III, for the count of distinct forced sets and the chain
argument, and [Fitting1983], Ch. 4, for the systematic-tableau construction. -/

omit [Hashable Atom] in
/-- Per-chain depth bound for created-world chains: the number of distinct
`(positive type, creation obligation)` pairs available over the subformula universe
of `φ` — `2 ^ |Sub φ|` positive types (subsets of the universe, the `posTypeAt`
projection over `U : Finset F` of the counting layer) times `|Sub φ|` obligations.
Derived from the blocking combinatorics only; `intUniverse`'s linear range plays no
role. -/
def intChainBound (φ : Proposition Atom) : Nat :=
  2 ^ (intSubfmls φ).toFinset.card * (intSubfmls φ).toFinset.card

omit [Hashable Atom] in
/-- Total world bound for the post-blocking tableau: the created-world tree has
branching factor at most the subformula count (one child per `F(· → ·)` subformula
fired at a world) and chain depth at most `intChainBound φ`, giving at most
`(|Sub φ| + 1) ^ (intChainBound φ + 1)` worlds. Exponential-in-exponential is
acceptable — this is a proof-side bound, not an evaluation step count. -/
def WBound (φ : Proposition Atom) : Nat :=
  ((intSubfmls φ).toFinset.card + 1) ^ (intChainBound φ + 1)

omit [Hashable Atom] in
/-- The world bound is positive: the root world always fits. Discharges the `hNW`
obligation at singleton call sites. -/
lemma WBound_pos (φ : Proposition Atom) : 1 ≤ WBound φ :=
  Nat.one_le_pow _ _ (Nat.succ_pos _)

omit [Hashable Atom] in
/-- Materializable per-branch fuel budget for the per-branch-fuel expansion engine
(`intExpandBranches`): one unit above twice the size bound of the enlarged cell
universe, `4 * (2 * φ.complexity + 1) * (WBound φ + 1) + 1`.

**This MUST stay a closed arithmetic form.** Never define it as
`2 * (intUniverseExt φ).length + 1` (nor via any other runtime traversal or membership
check against the `intUniverseExt` list): the LIST has `Θ(WBound φ)` elements — around
`10 ^ 13000000` for the conformance corpus's divergence-witness row — and can never be
built. Only the NUMERAL is feasible to materialize. The arithmetic form dominates
`2 * (intUniverseExt φ).length + 1` via `intUniverseExt_length_le`, which is all the
init bound `intWork_init_lt_intFuelExt` needs.

**Feasibility envelope**: for a formula with `s` distinct subformulas the fuel numeral
has on the order of `2 ^ s * s * log₁₀ (s + 1)` digits — comfortably materializable for
the conformance corpus (`s ≲ 22`; the largest corpus row's ~13.0-million-digit numeral
materializes in ~0.6 s), but around 0.5 GB of digits by `s ≈ 25`. This is an
evaluation-side envelope only; the proof side manipulates the closed form
symbolically. -/
def intFuelExt (φ : Proposition Atom) : Nat :=
  4 * (2 * φ.complexity + 1) * (WBound φ + 1) + 1

omit [DecidableEq Atom] [Hashable Atom] in
/-- The positive projection of a branch stays inside the subformula universe:
`posFormulasAt` only reads formulas off branch entries. -/
lemma mem_intSubfmls_of_mem_posFormulasAt {φ0 χ : Proposition Atom} {b : IBranch Atom}
    {w : Nat} (hsub : ∀ sf ∈ b, sf.formula ∈ intSubfmls φ0)
    (hχ : χ ∈ posFormulasAt b w) : χ ∈ intSubfmls φ0 := by
  simp only [posFormulasAt, List.mem_filterMap, Option.ite_none_right_eq_some,
    Option.some.injEq] at hχ
  obtain ⟨sf, hmem, -, hform⟩ := hχ
  exact hform ▸ hsub sf hmem

omit [Hashable Atom] in
/-- **Ancestor-chain bound**: along any edge chain `ws 0 → ws 1 → … → ws k` of worlds
created by unblocked `intFImpRule` firings on a branch `b`, the chain length `k` is at
most `intChainBound φ0`.

The chain data is carried by the hypotheses, all stated against the final branch `b`:
- `hobl`/`hnotpos`: each created world `ws (i + 1)` carries its creation obligation
  `F(ψs i)` as an explicit entry, and (openness) `ψs i` is not positively forced there;
- `hacc`/`hle`: the chain is monotone in accessibility and world labels
  (`isAccessible` is reflexive, so both include the degenerate index case);
- `hunb`: **unblockedness** — no world satisfies the five reuse conjuncts of
  `intFImpReuseWitnessAnc?` (`Expansion.lean`) at any creation site, transcribed
  against `b` (quantifying over all `x : Nat` is no stronger than over branch labels:
  the fifth conjunct forces `x` to be a label of `b`; and the third conjunct reads the
  created world's final positive content in place of its creation-time `Sfor`).
  Suppliers of this hypothesis own the transfer from the runtime check — evaluated on
  the branch state at firing time — to the final branch; that transfer belongs to the
  invariant-threading development, not to this lemma.

Proof: pigeonhole on `(posTypeAt, ψ)` pairs. More than `2 ^ |Sub φ0| * |Sub φ0|`
chain steps repeat a pair `(positive type of the created world, obligation)`; at the
later creation site the earlier created world is then a reuse witness satisfying all
five conjuncts, contradicting `hunb`. See [GargGenoveseNegri2012], §III.

**DP-2 status (report §4.1, plan Phase 9)**: this lemma is CORRECT and stays as originally
proved, but it is NOT the route consumed by the DP-2 development. Report §4.1 refutes the
runtime-check-to-final-branch transfer `hunb` would need (evaluated at firing time, then
transported to the final branch `b`): conjunct 3 of the reuse check moves the wrong way under
branch growth (positive content at a world only grows over time, so the implication that would
transport `hunb` from the firing-time branch to the final branch runs backwards), and no
monotonicity or additional final-branch invariant recovers it. The working route instead
consumes the runtime `none` result at MINT TIME, while the firing-time branch is still current
(`intFImp_mint_residue`, feeding `IWorldHist`'s (H5) clause), and re-derives an equivalent
depth bound directly from the STRUCTURAL invariant's witness functions rather than from `b`'s
final state (`intWorldHist_chain_le`, immediately below `IWorldHist_mint`). This lemma is
therefore preserved, unconsumed by that route, and untouched by the Phase 9 pigeonhole sibling:
its proof body is byte-identical to its pre-Phase-9 state (docstring-only change). -/
lemma intCreatedChain_le (φ0 : Proposition Atom) (b : IBranch Atom) (edges : IEdges)
    {k : Nat} (ws : Nat → Nat) (ψs : Nat → Proposition Atom)
    (hsub : ∀ sf ∈ b, sf.formula ∈ intSubfmls φ0)
    (hψ : ∀ i, i < k → ψs i ∈ intSubfmls φ0)
    (hobl : ∀ i, i < k → (⟨.neg, ψs i, ws (i + 1)⟩ : ISF Atom) ∈ b)
    (hnotpos : ∀ i, i < k → ψs i ∉ posFormulasAt b (ws (i + 1)))
    (hacc : ∀ i j, i ≤ j → j ≤ k → isAccessible edges (ws i) (ws j) = true)
    (hle : ∀ i j, i ≤ j → j ≤ k → ws i ≤ ws j)
    (hunb : ∀ j, j < k → ∀ x : Nat,
      ¬(isAccessible edges x (ws j) = true ∧ x ≤ ws j ∧
        (∀ χ ∈ posFormulasAt b (ws (j + 1)), χ ∈ posFormulasAt b x) ∧
        ψs j ∉ posFormulasAt b x ∧
        (⟨.neg, ψs j, x⟩ : ISF Atom) ∈ b)) :
    k ≤ intChainBound φ0 := by
  by_contra hk
  rw [Nat.not_le] at hk
  -- Pigeonhole over `(positive type of created world, creation obligation)` pairs.
  have hmaps : ∀ i ∈ Finset.range k,
      (((posFormulasAt b (ws (i + 1))).toFinset, ψs i) :
          Finset (Proposition Atom) × Proposition Atom) ∈
        (intSubfmls φ0).toFinset.powerset ×ˢ (intSubfmls φ0).toFinset := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Finset.mem_product, Finset.mem_powerset]
    refine ⟨fun χ hχ => ?_, List.mem_toFinset.mpr (hψ i hi)⟩
    rw [List.mem_toFinset] at hχ ⊢
    exact mem_intSubfmls_of_mem_posFormulasAt hsub hχ
  have hcard : ((intSubfmls φ0).toFinset.powerset ×ˢ (intSubfmls φ0).toFinset).card <
      (Finset.range k).card := by
    rw [Finset.card_product, Finset.card_powerset, Finset.card_range]
    simpa [intChainBound] using hk
  obtain ⟨i, hi, j, hj, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rw [Finset.mem_range] at hi hj
  rw [Prod.mk.injEq] at heq
  obtain ⟨heqT, heqψ⟩ := heq
  -- A repeated pair at indices `i < j` makes `ws (i + 1)` a reuse witness at the
  -- creation site of `ws (j + 1)`, contradicting `hunb`.
  have key : ∀ i j, i < j → j < k →
      (posFormulasAt b (ws (i + 1))).toFinset =
        (posFormulasAt b (ws (j + 1))).toFinset →
      ψs i = ψs j → False := by
    intro i j hij hjk hT hψeq
    refine hunb j hjk (ws (i + 1)) ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact hacc (i + 1) j hij (Nat.le_of_lt hjk)
    · exact hle (i + 1) j hij (Nat.le_of_lt hjk)
    · intro χ hχ
      have hmem : χ ∈ (posFormulasAt b (ws (j + 1))).toFinset :=
        List.mem_toFinset.mpr hχ
      rw [← hT] at hmem
      exact List.mem_toFinset.mp hmem
    · rw [← hψeq]
      exact hnotpos i (Nat.lt_trans hij hjk)
    · rw [← hψeq]
      exact hobl i (Nat.lt_trans hij hjk)
  rcases Nat.lt_or_ge i j with h | h
  · exact key i j h hj heqT heqψ
  · exact key j i (Nat.lt_of_le_of_ne h fun e => hne e.symm) hi heqT.symm heqψ.symm

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
  rcases hx with (hxb | hxnew) | hxcopy
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
          exact intTImpRule_outputs_subset hb hsfmem x hxmem
  · -- Generalized copy channel: `x = ⟨.pos, sf'.formula, w'⟩` for some `sf' ∈ b`; the
    -- formula is literally `sf'.formula` (no subformula step needed) and `w'` is an
    -- existing branch label.
    simp only [List.mem_flatten, List.mem_filterMap] at hxcopy
    obtain ⟨cs, ⟨sf', hsf'mem, hmatch⟩, hxmem⟩ := hxcopy
    cases hsign : sf'.sign with
    | neg => simp only [hsign] at hmatch; exact absurd hmatch (by simp)
    | pos =>
      simp only [hsign] at hmatch
      split at hmatch
      · simp at hmatch
      · simp only [Option.some.injEq] at hmatch
        rw [← hmatch] at hxmem
        simp only [List.mem_filterMap, List.mem_filter, List.mem_eraseDups,
          List.mem_map] at hxmem
        obtain ⟨w', ⟨⟨y, hymem, hyeq⟩, -⟩, hxeq⟩ := hxmem
        have hwle : w' ≤ φ0.complexity + 1 := by
          subst hyeq; exact intUniverse_mem_label (hb y hymem)
        have hformsub : sf'.formula ∈ intSubfmls φ0 := intUniverse_mem_formula (hb sf' hsf'mem)
        split at hxeq
        · simp at hxeq
        · simp only [Option.some.injEq] at hxeq
          exact hxeq ▸ mem_intUniverse_of hwle hformsub

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

/-! ## Enlarged Universe (post-blocking)

`intUniverseExt` is the measure domain the post-blocking fuel-sufficiency development
runs over: the same `(sign, subformula, world)` cell structure as `intUniverse`, with
the world range enlarged from the refuted linear range `0 .. φ.complexity + 1` to the
post-blocking world bound `0 .. WBound φ` (derived from the ancestor-blocking
combinatorics via `intChainBound` — see *Post-Blocking World Bound* above — never from
`intUniverse`'s linear range, which is refuted as a branch invariant). `intExpMeasure`
is already parametric in the universe list `U`, so no separate `Ext` measure definition
is needed: the enlarged measure is the partial application
`intExpMeasure (intUniverseExt φ)`. Only the universe, its length bound, its membership
lemmas, and the containment family below are new; they mirror the `intUniverse` family
above line-for-line, except that the world-creating arm of
`intApplyRuleFull_outputs_subset_ext` consumes `hnw : nextWorld ≤ WBound φ0` as a
threaded premise. Unlike the refuted linear `hnw` (see the warning on
`intApplyRuleFull_outputs_subset`), this premise is the one the `hNW` threading
invariant of the fuel-sufficiency development is designed to discharge; that discharge
is owned by the invariant-threading side, not by this section. -/

omit [Hashable Atom] in
/-- The enlarged `(sign, subformula, world)`-cell universe for `φ`: both signs, every
subformula of `φ`, at every world label `0 .. WBound φ`. Same cell structure as
`intUniverse`, with the refuted linear world range replaced by the post-blocking world
bound `WBound φ`. -/
def intUniverseExt (φ : Proposition Atom) : List (ISF Atom) :=
  (List.range (WBound φ + 1)).flatMap (fun w =>
    (intSubfmls φ).flatMap (fun ψ => [(⟨.pos, ψ, w⟩ : ISF Atom), ⟨.neg, ψ, w⟩]))

omit [Hashable Atom] in
/-- The enlarged universe has length at most
`2 * (2 * φ.complexity + 1) * (WBound φ + 1)` (mirrors `intUniverse_length_le`, with
the linear world-range factor swapped for the enlarged range) -- the bound the
`intFuel` resize is sized against. -/
lemma intUniverseExt_length_le (φ : Proposition Atom) :
    (intUniverseExt φ).length ≤ 2 * (2 * φ.complexity + 1) * (WBound φ + 1) := by
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
  unfold intUniverseExt
  rw [List.length_flatMap]
  have houter : (List.map (fun w =>
      ((intSubfmls φ).flatMap
        (fun ψ => [(⟨.pos, ψ, w⟩ : ISF Atom), ⟨.neg, ψ, w⟩])).length)
      (List.range (WBound φ + 1))).sum
      ≤ (List.range (WBound φ + 1)).length * (2 * (2 * φ.complexity + 1)) :=
    sum_map_le_length_mul (List.range (WBound φ + 1)) _
      (2 * (2 * φ.complexity + 1)) (fun w _ => hinner w)
  rw [List.length_range] at houter
  calc (List.map (fun w =>
        ((intSubfmls φ).flatMap
          (fun ψ => [(⟨.pos, ψ, w⟩ : ISF Atom), ⟨.neg, ψ, w⟩])).length)
        (List.range (WBound φ + 1))).sum
      ≤ (WBound φ + 1) * (2 * (2 * φ.complexity + 1)) := houter
    _ = 2 * (2 * φ.complexity + 1) * (WBound φ + 1) := by ring

omit [Hashable Atom] in
/-- Constructor direction for `intUniverseExt` membership: a signed formula with any
sign, a subformula of `φ0`, at a world label within the post-blocking bound, is in the
enlarged universe (mirrors `mem_intUniverse_of`). -/
private lemma mem_intUniverseExt_of {φ0 : Proposition Atom} {s : Sign}
    {φ : Proposition Atom} {w : Nat} (hw : w ≤ WBound φ0) (hφ : φ ∈ intSubfmls φ0) :
    (⟨s, φ, w⟩ : ISF Atom) ∈ intUniverseExt φ0 := by
  have hlt : w < WBound φ0 + 1 := by omega
  simp only [intUniverseExt, List.mem_flatMap, List.mem_range]
  exact ⟨w, hlt, φ, hφ, by cases s <;> simp⟩

omit [Hashable Atom] in
/-- Generic form of `mem_intUniverseExt_of`, stated for an arbitrary signed formula `z`
(mirrors `mem_intUniverse_of'`). -/
private lemma mem_intUniverseExt_of' {φ0 : Proposition Atom} {z : ISF Atom}
    (hw : z.label ≤ WBound φ0) (hφ : z.formula ∈ intSubfmls φ0) :
    z ∈ intUniverseExt φ0 := by
  obtain ⟨s, φ, w⟩ := z
  exact mem_intUniverseExt_of hw hφ

omit [Hashable Atom] in
/-- Extraction: the formula-component of any `intUniverseExt φ0` member is a subformula
of `φ0` (mirrors `intUniverse_mem_formula`). -/
private lemma intUniverseExt_mem_formula {φ0 : Proposition Atom} {x : ISF Atom}
    (hx : x ∈ intUniverseExt φ0) : x.formula ∈ intSubfmls φ0 := by
  simp only [intUniverseExt, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  obtain ⟨w, -, ψ, hψ, heq | heq⟩ := hx <;> (subst heq; exact hψ)

omit [Hashable Atom] in
/-- Extraction: the label-component of any `intUniverseExt φ0` member is bounded by
`WBound φ0` (mirrors `intUniverse_mem_label`). -/
private lemma intUniverseExt_mem_label {φ0 : Proposition Atom} {x : ISF Atom}
    (hx : x ∈ intUniverseExt φ0) : x.label ≤ WBound φ0 := by
  simp only [intUniverseExt, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  obtain ⟨w, hw, ψ, -, heq | heq⟩ := hx <;>
    (subst heq; change w ≤ WBound φ0; omega)

omit [Hashable Atom] in
/-- Containment for the persistent `T(φ → ψ)` rule over the enlarged universe (mirrors
`intTImpRule_outputs_subset`): every emitted formula stays inside `intUniverseExt φ0`,
given the branch invariant `hb` and the source membership `hsf`. As in the original,
the emitted label `w'` is always an EXISTING label already appearing on `b`, so no
world-bound hypothesis is needed here. -/
private lemma intTImpRule_outputs_subset_ext {φ0 : Proposition Atom} {b : IBranch Atom}
    {edges : IEdges} {φ ψ : Proposition Atom} {w : Nat}
    (hb : ∀ x ∈ b, x ∈ intUniverseExt φ0)
    (hsf : (⟨.pos, .imp φ ψ, w⟩ : ISF Atom) ∈ b) :
    ∀ x ∈ intTImpRule φ ψ w edges b, x ∈ intUniverseExt φ0 := by
  have hψsub : ψ ∈ intSubfmls φ0 := by
    have himp : (Proposition.imp φ ψ) ∈ intSubfmls φ0 :=
      intUniverseExt_mem_formula (hb _ hsf)
    have hψmem : ψ ∈ intSubfmls (Proposition.imp φ ψ) := by simp [intSubfmls]
    exact intSubfmls_trans hψmem himp
  intro x hx
  simp only [intTImpRule, List.mem_filterMap, List.mem_filter, List.mem_eraseDups,
    List.mem_map] at hx
  obtain ⟨w', ⟨⟨y, hymem, hyeq⟩, -⟩, hxeq⟩ := hx
  have hwle : w' ≤ WBound φ0 := by
    subst hyeq; exact intUniverseExt_mem_label (hb y hymem)
  split at hxeq
  · split at hxeq
    · simp at hxeq
    · simp only [Option.some.injEq] at hxeq
      exact hxeq ▸ mem_intUniverseExt_of hwle hψsub
  · simp at hxeq

omit [Hashable Atom] in
/-- Containment for one full round of `applyAllTImpRules` over the enlarged universe
(mirrors `applyAllTImpRules_subset`): the new formulas it appends stay inside
`intUniverseExt φ0`, given the branch invariant `hb`. -/
private lemma applyAllTImpRules_subset_ext {φ0 : Proposition Atom} {b : IBranch Atom}
    {edges : IEdges} (hb : ∀ x ∈ b, x ∈ intUniverseExt φ0) :
    ∀ x ∈ applyAllTImpRules b edges, x ∈ intUniverseExt φ0 := by
  intro x hx
  simp only [applyAllTImpRules, List.mem_append] at hx
  rcases hx with (hxb | hxnew) | hxcopy
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
          exact intTImpRule_outputs_subset_ext hb hsfmem x hxmem
  · -- Generalized copy channel, mirrors `applyAllTImpRules_subset`'s copy case over the
    -- enlarged universe.
    simp only [List.mem_flatten, List.mem_filterMap] at hxcopy
    obtain ⟨cs, ⟨sf', hsf'mem, hmatch⟩, hxmem⟩ := hxcopy
    cases hsign : sf'.sign with
    | neg => simp only [hsign] at hmatch; exact absurd hmatch (by simp)
    | pos =>
      simp only [hsign] at hmatch
      split at hmatch
      · simp at hmatch
      · simp only [Option.some.injEq] at hmatch
        rw [← hmatch] at hxmem
        simp only [List.mem_filterMap, List.mem_filter, List.mem_eraseDups,
          List.mem_map] at hxmem
        obtain ⟨w', ⟨⟨y, hymem, hyeq⟩, -⟩, hxeq⟩ := hxmem
        have hwle : w' ≤ WBound φ0 := by
          subst hyeq; exact intUniverseExt_mem_label (hb y hymem)
        have hformsub : sf'.formula ∈ intSubfmls φ0 :=
          intUniverseExt_mem_formula (hb sf' hsf'mem)
        split at hxeq
        · simp at hxeq
        · simp only [Option.some.injEq] at hxeq
          exact hxeq ▸ mem_intUniverseExt_of hwle hformsub

omit [Hashable Atom] in
/-- Containment is a loop invariant of `applyPersistenceFixpoint` over the enlarged
universe (mirrors `applyPersistenceFixpoint_subset`): iterating `applyAllTImpRules` to
fixpoint never breaches `intUniverseExt φ0`, given the branch invariant at entry. -/
private lemma applyPersistenceFixpoint_subset_ext {φ0 : Proposition Atom}
    (b : IBranch Atom) (edges : IEdges) (fuel : Nat)
    (hb : ∀ x ∈ b, x ∈ intUniverseExt φ0) :
    ∀ x ∈ applyPersistenceFixpoint b edges fuel, x ∈ intUniverseExt φ0 := by
  induction fuel generalizing b with
  | zero => simpa [applyPersistenceFixpoint] using hb
  | succ fuel' ih =>
    simp only [applyPersistenceFixpoint]
    split
    · exact hb
    · exact ih _ (applyAllTImpRules_subset_ext hb)

omit [Hashable Atom] in
/-- **Step-level containment dispatch over the enlarged universe** (mirrors
`intApplyRuleFull_outputs_subset`): every signed formula emitted by
`intApplyRuleFull sf nextWorld b` stays inside `intUniverseExt φ0`, given the branch
invariant `hb`, the source membership `hsf`, and the post-blocking world-bound
hypothesis `hnw : nextWorld ≤ WBound φ0` (consumed only by the world-creating
`F(φ → ψ)` case, to show the freshly minted label stays inside the enlarged range).

This is the load-bearing replacement of the original's refuted linear `hnw`: unlike
`nextWorld ≤ φ0.complexity + 1` (false at actual expansion call sites, see the warning
on `intApplyRuleFull_outputs_subset`), `nextWorld ≤ WBound φ0` is the bound the
blocking combinatorics supports. Here it is threaded as a premise only; its discharge
at the `intExpandBranches` call sites is owned by the `hNW` threading invariant of the
fuel-sufficiency development. -/
lemma intApplyRuleFull_outputs_subset_ext {φ0 : Proposition Atom} {sf : ISF Atom}
    {nextWorld : Nat} {b : IBranch Atom}
    (hb : ∀ x ∈ b, x ∈ intUniverseExt φ0) (hsf : sf ∈ b)
    (hnw : nextWorld ≤ WBound φ0) :
    (match intApplyRuleFull sf nextWorld b with
      | .linearResult formulas _ _ => ∀ x ∈ formulas, x ∈ intUniverseExt φ0
      | .branchingResult branches _ => ∀ x ∈ branches.flatten, x ∈ intUniverseExt φ0
      | .notApplicable => True) := by
  have hsfU : sf ∈ intUniverseExt φ0 := hb sf hsf
  obtain ⟨s, ff, l⟩ := sf
  unfold intApplyRuleFull
  cases s with
  | pos =>
    cases ff with
    | atom p => trivial
    | bot => trivial
    | imp φ ψ =>
      have hsub : (Proposition.imp φ ψ) ∈ intSubfmls φ0 := intUniverseExt_mem_formula hsfU
      have hlab : l ≤ WBound φ0 := intUniverseExt_mem_label hsfU
      intro x hx
      simp only [List.mem_flatten, List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨t, (rfl | rfl), hxt⟩ := hx <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxt <;>
        (subst hxt
         exact mem_intUniverseExt_of hlab (intSubfmls_trans (by simp [intSubfmls]) hsub))
    | and φ ψ =>
      have hsub : (Proposition.and φ ψ) ∈ intSubfmls φ0 := intUniverseExt_mem_formula hsfU
      have hlab : l ≤ WBound φ0 := intUniverseExt_mem_label hsfU
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact mem_intUniverseExt_of hlab (intSubfmls_trans (by simp [intSubfmls]) hsub)
      · exact mem_intUniverseExt_of hlab (intSubfmls_trans (by simp [intSubfmls]) hsub)
    | or φ ψ =>
      have hsub : (Proposition.or φ ψ) ∈ intSubfmls φ0 := intUniverseExt_mem_formula hsfU
      have hlab : l ≤ WBound φ0 := intUniverseExt_mem_label hsfU
      intro x hx
      simp only [List.mem_flatten, List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨t, (rfl | rfl), hxt⟩ := hx <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxt <;>
        (subst hxt
         exact mem_intUniverseExt_of hlab (intSubfmls_trans (by simp [intSubfmls]) hsub))
  | neg =>
    cases ff with
    | atom p => trivial
    | bot => trivial
    | and φ ψ =>
      have hsub : (Proposition.and φ ψ) ∈ intSubfmls φ0 := intUniverseExt_mem_formula hsfU
      have hlab : l ≤ WBound φ0 := intUniverseExt_mem_label hsfU
      intro x hx
      simp only [List.mem_flatten, List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨t, (rfl | rfl), hxt⟩ := hx <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxt <;>
        (subst hxt
         exact mem_intUniverseExt_of hlab (intSubfmls_trans (by simp [intSubfmls]) hsub))
    | or φ ψ =>
      have hsub : (Proposition.or φ ψ) ∈ intSubfmls φ0 := intUniverseExt_mem_formula hsfU
      have hlab : l ≤ WBound φ0 := intUniverseExt_mem_label hsfU
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact mem_intUniverseExt_of hlab (intSubfmls_trans (by simp [intSubfmls]) hsub)
      · exact mem_intUniverseExt_of hlab (intSubfmls_trans (by simp [intSubfmls]) hsub)
    | imp φ ψ =>
      have himp : (Proposition.imp φ ψ) ∈ intSubfmls φ0 := intUniverseExt_mem_formula hsfU
      simp only [intFImpRule, propagatePersistence, posFormulasAt]
      intro x hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_map, List.mem_filterMap] at hx
      rcases hx with (rfl | rfl) | ⟨ψ', ⟨sf', hsf'mem, hsf'eq⟩, hxeq⟩
      · exact mem_intUniverseExt_of hnw (intSubfmls_trans (by simp [intSubfmls]) himp)
      · exact mem_intUniverseExt_of hnw (intSubfmls_trans (by simp [intSubfmls]) himp)
      · split at hsf'eq
        · simp only [Option.some.injEq] at hsf'eq
          have hsf'U : sf' ∈ intUniverseExt φ0 := hb sf' hsf'mem
          exact hxeq ▸
            mem_intUniverseExt_of hnw (hsf'eq ▸ intUniverseExt_mem_formula hsf'U)
        · simp at hsf'eq

/-! ## `hUniv`/`hNW` Threading Invariants (Phase 5, division point DP-2)

Packages the two additional R1 hypotheses (Phase 6's per-branch fuel restatement of
`intExpandBranches_openBranch_sat`) as parallel-list invariants threaded ALONGSIDE
`IAllConsistent`/`IAllAccessConsistent` (same "companion, not merged" shape as that
pair, `IAllAccessConsistent`'s docstring above): `IAllUniv` (every branch stays inside
the enlarged universe `intUniverseExt φ0`) and `IAllNW` (every next-world counter stays
within the post-blocking bound `WBound φ0`). Supplies the per-arm STEP-preservation
lemmas Phase 6's functional induction over `intExpandBranches.go` consumes at each
case, mirroring `intStepBranch_linear_preserves`/`intStepBranch_branch_preserves`'s
existing shape.

Three of the four recursion arms (ALPHA, BETA, and the ancestor-reuse world-creating
arm) preserve both invariants by direct, complete proofs below. The fourth (the
fresh-mint world-creating arm, when `intFImpReuseWitnessAnc?` finds no reusable
ancestor) preserves `hUniv` unconditionally (`intApplyRuleFull_outputs_subset_ext`
already supplies this, GIVEN `hNW` holds at the point of creation) but carries the
DP-2 strategic sorry for `hNW`'s OWN forward preservation (`nw + 1 ≤ WBound φ0`): the
"labels minted so far ≤ tree size ≤ WBound φ0" creation-count invariant tied to
`intCreatedChain_le`'s pigeonhole bound (Phase 2), including the runtime-check-to-
final-branch transfer that lemma's docstring flags as owned by this very development.
Per plan v14 Phase 5's STOPPING CONDITION, this lemma's proof is deferred; the
statement is NOT weakened to dodge the gap -- the sorry comment records exactly which
premise (`nw < WBound φ0`, strict) is missing from the bare `hnwB : nw ≤ WBound φ0`
threaded by `IAllNW`. Follow-up: DP-2, see the plan's Planned Strategic Sorries
table. -/

/-- Branch-universe containment threaded across the pending/done worklists: every
formula on every branch stays inside `intUniverseExt φ0`. Unlike `IAllConsistent`,
this does not need simultaneous multi-list recursion (it constrains a single list),
so it is a plain `∀`, not a custom match-recursive `def`. -/
private def IAllUniv (φ0 : Proposition Atom) (bs : List (IBranch Atom)) : Prop :=
  ∀ b ∈ bs, ∀ x ∈ b, x ∈ intUniverseExt φ0

omit [Hashable Atom] in
/-- `IAllUniv` combines under list append (mirrors `IAllConsistent_append`; used to
extend `done` with the just-processed branch, and to combine `done` with the still-
`pending` tail). -/
private lemma IAllUniv_append {φ0 : Proposition Atom} {bs1 bs2 : List (IBranch Atom)}
    (h1 : IAllUniv φ0 bs1) (h2 : IAllUniv φ0 bs2) :
    IAllUniv φ0 (bs1 ++ bs2) := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact h1 b hb
  · exact h2 b hb

omit [Hashable Atom] in
/-- `IAllUniv` holds along a (possibly non-uniform) `map`: if every branch obtained by
applying `f` to a member of `branches'` satisfies `hUniv`, then `IAllUniv` holds of the
mapped list (mirrors `IAllConsistent_map`; covers the BETA arm's
`branches'.map (Branch.extendMany bPers ·)`). -/
private lemma IAllUniv_map {φ0 : Proposition Atom} {branches' : List (IBranch Atom)}
    (f : IBranch Atom → IBranch Atom)
    (h : ∀ br ∈ branches', ∀ x ∈ f br, x ∈ intUniverseExt φ0) :
    IAllUniv φ0 (branches'.map f) := by
  intro b hb
  simp only [List.mem_map] at hb
  obtain ⟨br, hbr, rfl⟩ := hb
  exact h br hbr

/-- Next-world-counter boundedness threaded across the pending/done worklists: every
counter stays within the post-blocking bound `WBound φ0`. -/
private def IAllNW (φ0 : Proposition Atom) (nws : List Nat) : Prop :=
  ∀ nw ∈ nws, nw ≤ WBound φ0

omit [Hashable Atom] in
/-- `IAllNW` combines under list append (mirrors `IAllConsistent_append`). -/
private lemma IAllNW_append {φ0 : Proposition Atom} {nws1 nws2 : List Nat}
    (h1 : IAllNW φ0 nws1) (h2 : IAllNW φ0 nws2) :
    IAllNW φ0 (nws1 ++ nws2) := by
  intro nw hnw
  rcases List.mem_append.mp hnw with hnw | hnw
  · exact h1 nw hnw
  · exact h2 nw hnw

omit [Hashable Atom] in
/-- `IAllNW` holds along a constant-valued `map` (mirrors `IAllConsistent_map`; covers
the BETA arm's `branches'.map (fun _ => nw')`, where every child inherits the SAME
counter). -/
private lemma IAllNW_map_const {φ0 : Proposition Atom} {α : Type*} {l : List α} {c : Nat}
    (h : c ≤ WBound φ0) :
    IAllNW φ0 (l.map (fun _ => c)) := by
  intro nw hnw
  simp only [List.mem_map] at hnw
  obtain ⟨_, -, rfl⟩ := hnw
  exact h

omit [Hashable Atom] in
/-- Branch-universe containment (`hUniv`) is preserved by a `linearResult` step of
`intStepBranch`, GIVEN the current next-world counter is within the post-blocking bound
(`hnwB`): covers both the ALPHA arm (`newEdge = none`) and the world-creating arm
(`newEdge = some _`, whether `go` later decides to reuse an ancestor or mint fresh --
that split happens downstream of `intStepBranch`, so this lemma is agnostic to it).
Direct corollary of `intApplyRuleFull_outputs_subset_ext` unfolded against
`intStepBranch_some_exists` and `Branch.extendMany`'s prepend shape. Companion of
`intStepBranch_linear_preserves` (which threads `IExpandedConsistent`/`ILabelBound`/
`IExpandedAccessConsistent`), threaded alongside it for `hUniv`. -/
private lemma intStepBranch_linear_preserves_univ {φ0 : Proposition Atom}
    {b : IBranch Atom} {e : List (ISF Atom)} {nw : Nat}
    {newForms : List (ISF Atom)} {nw' : Nat} {newEdge : Option (Nat × Nat)}
    {newExp : List (ISF Atom)}
    (hUniv : ∀ x ∈ b, x ∈ intUniverseExt φ0) (hnwB : nw ≤ WBound φ0)
    (hshape : IStepShape b e nw (.linearResult newForms nw' newEdge) newExp) :
    ∀ x ∈ Branch.extendMany b newForms, x ∈ intUniverseExt φ0 := by
  obtain ⟨sf, hsfb, hint, -⟩ := intStepBranch_some_exists hshape
  have houts := intApplyRuleFull_outputs_subset_ext hUniv hsfb hnwB
  simp only [hint] at houts
  intro x hx
  simp only [Branch.extendMany, List.mem_append] at hx
  rcases hx with hx | hx
  · exact houts x hx
  · exact hUniv x hx

omit [Hashable Atom] in
/-- Branch-universe containment (`hUniv`) is preserved by a `branchingResult` step of
`intStepBranch` on every sub-branch, GIVEN the current next-world counter is within the
post-blocking bound (`hnwB`). Covers the BETA arm. Companion of
`intStepBranch_branch_preserves`, threaded alongside it for `hUniv`. -/
private lemma intStepBranch_branch_preserves_univ {φ0 : Proposition Atom}
    {b : IBranch Atom} {e : List (ISF Atom)} {nw : Nat}
    {branches' : List (List (ISF Atom))} {nw' : Nat} {newExp : List (ISF Atom)}
    (hUniv : ∀ x ∈ b, x ∈ intUniverseExt φ0) (hnwB : nw ≤ WBound φ0)
    (hshape : IStepShape b e nw (.branchingResult branches' nw') newExp) :
    ∀ br ∈ branches', ∀ x ∈ Branch.extendMany b br, x ∈ intUniverseExt φ0 := by
  obtain ⟨sf, hsfb, hint, -⟩ := intStepBranch_some_exists hshape
  have houts := intApplyRuleFull_outputs_subset_ext hUniv hsfb hnwB
  simp only [hint] at houts
  intro br hbr x hx
  simp only [Branch.extendMany, List.mem_append] at hx
  rcases hx with hx | hx
  · exact houts x (List.mem_flatten.mpr ⟨br, hbr, hx⟩)
  · exact hUniv x hx

omit [Hashable Atom] [DecidableEq Atom] in
/-- The next-world counter output by `intApplyRuleFull`'s `linearResult` case is
unchanged when no edge is created (`.pos,.and` / `.neg,.or`, the ALPHA arm), and
increments by exactly one when an edge is created (`.neg,.imp`, the world-creating
rule -- the sole source of `newEdge = some _`, per `intFImpRule`'s
`nextWorld + 1` third component). Packages both the trivial and the fresh-mint
next-world facts as a single case split, feeding both `hNW` step lemmas below. -/
private lemma intApplyRuleFull_linearResult_nextWorld {sf : ISF Atom} {nw nw' : Nat}
    {b : IBranch Atom} {newForms : List (ISF Atom)} {newEdge : Option (Nat × Nat)}
    (hint : intApplyRuleFull sf nw b = .linearResult newForms nw' newEdge) :
    (newEdge = none ∧ nw' = nw) ∨ ∃ ed, newEdge = some ed ∧ nw' = nw + 1 := by
  obtain ⟨s, ff, l⟩ := sf
  cases s with
  | pos =>
    cases ff with
    | atom p => simp [intApplyRuleFull] at hint
    | bot => simp [intApplyRuleFull] at hint
    | imp φ ψ => simp [intApplyRuleFull] at hint
    | or φ ψ => simp [intApplyRuleFull] at hint
    | and φ ψ =>
      simp only [intApplyRuleFull, IntRuleResult.linearResult.injEq] at hint
      obtain ⟨-, hnw', hed⟩ := hint
      exact Or.inl ⟨hed.symm, hnw'.symm⟩
  | neg =>
    cases ff with
    | atom p => simp [intApplyRuleFull] at hint
    | bot => simp [intApplyRuleFull] at hint
    | and φ ψ => simp [intApplyRuleFull] at hint
    | or φ ψ =>
      simp only [intApplyRuleFull, IntRuleResult.linearResult.injEq] at hint
      obtain ⟨-, hnw', hed⟩ := hint
      exact Or.inl ⟨hed.symm, hnw'.symm⟩
    | imp φ ψ =>
      simp only [intApplyRuleFull, intFImpRule, IntRuleResult.linearResult.injEq] at hint
      obtain ⟨-, hnw', hed⟩ := hint
      exact Or.inr ⟨_, hed.symm, hnw'.symm⟩

omit [Hashable Atom] [DecidableEq Atom] in
/-- Full inversion for the world-creating arm of `intApplyRuleFull`: a `linearResult` carrying
`some newE` can only come from firing `F(φ → ψ)@l` via `intFImpRule`, and then every output
component is pinned: the new forms are the two planted facts at the fresh world `nw` followed
by the persistence group propagated from `l`, the counter increments by one, and the recorded
edge is `(nw, l)` (child, parent). Strengthens `intApplyRuleFull_linearResult_nextWorld`'s
`some`-branch with the full output shapes, as the mint arm's `IWorldHist` re-establishment
needs all of them (Phase 7). -/
private lemma intApplyRuleFull_some_edge_inv {sf : ISF Atom} {nw nw' : Nat}
    {b : IBranch Atom} {newForms : List (ISF Atom)} {newE : Nat × Nat}
    (hint : intApplyRuleFull sf nw b = .linearResult newForms nw' (some newE)) :
    ∃ φ ψ l, sf = ⟨.neg, .imp φ ψ, l⟩ ∧
      newForms = [⟨.pos, φ, nw⟩, ⟨.neg, ψ, nw⟩] ++ propagatePersistence b l nw ∧
      nw' = nw + 1 ∧ newE = (nw, l) := by
  obtain ⟨s, ff, l⟩ := sf
  cases s with
  | pos =>
    cases ff with
    | atom p => simp [intApplyRuleFull] at hint
    | bot => simp [intApplyRuleFull] at hint
    | imp φ ψ => simp [intApplyRuleFull] at hint
    | or φ ψ => simp [intApplyRuleFull] at hint
    | and φ ψ => simp [intApplyRuleFull] at hint
  | neg =>
    cases ff with
    | atom p => simp [intApplyRuleFull] at hint
    | bot => simp [intApplyRuleFull] at hint
    | and φ ψ => simp [intApplyRuleFull] at hint
    | or φ ψ => simp [intApplyRuleFull] at hint
    | imp φ ψ =>
      simp only [intApplyRuleFull, intFImpRule, IntRuleResult.linearResult.injEq,
        Option.some.injEq] at hint
      obtain ⟨hnf, hnw', hed⟩ := hint
      exact ⟨φ, ψ, l, rfl, hnf.symm, hnw'.symm, hed.symm⟩

omit [Hashable Atom] [DecidableEq Atom] in
/-- The next-world counter output by `intApplyRuleFull`'s `branchingResult` case is
always unchanged (none of `.neg,.and` / `.pos,.or` / `.pos,.imp` create a world). -/
private lemma intApplyRuleFull_branchingResult_nextWorld {sf : ISF Atom} {nw nw' : Nat}
    {b : IBranch Atom} {branches' : List (List (ISF Atom))}
    (hint : intApplyRuleFull sf nw b = .branchingResult branches' nw') :
    nw' = nw := by
  obtain ⟨s, ff, l⟩ := sf
  cases s with
  | pos =>
    cases ff with
    | atom p => simp [intApplyRuleFull] at hint
    | bot => simp [intApplyRuleFull] at hint
    | and φ ψ => simp [intApplyRuleFull] at hint
    | or φ ψ =>
      simp only [intApplyRuleFull, IntRuleResult.branchingResult.injEq] at hint
      exact hint.2.symm
    | imp φ ψ =>
      simp only [intApplyRuleFull, IntRuleResult.branchingResult.injEq] at hint
      exact hint.2.symm
  | neg =>
    cases ff with
    | atom p => simp [intApplyRuleFull] at hint
    | bot => simp [intApplyRuleFull] at hint
    | imp φ ψ => simp [intApplyRuleFull] at hint
    | or φ ψ => simp [intApplyRuleFull] at hint
    | and φ ψ =>
      simp only [intApplyRuleFull, IntRuleResult.branchingResult.injEq] at hint
      exact hint.2.symm

omit [Hashable Atom] [DecidableEq Atom] in
/-- `hNW` is preserved by a `linearResult` step of `intStepBranch` when no edge is
created (the ALPHA arm): the world counter is untouched. -/
private lemma intStepBranch_linear_preserves_nw_of_none
    {b : IBranch Atom} {e : List (ISF Atom)} {nw : Nat}
    {newForms : List (ISF Atom)} {nw' : Nat} {newExp : List (ISF Atom)}
    (hshape : IStepShape b e nw (.linearResult newForms nw' none) newExp) :
    nw' = nw := by
  obtain ⟨sf, -, hint, -⟩ := intStepBranch_some_exists hshape
  rcases intApplyRuleFull_linearResult_nextWorld hint with ⟨-, heq⟩ | ⟨ed, hcon, -⟩
  · exact heq
  · exact absurd hcon (by simp)

omit [Hashable Atom] [DecidableEq Atom] in
/-- `hNW` is preserved by a `branchingResult` step of `intStepBranch` on every
sub-branch (the BETA arm): the world counter is untouched, and every child inherits
the same (unchanged) counter. -/
private lemma intStepBranch_branch_preserves_nw
    {b : IBranch Atom} {e : List (ISF Atom)} {nw : Nat}
    {branches' : List (List (ISF Atom))} {nw' : Nat} {newExp : List (ISF Atom)}
    (hshape : IStepShape b e nw (.branchingResult branches' nw') newExp) :
    nw' = nw := by
  obtain ⟨sf, -, hint, -⟩ := intStepBranch_some_exists hshape
  exact intApplyRuleFull_branchingResult_nextWorld hint

omit [Hashable Atom] in
/-- **Phase 5 (DP-2 go/no-go gate; report section 4.2, the (★) residue)**: the mint-time
snapshot-free residue. Given a mint arm's runtime reuse-check result of `none` (`hnone`), and a
candidate world `c'` that (1) is accessible to the fired implication's source world `newE.2`
under the CURRENT edges (`hacc`, to be supplied downstream by Phase 1's one-hop extension
applied along the `par`-ancestor chain), (2) carries a smaller-or-equal label (`hle`), (3) is not
itself a contradiction source (`hNC`, `IntMinScheme.no_contradiction` specialized), (4) carries
the SAME obligation `ψ` the fired implication targets (`hmem`), and (5) has some recorded
forced-set `sforC'` contained in its actual forced formulas (`hsub`, the future (H3) planting
fact), concludes the residue: `sforC'` cannot contain every member of the mint's own propagated
positive set `newForms.filterMap (pos)`. The conclusion mentions no branch, no edge list, and no
snapshot beyond the two RECORDED sets `sforC'`/`newForms`'s filtered positives and the fixed
label `c'` -- it is permanently true (given its five hypotheses) and is exactly clause (H5) of
the (subsequent) `IWorldHist` invariant, discharged in Phase 7's mint arm by supplying `hacc`
from Phase 1, `hmem`/`hsub` from (H3), and `hNC` from Phase 3's threaded hypothesis. -/
private lemma intFImp_mint_residue {bPers : IBranch Atom} {edges : IEdges}
    {newForms : List (ISF Atom)} {newE : Nat × Nat} {ψ : Proposition Atom} {c' : Nat}
    {sforC' : List (Proposition Atom)}
    (hψ : newForms.findSome? (fun sf => if sf.sign == .neg then some sf.formula else none)
        = some ψ)
    (hnone : intFImpReuseWitnessAnc? bPers edges newForms newE = none)
    (hmem : (⟨.neg, ψ, c'⟩ : ISF Atom) ∈ bPers)
    (hacc : isAccessible edges c' newE.2 = true)
    (hle : c' ≤ newE.2)
    (hNC : ∀ (χ : Proposition Atom) (w : Nat), (⟨.neg, χ, w⟩ : ISF Atom) ∈ bPers →
        χ ∉ posFormulasAt bPers w)
    (hsub : ∀ χ ∈ sforC', χ ∈ posFormulasAt bPers c') :
    ¬ (∀ χ ∈ (newForms.filterMap fun sf => if sf.sign == .pos then some sf.formula else none),
        χ ∈ sforC') := by
  intro hsubAll
  have hx : c' ∈ (bPers.map (·.label)).eraseDups := by
    simp only [List.mem_eraseDups, List.mem_map]
    exact ⟨⟨.neg, ψ, c'⟩, hmem, rfl⟩
  have hnotpos : ψ ∉ posFormulasAt bPers c' := hNC ψ c' hmem
  have hnotposB : ¬ (posFormulasAt bPers c').contains ψ = true :=
    fun hcon => hnotpos (List.contains_iff_mem.mp hcon)
  refine intFImpReuseWitnessAnc?_none_spec hψ hnone hx ⟨hacc, hle, ?_, hnotposB,
    List.any_eq_true.mpr ⟨_, hmem, by simp⟩⟩
  rw [List.all_eq_true]
  intro χ hχ
  exact List.contains_iff_mem.mpr (hsub χ (hsubAll χ hχ))

/-! ## `IWorldHist`: the Structural Creation-History Invariant (Phase 6, DP-2)

Supplies the premise `intFreshMint_preserves_nw` below is now correctly stated in terms of
(Phase 11 resolves DP-2 by restating that lemma's premise as this structural invariant, in
place of the originally-attempted, and refuted, bare numeric strengthening) -- the structural
invariant report `01_dp2-mint-invariant-transfer.md` section 3.2 identifies as the actually
threadable quantity: for every created world `1 ≤ c < nw`, four witness functions record its
parent (`par`), the obligation it was created to satisfy (`obl`), the propagated positive set
(`sfor`), and the implication that fired to create it (`fire`). Every clause below is either
fixed arithmetic/subformula data or monotone in the CURRENT branch `b` -- no branch snapshot
appears anywhere, which is exactly what makes the invariant threadable across the mint-arm
recursion (Phases 7-8).

**Deviation from report section 3.2** (recorded per the plan's Phase 6 escape hatch): the
report's draft (H1) clause is bare edge membership `(c, par c) ∈ edges`. That alone is
insufficient to discharge Phase 7's mint-arm proof of (H5): `intFImp_mint_residue` (above)
needs `hacc : isAccessible edges c' p = true` for an ARBITRARY `parAncestor`-ancestor `c'` of
the new parent `p`, and this cannot be re-derived post-hoc from a fixed `edges` snapshot by
induction on the ancestor chain -- `isAccessible_one_hop_ext` (Phase 1, `Scheme.lean:451`) is
proved ONLY in the append-specialized shape `edges ++ [(c, p)]`; the corresponding
fixed-`edges` one-hop lemma has a provable one-unit fuel deficit (Phase 1's own deviation
note). The fix, added here as clause (H1-acc), carries genuine `isAccessible`
ancestor-accessibility as invariant DATA, maintained incrementally at each mint: OLD pairs
survive `edges`'s growth via `isAccessible_append_mono`, and the newly-minted world's
accessibility from every ancestor of its parent is built by composing the parent's
(inductively already-established) accessibility with `isAccessible_one_hop_ext` -- never
re-derived from scratch. This restatement is additive to the report's draft (H1)-(H5); it does
not remove or weaken any of them.

**Two further amendments (Phase 7, discovered at the mint-arm discharge)**, both additive:
(H0) `par 0 = 0` — without root normalization, the universally-quantified (H1-acc)/(H5)
`parAncestor` chains can pass through the root into unconstrained `par` values, and the mint
arm cannot re-establish (H1-acc) for the fresh world when the fired label is `0` (see
`parAncestor_le`/`parAncestor_of_extend`, the orbit-boundedness pair this clause enables); and
(H3-exp) `⟨.neg, fire c, par c⟩ ∈ e` — the previously-phantom expanded-set parameter `e` now
carries real data: each created world's fired implication is recorded in `e`, which is exactly
the fact needed to discharge (H4) between the fresh mint and any OLD world (the mint's fired
triple is fresh w.r.t. `e` by `intStepBranch`'s duplicate check, so equality of `(parent,
fired)` records with an old world is contradictory). Both amendments hold vacuously at entry
and are monotone along every arm (`e` only grows along a lineage). -/

/-- Reflexive-transitive closure of `par`, read as ancestry: `parAncestor par x y` holds iff
`x` is obtained from `y` by iterating `par` zero or more times (`x = y`, `x = par y`,
`x = par (par y)`, …). Well-founded whenever every step in range satisfies `par c < c` (the
(H1) clause of `IWorldHist` below). -/
private def parAncestor (par : Nat → Nat) (x y : Nat) : Prop :=
  Relation.ReflTransGen (fun a b => a = par b) x y

/-- With the root normalized (`par 0 = 0`, `IWorldHist`'s (H0) clause below), the only
`parAncestor`-ancestor of the root world `0` is `0` itself: the ancestor chain from `0` can
only self-loop. Needed at the mint arm's (H1-acc) discharge when the fired label is `0`. -/
private lemma parAncestor_zero {par : Nat → Nat} (hpar0 : par 0 = 0)
    {c' : Nat} (h : parAncestor par c' 0) : c' = 0 := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hab _hchain ih =>
    subst ih
    rw [hpar0] at hab
    exact hab

/-- Orbit boundedness: under (H0)-normalization and (H1)-descent, every
`parAncestor`-ancestor of a created world `c < nw` is `≤ c` — the ancestor chain descends
through `[1, nw)` (where (H1) forces `par x < x`) and bottoms out at the self-looping root.
This is what keeps the universally-quantified (H1-acc)/(H5) chains inside the range where the
invariant carries data, and it is the reason (H0) had to be ADDED to the report's draft
(H1)-(H5): without `par 0 = 0` a chain can pass through the root into unconstrained `par`
values, making (H1-acc) unprovable at the mint. -/
private lemma parAncestor_le {par : Nat → Nat} {nw : Nat}
    (hpar0 : par 0 = 0) (hdesc : ∀ x, 1 ≤ x → x < nw → par x < x)
    {c' c : Nat} (hc : c < nw) (h : parAncestor par c' c) : c' ≤ c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Nat.le_refl c
  | head hab hchain ih =>
    rename_i _a b
    subst hab
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · rw [hpar0]
      exact Nat.zero_le c
    · have := hdesc b hb (Nat.lt_of_le_of_lt ih hc)
      omega

/-- Chain transfer at a mint: extending `par` by one point AT the fresh world `nw` does not
create new ancestor chains for any target `c < nw` — every chain under the extended function
is already a chain under the original `par`, because (by `parAncestor_le`) all chain elements
stay `≤ c < nw` and never touch the extension point. -/
private lemma parAncestor_of_extend {par : Nat → Nat} {nw l : Nat}
    (hpar0 : par 0 = 0) (hdesc : ∀ x, 1 ≤ x → x < nw → par x < x)
    {c' c : Nat} (hc : c < nw)
    (h : parAncestor (fun x => if x = nw then l else par x) c' c) :
    parAncestor par c' c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | head hab hchain ih =>
    rename_i _a b
    have hble : b ≤ c := parAncestor_le hpar0 hdesc hc ih
    have hbne : b ≠ nw := by omega
    simp only [if_neg hbne] at hab
    exact Relation.ReflTransGen.head hab ih

/-- The structural creation-history invariant threaded per-branch across the world-creation
recursion (report section 3.2, with the (H1-acc) restatement documented above). Every created
world `c` (`1 ≤ c < nw`) satisfies: (H1) its parent edge is recorded and strictly smaller;
(H1-acc) it is genuinely edge-accessible from every `parAncestor`-ancestor under the CURRENT
`edges`; (H2) the recorded obligation, firing implication, and propagated positive set all lie
in `intSubfmls φ0`; (H3) the recorded obligation and positive set are actually planted on the
CURRENT branch `b` (monotone facts, surviving every later append); (H4) a `(parent, fired
implication)` pair determines its child uniquely (sibling uniqueness); (H5) the snapshot-free
mint-time reuse residue `(★)` of `intFImp_mint_residue` (above). -/
private def IWorldHist (φ0 : Proposition Atom) (b : IBranch Atom) (e : List (ISF Atom))
    (nw : Nat) (edges : IEdges) : Prop :=
  ∃ (par : Nat → Nat) (obl : Nat → Proposition Atom)
    (sfor : Nat → List (Proposition Atom)) (fire : Nat → Proposition Atom),
    -- (H0) root normalization: the root world is its own parent, so `parAncestor` chains
    -- bottom out at the self-looping root instead of escaping into unconstrained `par`
    -- values (see `parAncestor_le`; a Phase 7 amendment, required to make (H1-acc)
    -- establishable at the mint arm when the fired label is the root)
    par 0 = 0 ∧
    ∀ c, 1 ≤ c → c < nw →
      -- (H1) tree structure
      (c, par c) ∈ edges ∧ par c < c ∧
      -- (H1-acc) genuine ancestor-accessibility under the CURRENT edges (incremental)
      (∀ c', parAncestor par c' c → isAccessible edges c' c = true) ∧
      -- (H2) universe containment of the recorded data
      obl c ∈ intSubfmls φ0 ∧ fire c ∈ intSubfmls φ0 ∧
      (∀ χ ∈ sfor c, χ ∈ intSubfmls φ0) ∧
      -- (H3) planted, monotone facts (survive every later append to b)
      (⟨.neg, obl c, c⟩ : ISF Atom) ∈ b ∧
      (∀ χ ∈ sfor c, χ ∈ posFormulasAt b c) ∧
      -- (H3-exp) the fired implication is recorded in the CURRENT expanded set `e`
      -- (monotone: `e` only ever grows along a lineage; a Phase 7 amendment, required to
      -- discharge (H4) between the fresh mint and any OLD world: the mint's fired triple
      -- is fresh w.r.t. `e` by `intStepBranch`'s duplicate check, so no old world can
      -- carry the same `(parent, fired implication)` record)
      (⟨.neg, fire c, par c⟩ : ISF Atom) ∈ e ∧
      -- (H4) sibling uniqueness: (parent, fired implication) determines the child
      (∀ c', 1 ≤ c' → c' < nw → par c = par c' → fire c = fire c' → c = c') ∧
      -- (H5) the snapshot-free residue of the mint-time reuse check (★, section 4.2)
      (∀ c', 1 ≤ c' → c' < c → parAncestor par c' (par c) → obl c' = obl c →
        ¬ (∀ χ ∈ sfor c, χ ∈ sfor c'))

omit [DecidableEq Atom] [Hashable Atom] in
/-- Entry discharge (report section 5.5, entry case): with `nw = 1`, no `c` satisfies
`1 ≤ c < 1`, so `IWorldHist` holds vacuously for ANY branch, expanded set, and edge list --
the witness functions are irrelevant since the body is never invoked. Generalized over `b`,
`e`, `edges` (not just the literal initial state) since the vacuity argument does not depend
on them. -/
private lemma IWorldHist_entry (φ0 : Proposition Atom) (b : IBranch Atom)
    (e : List (ISF Atom)) (edges : IEdges) :
    IWorldHist φ0 b e 1 edges :=
  ⟨fun _ => 0, fun _ => φ0, fun _ => [], fun _ => φ0, rfl,
    fun c hc1 hc2 => absurd hc2 (by omega)⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- `IWorldHist` is monotone in the branch and the expanded set: every clause referencing `b`
((H3)'s planted facts) or `e` ((H3-exp)'s fired record) is a membership fact, preserved under
any superset; all other clauses reference only the fixed witness data, `nw`, and `edges`.
This is the single transfer lemma used by every NON-minting arm (skip-closed, alpha, reuse,
beta), where `nw` and `edges` are unchanged and both `b` and `e` only grow. -/
private lemma IWorldHist_mono {φ0 : Proposition Atom} {b b' : IBranch Atom}
    {e e' : List (ISF Atom)} {nw : Nat} {edges : IEdges}
    (hmem : ∀ x ∈ b, x ∈ b') (hexp : ∀ x ∈ e, x ∈ e')
    (h : IWorldHist φ0 b e nw edges) : IWorldHist φ0 b' e' nw edges := by
  obtain ⟨par, obl, sfor, fire, hpar0, hall⟩ := h
  refine ⟨par, obl, sfor, fire, hpar0, fun c hc1 hc2 => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hall c hc1 hc2
  refine ⟨h1, h2, h3, h4, h5, h6, hmem _ h7, fun χ hχ => ?_, hexp _ h9, h10, h11⟩
  have hχ' := h8 χ hχ
  simp only [posFormulasAt, List.mem_filterMap] at hχ' ⊢
  obtain ⟨sf, hsf, hcond⟩ := hχ'
  exact ⟨sf, hmem sf hsf, hcond⟩

/-- Counter-redundancy (report section 3.1): the next-world counter is exactly one more than
the number of edges recorded so far. Only the mint arm changes either side, and it changes
both by exactly one (Phase 7); the other three arms change neither (Phase 8). Threaded as a
companion parallel-list invariant below, not merged into `IAllNW`. -/
private def IWorldHistCounter (nw : Nat) (edges : IEdges) : Prop :=
  nw = edges.length + 1

omit [DecidableEq Atom] [Hashable Atom] in
/-- Entry discharge: `openBranch_countermodel`'s initial state has `nw = 1`, `edges = []`, so
`1 = 0 + 1` holds by `rfl`. -/
private lemma IWorldHistCounter_entry : IWorldHistCounter 1 ([] : IEdges) := rfl

/-! ### `ForestComparable`: par-linearity export (Phase 10's first construction step)

Handoffs 07/08 (`specs/430_.../handoffs/`) identified `ForestComparable`-style comparability --
any two raw-accessible ancestors of a common world are themselves comparable -- as a load-bearing
fact needed by the origin-tracing extension, not yet exported anywhere. This section derives it
as a pure COROLLARY of the already-landed `IWorldHist`/`IWorldHistCounter` invariants: no new
invariant needs threading through `intExpandBranches_openBranch_sat`'s 10-case induction. The
argument has three independent steps:

1. `edges_shape_of_worldHist`: a counting/pigeonhole corollary of (H1)'s membership clause plus
   `IWorldHistCounter`'s length fact -- since `edges` has length exactly `nw - 1` and already
   contains `nw - 1` pairwise-distinct required pairs `(c, par c)` (`1 ≤ c < nw`), it can contain
   NOTHING else: every member of `edges` has that shape.
2. `parAncestor_of_isAccessible`: given that shape fact, `isAccessible`'s DFS is shown to
   coincide with `parAncestor` (this is the direction (H1-acc) does NOT supply on its own --
   handoffs 07/08's identified gap -- closed here using only step 1, not the converse).
3. `parAncestor_comparable`: pure `par`-linearity (`par` being a genuine function makes any two
   ancestors of a common point comparable), via the standard `parAncestor`-as-iterate bridge.

`IWorldHist_forestComparable` combines all three with the already-landed (H1-acc) clause. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Counting/pigeonhole step: `edges`'s length exactly matches the number of DISTINCT required
`(c, par c)` pairs (`1 ≤ c < nw`), all of which are already members (H1); by
`Finset.eq_of_subset_of_card_le`, `edges.toFinset` cannot exceed that required set, so `edges`
contains nothing else. The conclusion also returns the `1 ≤ c < nw` bound the pigeonhole
argument already establishes internally (previously extracted and discarded): this is what
`IWorldHist_worldsPlanted` needs to invoke `IWorldHist`'s (H3) clause on the recovered `c`. -/
private lemma edges_shape_of_worldHist {par : Nat → Nat} {nw : Nat} {edges : IEdges}
    (hlen : nw = edges.length + 1)
    (hmem : ∀ c, 1 ≤ c → c < nw → (c, par c) ∈ edges) :
    ∀ p ∈ edges, ∃ c, 1 ≤ c ∧ c < nw ∧ p = (c, par c) := by
  classical
  have hlen' : edges.length = nw - 1 := by omega
  set S : Finset (Nat × Nat) := (Finset.Ico 1 nw).image (fun c => (c, par c)) with hS
  have hSinj : Set.InjOn (fun c => (c, par c)) (Finset.Ico 1 nw) := by
    intro a _ b _ hab
    simpa using congrArg Prod.fst hab
  have hScard : S.card = nw - 1 := by
    rw [hS, Finset.card_image_of_injOn hSinj, Nat.card_Ico]
  have hSsub : S ⊆ edges.toFinset := by
    intro p hp
    simp only [hS, Finset.mem_image, Finset.mem_Ico] at hp
    obtain ⟨c, ⟨hc1, hc2⟩, hceq⟩ := hp
    rw [List.mem_toFinset, ← hceq]
    exact hmem c hc1 hc2
  have htoFinsetCard_le : edges.toFinset.card ≤ S.card := by
    calc edges.toFinset.card ≤ edges.length := List.toFinset_card_le (l := edges)
      _ = nw - 1 := hlen'
      _ = S.card := hScard.symm
  have hSeq : S = edges.toFinset := Finset.eq_of_subset_of_card_le hSsub htoFinsetCard_le
  intro p hp
  have hpS : p ∈ S := by rw [hSeq]; exact List.mem_toFinset.mpr hp
  simp only [hS, Finset.mem_image, Finset.mem_Ico] at hpS
  obtain ⟨c, ⟨hc1, hc2⟩, hceq⟩ := hpS
  exact ⟨c, hc1, hc2, hceq.symm⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- The direction (H1-acc) does NOT supply: given `edges_shape_of_worldHist`'s shape fact,
raw `isAccessible` reachability implies `parAncestor`. Proved by unfolding `isAccessible.go`'s
DFS: each step it takes from `current` to a `child` with `(child, current) ∈ edges` is, by the
shape fact, exactly a `par`-step (`current = par child`), so the whole DFS trace assembles into
a `parAncestor` chain via `Relation.ReflTransGen.head`. -/
private lemma parAncestor_of_isAccessible {par : Nat → Nat} {edges : IEdges}
    (hshape : ∀ p ∈ edges, ∃ c, p = (c, par c))
    (w w' : Nat) (h : isAccessible edges w w' = true) :
    parAncestor par w w' := by
  simp only [isAccessible] at h
  by_cases heq : w == w'
  · have : w = w' := by simpa using heq
    subst this
    exact Relation.ReflTransGen.refl
  · simp only [heq, Bool.false_eq_true, ite_false] at h
    suffices key : ∀ (current fuel : Nat), isAccessible.go edges w' current fuel = true →
        current = w' ∨ parAncestor par current w' by
      rcases key w edges.length h with heq2 | hpar
      · subst heq2; exact Relation.ReflTransGen.refl
      · exact hpar
    intro current fuel
    induction fuel generalizing current with
    | zero => simp [isAccessible.go]
    | succ k ih =>
      simp only [isAccessible.go]
      intro hstep
      rw [List.any_eq_true] at hstep
      obtain ⟨child, hchild, hcond⟩ := hstep
      simp only [List.mem_filterMap] at hchild
      obtain ⟨⟨c, p⟩, hedges, hfilt⟩ := hchild
      by_cases hpc : p == current
      · have hpeq : p = current := by simpa using hpc
        subst hpeq
        simp only [hpc, ite_true, Option.some.injEq] at hfilt
        subst hfilt
        obtain ⟨c', hc'⟩ := hshape (c, p) hedges
        rw [Prod.mk.injEq] at hc'
        obtain ⟨hcc, hpar_eq⟩ := hc'
        subst hcc
        by_cases hce : c == w'
        · have hcw' : c = w' := by simpa using hce
          right
          rw [hcw'] at hpar_eq
          exact Relation.ReflTransGen.single hpar_eq
        · simp only [hce, Bool.false_eq_true, ite_false] at hcond
          rcases ih c hcond with heq3 | hpar3
          · right; rw [heq3] at hpar_eq; exact Relation.ReflTransGen.single hpar_eq
          · right; exact Relation.ReflTransGen.head hpar_eq hpar3
      · simp only [Bool.not_eq_true] at hpc
        simp [hpc] at hfilt

omit [DecidableEq Atom] [Hashable Atom] in
/-- Structural half of `IPosPersistRaw`'s side-condition gap (needs no `IWorldHist` invariant):
a non-reflexive `isAccessible` success means the target `w'` is a child endpoint of some edge in
`edges`. Proved by unfolding `isAccessible.go`'s DFS exactly as `parAncestor_of_isAccessible`
does above, but the conclusion tracked is raw edge-list membership at `w'` rather than a
`parAncestor` chain to the DFS's start point -- since that membership fact, once found at any
depth, needs no further composition, the induction is simpler than
`parAncestor_of_isAccessible`'s. -/
private lemma isAccessible_target_mem_edges {edges : IEdges} {w w' : Nat}
    (h : isAccessible edges w w' = true) (hne : w ≠ w') : ∃ p, (w', p) ∈ edges := by
  simp only [isAccessible] at h
  have hne' : ¬ (w == w') := by simpa using hne
  simp only [hne', Bool.false_eq_true, ite_false] at h
  suffices key : ∀ (current fuel : Nat), isAccessible.go edges w' current fuel = true →
      ∃ p, (w', p) ∈ edges from key w edges.length h
  intro current fuel
  induction fuel generalizing current with
  | zero => simp [isAccessible.go]
  | succ k ih =>
    simp only [isAccessible.go]
    intro hstep
    rw [List.any_eq_true] at hstep
    obtain ⟨child, hchild, hcond⟩ := hstep
    simp only [List.mem_filterMap] at hchild
    obtain ⟨⟨c, p⟩, hedges, hfilt⟩ := hchild
    by_cases hpc : p == current
    · simp only [hpc, ite_true, Option.some.injEq] at hfilt
      by_cases hce : child == w'
      · have hceq : child = w' := by simpa using hce
        exact ⟨p, (hfilt.trans hceq) ▸ hedges⟩
      · simp only [hce, Bool.false_eq_true, ite_false] at hcond
        exact ih child hcond
    · simp only [Bool.not_eq_true] at hpc
      simp [hpc] at hfilt

omit [DecidableEq Atom] [Hashable Atom] in
/-- `parAncestor` unwinds to explicit `par`-iteration -- the standard bridge that makes
`par`-linearity (`parAncestor_comparable` below) a direct consequence of `Nat`-comparability. -/
private lemma parAncestor_iff_iterate {par : Nat → Nat} {x y : Nat} :
    parAncestor par x y ↔ ∃ n, x = par^[n] y := by
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, rfl⟩
    | @head a b hab _hchain ih =>
      obtain ⟨m, hm⟩ := ih
      exact ⟨m + 1, by rw [Function.iterate_succ_apply', ← hm, hab]⟩
  · rintro ⟨n, hn⟩
    subst hn
    induction n with
    | zero => exact Relation.ReflTransGen.refl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact Relation.ReflTransGen.head rfl ih

omit [DecidableEq Atom] [Hashable Atom] in
/-- Pure `par`-linearity: any two `parAncestor`-ancestors of a common world `c` are themselves
comparable. Depends only on `par` being a genuine (single-valued) function -- via
`parAncestor_iff_iterate`, both are `par`-iterates of `c`, and `Nat`-iterate-counts are always
comparable. -/
private lemma parAncestor_comparable {par : Nat → Nat} {x y c : Nat}
    (hx : parAncestor par x c) (hy : parAncestor par y c) :
    parAncestor par x y ∨ parAncestor par y x := by
  obtain ⟨n, hn⟩ := parAncestor_iff_iterate.mp hx
  obtain ⟨m, hm⟩ := parAncestor_iff_iterate.mp hy
  rcases le_total n m with hle | hle
  · right
    apply parAncestor_iff_iterate.mpr
    refine ⟨m - n, ?_⟩
    rw [hm, hn, ← Function.iterate_add_apply]
    congr 1
    omega
  · left
    apply parAncestor_iff_iterate.mpr
    refine ⟨n - m, ?_⟩
    rw [hn, hm, ← Function.iterate_add_apply]
    congr 1
    omega

/-- Forest/chain comparability along raw edges: any two worlds `isAccessible`-reachable to a
common world `l` are themselves `isAccessible`-comparable. This is the `ForestComparable` shape
`specs/archive/430_prove_atom_persistence_upward_closure_for_intexpan/scratch/PersistPrototype.lean`
assumed as a hypothesis, before it was known to be derivable rather than needing fresh
construction. -/
private def ForestComparable (nw : Nat) (edges : IEdges) : Prop :=
  ∀ w x l : Nat, w < nw → x < nw →
    isAccessible edges w l = true → isAccessible edges x l = true →
    isAccessible edges w x = true ∨ isAccessible edges x w = true

omit [DecidableEq Atom] [Hashable Atom] in
/-- **`ForestComparable` export**: derived entirely from the already-landed `IWorldHist`
(supplying (H1)'s membership shape, (H0)'s root normalization, and (H1-acc)'s forward
accessibility) plus `IWorldHistCounter` (supplying the length fact `edges_shape_of_worldHist`
needs) -- no new invariant threading through `intExpandBranches_openBranch_sat`'s induction is
required. -/
private lemma IWorldHist_forestComparable {φ0 : Proposition Atom} {b : IBranch Atom}
    {e : List (ISF Atom)} {nw : Nat} {edges : IEdges}
    (hWH : IWorldHist φ0 b e nw edges) (hWHC : IWorldHistCounter nw edges) :
    ForestComparable nw edges := by
  obtain ⟨par, obl, sfor, fire, hpar0, hall⟩ := hWH
  have hshapeB : ∀ p ∈ edges, ∃ c, 1 ≤ c ∧ c < nw ∧ p = (c, par c) :=
    edges_shape_of_worldHist hWHC (fun c hc1 hc2 => (hall c hc1 hc2).1)
  have hshape : ∀ p ∈ edges, ∃ c, p = (c, par c) :=
    fun p hp => let ⟨c, _hc1, _hc2, hceq⟩ := hshapeB p hp; ⟨c, hceq⟩
  have hacc' : ∀ c' c, c < nw → parAncestor par c' c → isAccessible edges c' c = true := by
    intro c' c hcnw hpa
    rcases Nat.eq_zero_or_pos c with hc0 | hcpos
    · subst hc0
      have hc'0 : c' = 0 := parAncestor_zero hpar0 hpa
      subst hc'0
      simp [isAccessible]
    · exact (hall c hcpos hcnw).2.2.1 c' hpa
  intro w x l hwnw hxnw hwl hxl
  have hwl' : parAncestor par w l := parAncestor_of_isAccessible hshape w l hwl
  have hxl' : parAncestor par x l := parAncestor_of_isAccessible hshape x l hxl
  rcases parAncestor_comparable hwl' hxl' with hwx | hxw
  · left; exact hacc' w x hxnw hwx
  · right; exact hacc' x w hwnw hxw

omit [DecidableEq Atom] [Hashable Atom] in
/-- **Label-order export** (plan Phase 5, beta-priority repair): derived entirely from
`IWorldHist`/`IWorldHistCounter`, mirroring `IWorldHist_forestComparable`'s derivation pattern
-- no new invariant threading through `intExpandBranches_openBranch_sat`'s induction is
required. `isAccessible`-reachability under the raw edges only ever flows from a SMALLER label
(ancestor) to a LARGER one (descendant): a direct corollary of `parAncestor_of_isAccessible`
(isAccessible collapses to a `parAncestor` chain, given the `edges` shape `IWorldHist`
supplies) composed with `parAncestor_le`'s non-strict descent bound, sharpened to strict by the
`w ≠ w'` hypothesis. This is the fact the freeze argument needs to rule out a freshly-minted
world `w' ≥ w0` from ever appearing as an `isAccessible`-source reaching a target `w < w0` born
strictly earlier: such an edge would force `w' < w`, contradicting `w0 ≤ w'`. -/
private lemma IWorldHist_isAccessible_lt {φ0 : Proposition Atom} {b : IBranch Atom}
    {e : List (ISF Atom)} {nw : Nat} {edges : IEdges}
    (hWH : IWorldHist φ0 b e nw edges) (hWHC : IWorldHistCounter nw edges)
    {w w' : Nat} (hw' : w' < nw) (hacc : isAccessible edges w w' = true) (hne : w ≠ w') :
    w < w' := by
  obtain ⟨par, obl, sfor, fire, hpar0, hall⟩ := hWH
  have hshapeB : ∀ p ∈ edges, ∃ c, 1 ≤ c ∧ c < nw ∧ p = (c, par c) :=
    edges_shape_of_worldHist hWHC (fun c hc1 hc2 => (hall c hc1 hc2).1)
  have hshape : ∀ p ∈ edges, ∃ c, p = (c, par c) :=
    fun p hp => let ⟨c, _hc1, _hc2, hceq⟩ := hshapeB p hp; ⟨c, hceq⟩
  have hpar : parAncestor par w w' := parAncestor_of_isAccessible hshape w w' hacc
  have hdesc : ∀ x, 1 ≤ x → x < nw → par x < x := fun c hc1 hc2 => (hall c hc1 hc2).2.1
  have hle : w ≤ w' := parAncestor_le hpar0 hdesc hw' hpar
  exact lt_of_le_of_ne hle hne

/-! ### `IWorldsPlanted`: the provenance half of `IPosPersistRaw`'s side-condition gap

`IPosPersistRaw`'s (Scheme.lean:6701-6704) third hypothesis needs "the target world already has
*some* entry on `b`", `b.any (fun sf => sf.label == w') = true`, at every raw edge-list child.
This is the provenance half of the gap (§3 item 2 of the supporting research report), the
counterpart to `isAccessible_target_mem_edges`'s structural half above: it is a pure corollary
of the already-landed `IWorldHist`/`IWorldHistCounter` invariants, following exactly the
`ForestComparable` derivation pattern (`edges_shape_of_worldHist` plus `IWorldHist`'s (H3)
clause) -- no new invariant threading through `intExpandBranches_openBranch_sat`'s induction. -/

/-- Every raw edge-list child already has some entry planted on `b`. -/
private def IWorldsPlanted (edges : IEdges) (b : IBranch Atom) : Prop :=
  ∀ c p : Nat, (c, p) ∈ edges → b.any (fun sf => sf.label == c) = true

omit [DecidableEq Atom] [Hashable Atom] in
/-- `IWorldsPlanted` is monotone in the branch: a planted entry survives any superset. -/
private lemma IWorldsPlanted_mono {edges : IEdges} {b b' : IBranch Atom}
    (hmem : ∀ x ∈ b, x ∈ b') (h : IWorldsPlanted edges b) : IWorldsPlanted edges b' := by
  intro c p hcp
  obtain ⟨sf, hsf, hcond⟩ := List.any_eq_true.mp (h c p hcp)
  exact List.any_eq_true.mpr ⟨sf, hmem sf hsf, hcond⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- **`IWorldsPlanted` export**: derived entirely from `IWorldHist` (supplying (H1)'s membership
shape and (H3)'s planted-entry fact) plus `IWorldHistCounter` (supplying the length fact
`edges_shape_of_worldHist` needs), mirroring `IWorldHist_forestComparable` exactly -- same two
hypotheses, computable at the same exit site (Scheme.lean:7058). -/
private lemma IWorldHist_worldsPlanted {φ0 : Proposition Atom} {b : IBranch Atom}
    {e : List (ISF Atom)} {nw : Nat} {edges : IEdges}
    (hWH : IWorldHist φ0 b e nw edges) (hWHC : IWorldHistCounter nw edges) :
    IWorldsPlanted edges b := by
  obtain ⟨par, obl, sfor, fire, hpar0, hall⟩ := hWH
  have hshapeB : ∀ p ∈ edges, ∃ c, 1 ≤ c ∧ c < nw ∧ p = (c, par c) :=
    edges_shape_of_worldHist hWHC (fun c hc1 hc2 => (hall c hc1 hc2).1)
  intro c p hcp
  obtain ⟨c', hc1, hc2, hceq⟩ := hshapeB (c, p) hcp
  rw [Prod.mk.injEq] at hceq
  obtain ⟨hcc', -⟩ := hceq
  subst hcc'
  have hplanted : (⟨.neg, obl c, c⟩ : ISF Atom) ∈ b := (hall c hc1 hc2).2.2.2.2.2.2.1
  exact List.any_eq_true.mpr ⟨_, hplanted, by simp⟩

/-- List companion of `IWorldHistCounter`, a 2-list zip over `(nws, edgeSets)` mirroring
`IAllLabelBoundStrict`'s shape (companion, not merged, of `IAllNW`). -/
private def IAllWorldHistCounter (nws : List Nat) (edgeSets : List IEdges) : Prop :=
  match nws, edgeSets with
  | [], [] => True
  | nw :: nws', edges :: edgeSets' =>
      IWorldHistCounter nw edges ∧ IAllWorldHistCounter nws' edgeSets'
  | _, _ => False

omit [DecidableEq Atom] [Hashable Atom] in
/-- `IAllWorldHistCounter` combines under list append (mirrors `IAllLabelBoundStrict_append`). -/
private lemma IAllWorldHistCounter_append {nws1 nws2 : List Nat}
    {edgeSets1 edgeSets2 : List IEdges}
    (h1 : IAllWorldHistCounter nws1 edgeSets1) (h2 : IAllWorldHistCounter nws2 edgeSets2) :
    IAllWorldHistCounter (nws1 ++ nws2) (edgeSets1 ++ edgeSets2) := by
  induction nws1 generalizing edgeSets1 with
  | nil =>
    cases edgeSets1 with
    | nil => simpa using h2
    | cons eh et => simp [IAllWorldHistCounter] at h1
  | cons nwh nwt ih =>
    cases edgeSets1 with
    | nil => simp [IAllWorldHistCounter] at h1
    | cons eh et =>
      simp only [IAllWorldHistCounter] at h1
      obtain ⟨hc, hrest⟩ := h1
      simp only [List.cons_append]
      exact ⟨hc, ih hrest⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- `IAllWorldHistCounter` holds along a constant-valued `map` (mirrors `IAllNW_map_const`;
covers the BETA arm, where every child inherits the SAME counter and edge list). -/
private lemma IAllWorldHistCounter_map_const {α : Type*} {l : List α} {nw' : Nat}
    {edges' : IEdges} (h : IWorldHistCounter nw' edges') :
    IAllWorldHistCounter (l.map (fun _ => nw')) (l.map (fun _ => edges')) := by
  induction l with
  | nil => simp [IAllWorldHistCounter]
  | cons _ t ih => simp only [List.map_cons, IAllWorldHistCounter]; exact ⟨h, ih⟩

/-- List companion of `IWorldHist`, a 4-list zip over `(bs, es, nws, edgeSets)` -- a new shape
not present elsewhere in this file (existing companions `IAllConsistent`/`IAllAccessConsistent`
are 3-list zips only). Threaded ALONGSIDE `IAllConsistent`/`IAllNW` (companion, not merged). -/
private def IAllWorldHist (φ0 : Proposition Atom) (bs : List (IBranch Atom))
    (es : List (List (ISF Atom))) (nws : List Nat) (edgeSets : List IEdges) : Prop :=
  match bs, es, nws, edgeSets with
  | [], [], [], [] => True
  | b :: bs', e :: es', nw :: nws', edges :: edgeSets' =>
      IWorldHist φ0 b e nw edges ∧ IAllWorldHist φ0 bs' es' nws' edgeSets'
  | _, _, _, _ => False

omit [DecidableEq Atom] [Hashable Atom] in
/-- `IAllWorldHist` combines under list append (mirrors `IAllNW_append`). -/
private lemma IAllWorldHist_append {φ0 : Proposition Atom}
    {bs1 bs2 : List (IBranch Atom)} {es1 es2 : List (List (ISF Atom))}
    {nws1 nws2 : List Nat} {edgeSets1 edgeSets2 : List IEdges}
    (h1 : IAllWorldHist φ0 bs1 es1 nws1 edgeSets1)
    (h2 : IAllWorldHist φ0 bs2 es2 nws2 edgeSets2) :
    IAllWorldHist φ0 (bs1 ++ bs2) (es1 ++ es2) (nws1 ++ nws2) (edgeSets1 ++ edgeSets2) := by
  induction bs1 generalizing es1 nws1 edgeSets1 with
  | nil =>
    cases es1 with
    | nil =>
      cases nws1 with
      | nil =>
        cases edgeSets1 with
        | nil => simpa using h2
        | cons _ _ => simp [IAllWorldHist] at h1
      | cons _ _ => simp [IAllWorldHist] at h1
    | cons _ _ => simp [IAllWorldHist] at h1
  | cons bh bt ih =>
    cases es1 with
    | nil => simp [IAllWorldHist] at h1
    | cons eh et =>
      cases nws1 with
      | nil => simp [IAllWorldHist] at h1
      | cons nwh nwt =>
        cases edgeSets1 with
        | nil => simp [IAllWorldHist] at h1
        | cons edgesh edgest =>
          simp only [IAllWorldHist] at h1
          obtain ⟨hWH, hrest⟩ := h1
          simp only [List.cons_append]
          exact ⟨hWH, ih hrest⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- `IAllWorldHist` holds along a constant-valued `map` (mirrors `IAllNW_map_const` /
`IAllAccessConsistent_map`; covers the BETA arm, where every sub-branch shares the same
expanded set, counter, and edge list, and only the branch itself varies via `f`). -/
private lemma IAllWorldHist_map_const {φ0 : Proposition Atom} {branches' : List (IBranch Atom)}
    (f : IBranch Atom → IBranch Atom) {newExp : List (ISF Atom)} {nw' : Nat} {edges' : IEdges}
    (h : ∀ br ∈ branches', IWorldHist φ0 (f br) newExp nw' edges') :
    IAllWorldHist φ0 (branches'.map f) (branches'.map (fun _ => newExp))
      (branches'.map (fun _ => nw')) (branches'.map (fun _ => edges')) := by
  induction branches' with
  | nil => simp [IAllWorldHist]
  | cons bh bt ih =>
    simp only [List.map_cons, IAllWorldHist]
    exact ⟨h bh (List.mem_cons_self ..), ih fun br hbr => h br (List.mem_cons_of_mem _ hbr)⟩

omit [Hashable Atom] in
/-- **Mint-arm preservation of `IWorldHist` (Phase 7, report section 5.5's mint case)**: when
the reuse check fails (`hnone`) and the world-creating `F(φ → ψ)@l` rule mints the fresh world
`nwH` (extending the branch by `intFImpRule`'s output, the expanded set by the fired triple,
and the edge list by `(nwH, l)`), the invariant is re-established at counter `nwH + 1` by
extending the four witness functions at the single new point `c = nwH`:
`par nwH = l`, `obl nwH = ψ`, `sfor nwH = φ :: posFormulasAt bPers l`, `fire nwH = φ → ψ`.

Clause discharge: (H1) is the appended edge plus the strict label bound `hl`; (H1-acc)
composes the parent's inherited ancestor-accessibility with `isAccessible_one_hop_ext` for the
fresh world and transfers old chains via `parAncestor_of_extend` + `isAccessible_append_mono`;
(H2) extracts subformula membership from `hUniv` via `intUniverseExt_mem_formula`; (H3) reads
the planted facts off `intFImpRule`'s literal output; (H3-exp) is the appended fired triple;
(H4) between the mint and any old world is refuted by `hsfe` (the fired triple is fresh
w.r.t. `eH`, but an old equal record would put it in `eH` by (H3-exp)); (H5) at the mint is
exactly `intFImp_mint_residue` (Phase 5's (★)), fed `hacc`/`hle` from the transferred chain
and `hmem`/`hsub` from the old (H3). -/
private lemma IWorldHist_mint {φ0 : Proposition Atom} {bPers : IBranch Atom}
    {eH : List (ISF Atom)} {nwH l : Nat} {edgesH : IEdges} {φ ψ : Proposition Atom}
    (hWH : IWorldHist φ0 bPers eH nwH edgesH)
    (hnone : intFImpReuseWitnessAnc? bPers edgesH
        ([⟨.pos, φ, nwH⟩, ⟨.neg, ψ, nwH⟩] ++ propagatePersistence bPers l nwH)
        (nwH, l) = none)
    (hsfe : eH.any (· == (⟨.neg, .imp φ ψ, l⟩ : ISF Atom)) = false)
    (hNC : ∀ (χ : Proposition Atom) (w : Nat), (⟨.neg, χ, w⟩ : ISF Atom) ∈ bPers →
        χ ∉ posFormulasAt bPers w)
    (hUniv : ∀ x ∈ bPers, x ∈ intUniverseExt φ0)
    (hsfb : (⟨.neg, .imp φ ψ, l⟩ : ISF Atom) ∈ bPers)
    (hl : l < nwH) :
    IWorldHist φ0
      (Branch.extendMany bPers
        ([⟨.pos, φ, nwH⟩, ⟨.neg, ψ, nwH⟩] ++ propagatePersistence bPers l nwH))
      (eH ++ [⟨.neg, .imp φ ψ, l⟩]) (nwH + 1) (edgesH ++ [(nwH, l)]) := by
  obtain ⟨par, obl, sfor, fire, hpar0, hall⟩ := hWH
  have hdesc : ∀ x, 1 ≤ x → x < nwH → par x < x := fun x hx1 hx2 => (hall x hx1 hx2).2.1
  -- Universe facts for the fired implication and the propagated positive set
  have himp : Proposition.imp φ ψ ∈ intSubfmls φ0 :=
    intUniverseExt_mem_formula (hUniv _ hsfb)
  have hφsub : φ ∈ intSubfmls φ0 :=
    intSubfmls_trans (by
      simp only [intSubfmls]
      exact List.mem_cons_of_mem _ (List.mem_append_left _ (intSubfmls_self_mem φ))) himp
  have hψsub : ψ ∈ intSubfmls φ0 :=
    intSubfmls_trans (by
      simp only [intSubfmls]
      exact List.mem_cons_of_mem _ (List.mem_append_right _ (intSubfmls_self_mem ψ))) himp
  have hposSub : ∀ χ ∈ posFormulasAt bPers l, χ ∈ intSubfmls φ0 := by
    intro χ hχ
    simp only [posFormulasAt, List.mem_filterMap] at hχ
    obtain ⟨sf', hsf', hcond⟩ := hχ
    by_cases hc : sf'.sign == .pos && sf'.label == l
    · simp only [hc, if_true, Option.some.injEq] at hcond
      exact hcond ▸ intUniverseExt_mem_formula (hUniv sf' hsf')
    · simp [hc] at hcond
  -- The mint's recorded positive set, as `intFImpRule`'s propagated positives
  have hsfor_eq :
      (([⟨.pos, φ, nwH⟩, ⟨.neg, ψ, nwH⟩] ++ propagatePersistence bPers l nwH)
          : List (ISF Atom)).filterMap
        (fun sf => if sf.sign == .pos then some sf.formula else none)
      = φ :: posFormulasAt bPers l := by
    simp [propagatePersistence, List.filterMap_map]
  have hψeq :
      (([⟨.pos, φ, nwH⟩, ⟨.neg, ψ, nwH⟩] ++ propagatePersistence bPers l nwH)
          : List (ISF Atom)).findSome?
        (fun sf => if sf.sign == .neg then some sf.formula else none) = some ψ := by
    simp
  have hnotmem : (⟨.neg, .imp φ ψ, l⟩ : ISF Atom) ∉ eH := by
    intro hmem'
    have htrue : eH.any (· == (⟨.neg, .imp φ ψ, l⟩ : ISF Atom)) = true :=
      List.any_eq_true.mpr ⟨_, hmem', by simp⟩
    rw [htrue] at hsfe
    simp at hsfe
  -- Ancestor-accessibility of the parent `l` from each of its `par`-ancestors under the
  -- PRE-mint edges (l = 0: the chain collapses to the reflexive case; l ≥ 1: (H1-acc) at l)
  have hancL : ∀ c', parAncestor par c' l → isAccessible edgesH c' l = true := by
    intro c' hchain
    rcases Nat.eq_zero_or_pos l with rfl | hl1
    · have hc0 : c' = 0 := parAncestor_zero hpar0 hchain
      subst hc0
      simp [isAccessible]
    · exact (hall l hl1 hl).2.2.1 c' hchain
  refine ⟨fun c => if c = nwH then l else par c,
      fun c => if c = nwH then ψ else obl c,
      fun c => if c = nwH then φ :: posFormulasAt bPers l else sfor c,
      fun c => if c = nwH then .imp φ ψ else fire c,
      ?_, fun c hc1 hc2 => ?_⟩
  · -- (H0): the root is not the fresh world (`nwH > l ≥ 0`), so normalization carries over
    have h0 : (0 : Nat) ≠ nwH := by omega
    simp only [if_neg h0, hpar0]
  · by_cases hcn : c = nwH
    · -- The freshly minted world
      subst hcn
      simp only [if_pos]
      refine ⟨List.mem_append_right _ (List.mem_singleton_self _), hl, ?_, hψsub, himp,
        ?_, ?_, ?_, List.mem_append_right _ (List.mem_singleton_self _), ?_, ?_⟩
      · -- (H1-acc) for the fresh world
        intro c' hchain
        rcases Relation.ReflTransGen.cases_tail hchain with heq | ⟨b, hchain', hstep⟩
        · subst heq
          simp [isAccessible]
        · simp only [if_pos] at hstep
          subst hstep
          exact isAccessible_one_hop_ext
            (hancL c' (parAncestor_of_extend hpar0 hdesc hl hchain'))
      · -- (H2) for the mint's positive set
        intro χ hχ
        rcases List.mem_cons.mp hχ with rfl | hχ'
        · exact hφsub
        · exact hposSub χ hχ'
      · -- (H3) obligation planted at the fresh world
        simp only [Branch.extendMany, List.mem_append]
        simp
      · -- (H3) positive set planted at the fresh world
        intro χ hχ
        have hmem' : (⟨.pos, χ, c⟩ : ISF Atom) ∈
            ([⟨.pos, φ, c⟩, ⟨.neg, ψ, c⟩] ++ propagatePersistence bPers l c
              : List (ISF Atom)) := by
          rcases List.mem_cons.mp hχ with rfl | hχ'
          · exact List.mem_append_left _ (by simp)
          · refine List.mem_append_right _ ?_
            simp only [propagatePersistence, List.mem_map]
            exact ⟨χ, hχ', rfl⟩
        simp only [posFormulasAt, List.mem_filterMap]
        refine ⟨⟨.pos, χ, c⟩, ?_, by simp⟩
        simp only [Branch.extendMany, List.mem_append]
        exact Or.inl (List.mem_append.mp hmem')
      · -- (H4) between the mint and any world
        intro c' hc'1 hc'2 hpar hfire
        by_cases hc'n : c' = c
        · exact hc'n.symm
        · exfalso
          simp only [if_neg hc'n] at hpar hfire
          have hc'lt : c' < c := by omega
          have hrec := (hall c' hc'1 hc'lt).2.2.2.2.2.2.2.2.1
          rw [← hfire, ← hpar] at hrec
          exact hnotmem hrec
      · -- (H5) the mint-time residue (★)
        intro c' hc'1 hc'lt hchain hobl
        have hc'n : c' ≠ c := by omega
        simp only [if_neg hc'n] at hobl ⊢
        have hc'ltnw : c' < c := by omega
        have hchainL : parAncestor par c' l :=
          parAncestor_of_extend hpar0 hdesc hl hchain
        have hobl_mem : (⟨.neg, ψ, c'⟩ : ISF Atom) ∈ bPers := by
          rw [← hobl]
          exact (hall c' hc'1 hc'ltnw).2.2.2.2.2.2.1
        have hle : c' ≤ l := parAncestor_le hpar0 hdesc hl hchainL
        have hres := intFImp_mint_residue hψeq hnone hobl_mem (hancL c' hchainL) hle hNC
          ((hall c' hc'1 hc'ltnw).2.2.2.2.2.2.2.1)
        rw [hsfor_eq] at hres
        exact hres
    · -- An old world: every clause carried, monotone in `b`/`e`/`edges`
      have hclt : c < nwH := by omega
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hall c hc1 hclt
      simp only [if_neg hcn]
      refine ⟨List.mem_append_left _ h1, h2, ?_, h4, h5, h6, ?_, ?_,
        List.mem_append_left _ h9, ?_, ?_⟩
      · -- (H1-acc): chains never touch the fresh point, and the edge list only grew
        intro c' hchain
        exact isAccessible_append_mono _
          (h3 c' (parAncestor_of_extend hpar0 hdesc hclt hchain))
      · -- (H3) obligation, monotone under the branch append
        simp only [Branch.extendMany, List.mem_append]
        exact Or.inr h7
      · -- (H3) positive set, monotone under the branch append
        intro χ hχ
        have hχ' := h8 χ hχ
        simp only [posFormulasAt, List.mem_filterMap] at hχ' ⊢
        obtain ⟨sf', hsf', hcond⟩ := hχ'
        refine ⟨sf', ?_, hcond⟩
        simp only [Branch.extendMany, List.mem_append]
        exact Or.inr hsf'
      · -- (H4), now also against the fresh world
        intro c' hc'1 hc'2 hpar hfire
        by_cases hc'n : c' = nwH
        · exfalso
          subst hc'n
          simp only [if_pos] at hpar hfire
          rw [hfire, hpar] at h9
          exact hnotmem h9
        · have hc'lt : c' < nwH := by omega
          simp only [if_neg hc'n] at hpar hfire
          exact h10 c' hc'1 hc'lt hpar hfire
      · -- (H5): chain targets stay strictly below the fresh point
        intro c' hc'1 hc'lt hchain hobl
        have hc'n : c' ≠ nwH := by omega
        simp only [if_neg hc'n] at hobl ⊢
        have hparlt : par c < nwH := by omega
        exact h11 c' hc'1 hc'lt (parAncestor_of_extend hpar0 hdesc hparlt hchain) hobl

/-! ## Phase 9: Pigeonhole Depth Bound (DP-2, report §4.3)

Bounds the length of any `par`-ancestor chain of created worlds by `intChainBound φ0`, purely
from (H5) of `IWorldHist` (the mint-time reuse residue (★)). `parIter` is the iterated-`par`
step function (needed to STATE the chain-length bound, hence introduced here rather than
deferred entirely to Phase 10, which reuses it for the path injection); the actual minimal-depth
construction and the size-bound injection are Phase 10's job. -/

/-- Iterating `par` `n` times from `c`, applying `par` first and then recursing (so that
`ws (i + k) = parIter par k (ws i)` composes directly with a chain's defining equation
`ws (i+1) = par (ws i)`, `ws_eq_parIter` below). -/
private def parIter (par : Nat → Nat) : Nat → Nat → Nat
  | 0, c => c
  | n + 1, c => parIter par n (par c)

omit [Hashable Atom] in
/-- Every iterate of `par` from `c` is a `parAncestor`-ancestor of `c`. -/
private lemma parAncestor_parIter (par : Nat → Nat) : ∀ n c, parAncestor par (parIter par n c) c
  | 0, _ => Relation.ReflTransGen.refl
  | n + 1, c =>
      (parAncestor_parIter par n (par c)).trans (Relation.ReflTransGen.single rfl)

omit [Hashable Atom] in
/-- A chain `ws` obeying the single-step law `ws (i+1) = par (ws i)` agrees with iterated `par`
composition: the value `k` steps past `ws i` is `parIter par k (ws i)`. -/
private lemma ws_eq_parIter {par : Nat → Nat} {ws : Nat → Nat}
    (hwsdec : ∀ i, ws (i + 1) = par (ws i)) : ∀ k i, ws (i + k) = parIter par k (ws i)
  | 0, i => by simp [parIter]
  | k + 1, i => by
      have ih := ws_eq_parIter hwsdec k (i + 1)
      rw [show i + (k + 1) = (i + 1) + k from by omega, ih, hwsdec i]
      rfl

omit [Hashable Atom] in
/-- **Pigeonhole depth bound**: adapts `intCreatedChain_le`'s pigeonhole body (above), replacing
`posFormulasAt b (ws (i+1))` with `sfor` and the runtime unblockedness hypothesis `hunb` with
(H5)'s snapshot-free residue `hres`. Given a `par`-descent chain `ws` (`hwsdec`) that stays a
genuinely created world (`hwspos`/`hwslt`) for every index below `D`, the chain length `D` is at
most `intChainBound φ0`. `ws` is instantiated to `parIter par · c` at Phase 10's sole call site;
stating the lemma over an abstract `ws` keeps the pigeonhole argument itself free of `parIter`'s
recursive unfolding. -/
private lemma intWorldHist_chain_le {φ0 : Proposition Atom} {par : Nat → Nat}
    {obl : Nat → Proposition Atom} {sfor : Nat → List (Proposition Atom)} {nw : Nat}
    (hdesc : ∀ x, 1 ≤ x → x < nw → par x < x)
    (hoblSub : ∀ c, 1 ≤ c → c < nw → obl c ∈ intSubfmls φ0)
    (hsforSub : ∀ c, 1 ≤ c → c < nw → ∀ χ ∈ sfor c, χ ∈ intSubfmls φ0)
    (hres : ∀ c, 1 ≤ c → c < nw → ∀ c', 1 ≤ c' → c' < c →
        parAncestor par c' (par c) → obl c' = obl c →
        ¬ (∀ χ ∈ sfor c, χ ∈ sfor c'))
    {ws : Nat → Nat} {D : Nat} (hwsdec : ∀ i, ws (i + 1) = par (ws i))
    (hwspos : ∀ i, i < D → 1 ≤ ws i) (hwslt : ∀ i, i < D → ws i < nw) :
    D ≤ intChainBound φ0 := by
  by_contra hD
  rw [Nat.not_le] at hD
  -- Single-step strict descent for indices below `D`.
  have hstepLt : ∀ i, i < D → ws (i + 1) < ws i := by
    intro i hi
    rw [hwsdec i]
    exact hdesc (ws i) (hwspos i hi) (hwslt i hi)
  -- Chained strict descent: `i < j ≤ D → ws j < ws i`.
  have hchainLt : ∀ i j, i < j → j ≤ D → ws j < ws i := by
    intro i j
    induction j with
    | zero => omega
    | succ j ih =>
      intro hij hjD
      rcases Nat.lt_or_ge i j with h | h
      · exact Nat.lt_trans (hstepLt j (by omega)) (ih h (by omega))
      · have : i = j := by omega
        subst this
        exact hstepLt i (by omega)
  have hmaps : ∀ i ∈ Finset.range D,
      (((sfor (ws i)).toFinset, obl (ws i)) : Finset (Proposition Atom) × Proposition Atom) ∈
        (intSubfmls φ0).toFinset.powerset ×ˢ (intSubfmls φ0).toFinset := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Finset.mem_product, Finset.mem_powerset]
    refine ⟨fun χ hχ => ?_, List.mem_toFinset.mpr (hoblSub (ws i) (hwspos i hi) (hwslt i hi))⟩
    rw [List.mem_toFinset] at hχ ⊢
    exact hsforSub (ws i) (hwspos i hi) (hwslt i hi) χ hχ
  have hcard : ((intSubfmls φ0).toFinset.powerset ×ˢ (intSubfmls φ0).toFinset).card <
      (Finset.range D).card := by
    rw [Finset.card_product, Finset.card_powerset, Finset.card_range]
    simpa [intChainBound] using hD
  obtain ⟨i, hi, j, hj, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rw [Finset.mem_range] at hi hj
  rw [Prod.mk.injEq] at heq
  obtain ⟨heqT, heqObl⟩ := heq
  have key : ∀ i j, i < j → j < D →
      (sfor (ws i)).toFinset = (sfor (ws j)).toFinset →
      obl (ws i) = obl (ws j) → False := by
    intro i j hij hjD hT hOeq
    have hancestor : parAncestor par (ws j) (par (ws i)) := by
      rw [← hwsdec i]
      have hj' : (i + 1) + (j - (i + 1)) = j := by omega
      have heq : ws j = parIter par (j - (i + 1)) (ws (i + 1)) := by
        have hstep := ws_eq_parIter hwsdec (j - (i + 1)) (i + 1)
        rwa [hj'] at hstep
      rw [heq]
      exact parAncestor_parIter par (j - (i + 1)) (ws (i + 1))
    refine hres (ws i) (hwspos i (Nat.lt_trans hij hjD)) (hwslt i (Nat.lt_trans hij hjD))
      (ws j) (hwspos j hjD) (hchainLt i j hij (Nat.le_of_lt hjD)) hancestor hOeq.symm ?_
    intro χ hχ
    have h1 : χ ∈ (sfor (ws i)).toFinset := List.mem_toFinset.mpr hχ
    rw [hT] at h1
    exact List.mem_toFinset.mp h1
  rcases Nat.lt_or_ge i j with h | h
  · exact key i j h hj heqT heqObl
  · exact key j i (Nat.lt_of_le_of_ne h fun e => hne e.symm) hi heqT.symm heqObl.symm

/-! ## Phase 10: Path-Injection Size Bound and `intWorldHist_nw_le` (DP-2, report §4.5)

Converts the depth bound (Phase 9) plus the sibling-uniqueness branching bound (H4) into
`nw ≤ WBound φ0`, matching `WBound`'s exact shape `(B+1)^(D+1)` via an explicit injection from
created worlds into root-to-world paths of fired implications. -/

omit [Hashable Atom] in
/-- `parIter`'s "apply-last" unfolding (the defining equation is "apply-first":
`parIter par (n+1) c = parIter par n (par c)`; this is the other, non-definitional
decomposition, needed to reconstruct a chain forward from the root in the injectivity
argument below). -/
private lemma parIter_succ' (par : Nat → Nat) :
    ∀ n c, parIter par (n + 1) c = par (parIter par n c)
  | 0, _ => rfl
  | n + 1, c =>
      calc parIter par (n + 1 + 1) c = parIter par (n + 1) (par c) := rfl
        _ = par (parIter par n (par c)) := parIter_succ' par n (par c)
        _ = par (parIter par (n + 1) c) := rfl

/-- Fuel-bounded depth-to-root: the number of `par`-steps from `c` down to `0`, computed with
an explicit decreasing fuel argument (structural recursion, no well-foundedness proof needed).
`fuel = 0` returns `0` unconditionally (a safe default; never invoked in that regime by
`parDepth`, which always supplies `fuel = c ≥` the true depth, `parDepthFuel_spec` below). -/
private def parDepthFuel (par : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, c => if c = 0 then 0 else parDepthFuel par fuel (par c) + 1

/-- Depth-to-root of `c`, fuelled by `c` itself (sound since the true depth is always `≤ c`,
`parDepthFuel_spec` below). -/
private def parDepth (par : Nat → Nat) (c : Nat) : Nat := parDepthFuel par c c

omit [Hashable Atom] in
/-- Fuel-generalized correctness of `parDepthFuel`: whenever the fuel dominates the start value
(`c ≤ fuel`), `parDepthFuel` computes an honest depth -- it reaches `0` after exactly that many
steps, and every earlier iterate is still positive (hence a genuinely created world). Proved by
induction on the FUEL, not on `c`, so the recursive call's fuel/value mismatch (fuel drops by
exactly `1`, `c` drops to `par c`, possibly by much more) never needs a separate
fuel-invariance lemma. -/
private lemma parDepthFuel_spec {par : Nat → Nat} {nw : Nat}
    (hdesc : ∀ x, 1 ≤ x → x < nw → par x < x) :
    ∀ fuel c, c < nw → c ≤ fuel →
      parIter par (parDepthFuel par fuel c) c = 0 ∧
        ∀ i, i < parDepthFuel par fuel c → 1 ≤ parIter par i c
  | 0, c, _, hcf => by
      have hc0 : c = 0 := by omega
      subst hc0
      refine ⟨rfl, fun i hi => absurd hi ?_⟩
      simp [parDepthFuel]
  | fuel + 1, c, hc, hcf => by
      rcases Nat.eq_zero_or_pos c with rfl | hpos
      · refine ⟨rfl, fun i hi => absurd hi ?_⟩
        simp [parDepthFuel]
      · have hc0 : c ≠ 0 := by omega
        have hlt : par c < c := hdesc c hpos hc
        have hltnw : par c < nw := Nat.lt_trans hlt hc
        have hlef : par c ≤ fuel := by omega
        obtain ⟨hz, hp⟩ := parDepthFuel_spec hdesc fuel (par c) hltnw hlef
        have heqD : parDepthFuel par (fuel + 1) c = parDepthFuel par fuel (par c) + 1 := by
          simp [parDepthFuel, hc0]
        rw [heqD]
        refine ⟨hz, fun i hi => ?_⟩
        rcases Nat.eq_zero_or_pos i with rfl | hipos
        · show 1 ≤ parIter par 0 c
          simp only [parIter]
          omega
        · have hi' : i - 1 < parDepthFuel par fuel (par c) := by omega
          have hp' := hp (i - 1) hi'
          have heqi : parIter par i c = parIter par (i - 1) (par c) := by
            have hii : i = (i - 1) + 1 := by omega
            rw [hii]
            rfl
          rw [heqi]
          exact hp'

omit [Hashable Atom] in
/-- **Phase 10 (report §4.5)**: `parDepth` is a sound depth measure for every world inside the
created range -- it reaches `0` and every earlier iterate is positive. Corollary of
`parDepthFuel_spec` at `fuel := c`. -/
private lemma parDepth_spec {par : Nat → Nat} {nw : Nat}
    (hdesc : ∀ x, 1 ≤ x → x < nw → par x < x) {c : Nat} (hc : c < nw) :
    parIter par (parDepth par c) c = 0 ∧ ∀ i, i < parDepth par c → 1 ≤ parIter par i c :=
  parDepthFuel_spec hdesc c c hc (Nat.le_refl c)

omit [Hashable Atom] in
/-- **Phase 10**: `parDepth` never exceeds `intChainBound φ0` for a world inside `IWorldHist`'s
witness data. Instantiates Phase 9's abstract chain bound (`intWorldHist_chain_le`) at
`ws := fun i => parIter par i c`. -/
private lemma parDepth_le_intChainBound {φ0 : Proposition Atom} {par : Nat → Nat}
    {obl : Nat → Proposition Atom} {sfor : Nat → List (Proposition Atom)} {nw : Nat}
    (hpar0 : par 0 = 0) (hdesc : ∀ x, 1 ≤ x → x < nw → par x < x)
    (hoblSub : ∀ c, 1 ≤ c → c < nw → obl c ∈ intSubfmls φ0)
    (hsforSub : ∀ c, 1 ≤ c → c < nw → ∀ χ ∈ sfor c, χ ∈ intSubfmls φ0)
    (hres : ∀ c, 1 ≤ c → c < nw → ∀ c', 1 ≤ c' → c' < c →
        parAncestor par c' (par c) → obl c' = obl c →
        ¬ (∀ χ ∈ sfor c, χ ∈ sfor c'))
    {c : Nat} (hc : c < nw) :
    parDepth par c ≤ intChainBound φ0 := by
  obtain ⟨-, hpos⟩ := parDepth_spec hdesc hc
  refine intWorldHist_chain_le hdesc hoblSub hsforSub hres
    (ws := fun i => parIter par i c) (D := parDepth par c)
    (fun i => parIter_succ' par i c) hpos ?_
  intro i _hi
  exact Nat.lt_of_le_of_lt
    (parAncestor_le hpar0 hdesc hc (parAncestor_parIter par i c)) hc

/-- Path encoding of a created world as its root-to-world sequence of fired implications,
padded with `none` beyond the true depth. `D` is instantiated to `intChainBound φ0` at
`intWorldHist_nw_le`'s call site; `parDepth_le_intChainBound` is what keeps the padding
well-formed (every created world's depth is `≤ D`). Position `k = 0` is nearest the root,
`k = parDepth par c - 1` is the last-fired step creating `c` itself. -/
private def pathOf (φ0 : Proposition Atom) (par : Nat → Nat) (fire : Nat → Proposition Atom)
    (D c : Nat) (k : Fin (D + 1)) : Option {χ // χ ∈ (intSubfmls φ0).toFinset} :=
  if (k : Nat) < parDepth par c then
    if hm : fire (parIter par (parDepth par c - 1 - (k : Nat)) c) ∈ (intSubfmls φ0).toFinset then
      some ⟨fire (parIter par (parDepth par c - 1 - (k : Nat)) c), hm⟩
    else none
  else none

omit [Hashable Atom] in
/-- `pathOf` at a position past the depth is `none`. -/
private lemma pathOf_none {φ0 : Proposition Atom} {par : Nat → Nat} {fire : Nat → Proposition Atom}
    {D c : Nat} {k : Fin (D + 1)} (hk : parDepth par c ≤ (k : Nat)) :
    pathOf φ0 par fire D c k = none := by
  simp only [pathOf]
  rw [if_neg (by omega)]

omit [Hashable Atom] in
/-- `pathOf` at a position below the depth records the fired implication at that step,
GIVEN the universe-containment fact (H2) that supplies its membership witness. Stated via
`Option.map Subtype.val` so the STATEMENT never needs to spell out the membership proof term
(only the PROOF, where `dif_pos` naturally supplies it). -/
private lemma pathOf_some {φ0 : Proposition Atom} {par : Nat → Nat} {fire : Nat → Proposition Atom}
    {nw D c : Nat} (hfireSub : ∀ x, 1 ≤ x → x < nw → fire x ∈ intSubfmls φ0)
    (hpar0 : par 0 = 0) (hdesc : ∀ x, 1 ≤ x → x < nw → par x < x) (hc : c < nw)
    {k : Fin (D + 1)} (hk : (k : Nat) < parDepth par c) :
    (pathOf φ0 par fire D c k).map Subtype.val =
      some (fire (parIter par (parDepth par c - 1 - (k : Nat)) c)) := by
  simp only [pathOf]
  rw [if_pos hk]
  have hpos : 1 ≤ parIter par (parDepth par c - 1 - (k : Nat)) c :=
    (parDepth_spec hdesc hc).2 _ (by omega)
  have hlt : parIter par (parDepth par c - 1 - (k : Nat)) c < nw :=
    Nat.lt_of_le_of_lt
      (parAncestor_le hpar0 hdesc hc
        (parAncestor_parIter par (parDepth par c - 1 - (k : Nat)) c)) hc
  rw [dif_pos (List.mem_toFinset.mpr (hfireSub _ hpos hlt))]
  simp

omit [Hashable Atom] in
/-- **Phase 10 injectivity**: `pathOf` is injective on any two worlds inside `IWorldHist`'s
created range, given (H4) sibling-uniqueness. Equal paths force equal depths (the position of
the last `some` entry, `hdeq` below), then equal `fire` values at each step force equal
PARENTS at that step (by (H4)), reconstructed by downward induction from the root
(`hstep` below: `∀ m ≤ d, parIter par (d - m) c = parIter par (d - m) c'`, `m = 0` at the root,
`m = d` at `c`/`c'` themselves). -/
private lemma pathOf_injOn {φ0 : Proposition Atom} {par : Nat → Nat} {fire : Nat → Proposition Atom}
    {nw D : Nat}
    (hpar0 : par 0 = 0) (hdesc : ∀ x, 1 ≤ x → x < nw → par x < x)
    (hfireSub : ∀ x, 1 ≤ x → x < nw → fire x ∈ intSubfmls φ0)
    (hH4 : ∀ c, 1 ≤ c → c < nw → ∀ c', 1 ≤ c' → c' < nw →
        par c = par c' → fire c = fire c' → c = c')
    {c c' : Nat} (hc : c < nw) (hc' : c' < nw)
    (hDc : parDepth par c ≤ D) (hDc' : parDepth par c' ≤ D)
    (heq : ∀ k : Fin (D + 1), pathOf φ0 par fire D c k = pathOf φ0 par fire D c' k) :
    c = c' := by
  -- Abbreviate `c`'s depth as `d`; `c'`'s facts are normalized to `d` via `hdeq` as soon as
  -- they are produced, so `d` is the SOLE depth-index used from here on.
  -- Step 1: equal depths (the position of the last `some` entry is determined by `pathOf`).
  have hdeq : parDepth par c = parDepth par c' := by
    by_contra hne
    rcases Nat.lt_or_ge (parDepth par c) (parDepth par c') with hlt | hge
    · have hkb : parDepth par c < D + 1 := by omega
      have hL : pathOf φ0 par fire D c ⟨parDepth par c, hkb⟩ = none :=
        pathOf_none (k := ⟨parDepth par c, hkb⟩) (le_refl _)
      have hRmap := pathOf_some hfireSub hpar0 hdesc hc' (D := D) (k := ⟨parDepth par c, hkb⟩)
        (by simpa using hlt)
      have h1 := heq ⟨parDepth par c, hkb⟩
      rw [hL] at h1
      rw [← h1] at hRmap
      simp at hRmap
    · have hgt : parDepth par c' < parDepth par c := by omega
      have hkb : parDepth par c' < D + 1 := by omega
      have hR : pathOf φ0 par fire D c' ⟨parDepth par c', hkb⟩ = none :=
        pathOf_none (k := ⟨parDepth par c', hkb⟩) (le_refl _)
      have hLmap := pathOf_some hfireSub hpar0 hdesc hc (D := D) (k := ⟨parDepth par c', hkb⟩)
        (by simpa using hgt)
      have h1 := heq ⟨parDepth par c', hkb⟩
      rw [hR] at h1
      rw [h1] at hLmap
      simp at hLmap
  -- Step 2: equal fire values at every position below the common depth.
  have hfireEq : ∀ j, j < parDepth par c →
      fire (parIter par j c) = fire (parIter par j c') := by
    intro j hj
    have hkb : parDepth par c - 1 - j < D + 1 := by omega
    have h1 := heq ⟨parDepth par c - 1 - j, hkb⟩
    have hL := pathOf_some hfireSub hpar0 hdesc hc (D := D) (k := ⟨parDepth par c - 1 - j, hkb⟩)
      (show parDepth par c - 1 - j < parDepth par c by omega)
    have hR := pathOf_some hfireSub hpar0 hdesc hc' (D := D) (k := ⟨parDepth par c - 1 - j, hkb⟩)
      (show parDepth par c - 1 - j < parDepth par c' by omega)
    have hjeqL : parDepth par c - 1 - (parDepth par c - 1 - j) = j := by omega
    have hjeqR : parDepth par c' - 1 - (parDepth par c - 1 - j) = j := by omega
    rw [hjeqL] at hL
    rw [hjeqR] at hR
    have hc2 := congrArg (Option.map Subtype.val) h1
    rw [hL, hR] at hc2
    simpa using hc2
  -- Step 3: downward induction from the root reconstructs
  -- `parIter par (parDepth par c - m) c = parIter par (parDepth par c - m) c'`.
  have hstep : ∀ m, m ≤ parDepth par c →
      parIter par (parDepth par c - m) c = parIter par (parDepth par c - m) c' := by
    intro m
    induction m with
    | zero =>
      intro _
      obtain ⟨hz, -⟩ := parDepth_spec (par := par) (nw := nw) hdesc hc
      obtain ⟨hz', -⟩ := parDepth_spec (par := par) (nw := nw) hdesc hc'
      simp only [Nat.sub_zero]
      rw [hz, hdeq, hz']
    | succ m ih =>
      intro hm1
      have hm : m ≤ parDepth par c := by omega
      have ihm := ih hm
      have hj : parDepth par c - (m + 1) < parDepth par c := by omega
      have hjfire := hfireEq (parDepth par c - (m + 1)) hj
      have hidx : parDepth par c - (m + 1) + 1 = parDepth par c - m := by omega
      have hpar_eq : par (parIter par (parDepth par c - (m + 1)) c) =
          par (parIter par (parDepth par c - (m + 1)) c') := by
        have e1 : par (parIter par (parDepth par c - (m + 1)) c) =
            parIter par (parDepth par c - m) c := by
          rw [← parIter_succ' par (parDepth par c - (m + 1)) c, hidx]
        have e2 : par (parIter par (parDepth par c - (m + 1)) c') =
            parIter par (parDepth par c - m) c' := by
          rw [← parIter_succ' par (parDepth par c - (m + 1)) c', hidx]
        rw [e1, e2, ihm]
      obtain ⟨-, hposC⟩ := parDepth_spec (par := par) (nw := nw) hdesc hc
      obtain ⟨-, hposC'⟩ := parDepth_spec (par := par) (nw := nw) hdesc hc'
      have hp1 : 1 ≤ parIter par (parDepth par c - (m + 1)) c := hposC _ hj
      have hp2 : 1 ≤ parIter par (parDepth par c - (m + 1)) c' := hposC' _ (by omega)
      have hlt1 : parIter par (parDepth par c - (m + 1)) c < nw :=
        Nat.lt_of_le_of_lt (parAncestor_le hpar0 hdesc hc (parAncestor_parIter par _ c)) hc
      have hlt2 : parIter par (parDepth par c - (m + 1)) c' < nw :=
        Nat.lt_of_le_of_lt (parAncestor_le hpar0 hdesc hc' (parAncestor_parIter par _ c')) hc'
      exact hH4 _ hp1 hlt1 _ hp2 hlt2 hpar_eq hjfire
  have hfin := hstep (parDepth par c) (le_refl _)
  simpa [parIter] using hfin

omit [Hashable Atom] in
/-- **Phase 10 (report §4.5, DP-2)**: the post-blocking world bound, derived purely from
`IWorldHist`'s structural creation-history invariant. Combines the depth bound (Phase 9,
via `parDepth_le_intChainBound`) with the path-injection's injectivity (`pathOf_injOn`) to
inject every created world into `Fin (intChainBound φ0 + 1) → Option S`
(`S := {χ // χ ∈ (intSubfmls φ0).toFinset}`), whose cardinality is exactly `WBound φ0` by
`Fintype.card_pi_const` -- matching `WBound`'s `(B + 1) ^ (D + 1)` shape by design, purely
from blocking combinatorics (chain depth × branching), never from `intUniverse`'s linear
range. -/
private lemma intWorldHist_nw_le {φ0 : Proposition Atom} {b : IBranch Atom}
    {e : List (ISF Atom)} {nw : Nat} {edges : IEdges} (hWH : IWorldHist φ0 b e nw edges) :
    nw ≤ WBound φ0 := by
  obtain ⟨par, obl, sfor, fire, hpar0, hall⟩ := hWH
  have hdesc : ∀ x, 1 ≤ x → x < nw → par x < x := by
    intro x hx1 hx2
    obtain ⟨-, h2, -, -, -, -, -, -, -, -, -⟩ := hall x hx1 hx2
    exact h2
  have hoblSub : ∀ x, 1 ≤ x → x < nw → obl x ∈ intSubfmls φ0 := by
    intro x hx1 hx2
    obtain ⟨-, -, -, h4, -, -, -, -, -, -, -⟩ := hall x hx1 hx2
    exact h4
  have hfireSub : ∀ x, 1 ≤ x → x < nw → fire x ∈ intSubfmls φ0 := by
    intro x hx1 hx2
    obtain ⟨-, -, -, -, h5, -, -, -, -, -, -⟩ := hall x hx1 hx2
    exact h5
  have hsforSub : ∀ x, 1 ≤ x → x < nw → ∀ χ ∈ sfor x, χ ∈ intSubfmls φ0 := by
    intro x hx1 hx2
    obtain ⟨-, -, -, -, -, h6, -, -, -, -, -⟩ := hall x hx1 hx2
    exact h6
  have hH4 : ∀ x, 1 ≤ x → x < nw → ∀ x', 1 ≤ x' → x' < nw →
      par x = par x' → fire x = fire x' → x = x' := by
    intro x hx1 hx2
    obtain ⟨-, -, -, -, -, -, -, -, -, h10, -⟩ := hall x hx1 hx2
    exact h10
  have hres : ∀ x, 1 ≤ x → x < nw → ∀ x', 1 ≤ x' → x' < x →
      parAncestor par x' (par x) → obl x' = obl x →
      ¬ (∀ χ ∈ sfor x, χ ∈ sfor x') := by
    intro x hx1 hx2
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h11⟩ := hall x hx1 hx2
    exact h11
  have hDbound : ∀ c, c < nw → parDepth par c ≤ intChainBound φ0 :=
    fun c hc => parDepth_le_intChainBound hpar0 hdesc hoblSub hsforSub hres hc
  -- Build the target Finset EXPLICITLY via `Fintype.piFinset`/`Finset.attach`/`Finset.image`,
  -- rather than relying on a global `Fintype (Fin (D+1) → Option S)` instance: instance search
  -- for that Pi-type-of-a-Subtype-of-a-Finset combination does not resolve in this file's
  -- ambient context (confirmed empirically), even though every piece resolves individually.
  -- `piFinset` sidesteps the issue entirely -- it only needs per-coordinate `Finset`s, no
  -- `Fintype` instance for the codomain type itself.
  set S := {χ // χ ∈ (intSubfmls φ0).toFinset} with hS_def
  set sFin : Finset S := (intSubfmls φ0).toFinset.attach with hsFin_def
  set optFin : Finset (Option S) := insert none (sFin.image some) with hoptFin_def
  set target : Finset (Fin (intChainBound φ0 + 1) → Option S) :=
    Fintype.piFinset (fun _ : Fin (intChainBound φ0 + 1) => optFin) with htarget_def
  have hinj : Set.InjOn (fun c => pathOf φ0 par fire (intChainBound φ0) c)
      (↑(Finset.range nw) : Set Nat) := by
    intro c hc c' hc' heqf
    simp only [Finset.coe_range, Set.mem_Iio] at hc hc'
    exact pathOf_injOn hpar0 hdesc hfireSub hH4 hc hc' (hDbound c hc) (hDbound c' hc')
      (fun k => congrFun heqf k)
  have hmaps : Set.MapsTo (fun c => pathOf φ0 par fire (intChainBound φ0) c)
      (↑(Finset.range nw) : Set Nat) (↑target : Set (Fin (intChainBound φ0 + 1) → Option S)) := by
    intro c _
    rw [Finset.mem_coe, htarget_def, Fintype.mem_piFinset]
    intro k
    rw [hoptFin_def]
    rcases hval : pathOf φ0 par fire (intChainBound φ0) c k with _ | val
    · exact Finset.mem_insert.mpr (Or.inl hval)
    · refine Finset.mem_insert_of_mem ?_
      rw [Finset.mem_image]
      exact ⟨val, Finset.mem_attach _ val, hval.symm⟩
  have hcard := Finset.card_le_card_of_injOn (fun c => pathOf φ0 par fire (intChainBound φ0) c)
    hmaps hinj
  rw [Finset.card_range] at hcard
  have hnotmem : (none : Option S) ∉ sFin.image some := by simp
  have hoptcard : optFin.card = sFin.card + 1 := by
    rw [hoptFin_def, Finset.card_insert_of_notMem hnotmem,
      Finset.card_image_of_injective _ (Option.some_injective S)]
  have hsFincard : sFin.card = (intSubfmls φ0).toFinset.card := by
    rw [hsFin_def, Finset.card_attach]
  have htargetcard : target.card = WBound φ0 := by
    rw [htarget_def, Fintype.card_piFinset_const, hoptcard, hsFincard]
    rfl
  rwa [htargetcard] at hcard

omit [Hashable Atom] in
/-- **DP-2 (RESOLVED)**: `hNW` preservation for the fresh-mint arm -- when `intStepBranch`
returns a world-creating `linearResult` (`newEdge = some _`) and `go`'s ancestor-directed
loop-check (`intFImpReuseWitnessAnc?`) finds no reusable ancestor (a world IS actually
minted, `nw' = nw + 1` by `intApplyRuleFull_linearResult_nextWorld`), the freshly
incremented counter stays within the post-blocking world bound `WBound φ0`.

**History of the resolution.** The original numeric restatement took `hnwB : nw ≤ WBound φ0`
(the form `IAllNW` threads) as its premise. That is NOT sufficient: it is consistent with
`nw = WBound φ0`, which would make the conclusion false. Two routes for supplying the missing
strict information were considered and REFUTED (report §4.1, §6): (1) restating with a bare
numeric strict premise `nw < WBound φ0` is not inductive across the mint recursion -- after a
mint the counter is `nw + 1`, and `nw < WBound φ0` yields only `nw + 1 ≤ WBound φ0`, not the
strict form the NEXT mint on the same branch would need; (2) transferring the runtime
unblockedness check (evaluated at firing time) forward to the FINAL branch is not derivable,
since conjunct 3 of the reuse check moves the wrong way under branch growth (positive content
at a world only grows, so the needed implication runs backwards).

**The route actually taken**: consume the runtime `none` result of the reuse check AT MINT
TIME, while the firing-time branch is still current -- this is `intFImp_mint_residue`'s
snapshot-free residue (★), which becomes clause (H5) of the structural invariant
`IWorldHist` (Phase 6). The premise is therefore the STRUCTURAL post-mint history invariant,
not a numeric strengthening: `intWorldHist_nw_le` (Phase 10) re-derives the numeric bound
purely from blocking combinatorics -- pigeonhole depth (Phase 9, `intWorldHist_chain_le`)
times branching (H4 sibling-uniqueness, the path injection) -- exactly matching `WBound`'s
`(B + 1) ^ (D + 1)` shape. This lemma is now a direct corollary of `intWorldHist_nw_le`.

Two cheap alternative routes were also considered and refuted, and are NOT to be re-derived:
a fuel-bounded counter (circular -- the fuel bound is itself derived FROM this bound) and a
flat pigeonhole without the creation tree (siblings never block each other, so no bound on
branching survives without the tree structure). -/
private lemma intFreshMint_preserves_nw {φ0 : Proposition Atom} {b : IBranch Atom}
    {e : List (ISF Atom)} {nw : Nat} {edges : IEdges}
    (hWH : IWorldHist φ0 b e (nw + 1) edges) :
    nw + 1 ≤ WBound φ0 :=
  intWorldHist_nw_le hWH

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

/-! ## Strict-Decrease Engine

**Retained-but-unconsumed (post-fuel-materialization-repair).** This section, together with
`intExpMeasure`/`intWork`/`intUniverse` above, was the sum-measure sufficiency argument for the
now-retired GLOBAL-fuel expansion engine: a single `fuel : Nat` decremented once per step across
*all* branches, requiring `fuel ≥ intExpMeasure … = 3^Θ(WBound φ)` — a numeral physically
unmaterializable beyond small formulas. The live engine (`## Per-Branch-Fuel Expansion Engine`
below) replaced the global fuel with a per-branch budget `intFuelExt`, whose sufficiency needs
only `intWork_drop` + `intCount_notMem_mono` (linear in `WBound`, not exponential); this
section's lemmas quantify only over worklists and `intStepBranch`, never over
`intExpandBranches` itself, so they remain build-green and correct but are no longer consumed by
any live statement.

Two design alternatives considered and NOT adopted for the per-branch-fuel repair, recorded so
neither is re-proposed without re-litigating the reasons below:
- **Well-founded recursion directly on this measure** (skip the fuel numeral entirely): rejected
  for the repair because the measure only strictly decreases UNDER the `hb`/`hnw` containment
  invariants, which would then have to be re-established inside the engine's own
  `decreasing_by` obligations — exactly DP-2's unproven creation-count fact, but now
  load-bearing for the engine's *existence* rather than one theorem's conclusion. Remains a
  legitimate elective cleanup once DP-2 is closed, not a substitute for the fuel repair.
- **Splitting a proof-side (huge-fuel) procedure from an eval-side (small-fuel) procedure**:
  rejected because the equivalence obligation between the two procedures is not dischargeable —
  the engine's persistence call depends on remaining fuel beyond exhaustion, so two runs at
  different fuels compute different intermediate branches unless small-fuel sufficiency (the
  same fact the split was meant to avoid proving) is already available.

The per-branch-fuel engine is empirically feasible only up to `s ≲ 22` (fuel-numeral digit count
grows as `2^s · s · log₁₀(s+1)`; the conformance corpus's largest row sits at `s = 19`). Future
conformance rows must stay within that envelope. -/

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
not need): only `sf ∈ intUniverseExt φ0` is required, obtained directly from `hb` together with
`sf ∈ bh` (read off `intStepBranch`'s internal `findSome?` witness).

Re-targeted over the enlarged universe `intUniverseExt` (the post-blocking
fuel-sufficiency development): the statement is parametric in the universe list, and
the proof consumes `hb`-membership only -- it never unfolds the world range. -/
lemma intExpMeasure_step_lt
    (φ0 : Proposition Atom)
    (done bt : List (List (ISF Atom)))
    (doneExp es : List (List (ISF Atom)))
    (newExp : List (ISF Atom))
    (bh e : List (ISF Atom)) (nw nw' : Nat) (newForms : List (ISF Atom))
    (newEdge : Option (Nat × Nat)) (b' : List (ISF Atom))
    (hdlen : done.length = doneExp.length)
    (hb : ∀ x ∈ bh, x ∈ intUniverseExt φ0)
    (hsub : ∀ z ∈ bh, z ∈ b')
    (hshape : IStepShape bh e nw (.linearResult newForms nw' newEdge) newExp) :
    intExpMeasure (intUniverseExt φ0) (done ++ [b'] ++ bt) (doneExp ++ [newExp] ++ es) + 1
      ≤ intExpMeasure (intUniverseExt φ0) (done ++ bh :: bt) (doneExp ++ e :: es) := by
  set U := intUniverseExt φ0 with hUdef
  have hrhs := intExpMeasure_split U done doneExp bh e bt es hdlen
  have hlhs : intExpMeasure U (done ++ [b'] ++ bt) (doneExp ++ [newExp] ++ es) =
      intExpMeasure U done doneExp + 3 ^ intWork U b' newExp + intExpMeasure U bt es := by
    have hlen1 : (done ++ [b']).length = (doneExp ++ [newExp]).length := by simp [hdlen]
    rw [intExpMeasure_append U (done ++ [b']) bt (doneExp ++ [newExp]) es hlen1,
        intExpMeasure_append U done [b'] doneExp [newExp] hdlen]
    simp [intExpMeasure]
  rw [hrhs, hlhs]
  suffices h : 3 ^ intWork U b' newExp + 1 ≤ 3 ^ intWork U bh e by omega
  obtain ⟨sf, hsfmem, hsfne, -, hnewExp⟩ := hshape
  rw [hnewExp]
  have hany : e.any (· == sf) = false := any_beq_eq_false_of_not_mem hsfne
  have hsfU : sf ∈ U := hb sf hsfmem
  have hdrop : intWork U b' (e ++ [sf]) + 1 ≤ intWork U bh e :=
    intWork_drop U bh b' e sf hsfU hany hsub
  have hC : 1 ≤ intWork U bh e := by omega
  have h0 : intWork U b' (e ++ [sf]) ≤ intWork U bh e - 1 := by omega
  exact pow3_add_one_le hC h0

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
own branching case.

Re-targeted over the enlarged universe `intUniverseExt` (the post-blocking
fuel-sufficiency development), exactly as `intExpMeasure_step_lt` above: the proof
consumes `hb`-membership only and never unfolds the world range. -/
lemma intExpMeasure_step_lt_branch
    (φ0 : Proposition Atom)
    (done bt : List (List (ISF Atom)))
    (doneExp es : List (List (ISF Atom)))
    (newExp : List (ISF Atom))
    (bh e : List (ISF Atom)) (nw nw' : Nat)
    (branches' : List (List (ISF Atom)))
    (hdlen : done.length = doneExp.length)
    (hb : ∀ x ∈ bh, x ∈ intUniverseExt φ0)
    (hshape : IStepShape bh e nw (.branchingResult branches' nw') newExp) :
    intExpMeasure (intUniverseExt φ0)
        (done ++ branches'.map (Branch.extendMany bh ·) ++ bt)
        (doneExp ++ branches'.map (fun _ => newExp) ++ es) + 1
      ≤ intExpMeasure (intUniverseExt φ0) (done ++ bh :: bt) (doneExp ++ e :: es) := by
  set U := intUniverseExt φ0 with hUdef
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
  obtain ⟨sf, hsfmem, hsfne, hint, hnewExp⟩ := hshape
  rw [hnewExp]
  have hany : e.any (· == sf) = false := any_beq_eq_false_of_not_mem hsfne
  have hsfU : sf ∈ U := hb sf hsfmem
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

/-! ## Per-Branch-Fuel Expansion Engine

THE tableau expansion engine (the retired global-fuel predecessor lived in
`Expansion.lean`; all consumers, including the `intuitionisticTableau`/`minimalTableau`
entry points below, now run on this engine). The old single global `fuel : Nat` is
replaced by `fuels : List Nat`, a fourth parallel list carrying each branch's
remaining fuel budget, sized by the materializable `intFuelExt` (above `WBound`).
Termination is UNCONDITIONAL (no branch-containment or world-bound hypotheses) by the
lexicographic measure `(Σ 3 ^ fuelᵢ over pending ++ done, pending.length)`. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Every branching rule of the intuitionistic calculus splits into exactly two
sub-branches: the three `branchingResult` sites of `intApplyRuleFull` (F-and, T-or, and
the T-imp split) all emit literal 2-element lists. Consumed (via
`intStepBranch_branchingResult_length`) by `intExpandBranches.go`'s termination
argument: the beta arm's fuel-sum decrease is `2 * 3 ^ f < 3 ^ (f + 1)`. -/
lemma intApplyRuleFull_branchingResult_length {sf : ISF Atom} {nextWorld : Nat}
    {b : IBranch Atom} {brs : List (List (ISF Atom))} {nw' : Nat}
    (h : intApplyRuleFull sf nextWorld b = .branchingResult brs nw') :
    brs.length = 2 := by
  obtain ⟨s, ff, l⟩ := sf
  cases s <;> cases ff <;>
    first
      | (simp only [intApplyRuleFull, IntRuleResult.branchingResult.injEq] at h
         exact h.1 ▸ rfl)
      | simp [intApplyRuleFull] at h

omit [Hashable Atom] [DecidableEq Atom] in
/-- Branching-step lift of `intApplyRuleFull_branchingResult_length`: a branching step
always produces exactly two sub-branch extension lists. Generalized (Phase 3 of the
beta-priority repair) from `intStepBranch`-specific to `IStepShape`, so it serves both
`intStepBranch` (via `intStepBranch_some_shape`) and `intStepBranchPrio` (via
`intStepBranchPrio_some_exists`) at its call sites -- `intExpandBranches.go`'s own
termination proof (the beta-arm `decreasing_by` case) and `CslibTests/BetaSplitRefutation.lean`'s
`goRaw` termination measure, both of which now feed `intStepBranchPrio`. -/
lemma intStepBranch_branchingResult_length {b : IBranch Atom}
    {expanded : List (ISF Atom)} {nextWorld : Nat}
    {brs : List (List (ISF Atom))} {nw' : Nat} {exp' : List (ISF Atom)}
    (hshape : IStepShape b expanded nextWorld (.branchingResult brs nw') exp') :
    brs.length = 2 := by
  obtain ⟨sf, -, -, hint, -⟩ := hshape
  exact intApplyRuleFull_branchingResult_length hint

/-- Sum of `3 ^ ·` over a constant-fuel list is `length * 3 ^ c` (beta-arm bookkeeping
for `intExpandBranches.go`'s termination proof). -/
private lemma sum_map_pow_const {α : Type*} (l : List α) (c : Nat) :
    ((l.map (fun _ => c)).map (fun fl => 3 ^ fl)).sum = l.length * 3 ^ c := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    ring

/-- Lexicographic decrease from an equal-or-smaller first component and a strictly
smaller second component (termination helper for `intExpandBranches.go`). -/
private lemma lex_lt_of_le_of_lt {a a' b b' : Nat} (ha : a' ≤ a) (hb : b' < b) :
    Prod.Lex (· < ·) (· < ·) (a', b') (a, b) := by
  rcases Nat.eq_or_lt_of_le ha with heq | hlt
  · subst heq
    exact Prod.Lex.right a' hb
  · exact Prod.Lex.left _ _ hlt

/-! ## `hFuel` Threading Invariant (Phase 6, R1 restatement)

The third R1 hypothesis (alongside Phase 5's `IAllUniv`/`IAllNW`): a per-branch
parallel-list invariant, `IAllFuel`, mirroring `IAllConsistent`'s simultaneous-recursion
shape over three lists (branches, expanded sets, fuels). Unlike the retired global-fuel
engine's `intExpMeasure ≤ fuel` form, this is per-branch: `intWork U bᵢ eᵢ < fuelsᵢ` for
every `i`. Supplies the fuel-0 discharge (`intWork ... < 0` is absurd by `omega`) and,
via `intWork_persistence_le`/`intWork_drop`, the succ-case re-establishment through each
arm of `intExpandBranches.go`'s functional induction. -/

/-- Per-branch fuel sufficiency threaded across the pending/done worklists: every
branch's remaining work (`intWork`, over the enlarged universe `intUniverseExt φ0`)
strictly undercuts its own fuel budget. Defined by simultaneous recursion over the three
parallel lists (mirrors `IAllConsistent`, `Scheme.lean:1211`), so a length mismatch is
automatically `False`. -/
private def IAllFuel (φ0 : Proposition Atom) (bs : List (IBranch Atom))
    (es : List (List (ISF Atom))) (fuels : List Nat) : Prop :=
  match bs, es, fuels with
  | [], [], [] => True
  | b :: bs', e :: es', f :: fuels' =>
      intWork (intUniverseExt φ0) b e < f ∧ IAllFuel φ0 bs' es' fuels'
  | _, _, _ => False

omit [Hashable Atom] in
/-- `IAllFuel` combines under list append (mirrors `IAllConsistent_append`). -/
private lemma IAllFuel_append {φ0 : Proposition Atom} {bs1 bs2 : List (IBranch Atom)}
    {es1 es2 : List (List (ISF Atom))} {fuels1 fuels2 : List Nat}
    (h1 : IAllFuel φ0 bs1 es1 fuels1) (h2 : IAllFuel φ0 bs2 es2 fuels2) :
    IAllFuel φ0 (bs1 ++ bs2) (es1 ++ es2) (fuels1 ++ fuels2) := by
  induction bs1 generalizing es1 fuels1 with
  | nil =>
    cases es1 with
    | nil =>
      cases fuels1 with
      | nil => simpa using h2
      | cons fh ft => simp [IAllFuel] at h1
    | cons eh et => simp [IAllFuel] at h1
  | cons bh bt ih =>
    cases es1 with
    | nil => simp [IAllFuel] at h1
    | cons eh et =>
      cases fuels1 with
      | nil => simp [IAllFuel] at h1
      | cons fh ft =>
        simp only [IAllFuel] at h1
        obtain ⟨hf, hrest⟩ := h1
        simp only [List.cons_append]
        exact ⟨hf, ih hrest⟩

omit [Hashable Atom] in
/-- `IAllFuel` holds along a uniform `map` at a constant fuel and constant expanded set:
if every branch obtained by applying `mapFn` to a member of `branches'` has work
strictly under `fuel'` against the SAME expanded set `newExp` (the shape produced by a
branching-rule step), then `IAllFuel` holds of the mapped/replicated triple of lists
(mirrors `IAllConsistent_map`; covers the BETA arm's
`branches'.map (Branch.extendMany bPers ·)`). -/
private lemma IAllFuel_map {φ0 : Proposition Atom} {branches' : List (IBranch Atom)}
    (mapFn : IBranch Atom → IBranch Atom) {newExp : List (ISF Atom)} {fuel' : Nat}
    (h : ∀ br ∈ branches', intWork (intUniverseExt φ0) (mapFn br) newExp < fuel') :
    IAllFuel φ0 (branches'.map mapFn) (branches'.map (fun _ => newExp))
      (branches'.map (fun _ => fuel')) := by
  induction branches' with
  | nil => simp [IAllFuel]
  | cons bh bt ih =>
    simp only [List.map_cons, IAllFuel]
    exact ⟨h bh List.mem_cons_self, ih (fun br hbr => h br (List.mem_cons_of_mem _ hbr))⟩

omit [Hashable Atom] in
/-- Persistence can only DECREASE the work measure: it only ADDS formulas to the branch
(`applyPersistenceFixpoint_mem_preserved`), and `intWork`'s branch-side term is antitone
in branch-membership growth (`intCount_notMem_mono`); the expanded-set-side term is
untouched since persistence never touches `e`. Bridges the threaded `hFuel` (stated
relative to the raw pending branch `bh`) to the persisted branch `bPers` that
`intStepBranch` actually consumes. -/
private lemma intWork_persistence_le (U : List (ISF Atom)) (b : IBranch Atom)
    (edges : IEdges) (fuel : Nat) (e : List (ISF Atom)) :
    intWork U (applyPersistenceFixpoint b edges fuel) e ≤ intWork U b e := by
  have hmem : ∀ x ∈ b, x ∈ applyPersistenceFixpoint b edges fuel :=
    fun x hx => applyPersistenceFixpoint_mem_preserved b edges fuel x hx
  have hle := intCount_notMem_mono U b (applyPersistenceFixpoint b edges fuel) hmem
  unfold intWork
  omega

omit [Hashable Atom] in
/-- `intStepBranch_some_exists`, additionally exposing the "not already expanded"
witness (`e.any (· == sf) = false`) that `intWork_drop` needs, converted from `IStepShape`'s
`sf ∉ e` (Prop) negation via `any_beq_eq_false_of_not_mem`. Generalized (Phase 3 of the
beta-priority repair) from `intStepBranch`-specific to `IStepShape` directly: this lemma's
live call sites sit inside the `go` induction (`intExpandBranches_openBranch_sat`), which now
supplies the shape via `intStepBranchPrio_some_exists`. -/
private lemma intStepBranch_some_exists_fuel
    {b : IBranch Atom} {e : List (ISF Atom)} {nw : Nat}
    {result : IntRuleResult Atom} {newExp : List (ISF Atom)}
    (hshape : IStepShape b e nw result newExp) :
    ∃ sf, sf ∈ b ∧ e.any (· == sf) = false ∧ intApplyRuleFull sf nw b = result ∧
      newExp = e ++ [sf] := by
  obtain ⟨sf, hsfb, hsfne, hint, hnewExp⟩ := hshape
  exact ⟨sf, hsfb, any_beq_eq_false_of_not_mem hsfne, hint, hnewExp⟩

omit [Hashable Atom] in
/-- Inner worklist loop of `intExpandBranches`, lifted to a top-level definition so
that well-founded elaboration and functional induction are available.

Mirrors the retired global-fuel engine's nested `go` with the single global
fuel replaced by the parallel fuel lists `pendingFuels`/`doneFuels`:
- persistence receives the ACTIVE BRANCH's remaining fuel `f` (mirroring the old
  engine's `fuel' + 1` shape);
- the skip-closed arm is unchanged in content — the closed branch moves to `done`
  together with its fuel;
- an open active branch with `f = 0` is returned as `.openBranch` (the per-branch
  exhaustion arm, mirroring the old global fuel-0 arm; closed branches are still
  skipped first, so `.openBranch` only ever returns open branches);
- the linear, world-creating, and reuse arms step the active branch's `f + 1` to `f`;
- the beta arm gives each child `f` (from the parent's `f + 1`).

Termination is UNCONDITIONAL, by the lexicographic measure
`(Σ 3 ^ fuelᵢ over pending ++ done, pending.length)`: the skip-closed arm permutes the
fuel multiset between the two lists (sum unchanged) and shrinks `pending`;
single-successor arms replace `3 ^ (f + 1)` by `3 ^ f`; the beta arm replaces
`3 ^ (f + 1)` by `2 * 3 ^ f`, sound because every branching rule emits exactly two
children (`intStepBranch_branchingResult_length`). -/
def intExpandBranches.go
    (closurePred : IBranch Atom → Bool)
    (pending : List (IBranch Atom))
    (pendingExp : List (List (ISF Atom)))
    (pendingNW : List Nat)
    (pendingEdges : List IEdges)
    (pendingFuels : List Nat)
    (done : List (IBranch Atom))
    (doneExp : List (List (ISF Atom)))
    (doneNW : List Nat)
    (doneEdges : List IEdges)
    (doneFuels : List Nat) :
    IntTableauResult Atom :=
  match pending, pendingExp, pendingNW, pendingEdges, pendingFuels with
  | [], _, _, _, _ => .closed  -- All branches closed
  | b :: restBs, e :: restEs, nw :: restNW, edges :: restEdges, f :: restFs =>
    -- First apply persistence (at the active branch's remaining fuel) to get all
    -- T(φ → ψ) consequences
    let bPers := applyPersistenceFixpoint b edges f
    if closurePred bPers then
      -- Branch is closed: move it (with its fuel) to done
      intExpandBranches.go closurePred restBs restEs restNW restEdges restFs
        (done ++ [bPers]) (doneExp ++ [e]) (doneNW ++ [nw]) (doneEdges ++ [edges])
        (doneFuels ++ [f])
    else
      match f with
      | 0 =>
        -- Per-branch fuel exhausted: return the (open) branch as countermodel
        .openBranch bPers
      | f' + 1 =>
        match _hstep : intStepBranchPrio bPers e nw with
        | none =>
          -- Branch is saturated and open: countermodel
          .openBranch bPers
        | some (.linearResult newForms nw' newEdge, newExp) =>
          -- Alpha-rule or world-creation: extend branch
          match newEdge with
          | none =>
            -- Alpha-rule: no new world, edges unchanged
            intExpandBranches.go closurePred
              (done ++ [Branch.extendMany bPers newForms] ++ restBs)
              (doneExp ++ [newExp] ++ restEs)
              (doneNW ++ [nw'] ++ restNW)
              (doneEdges ++ [edges] ++ restEdges)
              (doneFuels ++ [f'] ++ restFs)
              [] [] [] [] []
          | some newE =>
            -- World-creating F(φ → ψ) rule: ancestor-directed Sfor-containment
            -- loop-check before committing to the fresh world (as in the old engine)
            match intFImpReuseWitnessAnc? bPers edges newForms newE with
            | some _x =>
              -- Reuse: F(φ → ψ)@w discharged without creating the world; the world
              -- counter stays at `nw` (unconsumed)
              intExpandBranches.go closurePred
                (done ++ [bPers] ++ restBs)
                (doneExp ++ [newExp] ++ restEs)
                (doneNW ++ [nw] ++ restNW)
                (doneEdges ++ [edges] ++ restEdges)
                (doneFuels ++ [f'] ++ restFs)
                [] [] [] [] []
            | none =>
              -- No reusable ancestor: create the world exactly as before
              intExpandBranches.go closurePred
                (done ++ [Branch.extendMany bPers newForms] ++ restBs)
                (doneExp ++ [newExp] ++ restEs)
                (doneNW ++ [nw'] ++ restNW)
                (doneEdges ++ [edges ++ [newE]] ++ restEdges)
                (doneFuels ++ [f'] ++ restFs)
                [] [] [] [] []
        | some (.branchingResult branches' nw', newExp) =>
          -- Beta-rule: split into sub-branches (each inherits the edge set and the
          -- parent's decremented fuel `f'`)
          intExpandBranches.go closurePred
            (done ++ branches'.map (Branch.extendMany bPers ·) ++ restBs)
            (doneExp ++ branches'.map (fun _ => newExp) ++ restEs)
            (doneNW ++ branches'.map (fun _ => nw') ++ restNW)
            (doneEdges ++ branches'.map (fun _ => edges) ++ restEdges)
            (doneFuels ++ branches'.map (fun _ => f') ++ restFs)
            [] [] [] [] []
        | some (.notApplicable, _) =>
          -- This case shouldn't happen (intStepBranch filters notApplicable)
          .openBranch bPers
  | _ :: restBs, _pExp, _pNW, _pEdges, _pFuels =>
    intExpandBranches.go closurePred restBs [] [] [] [] done doneExp doneNW doneEdges
      doneFuels
termination_by
  (((pendingFuels ++ doneFuels).map (fun fl => 3 ^ fl)).sum, pending.length)
decreasing_by
  · -- Skip-closed arm: fuel multiset permuted between the lists, pending shrinks
    have hsum : ((restFs ++ (doneFuels ++ [f])).map (fun fl => 3 ^ fl)).sum
        = (((f :: restFs) ++ doneFuels).map (fun fl => 3 ^ fl)).sum := by
      simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
        List.sum_cons, List.sum_nil]
      omega
    rw [hsum]
    exact Prod.Lex.right _ (by simp)
  · -- Alpha arm: 3 ^ (f' + 1) replaced by 3 ^ f'
    apply Prod.Lex.left
    have _hp : (3 : Nat) ^ (f' + 1) = 3 ^ f' * 3 := pow_succ 3 f'
    have h1 : 1 ≤ (3 : Nat) ^ f' := Nat.one_le_pow _ _ (by norm_num)
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, List.append_nil]
    omega
  · -- Reuse arm: 3 ^ (f' + 1) replaced by 3 ^ f'
    apply Prod.Lex.left
    have _hp : (3 : Nat) ^ (f' + 1) = 3 ^ f' * 3 := pow_succ 3 f'
    have h1 : 1 ≤ (3 : Nat) ^ f' := Nat.one_le_pow _ _ (by norm_num)
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, List.append_nil]
    omega
  · -- Fresh-world arm: 3 ^ (f' + 1) replaced by 3 ^ f'
    apply Prod.Lex.left
    have _hp : (3 : Nat) ^ (f' + 1) = 3 ^ f' * 3 := pow_succ 3 f'
    have h1 : 1 ≤ (3 : Nat) ^ f' := Nat.one_le_pow _ _ (by norm_num)
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, List.append_nil]
    omega
  · -- Beta arm: 3 ^ (f' + 1) replaced by 2 * 3 ^ f' (exactly two children)
    apply Prod.Lex.left
    have hlen : branches'.length = 2 :=
      intStepBranch_branchingResult_length (intStepBranchPrio_some_exists _hstep)
    have hconst := sum_map_pow_const branches' f'
    rw [hlen] at hconst
    have _hp : (3 : Nat) ^ (f' + 1) = 3 ^ f' * 3 := pow_succ 3 f'
    have h1 : 1 ≤ (3 : Nat) ^ f' := Nat.one_le_pow _ _ (by norm_num)
    simp only [List.map_append, List.map_cons, List.sum_append,
      List.sum_cons, List.append_nil, hconst]
    omega
  · -- Mismatch arm: fuel sum can only shrink (pending fuels dropped), pending shrinks
    have hle : ((([] : List Nat) ++ doneFuels).map (fun fl => 3 ^ fl)).sum
        ≤ ((_pFuels ++ doneFuels).map (fun fl => 3 ^ fl)).sum := by
      simp only [List.nil_append, List.map_append, List.sum_append]
      omega
    exact lex_lt_of_le_of_lt hle (by simp)

omit [Hashable Atom] in
/-- Per-branch-fuel expansion loop for the intuitionistic/minimal tableau — the engine
behind `intuitionisticTableau` and `minimalTableau` (below).

Same worklist shape and parallel lists as the retired global-fuel engine, with the
single global `fuel : Nat` replaced by `fuels : List Nat`, a fourth parallel list
carrying each branch's remaining fuel budget (sized by `intFuelExt` at the entry
points). See `intExpandBranches.go` for the arm-by-arm fuel discipline and the
unconditional lexicographic termination measure. -/
def intExpandBranches
    (branches : List (IBranch Atom))
    (expandedSets : List (List (ISF Atom)))
    (nextWorlds : List Nat)
    (edgeSets : List IEdges)
    (fuels : List Nat)
    (closurePred : IBranch Atom → Bool) :
    IntTableauResult Atom :=
  intExpandBranches.go closurePred branches expandedSets nextWorlds edgeSets fuels
    [] [] [] [] []

omit [Hashable Atom] in
/-- At the tableau entry point, the worklist count over the ENLARGED universe
`intUniverseExt φ` is strictly below the materializable per-branch fuel budget
`intFuelExt φ` — the call-site `hFuel` discharge for the per-branch-fuel restatement
(replacing the retired global-measure form `intExpMeasure_init_le_fuel` on the
B-engine side). The initial singleton branch `[⟨.neg, φ, 0⟩]` with empty expanded set
gives `intWork ≤ 2 * |intUniverseExt φ|` (branch-exclusion term via
`List.countP_le_length`; the expanded-set term is the full length since `e = []`
excludes nothing); `intUniverseExt_length_le` then bounds the length, and the strict
`+ 1` slack of `intFuelExt` closes by `omega` — no pow manipulation. -/
lemma intWork_init_lt_intFuelExt (φ : Proposition Atom) :
    intWork (intUniverseExt φ) [(⟨.neg, φ, 0⟩ : ISF Atom)] [] < intFuelExt φ := by
  have hwork : intWork (intUniverseExt φ) [(⟨.neg, φ, 0⟩ : ISF Atom)] [] ≤
      2 * (intUniverseExt φ).length := by
    have heq : intWork (intUniverseExt φ) [(⟨.neg, φ, 0⟩ : ISF Atom)] [] =
        (intUniverseExt φ).countP
          (fun sf => !(([(⟨.neg, φ, 0⟩ : ISF Atom)]).any (· == sf))) +
        (intUniverseExt φ).countP
          (fun sf => !((([] : List (ISF Atom))).any (· == sf))) := rfl
    rw [heq]
    have h2 : (intUniverseExt φ).countP
        (fun sf => !((([] : List (ISF Atom))).any (· == sf)))
        = (intUniverseExt φ).length := by
      simp
    rw [h2]
    have h1 : (intUniverseExt φ).countP
        (fun sf => !(([(⟨.neg, φ, 0⟩ : ISF Atom)]).any (· == sf))) ≤
        (intUniverseExt φ).length :=
      List.countP_le_length
    omega
  have hUlen := intUniverseExt_length_le φ
  have h2U : 2 * (intUniverseExt φ).length ≤
      2 * (2 * (2 * φ.complexity + 1) * (WBound φ + 1)) :=
    Nat.mul_le_mul_left 2 hUlen
  have heq2 : 2 * (2 * (2 * φ.complexity + 1) * (WBound φ + 1)) =
      4 * (2 * φ.complexity + 1) * (WBound φ + 1) := by ring
  unfold intFuelExt
  omega

/-! ## Decision Procedure Entry Points

The two tableau entry points, running on the per-branch-fuel engine above with the
singleton fuel list `[intFuelExt φ]` (they live here, after `WBound`/`intFuelExt`/the
engine, because `intFuelExt` needs `WBound`; the expansion rules themselves stay in
`Expansion.lean`). -/

/-- `propExpandBranches` is the generic propositional tableau expansion loop,
parameterized by `closurePred : IBranch Atom → Bool`.

This is a documentation alias for `intExpandBranches`, emphasizing that the expansion
loop is closure-predicate-agnostic. The two concrete instantiations are:
- `intuitionisticTableau`: `closurePred = isIntuitionisticallyClosed`
- `minimalTableau`: `closurePred = isMinimallyClosed`

The `IntMinScheme` structure (above) bundles both divergence points (closure
predicate and countermodel `botForces`) into a single parameterized interface. -/
@[inline] def propExpandBranches
    (branches : List (IBranch Atom))
    (expandedSets : List (List (ISF Atom)))
    (nextWorlds : List Nat)
    (edgeSets : List IEdges)
    (fuels : List Nat)
    (closurePred : IBranch Atom → Bool) :
    IntTableauResult Atom :=
  intExpandBranches branches expandedSets nextWorlds edgeSets fuels closurePred

/-- The intuitionistic propositional tableau decision procedure.

Given `φ`, starts with `F(φ)` at world 0 and expands using `IntuitionisticClosure`.
- Returns `closed` iff `φ` is intuitionistically valid (IValid).
- Returns `openBranch b` iff `φ` is not intuitionistically valid, with `b` an open
  saturated branch giving a Kripke countermodel.

The initial branch's per-branch fuel budget is `intFuelExt φ` — the materializable
closed arithmetic form sized by the post-blocking world bound `WBound` (see
`intFuelExt`'s docstring for the feasibility envelope and
`intWork_init_lt_intFuelExt` for the entry-point sufficiency bound it satisfies). -/
def intuitionisticTableau (φ : Proposition Atom) : IntTableauResult Atom :=
  intExpandBranches [[⟨.neg, φ, 0⟩]] [[]] [1] [[]] [intFuelExt φ]
    isIntuitionisticallyClosed

/-- The minimal propositional tableau decision procedure.

Identical to the intuitionistic tableau but uses `isMinimallyClosed` instead of
`isIntuitionisticallyClosed`: a branch closes when T(φ) and F(φ) coexist at the same
world for any formula φ (not only T(⊥)).

- Returns `closed` iff `φ` is minimally valid (MValid).
- Returns `openBranch b` iff `φ` is not minimally valid. -/
def minimalTableau (φ : Proposition Atom) : IntTableauResult Atom :=
  intExpandBranches [[⟨.neg, φ, 0⟩]] [[]] [1] [[]] [intFuelExt φ]
    isMinimallyClosed

/-! ## Persistence-loop fuel-sufficiency (`sat_timp` STOP-gate gap 1 continuation,
`Scheme.lean:485-533`)

Closes GAP 1 of the `sat_timp` STOP-gate above: a genuine termination bound for
`applyPersistenceFixpoint`'s OWN recursion, distinct from `intExpMeasure_step_lt` (which bounds
the OUTER alpha/beta/world-creation loop only). The key fact: each non-fixpoint round of
`applyAllTImpRules` strictly drops the count of `intUniverseExt φ0`-cells not yet on the branch
(mirrors the `intWork`/`intCount_notMem_append_drop` engine above, restricted to the
branch-membership term alone, since persistence has no separate `e` "expanded" set). Since this
count is bounded above by `|intUniverseExt φ0|` (a fixed function of `φ0` via
`intUniverseExt_length_le`), fuel at least this count suffices for a genuine fixpoint.
Re-targeted over the enlarged universe `intUniverseExt` (the post-blocking fuel-sufficiency
development). GAP 2 (determinacy) is NOT addressed here — see
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
/-- The generalized copy-propagation output (`genCopies`'s copy of a positive formula `χ` at
an accessible world `w'` lacking one) is never already on the branch: the
`if b.any … then none else …` guard in its construction is exactly this fact, restated as
membership. Generalizes the retired `T(φ → ψ)`-only self-copy version of this fact to an
arbitrary formula `χ`. -/
private lemma applyAllTImpRules_copy_notMem {χ : Proposition Atom} {l : Nat} {edges : IEdges}
    {b : IBranch Atom} {x : ISF Atom}
    (hx : x ∈ List.filterMap
        (fun w' =>
          if (List.any b fun y => y.sign == Sign.pos && y.formula == χ && y.label == w')
              = true then none
          else some (⟨.pos, χ, w'⟩ : ISF Atom))
        (List.filter (fun w => isAccessible edges l w)
          (List.map (fun y => y.label) b).eraseDups)) :
    b.any (· == x) = false := by
  simp only [List.mem_filterMap] at hx
  obtain ⟨w', -, hxeq⟩ := hx
  split at hxeq
  · simp at hxeq
  · simp only [Option.some.injEq] at hxeq
    rw [← hxeq, Bool.eq_false_iff]
    intro hcon
    rename_i hnotmem
    apply hnotmem
    rw [List.any_eq_true] at hcon ⊢
    obtain ⟨sf, hsfmem, hsfeq⟩ := hcon
    refine ⟨sf, hsfmem, ?_⟩
    rw [beq_iff_eq] at hsfeq
    simp [hsfeq]

omit [Hashable Atom] in
/-- One non-fixpoint round of `applyAllTImpRules` strictly drops the count of
`intUniverseExt φ0` cells not yet on the branch, given branch-containment `hb` (the
fuel-sufficiency gap 1 continuation; mirrors `intWork_drop`'s combinatorial core, restricted
to the branch-membership term since persistence tracks no separate expanded set). -/
private lemma applyAllTImpRules_count_drop
    {φ0 : Proposition Atom} {b : IBranch Atom} {edges : IEdges}
    (hb : ∀ x ∈ b, x ∈ intUniverseExt φ0)
    (hne : (applyAllTImpRules b edges).length ≠ b.length) :
    (intUniverseExt φ0).countP (fun sf => !((applyAllTImpRules b edges).any (· == sf))) + 1 ≤
      (intUniverseExt φ0).countP (fun sf => !(b.any (· == sf))) := by
  have happend : applyAllTImpRules b edges =
      (b ++ (b.filterMap fun sf =>
        match sf.sign, sf.formula with
        | .pos, .imp φ ψ =>
          let toAdd := intTImpRule φ ψ sf.label edges b
          if toAdd.isEmpty then none else some toAdd
        | _, _ => none).flatten) ++
      (b.filterMap fun sf =>
        match sf.sign with
        | .pos =>
          let accessibleWorlds :=
            (b.map (·.label)).eraseDups.filter (isAccessible edges sf.label ·)
          let copies := accessibleWorlds.filterMap fun w' =>
            if b.any (fun y => y.sign == .pos && y.formula == sf.formula && y.label == w') then
              none
            else some (⟨.pos, sf.formula, w'⟩ : ISF Atom)
          if copies.isEmpty then none else some copies
        | .neg => none).flatten := rfl
  set nf := (b.filterMap fun sf =>
        match sf.sign, sf.formula with
        | .pos, .imp φ ψ =>
          let toAdd := intTImpRule φ ψ sf.label edges b
          if toAdd.isEmpty then none else some toAdd
        | _, _ => none) with hnf_def
  set gc := (b.filterMap fun sf =>
        match sf.sign with
        | .pos =>
          let accessibleWorlds :=
            (b.map (·.label)).eraseDups.filter (isAccessible edges sf.label ·)
          let copies := accessibleWorlds.filterMap fun w' =>
            if b.any (fun y => y.sign == .pos && y.formula == sf.formula && y.label == w') then
              none
            else some (⟨.pos, sf.formula, w'⟩ : ISF Atom)
          if copies.isEmpty then none else some copies
        | .neg => none) with hgc_def
  have hne' : nf.flatten ≠ [] ∨ gc.flatten ≠ [] := by
    by_contra hcontra
    push Not at hcontra
    apply hne
    rw [happend, hcontra.1, hcontra.2, List.append_nil, List.append_nil]
  obtain ⟨x, hxor⟩ : ∃ x, x ∈ nf.flatten ∨ x ∈ gc.flatten := by
    rcases hne' with hne' | hne'
    · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne'
      exact ⟨x, Or.inl hx⟩
    · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne'
      exact ⟨x, Or.inr hx⟩
  have hxmemApply : x ∈ applyAllTImpRules b edges := by
    rw [happend]
    rcases hxor with hxor | hxor
    · exact List.mem_append_left _ (List.mem_append_right b hxor)
    · exact List.mem_append_right _ hxor
  have hxU : x ∈ intUniverseExt φ0 :=
    applyAllTImpRules_subset_ext (φ0 := φ0) (edges := edges) hb (x := x) hxmemApply
  have hxnotb : b.any (· == x) = false := by
    rcases hxor with hxmem | hxmem
    · simp only [hnf_def, List.mem_flatten, List.mem_filterMap] at hxmem
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
            exact intTImpRule_output_notMem hxmem
    · simp only [hgc_def, List.mem_flatten, List.mem_filterMap] at hxmem
      obtain ⟨cs, ⟨sf', hsf'mem, hmatch⟩, hxmem⟩ := hxmem
      cases hsign : sf'.sign with
      | neg => simp only [hsign] at hmatch; exact absurd hmatch (by simp)
      | pos =>
        simp only [hsign] at hmatch
        split at hmatch
        · simp at hmatch
        · simp only [Option.some.injEq] at hmatch
          rw [← hmatch] at hxmem
          exact applyAllTImpRules_copy_notMem hxmem
  have hdrop := intCount_notMem_append_drop (intUniverseExt φ0) b x hxU hxnotb
  have hmono := intCount_notMem_mono (intUniverseExt φ0) (b ++ [x]) (applyAllTImpRules b edges)
    (by
      intro z hz
      rw [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · rw [happend, List.mem_append]
        exact Or.inl (List.mem_append_left _ hz)
      · exact hxmemApply)
  omega

omit [Hashable Atom] in
/-- **Copy-completeness at a genuine fixpoint** (Phase 4, generalizing the ψ-consequence
observation in the `sat_timp` STOP-gate note above: "at a genuine fixpoint, `T(φ)@w' ∈ b →
T(ψ)@w' ∈ b`"). If one round of `applyAllTImpRules` changes nothing
(`applyAllTImpRules b edges = b`), the generalized copy channel has already delivered every
positive formula it owes along the RAW `edges`: for `T(χ)@w ∈ b` and any `w'` accessible from
`w` that already carries some entry on the branch, `T(χ)@w'` is on `b` too. Mirrors
`applyAllTImpRules_count_drop`'s combinatorial style: if the copy were missing, `genCopies`'s
`if b.any … then none else …` guard would have fired and produced a strictly longer branch,
contradicting the fixpoint hypothesis. -/
private lemma applyAllTImpRules_copy_complete_of_fixpoint
    {b : IBranch Atom} {edges : IEdges}
    (hfix : applyAllTImpRules b edges = b)
    {χ : Proposition Atom} {w w' : Nat}
    (hmem : (⟨.pos, χ, w⟩ : ISF Atom) ∈ b)
    (hacc : isAccessible edges w w' = true)
    (hw' : b.any (fun sf => sf.label == w') = true) :
    (⟨.pos, χ, w'⟩ : ISF Atom) ∈ b := by
  rw [← hfix]
  by_cases halready : (b.any fun y => y.sign == .pos && y.formula == χ && y.label == w') = true
  · -- Already present in `b`: lift the membership through the first append component.
    rw [List.any_eq_true] at halready
    obtain ⟨sf, hsfmem, hsfeq⟩ := halready
    simp only [Bool.and_eq_true, beq_iff_eq] at hsfeq
    obtain ⟨⟨hsign, hform⟩, hlabel⟩ := hsfeq
    have hsfeq' : sf = (⟨.pos, χ, w'⟩ : ISF Atom) := by
      obtain ⟨s, f, l⟩ := sf
      simp only [SignedFormula.mk.injEq]
      exact ⟨hsign, hform, hlabel⟩
    rw [← hsfeq']
    simp only [applyAllTImpRules, List.mem_append]
    exact Or.inl (Or.inl hsfmem)
  · -- Not yet present: `genCopies`'s guard fires from the source `⟨.pos, χ, w⟩` and delivers
    -- the copy directly.
    rw [Bool.not_eq_true] at halready
    have hw'mem : w' ∈ (b.map (·.label)).eraseDups := by
      simp only [List.mem_eraseDups, List.mem_map]
      rw [List.any_eq_true] at hw'
      obtain ⟨y, hymem, hyeq⟩ := hw'
      simp only [beq_iff_eq] at hyeq
      exact ⟨y, hymem, hyeq⟩
    have hw'acc : w' ∈ (b.map (·.label)).eraseDups.filter (isAccessible edges w ·) := by
      simp only [List.mem_filter]
      exact ⟨hw'mem, hacc⟩
    have hcopy_mem : (⟨.pos, χ, w'⟩ : ISF Atom) ∈
        ((b.map (·.label)).eraseDups.filter (isAccessible edges w ·)).filterMap fun w'' =>
          if b.any (fun y => y.sign == .pos && y.formula == χ && y.label == w'') then none
          else some (⟨.pos, χ, w''⟩ : ISF Atom) := by
      simp only [List.mem_filterMap]
      exact ⟨w', hw'acc, by simp [halready]⟩
    simp only [applyAllTImpRules, List.mem_append]
    refine Or.inr ?_
    simp only [List.mem_flatten, List.mem_filterMap]
    refine ⟨_, ⟨(⟨.pos, χ, w⟩ : ISF Atom), hmem, ?_⟩, hcopy_mem⟩
    have hne : (((b.map (·.label)).eraseDups.filter (isAccessible edges w ·)).filterMap
        fun w'' =>
          if b.any (fun y => y.sign == .pos && y.formula == χ && y.label == w'') then none
          else some (⟨.pos, χ, w''⟩ : ISF Atom)).isEmpty = false :=
      List.isEmpty_eq_false_iff_exists_mem.mpr ⟨_, hcopy_mem⟩
    simp only [hne, Bool.false_eq_true, ite_false]

omit [Hashable Atom] in
/-- If one round of `applyAllTImpRules` does not change the branch length, it does not
change the branch at all: both the ψ-consequence channel (`newForms`) and the generalized
copy channel (`genCopies`) must be empty. -/
private lemma applyAllTImpRules_eq_self_of_length_eq
    {b : IBranch Atom} {edges : IEdges}
    (hlen : (applyAllTImpRules b edges).length = b.length) :
    applyAllTImpRules b edges = b := by
  have happend : applyAllTImpRules b edges =
      (b ++ (b.filterMap fun sf =>
        match sf.sign, sf.formula with
        | .pos, .imp φ ψ =>
          let toAdd := intTImpRule φ ψ sf.label edges b
          if toAdd.isEmpty then none else some toAdd
        | _, _ => none).flatten) ++
      (b.filterMap fun sf =>
        match sf.sign with
        | .pos =>
          let accessibleWorlds :=
            (b.map (·.label)).eraseDups.filter (isAccessible edges sf.label ·)
          let copies := accessibleWorlds.filterMap fun w' =>
            if b.any (fun y => y.sign == .pos && y.formula == sf.formula && y.label == w') then
              none
            else some (⟨.pos, sf.formula, w'⟩ : ISF Atom)
          if copies.isEmpty then none else some copies
        | .neg => none).flatten := rfl
  rw [happend] at hlen ⊢
  rw [List.length_append, List.length_append] at hlen
  have hnf0 : (b.filterMap fun sf =>
        match sf.sign, sf.formula with
        | .pos, .imp φ ψ =>
          let toAdd := intTImpRule φ ψ sf.label edges b
          if toAdd.isEmpty then none else some toAdd
        | _, _ => none).flatten = [] :=
    List.length_eq_zero_iff.mp (by omega)
  have hgc0 : (b.filterMap fun sf =>
        match sf.sign with
        | .pos =>
          let accessibleWorlds :=
            (b.map (·.label)).eraseDups.filter (isAccessible edges sf.label ·)
          let copies := accessibleWorlds.filterMap fun w' =>
            if b.any (fun y => y.sign == .pos && y.formula == sf.formula && y.label == w') then
              none
            else some (⟨.pos, sf.formula, w'⟩ : ISF Atom)
          if copies.isEmpty then none else some copies
        | .neg => none).flatten = [] :=
    List.length_eq_zero_iff.mp (by omega)
  rw [hnf0, hgc0, List.append_nil, List.append_nil]

omit [Hashable Atom] in
/-- **Genuine-fixpoint sufficiency** (closes `sat_timp` STOP-gate GAP 1):
`applyPersistenceFixpoint b edges fuel` is a genuine fixpoint of `applyAllTImpRules` — applying
one more round changes nothing — whenever the fuel is at least the count of `intUniverseExt φ0`
cells not yet claimed by `b`. Combined with `intUniverseExt_length_le` (a fixed bound depending
only on `φ0`), any fuel `≥ |intUniverseExt φ0|` suffices regardless of `b`'s shape. -/
private lemma applyPersistenceFixpoint_genuine_of_count_le_fuel
    {φ0 : Proposition Atom} {edges : IEdges} (b : IBranch Atom) (fuel : Nat)
    (hb : ∀ x ∈ b, x ∈ intUniverseExt φ0)
    (hfuel : (intUniverseExt φ0).countP (fun sf => !(b.any (· == sf))) ≤ fuel) :
    applyAllTImpRules (applyPersistenceFixpoint b edges fuel) edges
      = applyPersistenceFixpoint b edges fuel := by
  induction fuel generalizing b with
  | zero =>
    have hlen : (applyAllTImpRules b edges).length = b.length := by
      by_contra hne
      have := applyAllTImpRules_count_drop (φ0 := φ0) hb hne
      omega
    have hval : applyAllTImpRules b edges = b :=
      applyAllTImpRules_eq_self_of_length_eq hlen
    simpa [applyPersistenceFixpoint] using hval
  | succ fuel' ih =>
    simp only [applyPersistenceFixpoint]
    split
    · rename_i hlenb
      rw [beq_iff_eq] at hlenb
      exact applyAllTImpRules_eq_self_of_length_eq hlenb
    · rename_i hlenb
      rw [Bool.not_eq_true, beq_eq_false_iff_ne] at hlenb
      have hb' : ∀ x ∈ applyAllTImpRules b edges, x ∈ intUniverseExt φ0 :=
        applyAllTImpRules_subset_ext hb
      have hfuel' : (intUniverseExt φ0).countP
          (fun sf => !((applyAllTImpRules b edges).any (· == sf))) ≤ fuel' := by
        have := applyAllTImpRules_count_drop (φ0 := φ0) hb hlenb
        omega
      exact ih (applyAllTImpRules b edges) hb' hfuel'

omit [Hashable Atom] in
/-- **Phase 4 composition**: pairing `applyPersistenceFixpoint_genuine_of_count_le_fuel` (the
fuel-sufficiency side, landed) with `applyAllTImpRules_copy_complete_of_fixpoint` (the
copy-completeness side, above) gives copy-completeness directly at
`applyPersistenceFixpoint b edges fuel`, for any fuel at least the count of
`intUniverseExt φ0` cells not yet claimed by `b`. This is the pairing the fixpoint-level
copy-completeness lemma was built to supply (`Scheme.lean`'s STOP-gate note, "What survives"
paragraph, generalized here from the ψ-consequence-only observation to every positive
formula). -/
private lemma applyPersistenceFixpoint_copy_complete
    {φ0 : Proposition Atom} {edges : IEdges} {b : IBranch Atom} {fuel : Nat}
    (hb : ∀ x ∈ b, x ∈ intUniverseExt φ0)
    (hfuel : (intUniverseExt φ0).countP (fun sf => !(b.any (· == sf))) ≤ fuel)
    {χ : Proposition Atom} {w w' : Nat}
    (hmem : (⟨.pos, χ, w⟩ : ISF Atom) ∈ applyPersistenceFixpoint b edges fuel)
    (hacc : isAccessible edges w w' = true)
    (hw' : (applyPersistenceFixpoint b edges fuel).any (fun sf => sf.label == w') = true) :
    (⟨.pos, χ, w'⟩ : ISF Atom) ∈ applyPersistenceFixpoint b edges fuel :=
  applyAllTImpRules_copy_complete_of_fixpoint
    (applyPersistenceFixpoint_genuine_of_count_le_fuel b fuel hb hfuel) hmem hacc hw'

/-! ## Engine-Quantifying Lemmas

The four lemmas whose induction skeleton is the engine recursion, stated over the
per-branch-fuel engine (`intExpandBranches`, above; ported from their retired
global-fuel forms). Statements carry the `fuels` parallel list and proofs run by
functional induction on `intExpandBranches.go` (one flat worklist induction replaces
the retired outer-fuel/inner-`go` nesting). -/

omit [Hashable Atom] in
/-- If the per-branch-fuel loop returns `.openBranch b`, then `closurePred b = false`.

Every `.openBranch` return site of `intExpandBranches.go` (per-branch exhaustion at
`f = 0`, saturation, and the defensive `notApplicable` arm) sits inside the `else`
branch of `if closurePred bPers`, so the returned branch is open. -/
private lemma intExpandBranches_openBranch_closed
    (branches : List (IBranch Atom))
    (expandedSets : List (List (ISF Atom)))
    (nextWorlds : List Nat)
    (edgeSets : List IEdges)
    (fuels : List Nat)
    (closurePred : IBranch Atom → Bool)
    (b : IBranch Atom)
    (h : intExpandBranches branches expandedSets nextWorlds edgeSets fuels closurePred
        = .openBranch b) :
    closurePred b = false := by
  rw [intExpandBranches] at h
  suffices key : ∀ (pending : List (IBranch Atom))
      (pendingExp : List (List (ISF Atom)))
      (pendingNW : List Nat)
      (pendingEdges : List IEdges)
      (pendingFuels : List Nat)
      (done : List (IBranch Atom))
      (doneExp : List (List (ISF Atom)))
      (doneNW : List Nat)
      (doneEdges : List IEdges)
      (doneFuels : List Nat),
      intExpandBranches.go closurePred pending pendingExp pendingNW pendingEdges pendingFuels
          done doneExp doneNW doneEdges doneFuels = .openBranch b →
      closurePred b = false from
    key branches expandedSets nextWorlds edgeSets fuels [] [] [] [] [] h
  intro pending pendingExp pendingNW pendingEdges pendingFuels done doneExp doneNW doneEdges
    doneFuels
  induction pending, pendingExp, pendingNW, pendingEdges, pendingFuels, done, doneExp, doneNW,
      doneEdges, doneFuels using intExpandBranches.go.induct (closurePred := closurePred) with
  | case1 =>
    intro hgo
    simp only [intExpandBranches.go] at hgo
    exact absurd hgo (by simp)
  | case2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bPers hcl ih =>
    intro hgo
    rw [intExpandBranches.go.eq_def] at hgo
    simp only [] at hgo
    rw [if_pos hcl] at hgo
    exact ih hgo
  | case3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ bPers hcl =>
    intro hgo
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    injection hgo with heq
    subst heq
    simpa using hcl
  | case4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bPers hcl hstep =>
    intro hgo
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    split at hgo
    · injection hgo with heq
      subst heq
      simpa using hcl
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
  | case5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bPers hcl hstep _ ih =>
    intro hgo
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    split at hgo
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i newForms1 nw1 newEdge1 newExp1 heq
      have hsome := hstep.symm.trans heq
      simp only [Option.some.injEq, Prod.mk.injEq,
        IntRuleResult.linearResult.injEq] at hsome
      obtain ⟨⟨hF, hN, hE⟩, hX⟩ := hsome
      subst hF; subst hN; subst hX; subst hE
      exact ih hgo
    · rename_i branches1 nw1 newExp1 heq
      have hcon := hstep.symm.trans heq
      simp at hcon
    · rename_i snd1 heq
      have hcon := hstep.symm.trans heq
      simp at hcon
  | case6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bPers hcl hstep hwit _ ih =>
    intro hgo
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    split at hgo
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i newForms1 nw1 newEdge1 newExp1 heq
      have hsome := hstep.symm.trans heq
      simp only [Option.some.injEq, Prod.mk.injEq,
        IntRuleResult.linearResult.injEq] at hsome
      obtain ⟨⟨hF, hN, hE⟩, hX⟩ := hsome
      subst hF; subst hN; subst hX; subst hE
      split at hgo
      · rename_i heqE heqH
        exact absurd heqE (by simp)
      · rename_i newE1 hstep1 heqE heqH
        injection heqE with heqE'
        subst heqE'
        split at hgo
        · exact ih hgo
        · rename_i hwit1
          exact absurd (hwit.symm.trans hwit1) (by simp)
    · rename_i branches1 nw1 newExp1 heq
      have hcon := hstep.symm.trans heq
      simp at hcon
    · rename_i snd1 heq
      have hcon := hstep.symm.trans heq
      simp at hcon
  | case7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bPers hcl hstep hwit _ ih =>
    intro hgo
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    split at hgo
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i newForms1 nw1 newEdge1 newExp1 heq
      have hsome := hstep.symm.trans heq
      simp only [Option.some.injEq, Prod.mk.injEq,
        IntRuleResult.linearResult.injEq] at hsome
      obtain ⟨⟨hF, hN, hE⟩, hX⟩ := hsome
      subst hF; subst hN; subst hX; subst hE
      split at hgo
      · rename_i heqE heqH
        exact absurd heqE (by simp)
      · rename_i newE1 hstep1 heqE heqH
        injection heqE with heqE'
        subst heqE'
        split at hgo
        · rename_i x1 hwit1
          exact absurd (hwit.symm.trans hwit1) (by simp)
        · exact ih hgo
    · rename_i branches1 nw1 newExp1 heq
      have hcon := hstep.symm.trans heq
      simp at hcon
    · rename_i snd1 heq
      have hcon := hstep.symm.trans heq
      simp at hcon
  | case8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bPers hcl hstep ih =>
    intro hgo
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    split at hgo
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i newForms1 nw1 newEdge1 newExp1 heq
      have hcon := hstep.symm.trans heq
      simp at hcon
    · rename_i branches1 nw1 newExp1 heq
      have hsome := hstep.symm.trans heq
      simp only [Option.some.injEq, Prod.mk.injEq,
        IntRuleResult.branchingResult.injEq] at hsome
      obtain ⟨⟨hB, hN⟩, hX⟩ := hsome
      subst hB; subst hN; subst hX
      exact ih hgo
    · rename_i snd1 heq
      have hcon := hstep.symm.trans heq
      simp at hcon
  | case9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bPers hcl hstep =>
    intro hgo
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    split at hgo
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i newForms1 nw1 newEdge1 newExp1 heq
      have hcon := hstep.symm.trans heq
      simp at hcon
    · rename_i branches1 nw1 newExp1 heq
      have hcon := hstep.symm.trans heq
      simp at hcon
    · injection hgo with heq
      subst heq
      simpa using hcl
  | case10 _ _ _ _ _ _ _ _ _ _ _ hmismatch ih =>
    intro hgo
    simp only [intExpandBranches.go] at hgo
    exact ih hgo

omit [Hashable Atom] in
/-- If the per-branch-fuel engine returns `closed`, then every input branch is
unsatisfiable. This is the core loop invariant for the soundness theorems below.

The statement carries the `fuels` parallel list (with its length hypothesis); the
proof runs by functional induction on `intExpandBranches.go` (per-arm content:
persistence satisfaction via `applyPersistenceFixpoint_sat`, rule preservation via
`intRule_preserves_sat`, and the `FreshAbove`/`MonotoneEdges` bookkeeping); the
per-branch fuel-exhaustion arm returns `.openBranch`, never `.closed`, so no
fuel-0 `findSome?` analysis is needed. -/
private lemma intExpandBranches_closed_unsat
    {World : Type*} [Preorder World]
    (val : World → Atom → Prop) (botForces : World → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    (closurePred : IBranch Atom → Bool)
    (closed_unsat : ∀ (worldOf : Nat → World) (b : IBranch Atom),
        closurePred b = true → ¬ intBranchSatisfied val botForces worldOf b) :
    ∀ (branches : List (IBranch Atom))
      (expandedSets : List (List (ISF Atom)))
      (nextWorlds : List Nat)
      (edgeSets : List IEdges)
      (fuels : List Nat),
      expandedSets.length = branches.length →
      nextWorlds.length = branches.length →
      edgeSets.length = branches.length →
      fuels.length = branches.length →
      (∀ b edges nw, ((b, edges), nw) ∈ (branches.zip edgeSets).zip nextWorlds →
          FreshAbove b edges nw) →
      intExpandBranches branches expandedSets nextWorlds edgeSets fuels closurePred
          = .closed →
      ∀ (b : IBranch Atom) (edges : IEdges),
          (b, edges) ∈ branches.zip edgeSets →
          ∀ (worldOf : Nat → World),
          MonotoneEdges worldOf edges →
          ¬ intBranchSatisfied val botForces worldOf b := by
  suffices key : ∀ (pending : List (IBranch Atom))
      (pendingExp : List (List (ISF Atom)))
      (pendingNW : List Nat)
      (pendingEdges : List IEdges)
      (pendingFuels : List Nat)
      (done : List (IBranch Atom))
      (doneExp : List (List (ISF Atom)))
      (doneNW : List Nat)
      (doneEdges : List IEdges)
      (doneFuels : List Nat),
      pendingExp.length = pending.length →
      pendingNW.length = pending.length →
      pendingEdges.length = pending.length →
      pendingFuels.length = pending.length →
      doneExp.length = done.length →
      doneNW.length = done.length →
      doneEdges.length = done.length →
      doneFuels.length = done.length →
      (∀ b e nw, ((b, e), nw) ∈ (pending.zip pendingEdges).zip pendingNW →
          FreshAbove b e nw) →
      (∀ b e nw, ((b, e), nw) ∈ (done.zip doneEdges).zip doneNW →
          FreshAbove b e nw) →
      intExpandBranches.go closurePred pending pendingExp pendingNW pendingEdges
          pendingFuels done doneExp doneNW doneEdges doneFuels = .closed →
      ∀ bp edgesP, (bp, edgesP) ∈ pending.zip pendingEdges →
          ∀ (wo : Nat → World), MonotoneEdges wo edgesP →
          ¬ intBranchSatisfied val botForces wo bp from by
    intro branches expandedSets nextWorlds edgeSets fuels hlenE hlenN hlenEd hlenF
        hfresh h b edges hbe worldOf hmono hsat
    rw [intExpandBranches] at h
    exact key branches expandedSets nextWorlds edgeSets fuels [] [] [] [] []
        hlenE hlenN hlenEd hlenF rfl rfl rfl rfl hfresh
        (fun _ _ _ hmem => by simp at hmem) h b edges hbe worldOf hmono hsat
  intro pending pendingExp pendingNW pendingEdges pendingFuels done doneExp doneNW
    doneEdges doneFuels
  induction pending, pendingExp, pendingNW, pendingEdges, pendingFuels, done, doneExp,
      doneNW, doneEdges, doneFuels
      using intExpandBranches.go.induct (closurePred := closurePred) with
  | case1 =>
    intro _ _ _ _ _ _ _ _ _ _ _ bp edgesP hzip_p _ _ _
    simp at hzip_p
  | case2 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT f fT
      bPers hcl ih =>
    intro hlenE hlenN hlenEd hlenF hdlenE hdlenN hdlenEd hdlenF hfreshPend hfreshDone hgo
        bp edgesP hzip_p wo hmono_p hsat_p
    rw [intExpandBranches.go.eq_def] at hgo
    simp only [] at hgo
    rw [if_pos hcl] at hgo
    simp only [List.length_cons] at hlenE hlenN hlenEd hlenF
    replace hlenE : eT.length = bt.length := by omega
    replace hlenN : nwT.length = bt.length := by omega
    replace hlenEd : edgesT.length = bt.length := by omega
    replace hlenF : fT.length = bt.length := by omega
    simp only [List.zip_cons_cons, List.mem_cons] at hzip_p
    have hfreshHead : FreshAbove bh edgesH nwH :=
      hfreshPend bh edgesH nwH (by
        simp only [List.zip_cons_cons, List.mem_cons]
        exact Or.inl trivial)
    have hfreshTail : ∀ b e nw,
        ((b, e), nw) ∈ (bt.zip edgesT).zip nwT → FreshAbove b e nw :=
      fun b e nw h => hfreshPend b e nw (by
        simp only [List.zip_cons_cons, List.mem_cons]
        exact Or.inr h)
    have hfreshAbove_pers : FreshAbove bPers edgesH nwH :=
      freshAbove_applyPersistenceFixpoint bh edgesH nwH f hfreshHead
    rcases hzip_p with ⟨rfl, rfl⟩ | hmem_rest
    · have hsat_pers : intBranchSatisfied val botForces wo bPers :=
        applyPersistenceFixpoint_sat val botForces v_uc bf_uc wo bh edgesH f
          hsat_p hmono_p
      exact closed_unsat wo bPers hcl hsat_pers
    · have hfreshDoneNew : ∀ b e nw,
          ((b, e), nw) ∈ ((done ++ [bPers]).zip (doneEdges ++ [edgesH])).zip
              (doneNW ++ [nwH]) → FreshAbove b e nw := by
        intro b e nw hmem
        have hlen_de : done.length = doneEdges.length := by omega
        have hlen_denz : (done.zip doneEdges).length = doneNW.length := by
          rw [List.length_zip]
          have : min done.length doneEdges.length = done.length :=
            Nat.min_eq_left (by omega)
          omega
        rw [List.zip_append hlen_de, List.zip_append hlen_denz,
            List.mem_append] at hmem
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
                   List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        rcases hmem with h1 | ⟨⟨rfl, rfl⟩, rfl⟩
        · exact hfreshDone b e nw h1
        · exact hfreshAbove_pers
      exact ih hlenE hlenN hlenEd hlenF
          (by simp [hdlenE]) (by simp [hdlenN]) (by simp [hdlenEd]) (by simp [hdlenF])
          hfreshTail hfreshDoneNew hgo bp edgesP hmem_rest wo hmono_p hsat_p
  | case3 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT fT
      bPers hcl =>
    intro _ _ _ _ _ _ _ _ _ _ hgo bp edgesP hzip_p wo hmono_p hsat_p
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    exact absurd hgo (by simp)
  | case4 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT fT f'
      bPers hcl hstep =>
    intro _ _ _ _ _ _ _ _ _ _ hgo bp edgesP hzip_p wo hmono_p hsat_p
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    split at hgo
    · exact absurd hgo (by simp)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
  | case5 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT fT f'
      newForms nw' newExp bPers hcl hstep hstep2 ih =>
    intro hlenE hlenN hlenEd hlenF hdlenE hdlenN hdlenEd hdlenF hfreshPend hfreshDone hgo
        bp edgesP hzip_p wo hmono_p hsat_p
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    split at hgo
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i newForms1 nw1 newEdge1 newExp1 heq
      have hsome := hstep.symm.trans heq
      simp only [Option.some.injEq, Prod.mk.injEq,
        IntRuleResult.linearResult.injEq] at hsome
      obtain ⟨⟨hF, hN, hE⟩, hX⟩ := hsome
      subst hF; subst hN; subst hX; subst hE
      simp only [List.length_cons] at hlenE hlenN hlenEd hlenF
      replace hlenE : eT.length = bt.length := by omega
      replace hlenN : nwT.length = bt.length := by omega
      replace hlenEd : edgesT.length = bt.length := by omega
      replace hlenF : fT.length = bt.length := by omega
      simp only [List.zip_cons_cons, List.mem_cons] at hzip_p
      have hfreshHead : FreshAbove bh edgesH nwH :=
        hfreshPend bh edgesH nwH (by
          simp only [List.zip_cons_cons, List.mem_cons]
          exact Or.inl trivial)
      have hfreshTail : ∀ b e nw,
          ((b, e), nw) ∈ (bt.zip edgesT).zip nwT → FreshAbove b e nw :=
        fun b e nw h => hfreshPend b e nw (by
          simp only [List.zip_cons_cons, List.mem_cons]
          exact Or.inr h)
      have hfreshAbove_pers : FreshAbove bPers edgesH nwH :=
        freshAbove_applyPersistenceFixpoint bh edgesH nwH (f' + 1) hfreshHead
      have hfresh : ∀ sf' ∈ bPers, sf'.label ≠ nwH :=
        fun sf' hmem' => Nat.ne_of_lt (hfreshAbove_pers.1 sf' hmem')
      obtain ⟨sf, hsf_mem, hresult_sf, -⟩ :=
        intStepBranch_some_exists (intStepBranchPrio_some_exists hstep)
      have hnw'eq := intApplyRuleFull_none_nw sf nwH bPers newForms nw' hresult_sf
      have hlabels :=
        intApplyRuleFull_none_labels sf nwH bPers newForms nw' hresult_sf
      have hfreshNew :
          FreshAbove (Branch.extendMany bPers newForms) edgesH nw' := by
        rw [hnw'eq]
        exact freshAbove_extendMany bPers edgesH nwH newForms hfreshAbove_pers
          (fun sf' h' => hlabels sf' h' ▸ hfreshAbove_pers.1 sf hsf_mem)
      have hfreshCombLin : ∀ b e nw,
          ((b, e), nw) ∈ ((done ++ [Branch.extendMany bPers newForms] ++ bt).zip
                          (doneEdges ++ [edgesH] ++ edgesT)).zip
                         (doneNW ++ [nw'] ++ nwT) → FreshAbove b e nw := by
        intro b e nw hmem
        have hlen1 : (done ++ [Branch.extendMany bPers newForms]).length =
                     (doneEdges ++ [edgesH]).length := by simp; omega
        have hlen2 : (done ++ [Branch.extendMany bPers newForms]).length =
                     (doneNW ++ [nw']).length := by simp; omega
        rw [List.zip_append hlen1] at hmem
        have hlen2_adj :
            ((done ++ [Branch.extendMany bPers newForms]).zip
             (doneEdges ++ [edgesH])).length =
             (doneNW ++ [nw']).length := by
          rw [List.length_zip,
              Nat.min_eq_left (Nat.le_of_eq hlen1)]; exact hlen2
        rw [List.zip_append hlen2_adj, List.mem_append] at hmem
        rcases hmem with h_front | h_back
        · have hlen_de : done.length = doneEdges.length := by omega
          have hlen_denz : (done.zip doneEdges).length = doneNW.length := by
            rw [List.length_zip]
            exact (Nat.min_eq_left (by omega)).trans (by omega)
          rw [List.zip_append hlen_de, List.zip_append hlen_denz,
              List.mem_append] at h_front
          simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
                     List.mem_nil_iff, or_false, Prod.mk.injEq] at h_front
          rcases h_front with h1 | ⟨⟨rfl, rfl⟩, rfl⟩
          · exact hfreshDone b e nw h1
          · exact hfreshNew
        · exact hfreshTail b e nw h_back
      rcases hzip_p with ⟨rfl, rfl⟩ | hmem_rest
      · have hsat_pers : intBranchSatisfied val botForces wo bPers :=
          applyPersistenceFixpoint_sat val botForces v_uc bf_uc wo bh edgesH (f' + 1)
            hsat_p hmono_p
        have hpres := intRule_preserves_sat val botForces v_uc bf_uc wo bPers sf
            hsf_mem hsat_pers nwH hfresh
        rw [hresult_sf] at hpres
        obtain ⟨worldOf', hagree, hsat_new, hord⟩ := hpres
        have hmono_new : MonotoneEdges worldOf' edgesH :=
          monotoneEdges_of_agree wo worldOf' edgesH nwH hfreshAbove_pers.2 hagree
            hmono_p
        refine absurd hsat_new
            (ih (by simp [hdlenE, hlenE]) (by simp [hdlenN, hlenN])
              (by simp [hdlenEd, hlenEd]) (by simp [hdlenF, hlenF])
              rfl rfl rfl rfl
              hfreshCombLin (fun _ _ _ hmem => by simp at hmem) hgo
              (Branch.extendMany bPers newForms) edgesH ?_ worldOf' hmono_new)
        rw [List.zip_append (by simp [hdlenEd]), List.mem_append]
        apply Or.inl
        rw [List.zip_append (by omega : done.length = doneEdges.length),
            List.mem_append]
        exact Or.inr (by simp)
      · refine ih (by simp [hdlenE, hlenE]) (by simp [hdlenN, hlenN])
            (by simp [hdlenEd, hlenEd]) (by simp [hdlenF, hlenF])
            rfl rfl rfl rfl
            hfreshCombLin (fun _ _ _ hmem => by simp at hmem) hgo
            bp edgesP ?_ wo hmono_p hsat_p
        rw [List.zip_append (by simp [hdlenEd]), List.mem_append]
        exact Or.inr hmem_rest
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
  | case6 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT fT f'
      newForms nw' newExp newE _x bPers hcl hstep hwit hstep2 ih =>
    intro hlenE hlenN hlenEd hlenF hdlenE hdlenN hdlenEd hdlenF hfreshPend hfreshDone hgo
        bp edgesP hzip_p wo hmono_p hsat_p
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    split at hgo
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i newForms1 nw1 newEdge1 newExp1 heq
      have hsome := hstep.symm.trans heq
      simp only [Option.some.injEq, Prod.mk.injEq,
        IntRuleResult.linearResult.injEq] at hsome
      obtain ⟨⟨hF, hN, hE⟩, hX⟩ := hsome
      subst hF; subst hN; subst hX; subst hE
      split at hgo
      · rename_i heqE heqH
        exact absurd heqE (by simp)
      · rename_i newE1 hstep1 heqE heqH
        injection heqE with heqE'
        subst heqE'
        split at hgo
        · -- Reuse witness found: recursion with `bPers` itself
          simp only [List.length_cons] at hlenE hlenN hlenEd hlenF
          replace hlenE : eT.length = bt.length := by omega
          replace hlenN : nwT.length = bt.length := by omega
          replace hlenEd : edgesT.length = bt.length := by omega
          replace hlenF : fT.length = bt.length := by omega
          simp only [List.zip_cons_cons, List.mem_cons] at hzip_p
          have hfreshHead : FreshAbove bh edgesH nwH :=
            hfreshPend bh edgesH nwH (by
              simp only [List.zip_cons_cons, List.mem_cons]
              exact Or.inl trivial)
          have hfreshTail : ∀ b e nw,
              ((b, e), nw) ∈ (bt.zip edgesT).zip nwT → FreshAbove b e nw :=
            fun b e nw h => hfreshPend b e nw (by
              simp only [List.zip_cons_cons, List.mem_cons]
              exact Or.inr h)
          have hfreshAbove_pers : FreshAbove bPers edgesH nwH :=
            freshAbove_applyPersistenceFixpoint bh edgesH nwH (f' + 1) hfreshHead
          have hfreshCombReuse : ∀ b e nw,
              ((b, e), nw) ∈ ((done ++ [bPers] ++ bt).zip
                              (doneEdges ++ [edgesH] ++ edgesT)).zip
                             (doneNW ++ [nwH] ++ nwT) → FreshAbove b e nw := by
            intro b e nw hmem
            have hlen1 : (done ++ [bPers]).length =
                         (doneEdges ++ [edgesH]).length := by simp; omega
            have hlen2 : (done ++ [bPers]).length =
                         (doneNW ++ [nwH]).length := by simp; omega
            rw [List.zip_append hlen1] at hmem
            have hlen2_adj :
                ((done ++ [bPers]).zip (doneEdges ++ [edgesH])).length =
                 (doneNW ++ [nwH]).length := by
              rw [List.length_zip,
                  Nat.min_eq_left (Nat.le_of_eq hlen1)]; exact hlen2
            rw [List.zip_append hlen2_adj, List.mem_append] at hmem
            rcases hmem with h_front | h_back
            · have hlen_de : done.length = doneEdges.length := by omega
              have hlen_denz : (done.zip doneEdges).length = doneNW.length := by
                rw [List.length_zip]
                exact (Nat.min_eq_left (by omega)).trans (by omega)
              rw [List.zip_append hlen_de, List.zip_append hlen_denz,
                  List.mem_append] at h_front
              simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
                         List.mem_nil_iff, or_false, Prod.mk.injEq] at h_front
              rcases h_front with h1 | ⟨⟨rfl, rfl⟩, rfl⟩
              · exact hfreshDone b e nw h1
              · exact hfreshAbove_pers
            · exact hfreshTail b e nw h_back
          rcases hzip_p with ⟨rfl, rfl⟩ | hmem_rest
          · have hsat_pers : intBranchSatisfied val botForces wo bPers :=
              applyPersistenceFixpoint_sat val botForces v_uc bf_uc wo bh edgesH
                (f' + 1) hsat_p hmono_p
            refine absurd hsat_pers
                (ih (by simp [hdlenE, hlenE]) (by simp [hdlenN, hlenN])
                  (by simp [hdlenEd, hlenEd]) (by simp [hdlenF, hlenF])
                  rfl rfl rfl rfl
                  hfreshCombReuse (fun _ _ _ hmem => by simp at hmem) hgo
                  bPers edgesH ?_ wo hmono_p)
            rw [List.zip_append (by simp [hdlenEd]), List.mem_append]
            apply Or.inl
            rw [List.zip_append (by omega : done.length = doneEdges.length),
                List.mem_append]
            exact Or.inr (by simp)
          · refine ih (by simp [hdlenE, hlenE]) (by simp [hdlenN, hlenN])
                (by simp [hdlenEd, hlenEd]) (by simp [hdlenF, hlenF])
                rfl rfl rfl rfl
                hfreshCombReuse (fun _ _ _ hmem => by simp at hmem) hgo
                bp edgesP ?_ wo hmono_p hsat_p
            rw [List.zip_append (by simp [hdlenEd]), List.mem_append]
            exact Or.inr hmem_rest
        · rename_i hwit1
          exact absurd (hwit.symm.trans hwit1) (by simp)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
  | case7 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT fT f'
      newForms nw' newExp newE bPers hcl hstep hwit hstep2 ih =>
    intro hlenE hlenN hlenEd hlenF hdlenE hdlenN hdlenEd hdlenF hfreshPend hfreshDone hgo
        bp edgesP hzip_p wo hmono_p hsat_p
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    split at hgo
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i newForms1 nw1 newEdge1 newExp1 heq
      have hsome := hstep.symm.trans heq
      simp only [Option.some.injEq, Prod.mk.injEq,
        IntRuleResult.linearResult.injEq] at hsome
      obtain ⟨⟨hF, hN, hE⟩, hX⟩ := hsome
      subst hF; subst hN; subst hX; subst hE
      split at hgo
      · rename_i heqE heqH
        exact absurd heqE (by simp)
      · rename_i newE1 hstep1 heqE heqH
        injection heqE with heqE'
        subst heqE'
        split at hgo
        · rename_i x1 hwit1
          exact absurd (hwit.symm.trans hwit1) (by simp)
        · -- No reusable ancestor: fresh world creation
          simp only [List.length_cons] at hlenE hlenN hlenEd hlenF
          replace hlenE : eT.length = bt.length := by omega
          replace hlenN : nwT.length = bt.length := by omega
          replace hlenEd : edgesT.length = bt.length := by omega
          replace hlenF : fT.length = bt.length := by omega
          simp only [List.zip_cons_cons, List.mem_cons] at hzip_p
          have hfreshHead : FreshAbove bh edgesH nwH :=
            hfreshPend bh edgesH nwH (by
              simp only [List.zip_cons_cons, List.mem_cons]
              exact Or.inl trivial)
          have hfreshTail : ∀ b e nw,
              ((b, e), nw) ∈ (bt.zip edgesT).zip nwT → FreshAbove b e nw :=
            fun b e nw h => hfreshPend b e nw (by
              simp only [List.zip_cons_cons, List.mem_cons]
              exact Or.inr h)
          have hfreshAbove_pers : FreshAbove bPers edgesH nwH :=
            freshAbove_applyPersistenceFixpoint bh edgesH nwH (f' + 1) hfreshHead
          have hfresh : ∀ sf' ∈ bPers, sf'.label ≠ nwH :=
            fun sf' hmem' => Nat.ne_of_lt (hfreshAbove_pers.1 sf' hmem')
          obtain ⟨sf, hsf_mem, hresult_sf, -⟩ :=
            intStepBranch_some_exists (intStepBranchPrio_some_exists hstep)
          obtain ⟨he, hnw'eq, hlabels⟩ :=
            intApplyRuleFull_some_info sf nwH bPers newForms nw' newE hresult_sf
          have hfreshNew : FreshAbove (Branch.extendMany bPers newForms)
              (edgesH ++ [newE]) nw' := by
            rw [he, hnw'eq]
            exact freshAbove_world_create bPers edgesH nwH sf.label newForms
              hfreshAbove_pers (hfreshAbove_pers.1 sf hsf_mem)
              (fun sf' h' => Nat.le_of_eq (hlabels sf' h'))
          have hfreshCombCreate : ∀ b e nw,
              ((b, e), nw) ∈ ((done ++ [Branch.extendMany bPers newForms] ++ bt).zip
                              (doneEdges ++ [edgesH ++ [newE]] ++ edgesT)).zip
                             (doneNW ++ [nw'] ++ nwT) → FreshAbove b e nw := by
            intro b e nw hmem
            have hlen1 : (done ++ [Branch.extendMany bPers newForms]).length =
                         (doneEdges ++ [edgesH ++ [newE]]).length := by simp; omega
            have hlen2 : (done ++ [Branch.extendMany bPers newForms]).length =
                         (doneNW ++ [nw']).length := by simp; omega
            rw [List.zip_append hlen1] at hmem
            have hlen2_adj :
                ((done ++ [Branch.extendMany bPers newForms]).zip
                 (doneEdges ++ [edgesH ++ [newE]])).length =
                 (doneNW ++ [nw']).length := by
              rw [List.length_zip,
                  Nat.min_eq_left (Nat.le_of_eq hlen1)]; exact hlen2
            rw [List.zip_append hlen2_adj, List.mem_append] at hmem
            rcases hmem with h_front | h_back
            · have hlen_de : done.length = doneEdges.length := by omega
              have hlen_denz : (done.zip doneEdges).length = doneNW.length := by
                rw [List.length_zip]
                exact (Nat.min_eq_left (by omega)).trans (by omega)
              rw [List.zip_append hlen_de, List.zip_append hlen_denz,
                  List.mem_append] at h_front
              simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
                         List.mem_nil_iff, or_false, Prod.mk.injEq] at h_front
              rcases h_front with h1 | ⟨⟨rfl, rfl⟩, rfl⟩
              · exact hfreshDone b e nw h1
              · exact hfreshNew
            · exact hfreshTail b e nw h_back
          rcases hzip_p with ⟨rfl, rfl⟩ | hmem_rest
          · have hsat_pers : intBranchSatisfied val botForces wo bPers :=
              applyPersistenceFixpoint_sat val botForces v_uc bf_uc wo bh edgesH
                (f' + 1) hsat_p hmono_p
            have hpres := intRule_preserves_sat val botForces v_uc bf_uc wo bPers sf
                hsf_mem hsat_pers nwH hfresh
            rw [hresult_sf] at hpres
            obtain ⟨worldOf', hagree, hsat_new, hord⟩ := hpres
            have hmono_new : MonotoneEdges worldOf' (edgesH ++ [newE]) := by
              rw [he]
              simp only [he] at hord
              have hwo'_eq : worldOf' = Function.update wo nwH (worldOf' nwH) := by
                funext k
                by_cases hk : k = nwH
                · subst hk; simp
                · rw [Function.update_of_ne hk, hagree k hk]
              rw [hwo'_eq]
              exact monotoneEdges_update wo edgesH nwH sf.label (worldOf' nwH)
                  (fun par h =>
                    absurd (hfreshAbove_pers.2 nwH par h).1 (Nat.lt_irrefl _))
                  (fun ch h =>
                    absurd (hfreshAbove_pers.2 ch nwH h).2 (Nat.lt_irrefl _))
                  (Nat.ne_of_lt (hfreshAbove_pers.1 sf hsf_mem))
                  hmono_p hord
            refine absurd hsat_new
                (ih (by simp [hdlenE, hlenE]) (by simp [hdlenN, hlenN])
                  (by simp [hdlenEd, hlenEd]) (by simp [hdlenF, hlenF])
                  rfl rfl rfl rfl
                  hfreshCombCreate (fun _ _ _ hmem => by simp at hmem) hgo
                  (Branch.extendMany bPers newForms) (edgesH ++ [newE]) ?_
                  worldOf' hmono_new)
            rw [List.zip_append (by simp [hdlenEd]), List.mem_append]
            apply Or.inl
            rw [List.zip_append (by omega : done.length = doneEdges.length),
                List.mem_append]
            exact Or.inr (by simp)
          · refine ih (by simp [hdlenE, hlenE]) (by simp [hdlenN, hlenN])
                (by simp [hdlenEd, hlenEd]) (by simp [hdlenF, hlenF])
                rfl rfl rfl rfl
                hfreshCombCreate (fun _ _ _ hmem => by simp at hmem) hgo
                bp edgesP ?_ wo hmono_p hsat_p
            rw [List.zip_append (by simp [hdlenEd]), List.mem_append]
            exact Or.inr hmem_rest
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
  | case8 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT fT f'
      branches' nw' newExp bPers hcl hstep ih =>
    intro hlenE hlenN hlenEd hlenF hdlenE hdlenN hdlenEd hdlenF hfreshPend hfreshDone hgo
        bp edgesP hzip_p wo hmono_p hsat_p
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    split at hgo
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i heq
      have hcon := hstep.symm.trans heq
      simp at hcon
    · rename_i branches1 nw1 newExp1 heq
      have hsome := hstep.symm.trans heq
      simp only [Option.some.injEq, Prod.mk.injEq,
        IntRuleResult.branchingResult.injEq] at hsome
      obtain ⟨⟨hB, hN⟩, hX⟩ := hsome
      subst hB; subst hN; subst hX
      simp only [List.length_cons] at hlenE hlenN hlenEd hlenF
      replace hlenE : eT.length = bt.length := by omega
      replace hlenN : nwT.length = bt.length := by omega
      replace hlenEd : edgesT.length = bt.length := by omega
      replace hlenF : fT.length = bt.length := by omega
      simp only [List.zip_cons_cons, List.mem_cons] at hzip_p
      have hfreshHead : FreshAbove bh edgesH nwH :=
        hfreshPend bh edgesH nwH (by
          simp only [List.zip_cons_cons, List.mem_cons]
          exact Or.inl trivial)
      have hfreshTail : ∀ b e nw,
          ((b, e), nw) ∈ (bt.zip edgesT).zip nwT → FreshAbove b e nw :=
        fun b e nw h => hfreshPend b e nw (by
          simp only [List.zip_cons_cons, List.mem_cons]
          exact Or.inr h)
      have hfreshAbove_pers : FreshAbove bPers edgesH nwH :=
        freshAbove_applyPersistenceFixpoint bh edgesH nwH (f' + 1) hfreshHead
      have hfresh : ∀ sf' ∈ bPers, sf'.label ≠ nwH :=
        fun sf' hmem' => Nat.ne_of_lt (hfreshAbove_pers.1 sf' hmem')
      obtain ⟨sf, hsf_mem, hresult_sf, -⟩ :=
        intStepBranch_some_exists (intStepBranchPrio_some_exists hstep)
      have hnw'eq : nw' = nwH :=
        intApplyRuleFull_branching_nw sf nwH bPers branches' nw' hresult_sf
      have hfreshBr : ∀ br ∈ branches',
          FreshAbove (Branch.extendMany bPers br) edgesH nwH := by
        intro br hbr
        have hlabels := intApplyRuleFull_branching_labels sf nwH bPers branches' nw'
            hresult_sf br hbr
        exact freshAbove_extendMany bPers edgesH nwH br hfreshAbove_pers
            (fun sf' hmem' => hlabels sf' hmem' ▸ hfreshAbove_pers.1 sf hsf_mem)
      have hfreshCombBr : ∀ b e nw,
          ((b, e), nw) ∈
            ((done ++ branches'.map (Branch.extendMany bPers ·) ++ bt).zip
             (doneEdges ++ branches'.map (fun _ => edgesH) ++ edgesT)).zip
            (doneNW ++ branches'.map (fun _ => nw') ++ nwT) →
            FreshAbove b e nw := by
        intro b e nw hmem
        have hlen1 : (done ++ branches'.map (Branch.extendMany bPers ·)).length =
                     (doneEdges ++ branches'.map (fun _ => edgesH)).length := by
          simp; omega
        have hlen2 : (done ++ branches'.map (Branch.extendMany bPers ·)).length =
                     (doneNW ++ branches'.map (fun _ => nw')).length := by
          simp; omega
        rw [List.zip_append hlen1] at hmem
        have hlen2_adj :
            ((done ++ branches'.map (Branch.extendMany bPers ·)).zip
             (doneEdges ++ branches'.map (fun _ => edgesH))).length =
             (doneNW ++ branches'.map (fun _ => nw')).length := by
          rw [List.length_zip,
              Nat.min_eq_left (Nat.le_of_eq hlen1)]; exact hlen2
        rw [List.zip_append hlen2_adj, List.mem_append] at hmem
        rcases hmem with h_front | h_back
        · have hlen_de : done.length = doneEdges.length := by omega
          have hlen_denz : (done.zip doneEdges).length = doneNW.length := by
            rw [List.length_zip]
            exact (Nat.min_eq_left (by omega)).trans (by omega)
          rw [List.zip_append hlen_de, List.zip_append hlen_denz,
              List.mem_append] at h_front
          rcases h_front with h1 | h1
          · exact hfreshDone b e nw h1
          · obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_getElem.mp h1
            simp only [List.getElem_zip, List.getElem_map] at hi_eq
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hi_eq
            have hi_br : i < branches'.length := by
              simp only [List.length_zip, List.length_map, Nat.min_self] at hi_lt
              exact hi_lt
            exact hnw'eq ▸ hfreshBr branches'[i] (List.getElem_mem hi_br)
        · exact hfreshTail b e nw h_back
      rcases hzip_p with ⟨rfl, rfl⟩ | hmem_rest
      · have hsat_pers : intBranchSatisfied val botForces wo bPers :=
          applyPersistenceFixpoint_sat val botForces v_uc bf_uc wo bh edgesH (f' + 1)
            hsat_p hmono_p
        have hpres := intRule_preserves_sat val botForces v_uc bf_uc wo bPers sf
            hsf_mem hsat_pers nwH hfresh
        rw [hresult_sf] at hpres
        obtain ⟨br, hbr_mem, hsat_br⟩ := hpres
        have hmem : (Branch.extendMany bPers br, edgesH) ∈
            (done ++ branches'.map (Branch.extendMany bPers ·) ++ bt).zip
            (doneEdges ++ branches'.map (fun _ => edgesH) ++ edgesT) := by
          rw [List.zip_append (by simp [hdlenEd])]
          simp only [List.mem_append]
          refine Or.inl ?_
          rw [List.zip_append (by exact hdlenEd.symm)]
          simp only [List.mem_append]
          refine Or.inr ?_
          obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_getElem.mp hbr_mem
          apply List.mem_iff_getElem.mpr
          exact ⟨i, by simp [hi_lt],
            by simp [List.getElem_zip, List.getElem_map, hi_eq]⟩
        exact ih (by simp [hdlenE, hlenE]) (by simp [hdlenN, hlenN])
            (by simp [hdlenEd, hlenEd]) (by simp [hdlenF, hlenF])
            rfl rfl rfl rfl
            hfreshCombBr (fun _ _ _ hmem' => by simp at hmem') hgo
            (Branch.extendMany bPers br) edgesH hmem wo hmono_p hsat_br
      · refine ih (by simp [hdlenE, hlenE]) (by simp [hdlenN, hlenN])
            (by simp [hdlenEd, hlenEd]) (by simp [hdlenF, hlenF])
            rfl rfl rfl rfl
            hfreshCombBr (fun _ _ _ hmem => by simp at hmem) hgo
            bp edgesP ?_ wo hmono_p hsat_p
        rw [List.zip_append (by simp [hdlenEd]), List.mem_append]
        exact Or.inr hmem_rest
    · rename_i heq
      have hcon := hstep.symm.trans heq
      simp at hcon
  | case9 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT fT f'
      snd bPers hcl hstep =>
    intro _ _ _ _ _ _ _ _ _ _ hgo bp edgesP hzip_p wo hmono_p hsat_p
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    split at hgo
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i heq
      have hcon := hstep.symm.trans heq
      simp at hcon
    · rename_i heq
      have hcon := hstep.symm.trans heq
      simp at hcon
    · exact absurd hgo (by simp)
  | case10 done doneExp doneNW doneEdges doneFuels head restBs pExp pNW pEdges pFuels
      hmismatch ih =>
    intro hlenE hlenN hlenEd hlenF _ _ _ _ _ _ hgo bp edgesP hzip_p wo hmono_p hsat_p
    cases hpE : pExp with
    | nil =>
      rw [hpE] at hlenE
      simp only [List.length_nil, List.length_cons] at hlenE
      omega
    | cons e restEs =>
      cases hpN : pNW with
      | nil =>
        rw [hpN] at hlenN
        simp only [List.length_nil, List.length_cons] at hlenN
        omega
      | cons nw restNW =>
        cases hpEd : pEdges with
        | nil =>
          rw [hpEd] at hlenEd
          simp only [List.length_nil, List.length_cons] at hlenEd
          omega
        | cons edges restEdges =>
          cases hpF : pFuels with
          | nil =>
            rw [hpF] at hlenF
            simp only [List.length_nil, List.length_cons] at hlenF
            omega
          | cons f restFs =>
            exact absurd
              (hmismatch e restEs nw restNW edges restEdges f restFs hpE hpN hpEd hpF)
              id

/-! ## Tableau Soundness -/

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
        [intFuelExt φ] S.closurePred = .closed) :
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
      (fun {_ _} _ hf => absurd hf id)
      S.closurePred
      (fun (worldOf' : Nat → World) (b : IBranch Atom) hcl =>
          closed_unsat val worldOf' b hcl)
      [[⟨.neg, φ, 0⟩]] [[]] [1] [[]] [intFuelExt φ]
      (by rfl) (by rfl) (by rfl) (by rfl)
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

/-- **Intuitionistic Tableau Soundness**: If `intuitionisticTableau φ = closed`, then
`φ` is intuitionistically valid (`IValid φ`).

Instantiates `tableau_sound` at `intScheme` with `intClosed_unsatisfiable`
(`Soundness.lean`); `intuitionisticTableau φ` is definitionally the engine at the
initial singleton worklist with fuel list `[intFuelExt φ]`. -/
theorem intuitionisticTableau_sound (φ : Proposition Atom)
    (h : intuitionisticTableau φ = .closed) : IValid φ :=
  tableau_sound intScheme
    (fun val worldOf b hcl => intClosed_unsatisfiable val worldOf b hcl) φ h

omit [Hashable Atom] in
/-- **Minimal Tableau Soundness**: If `minimalTableau φ = closed`, then `MValid φ`.

The proof instantiates `intExpandBranches_closed_unsat` with `isMinimallyClosed` and
`minClosed_unsatisfiable`, mirroring `intuitionisticTableau_sound` exactly. The key
differences from the intuitionistic case:
- `botForces` is arbitrary (from the MValid quantifier), so this cannot route through
  `tableau_sound` (whose conclusion pins `botForces = fun _ => False`).
- `isMinimallyClosed` (all complementary pairs) is used instead of
  `isIntuitionisticallyClosed`. -/
theorem minimalTableau_sound (φ : Proposition Atom)
    (h : minimalTableau φ = .closed) : MValid φ := by
  intro World _ val botForces v_uc bf_uc w₀
  by_contra hneg
  let worldOf : Nat → World := fun _ => w₀
  have hsat : intBranchSatisfied val botForces worldOf [⟨.neg, φ, 0⟩] := by
    intro sf hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    subst hmem
    exact ⟨fun h' => absurd h' (Sign.noConfusion), fun _ => hneg⟩
  simp only [minimalTableau] at h
  apply intExpandBranches_closed_unsat val botForces v_uc bf_uc
    isMinimallyClosed
    (fun worldOf' b hcl => minClosed_unsatisfiable val botForces worldOf' b hcl)
    [[⟨.neg, φ, 0⟩]] [[]] [1] [[]] [intFuelExt φ]
    (by rfl) (by rfl) (by rfl) (by rfl)
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

omit [Hashable Atom] in
/-- Every formula in every initial branch appears in the open branch returned by
`intExpandBranches`. This shows that F(φ)@0, present in the initial branch, is still
on the open countermodel branch.

Both `applyPersistenceFixpoint` and `Branch.extendMany` only prepend/append formulas,
so membership is monotone throughout the expansion; the per-branch fuel-exhaustion arm
returns the persistence-closed head branch, which inherits the head's membership. -/
private lemma intExpandBranches_openBranch_initial_mem (sf : ISF Atom) :
    ∀ (branches : List (IBranch Atom))
      (expandedSets : List (List (ISF Atom)))
      (nextWorlds : List Nat)
      (edgeSets : List IEdges)
      (fuels : List Nat)
      (closurePred : IBranch Atom → Bool),
      (∀ b₀ ∈ branches, sf ∈ b₀) →
      ∀ b, intExpandBranches branches expandedSets nextWorlds edgeSets fuels closurePred
          = .openBranch b →
        sf ∈ b := by
  intro branches expandedSets nextWorlds edgeSets fuels closurePred hAll b h
  rw [intExpandBranches] at h
  suffices key : ∀ (pending : List (IBranch Atom))
      (pendingExp : List (List (ISF Atom)))
      (pendingNW : List Nat)
      (pendingEdges : List IEdges)
      (pendingFuels : List Nat)
      (done : List (IBranch Atom))
      (doneExp : List (List (ISF Atom)))
      (doneNW : List Nat)
      (doneEdges : List IEdges)
      (doneFuels : List Nat),
      (∀ bp ∈ pending, sf ∈ bp) →
      (∀ bd ∈ done, sf ∈ bd) →
      intExpandBranches.go closurePred pending pendingExp pendingNW pendingEdges
          pendingFuels done doneExp doneNW doneEdges doneFuels = .openBranch b →
      sf ∈ b from
    key branches expandedSets nextWorlds edgeSets fuels [] [] [] [] []
        hAll (by simp) h
  intro pending pendingExp pendingNW pendingEdges pendingFuels done doneExp doneNW
    doneEdges doneFuels
  induction pending, pendingExp, pendingNW, pendingEdges, pendingFuels, done, doneExp,
      doneNW, doneEdges, doneFuels
      using intExpandBranches.go.induct (closurePred := closurePred) with
  | case1 =>
    intro _ _ hgo
    simp only [intExpandBranches.go] at hgo
    exact absurd hgo (by simp)
  | case2 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT f fT
      bPers hcl ih =>
    intro hPend hDone hgo
    rw [intExpandBranches.go.eq_def] at hgo
    simp only [] at hgo
    rw [if_pos hcl] at hgo
    have hbPers_sf : sf ∈ bPers :=
      applyPersistenceFixpoint_mem_preserved bh edgesH f sf (hPend bh List.mem_cons_self)
    refine ih (fun bp hbp => hPend bp (List.mem_cons_of_mem _ hbp)) ?_ hgo
    intro bd hbd
    simp only [List.mem_append, List.mem_singleton] at hbd
    rcases hbd with h1 | rfl
    · exact hDone bd h1
    · exact hbPers_sf
  | case3 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT fT
      bPers hcl =>
    intro hPend hDone hgo
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    injection hgo with heq
    subst heq
    exact applyPersistenceFixpoint_mem_preserved bh edgesH 0 sf
      (hPend bh List.mem_cons_self)
  | case4 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT fT f'
      bPers hcl hstep =>
    intro hPend hDone hgo
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    split at hgo
    · injection hgo with heq
      subst heq
      exact applyPersistenceFixpoint_mem_preserved bh edgesH (f' + 1) sf
        (hPend bh List.mem_cons_self)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
  | case5 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT fT f'
      newForms nw' newExp bPers hcl hstep hstep2 ih =>
    intro hPend hDone hgo
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    have hbPers_sf : sf ∈ bPers :=
      applyPersistenceFixpoint_mem_preserved bh edgesH (f' + 1) sf
        (hPend bh List.mem_cons_self)
    split at hgo
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i newForms1 nw1 newEdge1 newExp1 heq
      have hsome := hstep.symm.trans heq
      simp only [Option.some.injEq, Prod.mk.injEq,
        IntRuleResult.linearResult.injEq] at hsome
      obtain ⟨⟨hF, hN, hE⟩, hX⟩ := hsome
      subst hF; subst hN; subst hX; subst hE
      refine ih ?_ (by simp) hgo
      intro b₀ hb₀
      simp only [List.mem_append, List.mem_singleton] at hb₀
      rcases hb₀ with (hd | rfl) | hbt
      · exact hDone b₀ hd
      · simp only [Branch.extendMany, List.mem_append]
        exact Or.inr hbPers_sf
      · exact hPend b₀ (List.mem_cons_of_mem _ hbt)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
  | case6 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT fT f'
      newForms nw' newExp newE _x bPers hcl hstep hwit hstep2 ih =>
    intro hPend hDone hgo
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    have hbPers_sf : sf ∈ bPers :=
      applyPersistenceFixpoint_mem_preserved bh edgesH (f' + 1) sf
        (hPend bh List.mem_cons_self)
    split at hgo
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i newForms1 nw1 newEdge1 newExp1 heq
      have hsome := hstep.symm.trans heq
      simp only [Option.some.injEq, Prod.mk.injEq,
        IntRuleResult.linearResult.injEq] at hsome
      obtain ⟨⟨hF, hN, hE⟩, hX⟩ := hsome
      subst hF; subst hN; subst hX; subst hE
      split at hgo
      · rename_i heqE heqH
        exact absurd heqE (by simp)
      · rename_i newE1 hstep1 heqE heqH
        injection heqE with heqE'
        subst heqE'
        split at hgo
        · refine ih ?_ (by simp) hgo
          intro b₀ hb₀
          simp only [List.mem_append, List.mem_singleton] at hb₀
          rcases hb₀ with (hd | rfl) | hbt
          · exact hDone b₀ hd
          · exact hbPers_sf
          · exact hPend b₀ (List.mem_cons_of_mem _ hbt)
        · rename_i hwit1
          exact absurd (hwit.symm.trans hwit1) (by simp)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
  | case7 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT fT f'
      newForms nw' newExp newE bPers hcl hstep hwit hstep2 ih =>
    intro hPend hDone hgo
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    have hbPers_sf : sf ∈ bPers :=
      applyPersistenceFixpoint_mem_preserved bh edgesH (f' + 1) sf
        (hPend bh List.mem_cons_self)
    split at hgo
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i newForms1 nw1 newEdge1 newExp1 heq
      have hsome := hstep.symm.trans heq
      simp only [Option.some.injEq, Prod.mk.injEq,
        IntRuleResult.linearResult.injEq] at hsome
      obtain ⟨⟨hF, hN, hE⟩, hX⟩ := hsome
      subst hF; subst hN; subst hX; subst hE
      split at hgo
      · rename_i heqE heqH
        exact absurd heqE (by simp)
      · rename_i newE1 hstep1 heqE heqH
        injection heqE with heqE'
        subst heqE'
        split at hgo
        · rename_i x1 hwit1
          exact absurd (hwit.symm.trans hwit1) (by simp)
        · refine ih ?_ (by simp) hgo
          intro b₀ hb₀
          simp only [List.mem_append, List.mem_singleton] at hb₀
          rcases hb₀ with (hd | rfl) | hbt
          · exact hDone b₀ hd
          · simp only [Branch.extendMany, List.mem_append]
            exact Or.inr hbPers_sf
          · exact hPend b₀ (List.mem_cons_of_mem _ hbt)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
  | case8 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT fT f'
      branches' nw' newExp bPers hcl hstep ih =>
    intro hPend hDone hgo
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    have hbPers_sf : sf ∈ bPers :=
      applyPersistenceFixpoint_mem_preserved bh edgesH (f' + 1) sf
        (hPend bh List.mem_cons_self)
    split at hgo
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i heq
      have hcon := hstep.symm.trans heq
      simp at hcon
    · rename_i branches1 nw1 newExp1 heq
      have hsome := hstep.symm.trans heq
      simp only [Option.some.injEq, Prod.mk.injEq,
        IntRuleResult.branchingResult.injEq] at hsome
      obtain ⟨⟨hB, hN⟩, hX⟩ := hsome
      subst hB; subst hN; subst hX
      refine ih ?_ (by simp) hgo
      intro b₀ hb₀
      simp only [List.mem_append, List.mem_map] at hb₀
      rcases hb₀ with (hd | ⟨x, _, rfl⟩) | hbt
      · exact hDone b₀ hd
      · simp only [Branch.extendMany, List.mem_append]
        exact Or.inr hbPers_sf
      · exact hPend b₀ (List.mem_cons_of_mem _ hbt)
    · rename_i heq
      have hcon := hstep.symm.trans heq
      simp at hcon
  | case9 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT fT f'
      snd bPers hcl hstep =>
    intro hPend hDone hgo
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    split at hgo
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i heq
      have hcon := hstep.symm.trans heq
      simp at hcon
    · rename_i heq
      have hcon := hstep.symm.trans heq
      simp at hcon
    · injection hgo with heq
      subst heq
      exact applyPersistenceFixpoint_mem_preserved bh edgesH (f' + 1) sf
        (hPend bh List.mem_cons_self)
  | case10 done doneExp doneNW doneEdges doneFuels head restBs pExp pNW pEdges pFuels
      hmismatch ih =>
    intro hPend hDone hgo
    simp only [intExpandBranches.go] at hgo
    exact ih (fun bp hbp => hPend bp (List.mem_cons_of_mem _ hbp)) hDone hgo

/-- **Raw-edge positive-formula persistence** (plan Phase 7). **Update: this IS now sufficient**
to instantiate `truthLemma`'s `hpers` hypothesis when `edges := rawEdges` -- `truthLemma`'s
frame is a PARAMETER, not tied to the AUGMENTED `augSets` witness, and DP-5's T-imp case is
proved directly from `hpers` (see `truthLemma`'s T-imp case and the `sat_timp` discharge
STOP-gate note above it). The "NOT sufficient alone" framing this docstring originally carried
was accurate only for the (now-superseded) assumption that `truthLemma` would always be
instantiated at the augmented frame; it remains accurate for the AUGMENTED-edge version of
persistence specifically, which is REFUTED at that frame
(`CslibTests/BetaSplitRefutation.lean`) rather than merely unbuilt. Originally recorded so
`intExpandBranches_openBranch_sat`'s conclusion carries at least the raw-edge half of the
persistence invariant, with the augmented-edge version (`IPosPersist`, Phase 11) intended to
export once the reuse-time containment (Phase 8) and post-reuse closure lemma (Phase 9/10)
land -- that augmented-edge route is now known-refuted rather than pending, per
`openBranch_countermodel`'s frame-adequacy table.

The `hw'` side condition (some entry already present at `w'`) matches
`applyPersistenceFixpoint_copy_complete`'s own hypothesis exactly (Phase 4, landed
sorry-free): it is needed because the copy channel only plants a copy at worlds already
present on the branch, not at hypothetically-accessible-but-nonexistent labels. -/
private def IPosPersistRaw (edges : IEdges) (b : IBranch Atom) : Prop :=
  ∀ (χ : Proposition Atom) (w w' : Nat), isAccessible edges w w' = true →
    (⟨.pos, χ, w⟩ : ISF Atom) ∈ b → b.any (fun sf => sf.label == w') = true →
    (⟨.pos, χ, w'⟩ : ISF Atom) ∈ b

/-! ### Freeze step lemma (plan Phase 5)

`IFrozenBelow` (`Expansion.lean`) is the checkpoint precondition: once
`intStepBranchPrioFirstPass` returns `none` at `(bPers, e, nw)`, `bPers` is `IFrozenBelow nw e`.
This section supplies the STEP-level half of the freeze argument report §5.4 calls for: given
`IFrozenBelow w0 e b` for a threshold `w0 ≤ nw` (not necessarily the literal checkpoint value --
the invariant is stable, see `IFrozenBelow`'s docstring), a single `intStepBranchPrio` step can
only write new content at labels `≥ w0`. This is the "alpha/beta processing at that label is
impossible" half of the report's mechanism (Phase 5's investigation note, point 3(a)); it does
NOT yet cover the persistence-copy half (point 3(b), which additionally needs `IPosPersistRaw`
and is deferred to Phase 6, where it composes with the main induction's already-threaded
invariants rather than needing a second bespoke induction here). -/

/-- The labels an intuitionistic rule-application result can newly write are all `≥ w0`:
`.linearResult`'s `newForms` for the alpha/world-creating case, every branch's formulas for the
`.branchingResult` beta case, vacuously `True` for `.notApplicable`. -/
private def IResultLabelsGe (w0 : Nat) : IntRuleResult Atom → Prop
  | .linearResult newForms _ _ => ∀ sf' ∈ newForms, w0 ≤ sf'.label
  | .branchingResult branches' _ => ∀ br ∈ branches', ∀ sf' ∈ br, w0 ≤ sf'.label
  | .notApplicable => True

/-- The labels an intuitionistic rule-application result can newly write are all EXACTLY `l`:
the non-world-creating shape (mirrors `IResultLabelsGe` but with equality). -/
private def IResultLabelsEq (l : Nat) : IntRuleResult Atom → Prop
  | .linearResult newForms _ _ => ∀ sf' ∈ newForms, sf'.label = l
  | .branchingResult branches' _ => ∀ br ∈ branches', ∀ sf' ∈ br, sf'.label = l
  | .notApplicable => True

omit [DecidableEq Atom] [Hashable Atom] in
private lemma IResultLabelsEq_imp_Ge {l w0 : Nat} (hle : w0 ≤ l) {result : IntRuleResult Atom}
    (heq : IResultLabelsEq l result) : IResultLabelsGe w0 result := by
  cases result with
  | notApplicable => trivial
  | linearResult newForms nw' ed => intro x hx; rw [heq x hx]; exact hle
  | branchingResult branches' nw' => intro br hbr x hx; rw [heq br hbr x hx]; exact hle

omit [DecidableEq Atom] [Hashable Atom] in
/-- Non-world-creating `intApplyRuleFull` results write only at `sf.label` itself: covers every
shape but `.neg, .imp` (the world-creating one, whose output goes entirely to the fresh
`nextWorld` instead -- see `IFrozenBelow_intStepBranchPrio_ge`'s other case). Purely mechanical:
each of the five surviving shapes (`.pos/.neg` × `.and`/`.or`, plus `.pos, .imp`) constructs its
output list literally at `sf.label`; the six ruleless shapes (atoms, `⊥`) are `.notApplicable`,
vacuously satisfying `IResultLabelsEq`. -/
private lemma intApplyRuleFull_labels_eq_of_not_worldCreating
    {sf : ISF Atom} {nw : Nat} {b : IBranch Atom} (hwc : isWorldCreating sf ≠ true) :
    IResultLabelsEq sf.label (intApplyRuleFull sf nw b) := by
  rcases sf with ⟨s, f, l⟩
  simp only [isWorldCreating] at hwc
  cases s <;> cases f <;> simp_all [intApplyRuleFull, IResultLabelsEq]

omit [Hashable Atom] in
/-- **Freeze step** (plan Phase 5): once `IFrozenBelow w0 e b` holds and `w0 ≤ nw`, a single
`intStepBranchPrio` step's output is `IResultLabelsGe w0`. The selected formula `sf`
(`intStepBranchPrio_some_exists`) is either already `w0`-safe (`w0 ≤ sf.label`, in which case
`intApplyRuleFull_labels_eq_of_not_worldCreating` pins every non-world-creating rule's output at
`sf.label`, hence `≥ w0`) or world-creating (in which case `intFImpRule`'s output is entirely at
the fresh `nw ≥ w0`, regardless of `sf.label`); `sf ∈ e` is excluded by `IStepShape`, and `sf`
being neither world-creating nor `w0`-safe nor `e`-recorded would force `intApplyRuleFull sf nw
b = .notApplicable` (`IFrozenBelow`'s third disjunct via `intApplyRuleFull_notApplicable_iff`),
contradicting `intStepBranchPrio_result_ne_notApplicable`. -/
private lemma IFrozenBelow_intStepBranchPrio_ge
    {b : IBranch Atom} {e : List (ISF Atom)} {w0 nw : Nat} (hnw : w0 ≤ nw)
    (hfrz : IFrozenBelow w0 e b)
    {result : IntRuleResult Atom} {newExp : List (ISF Atom)}
    (hstep : intStepBranchPrio b e nw = some (result, newExp)) :
    IResultLabelsGe w0 result := by
  obtain ⟨sf, hsfb, hsfne, hint, -⟩ := intStepBranchPrio_some_exists hstep
  have hresne : result ≠ .notApplicable := intStepBranchPrio_result_ne_notApplicable hstep
  by_cases hwc : isWorldCreating sf = true
  · -- World-creating: `sf = ⟨.neg, .imp φ ψ, l⟩`; `intFImpRule`'s output is entirely at `nw`.
    rcases sf with ⟨s, f, l⟩
    simp only [isWorldCreating] at hwc
    cases s <;> cases f <;> simp_all only [Bool.false_eq_true]
    rename_i φ ψ
    simp only [intApplyRuleFull] at hint
    subst hint
    simp only [IResultLabelsGe]
    intro x hx
    simp only [intFImpRule] at hx
    rcases List.mem_append.mp hx with hx | hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> exact hnw
    · simp only [propagatePersistence, List.mem_map] at hx
      obtain ⟨χ, -, hχ⟩ := hx
      rw [← hχ]
      exact hnw
  · -- Not world-creating: `IFrozenBelow` forces `w0 ≤ sf.label`.
    have hlge : w0 ≤ sf.label := by
      by_contra hlt
      simp only [not_le] at hlt
      rcases hfrz sf hsfb hlt with hwc' | hexp | hns
      · exact hwc hwc'
      · exact hsfne hexp
      · exact hresne (hint ▸ (intApplyRuleFull_notApplicable_iff sf nw b).mpr hns)
    have heq := intApplyRuleFull_labels_eq_of_not_worldCreating (sf := sf) (nw := nw) (b := b) hwc
    rw [hint] at heq
    exact IResultLabelsEq_imp_Ge hlge heq

/-! ### Freeze persistence-fixpoint preservation (plan Phase 5, mechanism 3(b))

`IFrozenBelow_intStepBranchPrio_ge` covers a single `intStepBranchPrio` step in isolation. The
other half of the freeze argument (Phase 5's Investigation note, point 3(b)) is that
`applyPersistenceFixpoint`/`applyAllTImpRules`, run at the TOP of every `intExpandBranches.go`
call, also cannot introduce genuinely new content below a checkpoint `w0`, given `IFrozenBelow
w0 e b` together with the raw-edge persistence invariant `IPosPersistRaw edges b` and open-branch
consistency. Two channels make up `applyAllTImpRules`: the generalized copy channel (`genCopies`,
copying an existing positive formula to every accessible world lacking its own copy) is vacuous
below `w0` -- indeed everywhere -- directly from `IPosPersistRaw`, no `w0` restriction needed.
The ψ-consequence channel (`intTImpRule`'s direct clause, deriving `T(ψ)@w'` from `T(φ→ψ)@w` and
`T(φ)@w'`) needs more: `IWorldHist_isAccessible_lt` pins the SOURCE of any accessibility edge
landing below `w0` to also be below `w0`; `IFrozenBelow` then forces the source's copy of
`T(φ→ψ)` (itself already `IPosPersistRaw`-propagated to the target) to be `e`-expanded;
`IExpandedConsistent` reads off its Fitting-split resolution (`F(φ)@w' ∨ T(ψ)@w'`); and
open-branch consistency (no complementary `T(φ)`/`F(φ)` pair) rules out the `F(φ)@w'` disjunct
given `T(φ)@w'` is exactly `intTImpRule`'s own firing precondition -- leaving `T(ψ)@w'` already
present, so nothing new is ever added. -/

omit [Hashable Atom] in
/-- Extraction helper: a `List.any` witness for the `(sign, formula, label)` triple pins down
the exact `ISF Atom` membership (mirrors the extraction pattern in
`applyAllTImpRules_copy_complete_of_fixpoint`). -/
private lemma isf_any_mem {b' : IBranch Atom} {s : Sign} {χ : Proposition Atom} {l : Nat}
    (h : b'.any (fun sf => sf.sign == s && sf.formula == χ && sf.label == l) = true) :
    (⟨s, χ, l⟩ : ISF Atom) ∈ b' := by
  rw [List.any_eq_true] at h
  obtain ⟨sf, hsfmem, hsfeq⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq] at hsfeq
  obtain ⟨⟨hsign, hform⟩, hlabel⟩ := hsfeq
  have hsfeq' : sf = (⟨s, χ, l⟩ : ISF Atom) := by
    obtain ⟨s', f', l'⟩ := sf
    simp only [SignedFormula.mk.injEq]
    exact ⟨hsign, hform, hlabel⟩
  rw [← hsfeq']
  exact hsfmem

omit [Hashable Atom] in
/-- **Single-round freeze preservation**: given the checkpoint facts about a FIXED branch `b`
(`IFrozenBelow`, `IPosPersistRaw`, `IExpandedConsistent`, open-branch consistency, and the
`IWorldHist`/`IWorldHistCounter` pair `IWorldHist_isAccessible_lt` needs), one round of
`applyAllTImpRules` applied to any `bv` that agrees with `b` below `w0` (and contains `b`) still
agrees with `b` below `w0`. This is the per-round step of the fuel induction
`applyPersistenceFixpoint_agrees` below performs; `b` never changes across rounds, only `bv`
does, which is why every checkpoint hypothesis is stated about the fixed `b` and not `bv`. -/
private lemma applyAllTImpRules_agrees
    {φ0 : Proposition Atom} {edges : IEdges} {e : List (ISF Atom)} {w0 nw : Nat}
    {b : IBranch Atom}
    (hw0 : w0 ≤ nw) (hfrz : IFrozenBelow w0 e b) (hpp : IPosPersistRaw edges b)
    (hic : IExpandedConsistent b e)
    (hcons : ∀ w' : Nat, w' < w0 → ∀ χ : Proposition Atom,
      ¬ ((⟨.pos, χ, w'⟩ : ISF Atom) ∈ b ∧ (⟨.neg, χ, w'⟩ : ISF Atom) ∈ b))
    (hWH : IWorldHist φ0 b e nw edges) (hWHC : IWorldHistCounter nw edges)
    {bv : IBranch Atom} (hmono : ∀ x ∈ b, x ∈ bv)
    (hagree : ∀ sf ∈ bv, sf.label < w0 → sf ∈ b) :
    ∀ sf ∈ applyAllTImpRules bv edges, sf.label < w0 → sf ∈ b := by
  intro sf hsf hlt
  simp only [applyAllTImpRules, List.mem_append] at hsf
  rcases hsf with (hsf | hsf) | hsf
  · exact hagree sf hsf hlt
  · simp only [List.mem_flatten, List.mem_filterMap] at hsf
    obtain ⟨toAdd, ⟨y, hymem, hyeq⟩, hsfmem⟩ := hsf
    rcases y with ⟨ys, yf, yl⟩
    cases ys with
    | neg => simp at hyeq
    | pos =>
      cases yf with
      | atom a => simp at hyeq
      | bot => simp at hyeq
      | and φ ψ => simp at hyeq
      | or φ ψ => simp at hyeq
      | imp φ ψ =>
        simp only [] at hyeq
        split at hyeq
        · exact absurd hyeq (by simp)
        · rename_i hne
          rw [Option.some.injEq] at hyeq
          subst hyeq
          simp only [intTImpRule, List.mem_filterMap] at hsfmem
          obtain ⟨w', hw'mem, hsfeq⟩ := hsfmem
          simp only [List.mem_filter, List.mem_eraseDups, List.mem_map] at hw'mem
          obtain ⟨⟨z, hzmem, hzeq⟩, hacc⟩ := hw'mem
          split at hsfeq
          · rename_i hTphi
            split at hsfeq
            · simp at hsfeq
            · rename_i hTpsi
              rw [Bool.not_eq_true] at hTpsi
              rw [Option.some.injEq] at hsfeq
              subst hsfeq
              -- Source label `yl` is also `< w0`: reflexive (`yl = w'`) or via the
              -- label-order fact (`yl ≠ w'`).
              have hw'nw : w' < nw := lt_of_lt_of_le hlt hw0
              have hylw0 : yl < w0 := by
                by_cases hyw' : yl = w'
                · exact hyw' ▸ hlt
                · exact lt_trans (IWorldHist_isAccessible_lt hWH hWHC hw'nw hacc hyw') hlt
              -- The source copy `T(φ→ψ)@yl` is already in `b` (agreement, `yl < w0`).
              have hsrc_b : (⟨.pos, φ.imp ψ, yl⟩ : ISF Atom) ∈ b := hagree _ hymem hylw0
              -- `w'` already carries an entry on `b` too (witnessed by `T(φ)@w'`'s copy).
              have hTphi_b : (⟨.pos, φ, w'⟩ : ISF Atom) ∈ b := hagree _ (isf_any_mem hTphi) hlt
              have hw'ent_b : b.any (fun sf' => sf'.label == w') = true :=
                List.any_eq_true.mpr ⟨_, hTphi_b, by simp⟩
              -- `IPosPersistRaw` propagates the copy `T(φ→ψ)@w'` into `b`.
              have hcopy_b : (⟨.pos, φ.imp ψ, w'⟩ : ISF Atom) ∈ b :=
                hpp _ yl w' hacc hsrc_b hw'ent_b
              -- `IFrozenBelow` forces this copy to already be `e`-expanded.
              have hexp : (⟨.pos, φ.imp ψ, w'⟩ : ISF Atom) ∈ e := by
                rcases hfrz _ hcopy_b hlt with hwc | hexp | hns
                · exact absurd hwc (by simp [isWorldCreating])
                · exact hexp
                · exact absurd hns (by simp [isRuleShape])
              -- `IExpandedConsistent` reads off the Fitting-split resolution at `w'`.
              rcases hic _ hexp with hFphi | hTpsi_b
              · exact absurd ⟨hTphi_b, isf_any_mem hFphi⟩ (hcons w' hlt φ)
              · exact isf_any_mem hTpsi_b
          · simp at hsfeq
  · simp only [List.mem_flatten, List.mem_filterMap] at hsf
    obtain ⟨toAdd, ⟨y, hymem, hyeq⟩, hsfmem⟩ := hsf
    rcases y with ⟨ys, yf, yl⟩
    cases ys with
    | neg => simp at hyeq
    | pos =>
      simp only [] at hyeq
      split at hyeq
      · exact absurd hyeq (by simp)
      · rename_i hne
        rw [Option.some.injEq] at hyeq
        subst hyeq
        simp only [List.mem_filterMap] at hsfmem
        obtain ⟨w', hw'mem, hsfeq⟩ := hsfmem
        split at hsfeq
        · simp at hsfeq
        · rename_i hguard
          rw [Bool.not_eq_true] at hguard
          rw [Option.some.injEq] at hsfeq
          subst hsfeq
          simp only [List.mem_filter, List.mem_eraseDups, List.mem_map] at hw'mem
          obtain ⟨⟨z, hzmem, hzeq⟩, hacc⟩ := hw'mem
          have hw'nw : w' < nw := lt_of_lt_of_le hlt hw0
          have hylw0 : yl < w0 := by
            by_cases hyw' : yl = w'
            · exact hyw' ▸ hlt
            · exact lt_trans (IWorldHist_isAccessible_lt hWH hWHC hw'nw hacc hyw') hlt
          have hsrc_b : (⟨.pos, yf, yl⟩ : ISF Atom) ∈ b := hagree _ hymem hylw0
          have hz_b : z ∈ b := hagree z hzmem (hzeq ▸ hlt)
          have hw'ent_b : b.any (fun sf' => sf'.label == w') = true :=
            List.any_eq_true.mpr ⟨z, hz_b, by simp [hzeq]⟩
          have hcopy_b : (⟨.pos, yf, w'⟩ : ISF Atom) ∈ b := hpp yf yl w' hacc hsrc_b hw'ent_b
          have hcopy_bv : (⟨.pos, yf, w'⟩ : ISF Atom) ∈ bv := hmono _ hcopy_b
          have hcontra : (List.any bv fun y' =>
              y'.sign == Sign.pos && y'.formula == yf && y'.label == w') = true :=
            List.any_eq_true.mpr ⟨_, hcopy_bv, by simp⟩
          rw [hguard] at hcontra
          exact absurd hcontra (by simp)

omit [Hashable Atom] in
/-- **Fuel-recursive freeze preservation**: `applyAllTImpRules_agrees`, iterated across
`applyPersistenceFixpoint`'s fuel recursion. `b`, and every checkpoint fact about it, stays
fixed throughout; only the varying branch `bv` (and its agreement-with-`b`-below-`w0` witness)
is threaded as an explicit induction target, avoiding the need to `generalizing` the fixed
hypotheses. -/
private lemma applyPersistenceFixpoint_agrees
    {φ0 : Proposition Atom} {edges : IEdges} {e : List (ISF Atom)} {w0 nw : Nat}
    {b : IBranch Atom}
    (hw0 : w0 ≤ nw) (hfrz : IFrozenBelow w0 e b) (hpp : IPosPersistRaw edges b)
    (hic : IExpandedConsistent b e)
    (hcons : ∀ w' : Nat, w' < w0 → ∀ χ : Proposition Atom,
      ¬ ((⟨.pos, χ, w'⟩ : ISF Atom) ∈ b ∧ (⟨.neg, χ, w'⟩ : ISF Atom) ∈ b))
    (hWH : IWorldHist φ0 b e nw edges) (hWHC : IWorldHistCounter nw edges) :
    ∀ (fuel : Nat) (bv : IBranch Atom), (∀ x ∈ b, x ∈ bv) →
      (∀ sf ∈ bv, sf.label < w0 → sf ∈ b) →
      ∀ sf ∈ applyPersistenceFixpoint bv edges fuel, sf.label < w0 → sf ∈ b := by
  intro fuel
  induction fuel with
  | zero => intro bv _ hagree; simpa [applyPersistenceFixpoint] using hagree
  | succ fuel' ih =>
    intro bv hmono hagree
    simp only [applyPersistenceFixpoint]
    split
    · exact hagree
    · refine ih (applyAllTImpRules bv edges) ?_ ?_
      · intro x hx
        simp only [applyAllTImpRules, List.mem_append]
        exact Or.inl (Or.inl (hmono x hx))
      · exact applyAllTImpRules_agrees hw0 hfrz hpp hic hcons hWH hWHC hmono hagree

omit [Hashable Atom] in
/-- **Mechanism 3(b), landed**: `applyPersistenceFixpoint b edges fuel`, run at the top of a
`intExpandBranches.go` call, preserves `IFrozenBelow w0 e`. Direct corollary of
`applyPersistenceFixpoint_agrees` at `bv := b` (reflexive agreement/monotonicity): every element
of the persistence-fixpoint output with label `< w0` was already in `b`, hence already satisfies
one of `IFrozenBelow`'s three disjuncts by `hfrz` itself. -/
private lemma IFrozenBelow_applyPersistenceFixpoint
    {φ0 : Proposition Atom} {edges : IEdges} {e : List (ISF Atom)} {w0 nw : Nat} {fuel : Nat}
    {b : IBranch Atom}
    (hw0 : w0 ≤ nw) (hfrz : IFrozenBelow w0 e b) (hpp : IPosPersistRaw edges b)
    (hic : IExpandedConsistent b e)
    (hcons : ∀ w' : Nat, w' < w0 → ∀ χ : Proposition Atom,
      ¬ ((⟨.pos, χ, w'⟩ : ISF Atom) ∈ b ∧ (⟨.neg, χ, w'⟩ : ISF Atom) ∈ b))
    (hWH : IWorldHist φ0 b e nw edges) (hWHC : IWorldHistCounter nw edges) :
    IFrozenBelow w0 e (applyPersistenceFixpoint b edges fuel) := by
  intro sf hsf hlt
  exact hfrz sf
    (applyPersistenceFixpoint_agrees hw0 hfrz hpp hic hcons hWH hWHC fuel b (fun _ h => h)
      (fun _ h _ => h) sf hsf hlt) hlt

/-- **Reuse-time containment, per recorded loop-back edge** (plan Phase 8): for every
loop-back edge `(x, l)` recorded so far (NOT the raw parent-child edges, which
`IPosPersistRaw` already covers more strongly), there EXISTS a branch snapshot `bSnap`,
contained in the CURRENT branch `b`, at which containment of `l`'s positive content in
`x`'s already held. This existential-snapshot shape -- rather than a bare
`posFormulasAt b l ⊆ posFormulasAt b x` claim about the CURRENT branch -- is what makes the
invariant preserved automatically under branch growth: the SAME witness `bSnap`, planted
once at reuse time, transfers to any later, larger branch, since `∀ y ∈ bSnap, y ∈ b` only
needs `b` to grow (a bare current-branch claim would instead require EVERYTHING that later
arrives at `l` to also arrive at `x`, which is the genuinely large post-reuse closure lemma,
not this export -- see `handoffs/05_phase7-complete-phase8-handoff.md`). -/
private def IReuseContain (lbH : IEdges) (b : IBranch Atom) : Prop :=
  ∀ x l : Nat, (x, l) ∈ lbH →
    ∃ bSnap : IBranch Atom, (∀ y ∈ bSnap, y ∈ b) ∧
      ∀ χ : Proposition Atom, (⟨.pos, χ, l⟩ : ISF Atom) ∈ bSnap →
        (⟨.pos, χ, x⟩ : ISF Atom) ∈ bSnap

omit [Hashable Atom] [DecidableEq Atom] in
/-- `IReuseContain` is monotone in the branch: every recorded loop-back edge's witness
`bSnap` is contained in `b`, hence in any superset `b'` -- the containment fact about
`bSnap` itself is untouched. -/
private lemma IReuseContain_mono {lbH : IEdges} {b b' : IBranch Atom}
    (hmem : ∀ y ∈ b, y ∈ b') (h : IReuseContain lbH b) : IReuseContain lbH b' := by
  intro x l hxl
  obtain ⟨bSnap, hsub, hcont⟩ := h x l hxl
  exact ⟨bSnap, fun y hy => hmem _ (hsub y hy), hcont⟩

omit [Hashable Atom] [DecidableEq Atom] in
/-- Extending `IReuseContain` by a newly recorded loop-back edge `(x, l)`, planted using
the CURRENT branch `b` itself as the snapshot witness (reflexively contained in itself),
given the containment fact directly -- at the reuse arm this is exactly
`intFImpReuseWitnessAnc?_spec`'s `hcont` conjunct, since `sfor` there is
`{φ} ∪ posFormulasAt bPers l`, so `hcont` already ranges over every `χ` with
`T(χ)@l ∈ bPers`, not merely the single formula `φ`. -/
private lemma IReuseContain_snoc {lbH : IEdges} {b : IBranch Atom} {x l : Nat}
    (h : IReuseContain lbH b)
    (hcont : ∀ χ : Proposition Atom, (⟨.pos, χ, l⟩ : ISF Atom) ∈ b →
      (⟨.pos, χ, x⟩ : ISF Atom) ∈ b) :
    IReuseContain (lbH ++ [(x, l)]) b := by
  intro x' l' hx'l'
  rcases List.mem_append.mp hx'l' with h' | h'
  · exact h x' l' h'
  · simp only [List.mem_singleton, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    exact ⟨b, fun y hy => hy, hcont⟩

/-- List companion of `IReuseContain`, a 2-list zip over `(bs, lbSets)` mirroring
`IAllAccessConsistent`'s shape (companion, not merged, threaded ALONGSIDE it through a
SEPARATE parallel list `lbSets`, since `IReuseContain` only concerns recorded loop-back
edges, a strict subset of the full augmented edge list `IAllAccessConsistent` tracks). -/
private def IAllReuseContain (bs : List (IBranch Atom)) (lbSets : List IEdges) : Prop :=
  match bs, lbSets with
  | [], [] => True
  | b :: bs', lbH :: lbT' => IReuseContain lbH b ∧ IAllReuseContain bs' lbT'
  | _, _ => False

omit [Hashable Atom] [DecidableEq Atom] in
/-- `IAllReuseContain` combines under list append (mirrors `IAllAccessConsistent_append`). -/
private lemma IAllReuseContain_append {bs1 bs2 : List (IBranch Atom)}
    {lb1 lb2 : List IEdges}
    (h1 : IAllReuseContain bs1 lb1) (h2 : IAllReuseContain bs2 lb2) :
    IAllReuseContain (bs1 ++ bs2) (lb1 ++ lb2) := by
  induction bs1 generalizing lb1 with
  | nil =>
    cases lb1 with
    | nil => simpa using h2
    | cons _ _ => simp [IAllReuseContain] at h1
  | cons bh bt ih =>
    cases lb1 with
    | nil => simp [IAllReuseContain] at h1
    | cons lbh lbt =>
      simp only [IAllReuseContain] at h1
      obtain ⟨hARC, hrest⟩ := h1
      simp only [List.cons_append]
      exact ⟨hARC, ih hrest⟩

omit [Hashable Atom] [DecidableEq Atom] in
/-- `IAllReuseContain` holds along a constant-valued `map` (mirrors
`IAllAccessConsistent_map`; used for the BETA arm, where every child shares the same
loop-back list since branching never records a new loop-back edge). -/
private lemma IAllReuseContain_map_const {branches' : List (IBranch Atom)}
    (f : IBranch Atom → IBranch Atom) {lbH' : IEdges}
    (h : ∀ br ∈ branches', IReuseContain lbH' (f br)) :
    IAllReuseContain (branches'.map f) (branches'.map (fun _ => lbH')) := by
  induction branches' with
  | nil => simp [IAllReuseContain]
  | cons bh bt ih =>
    simp only [List.map_cons, IAllReuseContain]
    exact ⟨h bh (List.mem_cons_self ..), ih fun br hbr => h br (List.mem_cons_of_mem _ hbr)⟩

/-- **R1 restatement** (Phase 6: `hUniv`/`hNW`/per-branch `hFuel` hypothesis threading;
subsumes the prior fuel-materialization report's F5 form). If the per-branch-fuel engine
returns `.openBranch b`, then `b` is Hintikka-saturated and carries an `IFimpAccess`
edge witness, GIVEN the three R1 invariants at the entry worklist: `hUniv` (every branch
stays inside the enlarged universe `intUniverseExt φ0`, Phase 5), `hNW` (every
next-world counter stays within `WBound φ0`, Phase 5), and `hFuel` (every branch's
`intWork` strictly undercuts its own fuel, this phase's `IAllFuel`).

The per-branch fuel-exhaustion arm (`f = 0`) is EXACTLY the refuted fuel-0 goal of the
retired global-fuel lemma — UNPROVABLE at the pre-R1 statement (see the counter-instance
below, kept as the durable record of why the R1 hypotheses exist) — but is discharged
here: `hFuel` at that arm gives `intWork (intUniverseExt φ0) bh eH < 0`, absurd by
`omega` since `intWork` is a `Nat`. All other arms transferred from the retired proof's
succ case, with `hUniv`/`hNW` re-established via Phase 5's preservation lemmas and
`hFuel` re-established via `intWork_persistence_le` + `intWork_drop`.

**Phase 7 addition**: the conclusion also carries `IPosPersistRaw edges b`, the RAW-edge
positive-formula persistence fact -- a cheap stepping stone (see `IPosPersistRaw`'s own
docstring for why it is not sufficient alone). -/
private lemma intExpandBranches_openBranch_sat
    (φ0 : Proposition Atom)
    (branches : List (IBranch Atom))
    (expandedSets : List (List (ISF Atom)))
    (nextWorlds : List Nat)
    (edgeSets : List IEdges)
    (fuels : List Nat)
    (augSets : List IEdges)
    (lbSets : List IEdges)
    (closurePred : IBranch Atom → Bool)
    (b : IBranch Atom)
    (hAC : IAllConsistent branches expandedSets nextWorlds)
    (hLen0 : branches.length = edgeSets.length)
    (hLenF0 : fuels.length = branches.length)
    (hACC : IAllAccessConsistent branches expandedSets augSets)
    (hARC : IAllReuseContain branches lbSets)
    (hUniv : IAllUniv φ0 branches)
    (hNW : IAllNW φ0 nextWorlds)
    (hFuel : IAllFuel φ0 branches expandedSets fuels)
    (hLBS : IAllLabelBoundStrict branches nextWorlds)
    (hWH : IAllWorldHist φ0 branches expandedSets nextWorlds edgeSets)
    (hWHC : IAllWorldHistCounter nextWorlds edgeSets)
    (hNC : ∀ (b' : IBranch Atom), closurePred b' = false →
        ∀ (ψ : Proposition Atom) (w : Nat), (⟨.neg, ψ, w⟩ : ISF Atom) ∈ b' →
          ψ ∉ posFormulasAt b' w)
    (h : intExpandBranches branches expandedSets nextWorlds edgeSets fuels closurePred
        = .openBranch b) :
    ∃ (edges rawEdges lbEdges : IEdges) (nwF : Nat), IBranchSaturation Atom b ∧
      IFimpAccess edges b ∧ IPosPersistRaw rawEdges b ∧ IReuseContain lbEdges b ∧
      ForestComparable nwF rawEdges ∧ IWorldsPlanted rawEdges b := by
  rw [intExpandBranches] at h
  suffices key : ∀ (pending : List (IBranch Atom))
      (pendingExp : List (List (ISF Atom)))
      (pendingNW : List Nat)
      (pendingEdges : List IEdges)
      (pendingFuels : List Nat)
      (done : List (IBranch Atom))
      (doneExp : List (List (ISF Atom)))
      (doneNW : List Nat)
      (doneEdges : List IEdges)
      (doneFuels : List Nat),
      ∀ (pendingAug doneAug pendingLB doneLB : List IEdges),
      IAllConsistent pending pendingExp pendingNW →
      pending.length = pendingEdges.length →
      pendingFuels.length = pending.length →
      IAllConsistent done doneExp doneNW →
      done.length = doneEdges.length →
      doneFuels.length = done.length →
      IAllAccessConsistent pending pendingExp pendingAug →
      IAllAccessConsistent done doneExp doneAug →
      IAllReuseContain pending pendingLB →
      IAllReuseContain done doneLB →
      IAllUniv φ0 pending →
      IAllNW φ0 pendingNW →
      IAllFuel φ0 pending pendingExp pendingFuels →
      IAllUniv φ0 done →
      IAllNW φ0 doneNW →
      IAllFuel φ0 done doneExp doneFuels →
      IAllLabelBoundStrict pending pendingNW →
      IAllLabelBoundStrict done doneNW →
      IAllWorldHist φ0 pending pendingExp pendingNW pendingEdges →
      IAllWorldHist φ0 done doneExp doneNW doneEdges →
      IAllWorldHistCounter pendingNW pendingEdges →
      IAllWorldHistCounter doneNW doneEdges →
      intExpandBranches.go closurePred pending pendingExp pendingNW pendingEdges
          pendingFuels done doneExp doneNW doneEdges doneFuels = .openBranch b →
      ∃ (edges rawEdges lbEdges : IEdges) (nwF : Nat), IBranchSaturation Atom b ∧
        IFimpAccess edges b ∧ IPosPersistRaw rawEdges b ∧ IReuseContain lbEdges b ∧
        ForestComparable nwF rawEdges ∧ IWorldsPlanted rawEdges b from
    key branches expandedSets nextWorlds edgeSets fuels [] [] [] [] [] augSets [] lbSets []
      hAC hLen0 hLenF0 trivial rfl rfl hACC trivial hARC trivial
      hUniv hNW hFuel (by simp [IAllUniv]) (by simp [IAllNW]) trivial
      hLBS (by simp [IAllLabelBoundStrict]) hWH trivial hWHC trivial h
  intro pending pendingExp pendingNW pendingEdges pendingFuels done doneExp doneNW
    doneEdges doneFuels
  induction pending, pendingExp, pendingNW, pendingEdges, pendingFuels, done, doneExp,
      doneNW, doneEdges, doneFuels
      using intExpandBranches.go.induct (closurePred := closurePred) with
  | case1 =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hgo
    simp only [intExpandBranches.go] at hgo
    exact absurd hgo (by simp)
  | case2 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT f fT
      bPers hcl ih =>
    intro pendingAug doneAug pendingLB doneLB hPending hLenP hLenPF hDone hLenD hLenDF
        hPendingACC hDoneACC hPendingARC hDoneARC hUnivP hNWP hFuelP hUnivD hNWD hFuelD
        hLBSP hLBSD hWHP hWHD hWHCP hWHCD hgo
    rw [intExpandBranches.go.eq_def] at hgo
    simp only [] at hgo
    rw [if_pos hcl] at hgo
    simp only [IAllConsistent] at hPending
    obtain ⟨hIC_bh_eH, hLB_bh_nwH, hPendingTail⟩ := hPending
    have hUnivP_head : ∀ x ∈ bh, x ∈ intUniverseExt φ0 := hUnivP bh List.mem_cons_self
    have hUnivP_tail : IAllUniv φ0 bt :=
      fun b' hb' => hUnivP b' (List.mem_cons_of_mem bh hb')
    have hNWP_head : nwH ≤ WBound φ0 := hNWP nwH List.mem_cons_self
    have hNWP_tail : IAllNW φ0 nwT :=
      fun nw' hnw' => hNWP nw' (List.mem_cons_of_mem nwH hnw')
    simp only [IAllFuel] at hFuelP
    obtain ⟨hFuel_bh_eH, hFuelP_tail⟩ := hFuelP
    simp only [IAllLabelBoundStrict] at hLBSP
    obtain ⟨hLBS_bh_nwH, hLBSP_tail⟩ := hLBSP
    simp only [IAllWorldHist] at hWHP
    obtain ⟨hWH_head, hWHP_tail⟩ := hWHP
    simp only [IAllWorldHistCounter] at hWHCP
    obtain ⟨hWHC_head, hWHCP_tail⟩ := hWHCP
    cases hpAug : pendingAug with
    | nil =>
      rw [hpAug] at hPendingACC
      simp only [IAllAccessConsistent] at hPendingACC
    | cons augH augT =>
      rw [hpAug] at hPendingACC
      simp only [IAllAccessConsistent] at hPendingACC
      obtain ⟨hACC_bh_eH, hACCTail⟩ := hPendingACC
      cases hpLB : pendingLB with
      | nil =>
        rw [hpLB] at hPendingARC
        simp only [IAllReuseContain] at hPendingARC
      | cons lbH lbT =>
        rw [hpLB] at hPendingARC
        simp only [IAllReuseContain] at hPendingARC
        obtain ⟨hARC_bh_head, hARCTail⟩ := hPendingARC
        have hmemP : ∀ x ∈ bh, x ∈ bPers :=
          fun x hx => applyPersistenceFixpoint_mem_preserved bh edgesH f x hx
        have hIC_bPers : IExpandedConsistent bPers eH :=
          IExpandedConsistent_mono hmemP hIC_bh_eH
        have hLB_bPers : ILabelBound bPers nwH :=
          ILabelBound_applyPersistenceFixpoint f hLB_bh_nwH
        have hACC_bPers : IExpandedAccessConsistent augH bPers eH :=
          IExpandedAccessConsistent_mono hmemP hACC_bh_eH
        have hARC_bPers : IReuseContain lbH bPers := IReuseContain_mono hmemP hARC_bh_head
        have hUniv_bPers : ∀ x ∈ bPers, x ∈ intUniverseExt φ0 :=
          applyPersistenceFixpoint_subset_ext bh edgesH f hUnivP_head
        have hFuel_bPers : intWork (intUniverseExt φ0) bPers eH < f :=
          lt_of_le_of_lt (intWork_persistence_le (intUniverseExt φ0) bh edgesH f eH)
            hFuel_bh_eH
        have hLBS_bPers : ILabelBoundStrict bPers nwH :=
          ILabelBoundStrict_applyPersistenceFixpoint f hLBS_bh_nwH
        refine ih augT (doneAug ++ [augH]) lbT (doneLB ++ [lbH]) hPendingTail
            (by simp only [List.length_cons] at hLenP; omega)
            (by simp only [List.length_cons] at hLenPF; omega)
            (IAllConsistent_append hDone ⟨hIC_bPers, hLB_bPers, trivial⟩)
            (by simp [hLenD]) (by simp [hLenDF]) hACCTail
            (IAllAccessConsistent_append hDoneACC ⟨hACC_bPers, trivial⟩)
            hARCTail
            (IAllReuseContain_append hDoneARC ⟨hARC_bPers, trivial⟩)
            hUnivP_tail hNWP_tail hFuelP_tail
            (IAllUniv_append hUnivD
              (fun b' hb' => by
                simp only [List.mem_singleton] at hb'; subst hb'; exact hUniv_bPers))
            (IAllNW_append hNWD
              (fun nw' hnw' => by
                simp only [List.mem_singleton] at hnw'; subst hnw'; exact hNWP_head))
            (IAllFuel_append hFuelD ⟨hFuel_bPers, trivial⟩)
            hLBSP_tail (IAllLabelBoundStrict_append hLBSD ⟨hLBS_bPers, trivial⟩)
            hWHP_tail
            (IAllWorldHist_append hWHD
              ⟨IWorldHist_mono hmemP (fun x hx => hx) hWH_head, trivial⟩)
            hWHCP_tail (IAllWorldHistCounter_append hWHCD ⟨hWHC_head, trivial⟩) hgo
  | case3 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT fT
      bPers hcl =>
    intro _pendingAug _doneAug _pendingLB _doneLB _hPending _hLenP _hLenPF _hDone _hLenD
        _hLenDF _hPendingACC _hDoneACC _hPendingARC _hDoneARC _hUnivP _hNWP hFuelP _hUnivD
        _hNWD _hFuelD _hLBSP _hLBSD _hWHP _hWHD _hWHCP _hWHCD hgo
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    injection hgo with heq
    subst heq
    -- Per-branch fuel-exhaustion arm: `pendingFuels`'s head is literally `0` here (the
    -- `match f with | 0 => ...` branch this case corresponds to). `hFuel`'s head
    -- component at `bh`/`eH` then gives `intWork … < 0`, impossible for a `Nat` —
    -- this is the R1 restatement's discharge.
    --
    -- Counter-instance (carried verbatim from the retired global-fuel lemma's fuel-0 arm,
    -- where it was Lean-verified; the durable record of why the hypotheses above must
    -- exist): with the singleton worklist `[[⟨.neg, p ∧ q, 0⟩]]`, `expandedSets = [[]]`,
    -- `nextWorlds = [1]`, `edgeSets = [[]]` and per-branch fuel `0`, every PRE-R1
    -- hypothesis holds (`ILabelBound` trivially, `IExpandedConsistent`/
    -- `IAllAccessConsistent` vacuously, all lengths `(1, 1)`), and the engine returns
    -- `.openBranch [⟨.neg, p ∧ q, 0⟩]` unmodified — never saturated. But
    -- `IBranchSaturation.sat_fand`'s premise (`F(p ∧ q)@0` present) evaluates `true` while
    -- both required disjuncts (`F(p)@0` or `F(q)@0` present) evaluate `false`, so
    -- `IBranchSaturation` is false at that branch and the existential goal is
    -- unsatisfiable despite every PRE-R1 hypothesis holding — this is exactly why `hFuel`
    -- (which is FALSE at this counter-instance: `intWork … < 0` never holds) had to be
    -- added as a premise.
    simp only [IAllFuel] at hFuelP
    obtain ⟨hFuel_bh_eH, -⟩ := hFuelP
    omega
  | case4 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT fT f'
      bPers hcl hstep =>
    intro pendingAug doneAug pendingLB doneLB hPending hLenP hLenPF hDone hLenD hLenDF
        hPendingACC hDoneACC hPendingARC hDoneARC hUnivP _hNWP hFuelP _hUnivD _hNWD
        _hFuelD _hLBSP _hLBSD hWHP _hWHD hWHCP _hWHCD hgo
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    split at hgo
    · injection hgo with heq
      subst heq
      simp only [IAllConsistent] at hPending
      obtain ⟨hIC_bh_eH, hLB_bh_nwH, -⟩ := hPending
      simp only [IAllWorldHist] at hWHP
      obtain ⟨hWH_head, -⟩ := hWHP
      simp only [IAllWorldHistCounter] at hWHCP
      obtain ⟨hWHC_head, -⟩ := hWHCP
      cases hpAug : pendingAug with
      | nil =>
        rw [hpAug] at hPendingACC
        simp only [IAllAccessConsistent] at hPendingACC
      | cons augH augT =>
        rw [hpAug] at hPendingACC
        simp only [IAllAccessConsistent] at hPendingACC
        obtain ⟨hACC_bh_eH, -⟩ := hPendingACC
        cases hpLB : pendingLB with
        | nil =>
          rw [hpLB] at hPendingARC
          simp only [IAllReuseContain] at hPendingARC
        | cons lbH lbT =>
          rw [hpLB] at hPendingARC
          simp only [IAllReuseContain] at hPendingARC
          obtain ⟨hARC_bh_head, -⟩ := hPendingARC
          have hmemP : ∀ x ∈ bh, x ∈ bPers :=
            fun x hx => applyPersistenceFixpoint_mem_preserved bh edgesH (f' + 1) x hx
          have hIC_bPers : IExpandedConsistent bPers eH :=
            IExpandedConsistent_mono hmemP hIC_bh_eH
          have hACC_bPers : IExpandedAccessConsistent augH bPers eH :=
            IExpandedAccessConsistent_mono hmemP hACC_bh_eH
          have hARC_bPers : IReuseContain lbH bPers := IReuseContain_mono hmemP hARC_bh_head
          -- Phase 7: the raw-edge persistence conjunct, composed from `IAllUniv`/`IAllFuel`
          -- (already threaded through this induction) plus Phase 4's landed
          -- `applyPersistenceFixpoint_copy_complete` -- see `IPosPersistRaw`'s docstring.
          have hUnivP_head : ∀ x ∈ bh, x ∈ intUniverseExt φ0 := hUnivP bh List.mem_cons_self
          simp only [IAllFuel] at hFuelP
          obtain ⟨hFuel_bh_eH, -⟩ := hFuelP
          have hfuel_bh : (intUniverseExt φ0).countP (fun sf => !(bh.any (· == sf))) ≤ f' + 1 := by
            simp only [intWork] at hFuel_bh_eH
            omega
          have hpp : IPosPersistRaw edgesH bPers := by
            intro χ w w' hacc hmem hw'
            exact applyPersistenceFixpoint_copy_complete (φ0 := φ0) hUnivP_head hfuel_bh hmem
              hacc hw'
          -- Phase 10 (first construction step): the `ForestComparable` export, a pure
          -- corollary of `IWorldHist`/`IWorldHistCounter` (no new invariant threading needed).
          have hfc : ForestComparable nwH edgesH := IWorldHist_forestComparable hWH_head hWHC_head
          -- Provenance half of `IPosPersistRaw`'s side-condition gap: same corollary shape as
          -- `hfc` above, transported from `bh` to `bPers` via `hmemP` (mirrors `hARC_bPers`'s
          -- transport just above).
          have hwp : IWorldsPlanted edgesH bPers :=
            IWorldsPlanted_mono hmemP (IWorldHist_worldsPlanted hWH_head hWHC_head)
          exact ⟨augH, edgesH, lbH, nwH,
            IExpandedConsistent_sat (intStepBranchPrio_none_iff.mp hstep) hIC_bPers,
            IExpandedAccessConsistent_sat (intStepBranchPrio_none_iff.mp hstep) hACC_bPers,
            hpp, hARC_bPers, hfc, hwp⟩
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
  | case5 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT fT f'
      newForms nw' newExp bPers hcl hstep hstep2 ih =>
    intro pendingAug doneAug pendingLB doneLB hPending hLenP hLenPF hDone hLenD hLenDF
        hPendingACC hDoneACC hPendingARC hDoneARC hUnivP hNWP hFuelP hUnivD hNWD hFuelD
        hLBSP hLBSD hWHP hWHD hWHCP hWHCD hgo
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    have hUnivP_head : ∀ x ∈ bh, x ∈ intUniverseExt φ0 := hUnivP bh List.mem_cons_self
    have hUnivP_tail : IAllUniv φ0 bt :=
      fun b' hb' => hUnivP b' (List.mem_cons_of_mem bh hb')
    have hNWP_head : nwH ≤ WBound φ0 := hNWP nwH List.mem_cons_self
    have hNWP_tail : IAllNW φ0 nwT :=
      fun nw2 hnw2 => hNWP nw2 (List.mem_cons_of_mem nwH hnw2)
    simp only [IAllFuel] at hFuelP
    obtain ⟨hFuel_bh_eH, hFuelP_tail⟩ := hFuelP
    simp only [IAllLabelBoundStrict] at hLBSP
    obtain ⟨hLBS_bh_nwH, hLBSP_tail⟩ := hLBSP
    simp only [IAllWorldHist] at hWHP
    obtain ⟨hWH_head, hWHP_tail⟩ := hWHP
    simp only [IAllWorldHistCounter] at hWHCP
    obtain ⟨hWHC_head, hWHCP_tail⟩ := hWHCP
    have hUniv_bPers : ∀ x ∈ bPers, x ∈ intUniverseExt φ0 :=
      applyPersistenceFixpoint_subset_ext bh edgesH (f' + 1) hUnivP_head
    have hFuel_bPers : intWork (intUniverseExt φ0) bPers eH < f' + 1 :=
      lt_of_le_of_lt (intWork_persistence_le (intUniverseExt φ0) bh edgesH (f' + 1) eH)
        hFuel_bh_eH
    split at hgo
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i newForms1 nw1 newEdge1 newExp1 heq
      have hsome := hstep.symm.trans heq
      simp only [Option.some.injEq, Prod.mk.injEq,
        IntRuleResult.linearResult.injEq] at hsome
      obtain ⟨⟨hF, hN, hE⟩, hX⟩ := hsome
      subst hF; subst hN; subst hX; subst hE
      simp only [IAllConsistent] at hPending
      obtain ⟨hIC_bh_eH, hLB_bh_nwH, hPendingTail⟩ := hPending
      cases hpAug : pendingAug with
      | nil =>
        rw [hpAug] at hPendingACC
        simp only [IAllAccessConsistent] at hPendingACC
      | cons augH augT =>
        rw [hpAug] at hPendingACC
        simp only [IAllAccessConsistent] at hPendingACC
        obtain ⟨hACC_bh_eH, hACCTail⟩ := hPendingACC
        cases hpLB : pendingLB with
        | nil =>
          rw [hpLB] at hPendingARC
          simp only [IAllReuseContain] at hPendingARC
        | cons lbH lbT =>
          rw [hpLB] at hPendingARC
          simp only [IAllReuseContain] at hPendingARC
          obtain ⟨hARC_bh_head, hARCTail⟩ := hPendingARC
          simp only [List.length_cons] at hLenP hLenPF
          have hLenPt : bt.length = edgesT.length := by omega
          have hLenPFt : fT.length = bt.length := by omega
          have hmemP : ∀ x ∈ bh, x ∈ bPers :=
            fun x hx => applyPersistenceFixpoint_mem_preserved bh edgesH (f' + 1) x hx
          have hIC_bPers : IExpandedConsistent bPers eH :=
            IExpandedConsistent_mono hmemP hIC_bh_eH
          have hLB_bPers : ILabelBound bPers nwH :=
            ILabelBound_applyPersistenceFixpoint (f' + 1) hLB_bh_nwH
          have hACC_bPers : IExpandedAccessConsistent augH bPers eH :=
            IExpandedAccessConsistent_mono hmemP hACC_bh_eH
          have hLBS_bPers : ILabelBoundStrict bPers nwH :=
            ILabelBoundStrict_applyPersistenceFixpoint (f' + 1) hLBS_bh_nwH
          obtain ⟨hIC_ext, hLB_ext, hACC_ext⟩ :=
            intStepBranch_linear_preserves hIC_bPers hLB_bPers hACC_bPers
              (intStepBranchPrio_some_exists hstep)
          -- R1 threading: hUniv, hNW, hFuel for the ALPHA child
          -- `Branch.extendMany bPers newForms`.
          have hUniv_ext : ∀ x ∈ Branch.extendMany bPers newForms, x ∈ intUniverseExt φ0 :=
            intStepBranch_linear_preserves_univ hUniv_bPers hNWP_head
              (intStepBranchPrio_some_exists hstep)
          have hnw'_eq : nw' = nwH :=
            intStepBranch_linear_preserves_nw_of_none (intStepBranchPrio_some_exists hstep)
          have hNW_ext : nw' ≤ WBound φ0 := hnw'_eq ▸ hNWP_head
          have hLBS_ext : ILabelBoundStrict (Branch.extendMany bPers newForms) nw' :=
            intStepBranch_linear_preserves_labelStrict hLBS_bPers
              (intStepBranchPrio_some_exists hstep)
          obtain ⟨sf, hsfb, hsfe, -, hnewExp⟩ :=
            intStepBranch_some_exists_fuel (intStepBranchPrio_some_exists hstep)
          have hsfU : sf ∈ intUniverseExt φ0 := hUniv_bPers sf hsfb
          have hsub : ∀ z ∈ bPers, z ∈ Branch.extendMany bPers newForms :=
            fun z hz => by simp only [Branch.extendMany, List.mem_append]; exact Or.inr hz
          have hARC_ext : IReuseContain lbH (Branch.extendMany bPers newForms) :=
            IReuseContain_mono (fun x hx => hsub _ (hmemP x hx)) hARC_bh_head
          have hdrop := intWork_drop (intUniverseExt φ0) bPers
            (Branch.extendMany bPers newForms) eH sf hsfU hsfe hsub
          rw [← hnewExp] at hdrop
          have hFuel_ext : intWork (intUniverseExt φ0)
              (Branch.extendMany bPers newForms) newExp < f' := by omega
          -- `IWorldHist` transfer for the non-minting (alpha/reuse) linear arm: `nw`/`edges`
          -- are unchanged (`hnw'_eq`), and `newExp = eH ++ [sf]` is a strict append, so the
          -- old witness carries over via `IWorldHist_mono` composed through `bh ⊆ bPers ⊆
          -- Branch.extendMany bPers newForms`.
          have hexp_ext : ∀ x ∈ eH, x ∈ newExp := fun x hx => hnewExp ▸ List.mem_append_left _ hx
          have hWH_ext : IWorldHist φ0 (Branch.extendMany bPers newForms) newExp nw' edgesH := by
            rw [hnw'_eq]
            exact IWorldHist_mono (fun x hx => hsub _ (hmemP x hx)) hexp_ext hWH_head
          have hWHC_ext : IWorldHistCounter nw' edgesH := hnw'_eq ▸ hWHC_head
          refine ih (doneAug ++ [augH] ++ augT) [] (doneLB ++ [lbH] ++ lbT) []
              (IAllConsistent_append
                (IAllConsistent_append hDone ⟨hIC_ext, hLB_ext, trivial⟩) hPendingTail)
              (by simp only [List.length_append, List.length_cons, List.length_nil]
                  omega)
              (by simp only [List.length_append, List.length_cons, List.length_nil]
                  omega)
              trivial rfl rfl
              (IAllAccessConsistent_append
                (IAllAccessConsistent_append hDoneACC ⟨hACC_ext, trivial⟩) hACCTail)
              trivial
              (IAllReuseContain_append
                (IAllReuseContain_append hDoneARC ⟨hARC_ext, trivial⟩) hARCTail)
              trivial
              (IAllUniv_append
                (IAllUniv_append hUnivD
                  (fun b' hb' => by
                    simp only [List.mem_singleton] at hb'; subst hb'; exact hUniv_ext))
                hUnivP_tail)
              (IAllNW_append
                (IAllNW_append hNWD
                  (fun nw2 hnw2 => by
                    simp only [List.mem_singleton] at hnw2; subst hnw2; exact hNW_ext))
                hNWP_tail)
              (IAllFuel_append
                (IAllFuel_append hFuelD ⟨hFuel_ext, trivial⟩) hFuelP_tail)
              (by simp [IAllUniv]) (by simp [IAllNW]) trivial
              (IAllLabelBoundStrict_append
                (IAllLabelBoundStrict_append hLBSD ⟨hLBS_ext, trivial⟩) hLBSP_tail)
              (by simp [IAllLabelBoundStrict])
              (IAllWorldHist_append
                (IAllWorldHist_append hWHD ⟨hWH_ext, trivial⟩) hWHP_tail)
              (by simp [IAllWorldHist])
              (IAllWorldHistCounter_append
                (IAllWorldHistCounter_append hWHCD ⟨hWHC_ext, trivial⟩) hWHCP_tail)
              (by simp [IAllWorldHistCounter])
            hgo
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
  | case6 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT fT f'
      newForms nw' newExp newE x bPers hcl hstep hwit hstep2 ih =>
    intro pendingAug doneAug pendingLB doneLB hPending hLenP hLenPF hDone hLenD hLenDF
        hPendingACC hDoneACC hPendingARC hDoneARC hUnivP hNWP hFuelP hUnivD hNWD hFuelD
        hLBSP hLBSD hWHP hWHD hWHCP hWHCD hgo
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    have hUnivP_head : ∀ x ∈ bh, x ∈ intUniverseExt φ0 := hUnivP bh List.mem_cons_self
    have hUnivP_tail : IAllUniv φ0 bt :=
      fun b' hb' => hUnivP b' (List.mem_cons_of_mem bh hb')
    have hNWP_head : nwH ≤ WBound φ0 := hNWP nwH List.mem_cons_self
    have hNWP_tail : IAllNW φ0 nwT :=
      fun nw2 hnw2 => hNWP nw2 (List.mem_cons_of_mem nwH hnw2)
    simp only [IAllFuel] at hFuelP
    obtain ⟨hFuel_bh_eH, hFuelP_tail⟩ := hFuelP
    simp only [IAllLabelBoundStrict] at hLBSP
    obtain ⟨hLBS_bh_nwH, hLBSP_tail⟩ := hLBSP
    simp only [IAllWorldHist] at hWHP
    obtain ⟨hWH_head, hWHP_tail⟩ := hWHP
    simp only [IAllWorldHistCounter] at hWHCP
    obtain ⟨hWHC_head, hWHCP_tail⟩ := hWHCP
    have hUniv_bPers : ∀ x ∈ bPers, x ∈ intUniverseExt φ0 :=
      applyPersistenceFixpoint_subset_ext bh edgesH (f' + 1) hUnivP_head
    have hFuel_bPers : intWork (intUniverseExt φ0) bPers eH < f' + 1 :=
      lt_of_le_of_lt (intWork_persistence_le (intUniverseExt φ0) bh edgesH (f' + 1) eH)
        hFuel_bh_eH
    have hLBS_bPers : ILabelBoundStrict bPers nwH :=
      ILabelBoundStrict_applyPersistenceFixpoint (f' + 1) hLBS_bh_nwH
    split at hgo
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i newForms1 nw1 newEdge1 newExp1 heq
      have hsome := hstep.symm.trans heq
      simp only [Option.some.injEq, Prod.mk.injEq,
        IntRuleResult.linearResult.injEq] at hsome
      obtain ⟨⟨hF, hN, hE⟩, hX⟩ := hsome
      subst hF; subst hN; subst hX; subst hE
      split at hgo
      · rename_i heqE heqH
        exact absurd heqE (by simp)
      · rename_i newE1 hstep1 heqE heqH
        injection heqE with heqE'
        subst heqE'
        split at hgo
        · -- Reuse witness found: the branch is literally `bPers` (unchanged)
          simp only [IAllConsistent] at hPending
          obtain ⟨hIC_bh_eH, hLB_bh_nwH, hPendingTail⟩ := hPending
          cases hpAug : pendingAug with
          | nil =>
            rw [hpAug] at hPendingACC
            simp only [IAllAccessConsistent] at hPendingACC
          | cons augH augT =>
            rw [hpAug] at hPendingACC
            simp only [IAllAccessConsistent] at hPendingACC
            obtain ⟨hACC_bh_eH, hACCTail⟩ := hPendingACC
            cases hpLB : pendingLB with
            | nil =>
              rw [hpLB] at hPendingARC
              simp only [IAllReuseContain] at hPendingARC
            | cons lbH lbT =>
              rw [hpLB] at hPendingARC
              simp only [IAllReuseContain] at hPendingARC
              obtain ⟨hARC_bh_head, hARCTail⟩ := hPendingARC
              simp only [List.length_cons] at hLenP hLenPF
              have hLenPt : bt.length = edgesT.length := by omega
              have hLenPFt : fT.length = bt.length := by omega
              have hmemP : ∀ y ∈ bh, y ∈ bPers :=
                fun y hy => applyPersistenceFixpoint_mem_preserved bh edgesH (f' + 1) y hy
              have hIC_bPers : IExpandedConsistent bPers eH :=
                IExpandedConsistent_mono hmemP hIC_bh_eH
              have hLB_bPers : ILabelBound bPers nwH :=
                ILabelBound_applyPersistenceFixpoint (f' + 1) hLB_bh_nwH
              have hACC_bPers : IExpandedAccessConsistent augH bPers eH :=
                IExpandedAccessConsistent_mono hmemP hACC_bh_eH
              have hARC_bPers : IReuseContain lbH bPers := IReuseContain_mono hmemP hARC_bh_head
              obtain ⟨sf, hsfb, hsfe, hint, hnewExp⟩ :=
                intStepBranch_some_exists_fuel (intStepBranchPrio_some_exists hstep)
              have hsfU : sf ∈ intUniverseExt φ0 := hUniv_bPers sf hsfb
              have hdrop := intWork_drop (intUniverseExt φ0) bPers bPers eH sf hsfU hsfe
                (fun z hz => hz)
              have hFuel_child : intWork (intUniverseExt φ0) bPers newExp < f' := by
                rw [hnewExp]; omega
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
                  obtain ⟨hacc, hle, hcont, hnotmem, hFpsi⟩ :=
                    intFImpReuseWitnessAnc?_spec hψ hwit
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
                  -- Phase 8: the GENERAL reuse-time containment fact (not just for `φ`) --
                  -- `hcont` ranges over ALL of `sfor = {φ} ∪ posFormulasAt bPers l` (see
                  -- `IReuseContain`'s docstring), so this is exactly the exported witness.
                  have hcontGen : ∀ χ : Proposition Atom, (⟨.pos, χ, l⟩ : ISF Atom) ∈ bPers →
                      (⟨.pos, χ, x⟩ : ISF Atom) ∈ bPers := by
                    intro χ hχ
                    have hχmem : χ ∈ posFormulasAt bPers l :=
                      List.mem_filterMap.mpr ⟨⟨.pos, χ, l⟩, hχ, by simp⟩
                    have hχprop : (⟨.pos, χ, nwH⟩ : ISF Atom) ∈ propagatePersistence bPers l nwH :=
                      List.mem_map.mpr ⟨χ, hχmem, rfl⟩
                    have hχsfor : χ ∈ (newForms.filterMap fun sf =>
                        if sf.sign == .pos then some sf.formula else none) := by
                      rw [← hnf, List.filterMap_append, List.mem_append]
                      right
                      exact List.mem_filterMap.mpr ⟨⟨.pos, χ, nwH⟩, hχprop, by simp⟩
                    have hcontχ : (posFormulasAt bPers x).contains χ = true :=
                      List.all_eq_true.mp hcont χ hχsfor
                    rw [List.contains_iff_mem] at hcontχ
                    obtain ⟨y, hy_mem, hy_cond⟩ := List.mem_filterMap.mp hcontχ
                    by_cases hs : y.sign == .pos && y.label == x
                    · simp only [hs, if_true, Option.some.injEq] at hy_cond
                      simp only [Bool.and_eq_true, beq_iff_eq] at hs
                      obtain ⟨hs1, hs2⟩ := hs
                      have hyeq : y = ⟨.pos, χ, x⟩ := by
                        cases y with
                        | mk ys yf yl => simp_all
                      rw [hyeq] at hy_mem
                      exact hy_mem
                    · simp [hs] at hy_cond
                  have hARC_new : IReuseContain (lbH ++ [(x, l)]) bPers :=
                    IReuseContain_snoc hARC_bPers hcontGen
                  have hreuse_sat : IExpandedConsistent bPers newExp ∧
                      IExpandedAccessConsistent (augH ++ [(x, l)]) bPers newExp := by
                    subst hnewExp
                    constructor
                    · intro sf' hsf'
                      rcases List.mem_append.mp hsf' with h' | h'
                      · exact hIC_bPers sf' h'
                      · rw [List.mem_singleton] at h'
                        subst h'
                        show sfSatisfied bPers ⟨.neg, .imp φ ψ₀, l⟩
                        simp only [sfSatisfied]
                        exact ⟨x, houtPhi, hFpsi⟩
                    · intro sf' hsf'
                      rcases List.mem_append.mp hsf' with h' | h'
                      · exact sfAccessSat_edges_mono (x, l) (hACC_bPers sf' h')
                      · rw [List.mem_singleton] at h'
                        subst h'
                        show sfAccessSat (augH ++ [(x, l)]) bPers
                          ⟨.neg, .imp φ ψ₀, l⟩
                        simp only [sfAccessSat]
                        exact ⟨x, isAccessible_one_step (by simp), houtPhi, hFpsi⟩
                  -- `IWorldHist` transfer for the reuse arm: the branch `bPers` is reused
                  -- unchanged (no mint), `nw`/`edges` stay `nwH`/`edgesH`, and `newExp` only
                  -- grows by the fired triple (`hnewExp`), so `IWorldHist_mono` applies.
                  have hexp_ext : ∀ x ∈ eH, x ∈ newExp := fun x hx =>
                    hnewExp ▸ List.mem_append_left _ hx
                  have hWH_ext : IWorldHist φ0 bPers newExp nwH edgesH :=
                    IWorldHist_mono hmemP hexp_ext hWH_head
                  refine ih (doneAug ++ [augH ++ [(x, l)]] ++ augT) []
                      (doneLB ++ [lbH ++ [(x, l)]] ++ lbT) []
                      (IAllConsistent_append
                        (IAllConsistent_append hDone
                          ⟨hreuse_sat.1, hLB_bPers, trivial⟩) hPendingTail)
                      (by simp only [List.length_append, List.length_cons,
                            List.length_nil]
                          omega)
                      (by simp only [List.length_append, List.length_cons,
                            List.length_nil]
                          omega)
                      trivial rfl rfl
                      (IAllAccessConsistent_append
                        (IAllAccessConsistent_append hDoneACC
                          ⟨hreuse_sat.2, trivial⟩) hACCTail)
                      trivial
                      (IAllReuseContain_append
                        (IAllReuseContain_append hDoneARC ⟨hARC_new, trivial⟩) hARCTail)
                      trivial
                      (IAllUniv_append
                        (IAllUniv_append hUnivD
                          (fun b' hb' => by
                            simp only [List.mem_singleton] at hb'; subst hb'
                            exact hUniv_bPers))
                        hUnivP_tail)
                      (IAllNW_append
                        (IAllNW_append hNWD
                          (fun nw2 hnw2 => by
                            simp only [List.mem_singleton] at hnw2; subst hnw2
                            exact hNWP_head))
                        hNWP_tail)
                      (IAllFuel_append
                        (IAllFuel_append hFuelD ⟨hFuel_child, trivial⟩) hFuelP_tail)
                      (by simp [IAllUniv]) (by simp [IAllNW]) trivial
                      (IAllLabelBoundStrict_append
                        (IAllLabelBoundStrict_append hLBSD ⟨hLBS_bPers, trivial⟩) hLBSP_tail)
                      (by simp [IAllLabelBoundStrict])
                      (IAllWorldHist_append
                        (IAllWorldHist_append hWHD ⟨hWH_ext, trivial⟩) hWHP_tail)
                      (by simp [IAllWorldHist])
                      (IAllWorldHistCounter_append
                        (IAllWorldHistCounter_append hWHCD ⟨hWHC_head, trivial⟩) hWHCP_tail)
                      (by simp [IAllWorldHistCounter])
                      hgo
        · rename_i hwit1
          exact absurd (hwit.symm.trans hwit1) (by simp)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
  | case7 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT fT f'
      newForms nw' newExp newE bPers hcl hstep hwit hstep2 ih =>
    intro pendingAug doneAug pendingLB doneLB hPending hLenP hLenPF hDone hLenD hLenDF
        hPendingACC hDoneACC hPendingARC hDoneARC hUnivP hNWP hFuelP hUnivD hNWD hFuelD
        hLBSP hLBSD hWHP hWHD hWHCP hWHCD hgo
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    have hUnivP_head : ∀ x ∈ bh, x ∈ intUniverseExt φ0 := hUnivP bh List.mem_cons_self
    have hUnivP_tail : IAllUniv φ0 bt :=
      fun b' hb' => hUnivP b' (List.mem_cons_of_mem bh hb')
    have hNWP_head : nwH ≤ WBound φ0 := hNWP nwH List.mem_cons_self
    have hNWP_tail : IAllNW φ0 nwT :=
      fun nw2 hnw2 => hNWP nw2 (List.mem_cons_of_mem nwH hnw2)
    simp only [IAllFuel] at hFuelP
    obtain ⟨hFuel_bh_eH, hFuelP_tail⟩ := hFuelP
    simp only [IAllLabelBoundStrict] at hLBSP
    obtain ⟨hLBS_bh_nwH, hLBSP_tail⟩ := hLBSP
    simp only [IAllWorldHist] at hWHP
    obtain ⟨hWH_head, hWHP_tail⟩ := hWHP
    simp only [IAllWorldHistCounter] at hWHCP
    obtain ⟨hWHC_head, hWHCP_tail⟩ := hWHCP
    have hUniv_bPers : ∀ x ∈ bPers, x ∈ intUniverseExt φ0 :=
      applyPersistenceFixpoint_subset_ext bh edgesH (f' + 1) hUnivP_head
    have hFuel_bPers : intWork (intUniverseExt φ0) bPers eH < f' + 1 :=
      lt_of_le_of_lt (intWork_persistence_le (intUniverseExt φ0) bh edgesH (f' + 1) eH)
        hFuel_bh_eH
    have hLBS_bPers : ILabelBoundStrict bPers nwH :=
      ILabelBoundStrict_applyPersistenceFixpoint (f' + 1) hLBS_bh_nwH
    split at hgo
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i newForms1 nw1 newEdge1 newExp1 heq
      have hsome := hstep.symm.trans heq
      simp only [Option.some.injEq, Prod.mk.injEq,
        IntRuleResult.linearResult.injEq] at hsome
      obtain ⟨⟨hF, hN, hE⟩, hX⟩ := hsome
      subst hF; subst hN; subst hX; subst hE
      split at hgo
      · rename_i heqE heqH
        exact absurd heqE (by simp)
      · rename_i newE1 hstep1 heqE heqH
        injection heqE with heqE'
        subst heqE'
        split at hgo
        · rename_i x1 hwit1
          exact absurd (hwit.symm.trans hwit1) (by simp)
        · -- No reusable ancestor: fresh world creation
          simp only [IAllConsistent] at hPending
          obtain ⟨hIC_bh_eH, hLB_bh_nwH, hPendingTail⟩ := hPending
          cases hpAug : pendingAug with
          | nil =>
            rw [hpAug] at hPendingACC
            simp only [IAllAccessConsistent] at hPendingACC
          | cons augH augT =>
            rw [hpAug] at hPendingACC
            simp only [IAllAccessConsistent] at hPendingACC
            obtain ⟨hACC_bh_eH, hACCTail⟩ := hPendingACC
            cases hpLB : pendingLB with
            | nil =>
              rw [hpLB] at hPendingARC
              simp only [IAllReuseContain] at hPendingARC
            | cons lbH lbT =>
              rw [hpLB] at hPendingARC
              simp only [IAllReuseContain] at hPendingARC
              obtain ⟨hARC_bh_head, hARCTail⟩ := hPendingARC
              simp only [List.length_cons] at hLenP hLenPF
              have hLenPt : bt.length = edgesT.length := by omega
              have hLenPFt : fT.length = bt.length := by omega
              have hmemP : ∀ y ∈ bh, y ∈ bPers :=
                fun y hy => applyPersistenceFixpoint_mem_preserved bh edgesH (f' + 1) y hy
              have hIC_bPers : IExpandedConsistent bPers eH :=
                IExpandedConsistent_mono hmemP hIC_bh_eH
              have hLB_bPers : ILabelBound bPers nwH :=
                ILabelBound_applyPersistenceFixpoint (f' + 1) hLB_bh_nwH
              have hACC_bPers : IExpandedAccessConsistent augH bPers eH :=
                IExpandedAccessConsistent_mono hmemP hACC_bh_eH
              obtain ⟨hIC_ext, hLB_ext, hACC_ext⟩ :=
                intStepBranch_linear_preserves hIC_bPers hLB_bPers hACC_bPers
                  (intStepBranchPrio_some_exists hstep)
              -- R1 threading: hUniv, hNW (DP-2 fresh-mint), hFuel for the fresh-mint child
              -- `Branch.extendMany bPers newForms`.
              have hUniv_ext : ∀ x ∈ Branch.extendMany bPers newForms, x ∈ intUniverseExt φ0 :=
                intStepBranch_linear_preserves_univ hUniv_bPers hNWP_head
                  (intStepBranchPrio_some_exists hstep)
              obtain ⟨sf, hsfb, hsfe, hintSf, hnewExp⟩ :=
                intStepBranch_some_exists_fuel (intStepBranchPrio_some_exists hstep)
              have hnw'_eq : nw' = nwH + 1 := by
                rcases intApplyRuleFull_linearResult_nextWorld hintSf with
                  ⟨hc, -⟩ | ⟨ed, -, heqnw⟩
                · exact absurd hc (by simp)
                · exact heqnw
              have hLBS_ext : ILabelBoundStrict (Branch.extendMany bPers newForms) nw' :=
                intStepBranch_linear_preserves_labelStrict hLBS_bPers
                  (intStepBranchPrio_some_exists hstep)
              have hsfU : sf ∈ intUniverseExt φ0 := hUniv_bPers sf hsfb
              have hsub : ∀ z ∈ bPers, z ∈ Branch.extendMany bPers newForms :=
                fun z hz => by simp only [Branch.extendMany, List.mem_append]; exact Or.inr hz
              have hARC_ext : IReuseContain lbH (Branch.extendMany bPers newForms) :=
                IReuseContain_mono (fun x hx => hsub _ (hmemP x hx)) hARC_bh_head
              have hdrop := intWork_drop (intUniverseExt φ0) bPers
                (Branch.extendMany bPers newForms) eH sf hsfU hsfe hsub
              rw [← hnewExp] at hdrop
              have hFuel_ext : intWork (intUniverseExt φ0)
                  (Branch.extendMany bPers newForms) newExp < f' := by omega
              -- `IWorldHist` re-establishment for the mint arm: `IWorldHist_mint` (Phase 7,
              -- report section 5.5). `sf` is pinned to `⟨.neg, φ → ψ, l⟩` by
              -- `intApplyRuleFull_some_edge_inv`, which also gives `newForms`/`nw'`/`newE`'s
              -- literal shapes -- exactly what `IWorldHist_mint`'s conclusion needs.
              obtain ⟨φm, ψm, lm, hsfEq, hnfEq, hnw'Eq2, hnewEEq⟩ :=
                intApplyRuleFull_some_edge_inv hintSf
              have hWH_bPers : IWorldHist φ0 bPers eH nwH edgesH :=
                IWorldHist_mono hmemP (fun x hx => hx) hWH_head
              have hl_strict : lm < nwH := by simpa [hsfEq] using hLBS_bPers sf hsfb
              have hnone : intFImpReuseWitnessAnc? bPers edgesH
                  ([⟨.pos, φm, nwH⟩, ⟨.neg, ψm, nwH⟩] ++ propagatePersistence bPers lm nwH)
                  (nwH, lm) = none := by rw [← hnfEq, ← hnewEEq]; exact hwit
              have hclFalse : closurePred bPers = false := by simpa using hcl
              have hWH_ext : IWorldHist φ0 (Branch.extendMany bPers newForms) newExp nw'
                  (edgesH ++ [newE]) := by
                rw [hnw'_eq, hnfEq, hnewExp, hsfEq, hnewEEq]
                exact IWorldHist_mint hWH_bPers hnone (hsfEq ▸ hsfe) (hNC bPers hclFalse)
                  hUniv_bPers (hsfEq ▸ hsfb) hl_strict
              -- DP-2 (RESOLVED, Phase 11): `hNW_ext` is now discharged from the just-established
              -- structural invariant `hWH_ext` via `intFreshMint_preserves_nw`/`intWorldHist_nw_le`
              -- (Phase 10), not from the bare `hnwB : nw ≤ WBound φ0` the false numeric restatement
              -- used to (silently) assume.
              have hNW_ext : nw' ≤ WBound φ0 := intWorldHist_nw_le hWH_ext
              have hWHC_ext : IWorldHistCounter nw' (edgesH ++ [newE]) := by
                simp only [IWorldHistCounter, List.length_append, List.length_cons,
                  List.length_nil] at hWHC_head ⊢
                omega
              refine ih (doneAug ++ [augH ++ [newE]] ++ augT) []
                  (doneLB ++ [lbH] ++ lbT) []
                  (IAllConsistent_append
                    (IAllConsistent_append hDone ⟨hIC_ext, hLB_ext, trivial⟩)
                    hPendingTail)
                  (by simp only [List.length_append, List.length_cons, List.length_nil]
                      omega)
                  (by simp only [List.length_append, List.length_cons, List.length_nil]
                      omega)
                  trivial rfl rfl
                  (IAllAccessConsistent_append
                    (IAllAccessConsistent_append hDoneACC ⟨hACC_ext, trivial⟩) hACCTail)
                  trivial
                  (IAllReuseContain_append
                    (IAllReuseContain_append hDoneARC ⟨hARC_ext, trivial⟩) hARCTail)
                  trivial
                  (IAllUniv_append
                    (IAllUniv_append hUnivD
                      (fun b' hb' => by
                        simp only [List.mem_singleton] at hb'; subst hb'; exact hUniv_ext))
                    hUnivP_tail)
                  (IAllNW_append
                    (IAllNW_append hNWD
                      (fun nw2 hnw2 => by
                        simp only [List.mem_singleton] at hnw2; subst hnw2; exact hNW_ext))
                    hNWP_tail)
                  (IAllFuel_append
                    (IAllFuel_append hFuelD ⟨hFuel_ext, trivial⟩) hFuelP_tail)
                  (by simp [IAllUniv]) (by simp [IAllNW]) trivial
                  (IAllLabelBoundStrict_append
                    (IAllLabelBoundStrict_append hLBSD ⟨hLBS_ext, trivial⟩) hLBSP_tail)
                  (by simp [IAllLabelBoundStrict])
                  (IAllWorldHist_append
                    (IAllWorldHist_append hWHD ⟨hWH_ext, trivial⟩) hWHP_tail)
                  (by simp [IAllWorldHist])
                  (IAllWorldHistCounter_append
                    (IAllWorldHistCounter_append hWHCD ⟨hWHC_ext, trivial⟩) hWHCP_tail)
                  (by simp [IAllWorldHistCounter])
                  hgo
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
  | case8 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT fT f'
      branches' nw' newExp bPers hcl hstep ih =>
    intro pendingAug doneAug pendingLB doneLB hPending hLenP hLenPF hDone hLenD hLenDF
        hPendingACC hDoneACC hPendingARC hDoneARC hUnivP hNWP hFuelP hUnivD hNWD hFuelD
        hLBSP hLBSD hWHP hWHD hWHCP hWHCD hgo
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    have hUnivP_head : ∀ x ∈ bh, x ∈ intUniverseExt φ0 := hUnivP bh List.mem_cons_self
    have hUnivP_tail : IAllUniv φ0 bt :=
      fun b' hb' => hUnivP b' (List.mem_cons_of_mem bh hb')
    have hNWP_head : nwH ≤ WBound φ0 := hNWP nwH List.mem_cons_self
    have hNWP_tail : IAllNW φ0 nwT :=
      fun nw2 hnw2 => hNWP nw2 (List.mem_cons_of_mem nwH hnw2)
    simp only [IAllFuel] at hFuelP
    obtain ⟨hFuel_bh_eH, hFuelP_tail⟩ := hFuelP
    simp only [IAllLabelBoundStrict] at hLBSP
    obtain ⟨hLBS_bh_nwH, hLBSP_tail⟩ := hLBSP
    simp only [IAllWorldHist] at hWHP
    obtain ⟨hWH_head, hWHP_tail⟩ := hWHP
    simp only [IAllWorldHistCounter] at hWHCP
    obtain ⟨hWHC_head, hWHCP_tail⟩ := hWHCP
    have hUniv_bPers : ∀ x ∈ bPers, x ∈ intUniverseExt φ0 :=
      applyPersistenceFixpoint_subset_ext bh edgesH (f' + 1) hUnivP_head
    have hFuel_bPers : intWork (intUniverseExt φ0) bPers eH < f' + 1 :=
      lt_of_le_of_lt (intWork_persistence_le (intUniverseExt φ0) bh edgesH (f' + 1) eH)
        hFuel_bh_eH
    have hLBS_bPers : ILabelBoundStrict bPers nwH :=
      ILabelBoundStrict_applyPersistenceFixpoint (f' + 1) hLBS_bh_nwH
    split at hgo
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i heq
      have hcon := hstep.symm.trans heq
      simp at hcon
    · rename_i branches1 nw1 newExp1 heq
      have hsome := hstep.symm.trans heq
      simp only [Option.some.injEq, Prod.mk.injEq,
        IntRuleResult.branchingResult.injEq] at hsome
      obtain ⟨⟨hB, hN⟩, hX⟩ := hsome
      subst hB; subst hN; subst hX
      simp only [IAllConsistent] at hPending
      obtain ⟨hIC_bh_eH, hLB_bh_nwH, hPendingTail⟩ := hPending
      cases hpAug : pendingAug with
      | nil =>
        rw [hpAug] at hPendingACC
        simp only [IAllAccessConsistent] at hPendingACC
      | cons augH augT =>
        rw [hpAug] at hPendingACC
        simp only [IAllAccessConsistent] at hPendingACC
        obtain ⟨hACC_bh_eH, hACCTail⟩ := hPendingACC
        cases hpLB : pendingLB with
        | nil =>
          rw [hpLB] at hPendingARC
          simp only [IAllReuseContain] at hPendingARC
        | cons lbH lbT =>
          rw [hpLB] at hPendingARC
          simp only [IAllReuseContain] at hPendingARC
          obtain ⟨hARC_bh_head, hARCTail⟩ := hPendingARC
          simp only [List.length_cons] at hLenP hLenPF
          have hLenPt : bt.length = edgesT.length := by omega
          have hLenPFt : fT.length = bt.length := by omega
          have hmemP : ∀ y ∈ bh, y ∈ bPers :=
            fun y hy => applyPersistenceFixpoint_mem_preserved bh edgesH (f' + 1) y hy
          have hIC_bPers : IExpandedConsistent bPers eH :=
            IExpandedConsistent_mono hmemP hIC_bh_eH
          have hLB_bPers : ILabelBound bPers nwH :=
            ILabelBound_applyPersistenceFixpoint (f' + 1) hLB_bh_nwH
          have hACC_bPers : IExpandedAccessConsistent augH bPers eH :=
            IExpandedAccessConsistent_mono hmemP hACC_bh_eH
          have hbr := intStepBranch_branch_preserves hIC_bPers hLB_bPers hACC_bPers
            (intStepBranchPrio_some_exists hstep)
          have hbrLBS := intStepBranch_branch_preserves_labelStrict hLBS_bPers
            (intStepBranchPrio_some_exists hstep)
          -- R1 threading: hUniv, hNW, hFuel for every BETA child
          -- `Branch.extendMany bPers br`, `br ∈ branches'`.
          have hUniv_branch := intStepBranch_branch_preserves_univ hUniv_bPers hNWP_head
            (intStepBranchPrio_some_exists hstep)
          have hnw'_eq : nw' = nwH :=
            intStepBranch_branch_preserves_nw (intStepBranchPrio_some_exists hstep)
          have hNW_ext : nw' ≤ WBound φ0 := by rw [hnw'_eq]; exact hNWP_head
          obtain ⟨sf, hsfb, hsfe, -, hnewExp⟩ :=
            intStepBranch_some_exists_fuel (intStepBranchPrio_some_exists hstep)
          have hsfU : sf ∈ intUniverseExt φ0 := hUniv_bPers sf hsfb
          have hFuel_branch : ∀ br ∈ branches', intWork (intUniverseExt φ0)
              (Branch.extendMany bPers br) newExp < f' := by
            intro br _hbr
            have hsub : ∀ z ∈ bPers, z ∈ Branch.extendMany bPers br :=
              fun z hz => by simp only [Branch.extendMany, List.mem_append]; exact Or.inr hz
            have hdrop := intWork_drop (intUniverseExt φ0) bPers
              (Branch.extendMany bPers br) eH sf hsfU hsfe hsub
            rw [← hnewExp] at hdrop
            omega
          have hARC_branch : ∀ br ∈ branches', IReuseContain lbH (Branch.extendMany bPers br) := by
            intro br _hbr
            exact IReuseContain_mono
              (fun x hx => by
                simp only [Branch.extendMany, List.mem_append]; exact Or.inr (hmemP x hx))
              hARC_bh_head
          -- `IWorldHist` transfer for the BETA (branching) arm: `nw`/`edges` are unchanged
          -- (`hnw'_eq`), `newExp` only grows (`hnewExp`), and every child branch is
          -- `Branch.extendMany bPers br`, so the same monotone witness transfers to each.
          have hexp_ext : ∀ x ∈ eH, x ∈ newExp := fun x hx => hnewExp ▸ List.mem_append_left _ hx
          have hWH_branch : ∀ br ∈ branches',
              IWorldHist φ0 (Branch.extendMany bPers br) newExp nw' edgesH := by
            intro br _hbr
            rw [hnw'_eq]
            exact IWorldHist_mono
              (fun x hx => by
                simp only [Branch.extendMany, List.mem_append]; exact Or.inr (hmemP x hx))
              hexp_ext hWH_head
          have hWHC_ext : IWorldHistCounter nw' edgesH := by rw [hnw'_eq]; exact hWHC_head
          refine ih (doneAug ++ branches'.map (fun _ => augH) ++ augT) []
              (doneLB ++ branches'.map (fun _ => lbH) ++ lbT) []
              (IAllConsistent_append
                (IAllConsistent_append hDone
                  (IAllConsistent_map (Branch.extendMany bPers ·)
                    (fun br hbr' => ⟨(hbr br hbr').1, (hbr br hbr').2.1⟩)))
                hPendingTail)
              (by simp only [List.length_append, List.length_map]
                  omega)
              (by simp only [List.length_append, List.length_map]
                  omega)
              trivial rfl rfl
              (IAllAccessConsistent_append
                (IAllAccessConsistent_append hDoneACC
                  (IAllAccessConsistent_map (Branch.extendMany bPers ·)
                    (fun br hbr' => (hbr br hbr').2.2)))
                hACCTail)
              trivial
              (IAllReuseContain_append
                (IAllReuseContain_append hDoneARC
                  (IAllReuseContain_map_const (Branch.extendMany bPers ·) hARC_branch))
                hARCTail)
              trivial
              (IAllUniv_append
                (IAllUniv_append hUnivD (IAllUniv_map (Branch.extendMany bPers ·) hUniv_branch))
                hUnivP_tail)
              (IAllNW_append
                (IAllNW_append hNWD (IAllNW_map_const (l := branches') hNW_ext))
                hNWP_tail)
              (IAllFuel_append
                (IAllFuel_append hFuelD
                  (IAllFuel_map (Branch.extendMany bPers ·) hFuel_branch))
                hFuelP_tail)
              (by simp [IAllUniv]) (by simp [IAllNW]) trivial
              (IAllLabelBoundStrict_append
                (IAllLabelBoundStrict_append hLBSD
                  (IAllLabelBoundStrict_map (Branch.extendMany bPers ·) hbrLBS))
                hLBSP_tail)
              (by simp [IAllLabelBoundStrict])
              (IAllWorldHist_append
                (IAllWorldHist_append hWHD
                  (IAllWorldHist_map_const (f := Branch.extendMany bPers) hWH_branch))
                hWHP_tail)
              (by simp [IAllWorldHist])
              (IAllWorldHistCounter_append
                (IAllWorldHistCounter_append hWHCD
                  (IAllWorldHistCounter_map_const (l := branches') hWHC_ext))
                hWHCP_tail)
              (by simp [IAllWorldHistCounter])
              hgo
    · rename_i heq
      have hcon := hstep.symm.trans heq
      simp at hcon
  | case9 done doneExp doneNW doneEdges doneFuels bh bt eH eT nwH nwT edgesH edgesT fT f'
      snd bPers hcl hstep =>
    intro pendingAug doneAug pendingLB doneLB hPending hLenP hLenPF hDone hLenD hLenDF
        hPendingACC hDoneACC hPendingARC hDoneARC _hUnivP _hNWP _hFuelP _hUnivD _hNWD
        _hFuelD _hLBSP _hLBSD _hWHP _hWHD _hWHCP _hWHCD hgo
    simp only [intExpandBranches.go] at hgo
    rw [if_neg hcl] at hgo
    split at hgo
    · rename_i heq
      exact absurd (hstep.symm.trans heq) (by simp)
    · rename_i heq
      have hcon := hstep.symm.trans heq
      simp at hcon
    · rename_i heq
      have hcon := hstep.symm.trans heq
      simp at hcon
    · exact absurd rfl (intStepBranchPrio_result_ne_notApplicable hstep)
  | case10 done doneExp doneNW doneEdges doneFuels head restBs pExp pNW pEdges pFuels
      hmismatch ih =>
    intro pendingAug doneAug pendingLB doneLB hPending hLenP hLenPF hDone hLenD hLenDF
        hPendingACC hDoneACC hPendingARC hDoneARC _hUnivP _hNWP _hFuelP _hUnivD _hNWD
        _hFuelD _hLBSP _hLBSD _hWHP _hWHD _hWHCP _hWHCD hgo
    cases hpE : pExp with
    | nil =>
      rw [hpE] at hPending
      simp only [IAllConsistent] at hPending
    | cons eH eT =>
      cases hpN : pNW with
      | nil =>
        rw [hpE, hpN] at hPending
        simp only [IAllConsistent] at hPending
      | cons nwH nwT =>
        cases hpEd : pEdges with
        | nil =>
          rw [hpEd] at hLenP
          simp only [List.length_nil, List.length_cons] at hLenP
          omega
        | cons edgesH edgesT =>
          cases hpF : pFuels with
          | nil =>
            rw [hpF] at hLenPF
            simp only [List.length_nil, List.length_cons] at hLenPF
            omega
          | cons f restFs =>
            exact absurd
              (hmismatch eH eT nwH nwT edgesH edgesT f restFs hpE hpN hpEd hpF)
              id

/-! ## Parametric Open Branch Countermodel -/

/-- **Parametric Open Branch Countermodel**: An open branch returned by the parametric
expansion witnesses that `φ` is not forced in the branch-derived Kripke model.

If the expansion with `S.closurePred` returns `.openBranch b`, then the extracted
valuation `intExtractValuation b` with `botForces = S.modelBot b` falsifies `φ` at
world 0.

- At `intScheme`: specializes to `intuitionisticOpenBranch_countermodel`.
- At `minScheme`: specializes to `minOpenBranch_countermodel`.

## Proof structure

The proof is currently a single `sorry` over the whole existential (see the sorry-site comment
below): no `edges` witness is committed. An earlier revision extracted `h`'s structural facts
(`hopen`, `hsat`/`hfimp`, `hFmem : F(φ)@0 ∈ b`, and `edges` itself via
`intExpandBranches_openBranch_sat`) and closed the `¬IForces` conjunct with
`(truthLemma S b edges hopen hsat hfimp hpers φ 0).2 hFmem`, committed to the AUGMENTED
`augSets` witness via an early `refine` -- but `hpers` is REFUTED at that frame (see the
frame-adequacy table below), so that route cannot supply `truthLemma`'s hypotheses honestly.
The identical extraction machinery survives verbatim in `openBranch_rawEdges_upward_closed`
immediately below, so it is available to a future attempt without being re-derived; existentially
packaging `edges` here (rather than fixing it) is a Postmortem-5 revision -- this internal
conclusion MAY expose `edges`, while the stable public `tableau_complete`/`Decidable` contract,
discharged elsewhere, does not.

**Statement-shape fix (upward-closure conjuncts).** The conclusion existentially quantifies over
`edges`, unlike the machine-verified defective premise `tableau_complete` used to demand
(`CslibTests/HvalidShapeRefutation.lean`, `lake env lean` clean, zero sorries: `hvalid`'s old
unconstrained-`(edges, b)` shape is false at a concrete witness even though the formula it is
applied to is valid). Moving the obligation here, where `b`'s real provenance
(`hUniv`/`hFuel`/`hACC` from `intExpandBranches_openBranch_sat`) is in scope, is what makes it
fillable at all. `tableau_complete` itself stays sorry-free; only this lemma carries the deferred
obligation, relocated from the unfillable shape DP-3/DP-4 used to have.

**Third conjunct: `S.modelBot b`'s upward-closure.** The existential carries a THIRD conjunct
beyond the valuation upward-closure and the `¬IForces` obligation:
`∀ {w w'}, w ≤ w' → S.modelBot b w → S.modelBot b w'`. This mirrors the analogous, previously
missing conjunct of `MValid`/`IValid` (`CslibTests/MvalidBotShapeRefutation.lean` machine-checks
that omitting it makes the old `hvalid` premise shape false even when the valuation conjunct
holds). Unlike conjunct 2 above, this third conjunct costs NOTHING beyond what conjunct 1
already proves: `openBranch_rawEdges_upward_closed`'s `χ`-general statement (proved above this
lemma) already discharges upward closure for ANY positive-formula shape at ONE shared `rawEdges`
witness, so `openBranch_rawEdges_both_upward_closed`'s valuation instance (`χ := .atom p`) and
`⊥`-shape instance (`χ := HasBot.bot`) are two instantiations of the same fact, not two separate
obligations. Whatever witness this lemma's still-open `sorry` eventually commits to for
conjuncts 1/2, if it is a sub-frame of `rawEdges` (any edge list `edges'` with
`∀ e ∈ edges', e ∈ rawEdges`), `intAccessPreorder_mono_subset` transfers BOTH upward-closure
facts to it for free -- the third conjunct never needs its own frame search.

**Open — no `edges` witness is committed by this proof.** Unlike an earlier revision, the proof
below does NOT `refine` a specific `edges` (e.g. the AUGMENTED `augSets` witness
`intExpandBranches_openBranch_sat` threads) and then `sorry` one conjunct over it — doing so
would put a REFUTED statement (see the frame-adequacy table below) behind the `sorry`. The whole
existential stays `sorry`, and that goal genuinely IS open, not refuted: `IValid φ` quantifies
over every preorder and every upward-closed valuation, so any refutation would have to exhibit
an IPC-valid `φ` on which the algorithm returns `.openBranch`, and no such `φ` is known or
sought here.

**Frame-adequacy table (machine-checked).** `truthLemma` consumes exactly two frame-dependent
facts: `IFimpAccess edges b` (F-imp case) and positive persistence `hpers` along `edges` (T-imp
case, DP-5, now discharged above). Conjunct 1 of this lemma is the atom-shaped special case of
`hpers`. The two edge lists the algorithm produces sit on OPPOSITE sides of this pair:

| frame | `IFimpAccess` | `hpers` |
|---|---|---|
| augmented (`augSets`) | holds (`:6924`) | REFUTED (`BetaSplitRefutation.lean`) |
| raw (`rawEdges`) | REFUTED (`phiRef1`/`phiRef2` @2, `phiRef3` @3,4) | holds (`IPosPersistRaw`) |

Both refutations are machine-checked against the real algorithm at the real fuel: no candidate
`edges` built from the algorithm's current output carries both predicates simultaneously, so no
`truthLemma` call — over either edge list — closes this lemma's `¬IForces` conjunct together
with a matching upward-closure proof.

**`rawEdges` is REFUTED as a conjunct-2 witness**, not merely unproved:
`CslibTests/WitnessProbe.lean:174-176` (`#eval check [(1,0),(2,1)]` reports `some (true, true)` —
upward-closed but FORCES `phiRef1` at world 0) together with
`CslibTests/BetaSplitRefutation.lean:304` (the algorithm's real raw edge list for `phiRef1` at
the real fuel `intFuelExt phiRef1` is exactly `[(1,0),(2,1)]`) and `:387`
(`branchesAgree = true`, confirming that recreated list matches the REAL `intuitionisticTableau`
run) together pin the algorithm's actual `rawEdges` output to a frame that satisfies conjunct 1
but FAILS conjunct 2.

**Three candidate sub-frame constructions are EXCLUDED**, not merely untried: pruning at blocked
worlds and pruning at strictly-blocked worlds contradict each other on the same syntactic signal
(the former fails `dblNeg`/`peirce`, the latter fails `phiRef3`), and the greatest
`IFimpAccess`-supported fixpoint `K` — the construction a truth-lemma proof would actually need,
since it makes the F-imp case close by construction — collapses to `K = ∅` for
`phiRef1`/`phiRef2`/`phiRef3` (the unsupported blocked world strands its parent, up to world 0).
The maximal atom-inclusion frame `⊑` was already excluded (fails `phiRef1`/`phiRef3`). None of
the five natural constructions tried is a uniform witness.

**The residual obligation is precisely this**: a frame carrying `IFimpAccess` and positive
persistence SIMULTANEOUSLY, which the current calculus does not produce. This IS the surviving
`sorry`'s goal, and it is OPEN, not refuted — the sub-frame search is not exhausted, merely
unsuccessful with the constructions tried, and conjunct 2 can hold WITHOUT a truth lemma at all
(e.g. `rawEdges` itself is a witness for `phiRef2`, even though the `IFimpAccess` fixpoint
collapses there too) — so truth-lemma routes are strictly stronger than the goal and can fail
where the goal succeeds.

**Root cause, out of this file's scope.** Every route above dead-ends on the same defect:
`intFImpReuseWitnessAnc?` (`Expansion.lean`) records a loop-back edge on a containment check it
never re-validates as the branch grows. Re-validating it is what would let the augmented frame
carry positive persistence, giving one frame with both predicates and collapsing this whole
problem — that is calculus-level work in `Expansion.lean`, tracked separately from this file.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4 -/
lemma openBranch_countermodel (S : IntMinScheme Atom) (φ : Proposition Atom)
    (b : IBranch Atom)
    (h : intExpandBranches [[⟨.neg, φ, 0⟩]] [[]] [1] [[]]
        [intFuelExt φ] S.closurePred = .openBranch b) :
    ∃ edges : IEdges,
      (∀ {w w' : Nat} (p : Atom), @LE.le Nat (intAccessPreorder edges).toLE w w' →
        intExtractValuation b w p → intExtractValuation b w' p) ∧
      (∀ {w w' : Nat}, @LE.le Nat (intAccessPreorder edges).toLE w w' →
        S.modelBot b w → S.modelBot b w') ∧
      ¬ @IForces Atom Nat (intAccessPreorder edges) (intExtractValuation b) (S.modelBot b) 0 φ
      := by
  -- sorry: the whole existential -- OPEN, not refuted (see the docstring's frame-adequacy
  -- table above for the full disposition). No `edges` witness is committed here: an earlier
  -- revision `refine`d the AUGMENTED `augSets` witness and then `sorry`d the upward-closure
  -- conjunct alone, which put a REFUTED statement (augmented-frame positive persistence,
  -- `CslibTests/BetaSplitRefutation.lean`) behind that `sorry`. `rawEdges` is REFUTED as a
  -- conjunct-2 witness (`CslibTests/WitnessProbe.lean:174-176`,
  -- `CslibTests/BetaSplitRefutation.lean:304,387`); three pruning-rule constructions and the
  -- `IFimpAccess` greatest fixpoint are EXCLUDED (collapse to `K = ∅`); the maximal
  -- atom-inclusion frame `⊑` was already excluded. The residual obligation is a frame carrying
  -- both `IFimpAccess` and positive persistence, which the current calculus does not produce --
  -- root cause is `intFImpReuseWitnessAnc?` (`Expansion.lean`), calculus-level work outside
  -- this file. The extraction/`refine` machinery an earlier revision used here survives
  -- verbatim in `openBranch_rawEdges_upward_closed` immediately below, so nothing is lost.
  sorry

/-- **Conjunct 1 of `openBranch_countermodel`, discharged uniformly for arbitrary `χ`.**
Constructs `edges` as `rawEdges` -- the tree-only parent-child edge witness
`intExpandBranches_openBranch_sat` already produces and `openBranch_countermodel` discards as
`_rawEdges` -- and proves upward-closure of positive `χ`-membership in `b` along
`intAccessPreorder rawEdges`, for ANY `χ : Proposition Atom`, not just `χ := .atom p`. Needs no
fact about the tableau algorithm beyond `IPosPersistRaw` (already sorry-free, `χ`-general at
`Scheme.lean:6701-6704`) plus `IWorldsPlanted` (the branch-entry-existence corollary of
`IWorldHist`'s (H3) clause, derived above) chained over one `Relation.ReflTransGen` step at a
time. Instantiating `χ` at `.atom p` recovers `intExtractValuation` upward-closure; instantiating
it at `HasBot.bot` gives `minBranchBotForces` upward-closure at the SAME `edges` witness -- see
`openBranch_rawEdges_both_upward_closed` immediately below.

Conjunct 2 (`¬ IForces ...`) is deliberately NOT addressed here. This lemma is decoupled from
`openBranch_countermodel`'s own `sorry` above, which commits to no `edges` witness at all (see
that lemma's docstring for the frame-adequacy table). Reconciling the two conjuncts over one
uniform `edges` is now KNOWN IMPOSSIBLE on the algorithm's current output, not merely
undone: `rawEdges` supports positive persistence but is REFUTED for `IFimpAccess`
(`CslibTests/BetaSplitRefutation.lean`, `CslibTests/WitnessProbe.lean:174-176`), while the
augmented frame `openBranch_countermodel` used to commit to supports `IFimpAccess` but is
REFUTED for positive persistence -- neither edge list the algorithm currently produces carries
both. Closing this gap is calculus-level work on `intFImpReuseWitnessAnc?` (`Expansion.lean`),
outside this file's scope. -/
lemma openBranch_rawEdges_upward_closed (S : IntMinScheme Atom) (φ : Proposition Atom)
    (b : IBranch Atom)
    (h : intExpandBranches [[⟨.neg, φ, 0⟩]] [[]] [1] [[]]
        [intFuelExt φ] S.closurePred = .openBranch b) :
    ∃ edges : IEdges,
      ∀ (χ : Proposition Atom) {w w' : Nat}, @LE.le Nat (intAccessPreorder edges).toLE w w' →
        b.any (fun sf => sf.sign == .pos && sf.formula == χ && sf.label == w) = true →
        b.any (fun sf => sf.sign == .pos && sf.formula == χ && sf.label == w') = true := by
  obtain ⟨_edges, rawEdges, _lbEdges, _nwF, _hsat, _hfimp, hpp, _hrc, _hfc, hwp⟩ :=
    intExpandBranches_openBranch_sat φ [[⟨.neg, φ, 0⟩]] [[]] [1] [[]] [intFuelExt φ]
      [[]] [[]] _ _
      (by simp [IAllConsistent, IExpandedConsistent, ILabelBound]) rfl rfl
      (by simp [IAllAccessConsistent, IExpandedAccessConsistent])
      (by simp [IAllReuseContain, IReuseContain])
      (fun b hb x hx => by
        simp only [List.mem_singleton] at hb
        subst hb
        simp only [List.mem_singleton] at hx
        subst hx
        exact mem_intUniverseExt_of (Nat.zero_le _) (intSubfmls_self_mem φ))
      (fun nw hnw => by simp only [List.mem_singleton] at hnw; subst hnw; exact WBound_pos φ)
      (by simp only [IAllFuel]; exact ⟨intWork_init_lt_intFuelExt φ, trivial⟩)
      (by simp [IAllLabelBoundStrict, ILabelBoundStrict])
      ⟨IWorldHist_entry _ _ _ _, trivial⟩
      ⟨IWorldHistCounter_entry, trivial⟩
      (fun b' hb' ψ w hmem hcontra => by
        simp only [posFormulasAt, List.mem_filterMap] at hcontra
        obtain ⟨sf, hsfmem, hif⟩ := hcontra
        by_cases hcond : sf.sign == .pos && sf.label == w
        · simp only [hcond, ite_true, Option.some.injEq] at hif
          simp only [Bool.and_eq_true] at hcond
          have hposAny : b'.any (fun sf => sf.sign == .pos && sf.formula == ψ && sf.label == w)
              = true :=
            List.any_eq_true.mpr ⟨sf, hsfmem, by simp [hcond.1, hcond.2, hif]⟩
          have hnegAny : b'.any (fun sf => sf.sign == .neg && sf.formula == ψ && sf.label == w)
              = true :=
            List.any_eq_true.mpr ⟨_, hmem, by simp⟩
          exact S.no_contradiction b' hb' ψ w ⟨hposAny, hnegAny⟩
        · simp only [hcond, Bool.false_eq_true, ite_false] at hif
          exact absurd hif (by simp))
      h
  refine ⟨rawEdges, ?_⟩
  intro χ w w' hle hval
  induction hle with
  | refl => exact hval
  | @tail y w2 hchain hstep ih =>
    by_cases hyw2 : y = w2
    · exact hyw2 ▸ ih
    · simp only [List.any_eq_true] at ih
      obtain ⟨sf, hsfb, hsfp⟩ := ih
      simp only [Bool.and_eq_true, beq_iff_eq] at hsfp
      obtain ⟨⟨hs, hf⟩, hl⟩ := hsfp
      have hsfeq : sf = (⟨.pos, χ, y⟩ : ISF Atom) := by cases sf; simp_all
      have hmem_y : (⟨.pos, χ, y⟩ : ISF Atom) ∈ b := hsfeq ▸ hsfb
      obtain ⟨p', hp'⟩ := isAccessible_target_mem_edges hstep hyw2
      have hentry : b.any (fun sf => sf.label == w2) = true := hwp w2 p' hp'
      have hmem_w2 : (⟨.pos, χ, w2⟩ : ISF Atom) ∈ b :=
        hpp χ y w2 hstep hmem_y hentry
      exact List.any_eq_true.mpr ⟨_, hmem_w2, by simp⟩

/-- Both of `openBranch_rawEdges_upward_closed`'s upward-closure instances -- valuation and
`⊥`-shape (`minBranchBotForces`) -- derived at one shared `edges` witness from a single call to
the `χ`-general lemma above. `minBranchBotForces` and `intExtractValuation` are the same
`List.any` shape at different formula constructors (`HasBot.bot` versus `.atom p`), so no
coercion is needed at either instantiation. This is the lemma that makes `minBranchBotForces`'s
upward closure "free" from the already-`χ`-general `IPosPersistRaw`: no new proof obligation,
just a second instantiation of the same generalized fact. -/
lemma openBranch_rawEdges_both_upward_closed (S : IntMinScheme Atom) (φ : Proposition Atom)
    (b : IBranch Atom)
    (h : intExpandBranches [[⟨.neg, φ, 0⟩]] [[]] [1] [[]]
        [intFuelExt φ] S.closurePred = .openBranch b) :
    ∃ edges : IEdges,
      (∀ {w w' : Nat} (p : Atom), @LE.le Nat (intAccessPreorder edges).toLE w w' →
        intExtractValuation b w p → intExtractValuation b w' p) ∧
      (∀ {w w' : Nat}, @LE.le Nat (intAccessPreorder edges).toLE w w' →
        minBranchBotForces b w → minBranchBotForces b w') := by
  obtain ⟨edges, hgen⟩ := openBranch_rawEdges_upward_closed S φ b h
  refine ⟨edges, ?_, ?_⟩
  · intro w w' p hle hval
    exact hgen (.atom p) hle hval
  · intro w w' hle hbot
    exact hgen (HasBot.bot : Proposition Atom) hle hbot

/-! ## Parametric Tableau Completeness -/

/-- **Parametric Tableau Completeness**: If `φ` is forced at world 0 in every
branch-derived Kripke model, then the parametric expansion closes on `φ`.

Proof: by contrapositive. If the expansion returns `.openBranch b`, then
`openBranch_countermodel S` gives `∃ edges, huc ∧ hbuc ∧ ¬ @IForces Atom Nat
(intAccessPreorder edges) (intExtractValuation b) (S.modelBot b) 0 φ` (Route (a)), where `huc`
is the upward-closure of `intExtractValuation b` and `hbuc` is the upward-closure of
`S.modelBot b`, both along `intAccessPreorder edges`; feeding all three to
`hvalid edges b huc hbuc` contradicts the `¬IForces` conjunct.

**Statement-shape fix.** `hvalid` now accepts BOTH upward-closure facts as explicit hypotheses
rather than demanding `IForces` unconditionally at an arbitrary, unconstrained `(edges, b)` pair
-- the old shape (valuation premise only) was machine-verified FALSE as a consequence of
`IValid φ`/`MValid φ` in two separate ways: `CslibTests/HvalidShapeRefutation.lean`
(`IValid (p → (q → p))` holds while the old `hvalid`'s body is false at `edges = [(1, 0)]`,
`b = [T(p)@0, T(q)@1]`, a valuation that is not upward-closed) and
`CslibTests/MvalidBotShapeRefutation.lean` (the `⊥`-shape analogue: `MValid` true, valuation
upward-closed, `bot_forces` upward-closure still missing, `hvalid`'s body still false). The
hypothesis `hvalid` encodes the per-scheme validity notion, quantified over the
`edges`-parameterized `intAccessPreorder` frame (Route (a): `edges` is only discovered inside
`openBranch_countermodel`'s own proof, so `hvalid` must accept it as an argument), now WITH both
upward-closure premises `openBranch_countermodel` supplies:
- For `intScheme` (where `modelBot b = fun _ => False`): `hvalid edges b huc hbuc` follows from
  `IValid φ` applied at World `= ℕ` with the `intAccessPreorder edges` instance,
  `val = intExtractValuation b`, using `huc` and `hbuc` directly as `IValid`'s two
  upward-closure hypotheses (`hbuc` is trivial here, since `modelBot` is always `False`).
- For `minScheme` (where `modelBot b = minBranchBotForces b`): `hvalid edges b huc hbuc` follows
  from `MValid φ` applied analogously, using `huc` for `MValid`'s valuation upward-closure
  hypothesis and `hbuc` for its `bot_forces` upward-closure hypothesis -- both supplied together
  by `openBranch_countermodel`, not established separately.

This theorem is sorry-free given `openBranch_countermodel S`; the deferred obligation (proving
`huc`/`hbuc` themselves) now lives entirely inside `openBranch_countermodel`, not in `hvalid`'s
callers.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4 -/
theorem tableau_complete (S : IntMinScheme Atom) (φ : Proposition Atom)
    (hvalid : ∀ (edges : IEdges) (b : IBranch Atom),
      (∀ {w w' : Nat} (p : Atom), @LE.le Nat (intAccessPreorder edges).toLE w w' →
        intExtractValuation b w p → intExtractValuation b w' p) →
      (∀ {w w' : Nat}, @LE.le Nat (intAccessPreorder edges).toLE w w' →
        S.modelBot b w → S.modelBot b w') →
      @IForces Atom Nat (intAccessPreorder edges) (intExtractValuation b) (S.modelBot b) 0 φ) :
    intExpandBranches [[⟨.neg, φ, 0⟩]] [[]] [1] [[]]
        [intFuelExt φ] S.closurePred = .closed := by
  by_contra hne
  cases hresult : intExpandBranches [[⟨.neg, φ, 0⟩]] [[]] [1] [[]]
      [intFuelExt φ] S.closurePred with
  | closed => exact hne hresult
  | openBranch b =>
    obtain ⟨edges, huc, hbuc, hcm⟩ := openBranch_countermodel S φ b hresult
    exact absurd (hvalid edges b huc hbuc) hcm

end Cslib.Logic.PL

end
