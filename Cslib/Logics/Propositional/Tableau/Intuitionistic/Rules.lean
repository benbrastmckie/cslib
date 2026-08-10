/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.Tableau.SignedFormula
public import Cslib.Logics.Propositional.Defs
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.SetLike
public import Mathlib.Tactic.ToAdditive

/-! # Intuitionistic Propositional Tableau Rules

This module defines the world-creating and world-persistent rules specific to the
intuitionistic propositional tableau, where `L = Nat` (labels index Kripke worlds).

## Intuitionistic Rules

The standard classical propositional rules apply at each world for `and`, `or`,
and the `T`-signed `bot`. The key differences from classical tableau are:

1. **F(φ → ψ) at world w**: World-creating rule. Creates a fresh world `w'` with:
   - `T(φ)` at `w'` (the antecedent is forced at the new world)
   - `F(ψ)` at `w'` (the consequent fails at the new world)
   - All `T(α)` formulas from world `w` propagated to `w'` (by persistence)

2. **T(φ → ψ) at world w**: Persistent rule. For each world `w'` accessible from `w`
   with `T(φ)` at `w'`, add `T(ψ)` at `w'`. This rule must be re-applied whenever
   new worlds are created.

3. **Closure**: A branch closes when it contains T(⊥) at any label, or when it contains
   T(φ) and F(φ) at the same label for some formula φ (complementary pair).

## World Management

The world counter starts at 0 and increases by 1 for each new world created.
Accessibility is tracked via explicit parent-child edges: world `w'` is accessible
from world `w` if there is a path `w = w₀ → w₁ → … → wₙ = w'` in the edge list,
or `w = w'` (reflexivity). Explicit edge tracking prevents sibling worlds from being
treated as accessible to one another.

## Accessibility Edges

Parent-child edges are stored as `List (Nat × Nat)` where each pair `(child, parent)`
records that `parent` is the direct parent of `child`. The reflexive-transitive closure
of these edges gives the Kripke accessibility relation. This explicit representation
replaces the earlier approximate proxy `w' ≥ w` which was incorrect for branching
formulas: at a branch point, two sibling worlds `w₁` and `w₂` both satisfy `wᵢ ≥ w`
for their common ancestor `w`, but `w₁` is NOT accessible from `w₂` or vice versa.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Section 2.2
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## World-Labeled Signed Formulas -/

/-- A signed formula labeled with a natural number (Kripke world index). -/
abbrev ISF (Atom : Type*) := SignedFormula (Proposition Atom) Nat

/-- A labeled branch for intuitionistic/minimal tableau. -/
abbrev IBranch (Atom : Type*) := List (ISF Atom)

/-! ## Accessibility Infrastructure -/

/-- Parent-child edge list for tracking Kripke accessibility.

Each pair `(child, parent)` records that `parent` is the direct predecessor of `child`
in the Kripke tree. The reflexive-transitive closure of these edges gives the actual
Kripke accessibility relation used by `T(φ → ψ)`. -/
abbrev IEdges := List (Nat × Nat)

/-- Check whether world `w'` is accessible from world `w` using a parent-child edge list.

Accessibility is the reflexive-transitive closure of the parent-child relation. This
function traverses the edge list to check reachability with a fuel bound to ensure
termination. The fuel equals the number of edges, which bounds the longest possible path. -/
def isAccessible (edges : IEdges) (w w' : Nat) : Bool :=
  if w == w' then true
  else
    -- DFS over the reverse edge graph: from `w`, which worlds are reachable.
    -- Uses `fuel` to bound the search depth and prevent non-termination.
    let rec @[nolint docBlame] go (current : Nat) (fuel : Nat) : Bool :=
      match fuel with
      | 0 => false
      | fuel' + 1 =>
        -- Find all direct children of current
        let children := edges.filterMap fun (child, parent) =>
          if parent == current then some child else none
        children.any fun child =>
          if child == w' then true
          else go child fuel'
    go w edges.length

/-! ## Intuitionistic Tableau State -/

/-- The state of the intuitionistic tableau expansion loop.

Tracks:
- `branch`: The current list of signed formulas with world labels.
- `nextWorld`: The next fresh world index to use when creating new worlds.
- `expanded`: The set of signed formulas already processed (to avoid re-expansion).

The accessibility relation is maintained by explicit parent-child edges threaded
through the expansion loop. -/
structure IntTableauState (Atom : Type*) where
  /-- The current branch with world-labeled signed formulas. -/
  branch : IBranch Atom
  /-- The next fresh world counter (0-indexed). -/
  nextWorld : Nat
  /-- The set of already-expanded signed formulas (to avoid re-expansion). -/
  expanded : List (ISF Atom)

/-! ## Persistence Propagation -/

/-- Collect all T-signed formulas at world `w` on the branch (for persistence propagation). -/
def posFormulasAt (b : IBranch Atom) (w : Nat) : List (Proposition Atom) :=
  b.filterMap fun sf =>
    if sf.sign == .pos && sf.label == w then some sf.formula else none

/-- Propagate all T(α) formulas from world `w` to fresh world `w'`.

By the intuitionistic persistence lemma, if T(α) holds at world `w` and `w ≤ w'`,
then T(α) must hold at `w'`. We propagate atoms and implications (not disjunctions,
since intuitionistic disjunction does not persist -- only the split forces persistence
at each branch). Actually, ALL positive formulas persist in the Kripke model. We
propagate all of them to ensure correctness.

The propagated formulas are added to the branch with label `w'`. -/
def propagatePersistence (b : IBranch Atom) (fromWorld toWorld : Nat) : IBranch Atom :=
  let tFormulas := posFormulasAt b fromWorld
  tFormulas.map fun φ => ⟨.pos, φ, toWorld⟩

/-! ## World-Creating Rules -/

/-- Apply the F(φ → ψ) world-creating rule at world `w`.

Creates a fresh world `w' = nextWorld` and adds:
- `T(φ)` at `w'` (antecedent forced at new world)
- `F(ψ)` at `w'` (consequent fails at new world)
- Propagation of all T(α) from `w` to `w'` (persistence from `w` to successor `w'`)

Returns the new signed formulas to add to the branch, the next world counter, and
the new parent-child edge `(w', w)` recording that `w` is the direct parent of `w'`. -/
def intFImpRule (φ ψ : Proposition Atom) (w nextWorld : Nat) (b : IBranch Atom) :
    List (ISF Atom) × Nat × (Nat × Nat) :=
  let w' := nextWorld
  let newForms : List (ISF Atom) := [⟨.pos, φ, w'⟩, ⟨.neg, ψ, w'⟩]
  let persistent := propagatePersistence b w w'
  (newForms ++ persistent, nextWorld + 1, (w', w))

/-! ## Persistent T(φ → ψ) Handling -/

/-- Apply T(φ → ψ) at world `w` for all worlds `w'` accessible from `w`.

For each world label `w'` on the branch accessible from `w` (via the explicit edge list),
if `T(φ)` is at `w'` and `T(ψ)` is not yet at `w'`, add `T(ψ)` at `w'`.

This implements the intuitionistic truth condition for implication:
  `⊩_w (φ → ψ)` iff `∀ w' accessible from w, ⊩_{w'} φ → ⊩_{w'} ψ`

The rule fires at all worlds accessible via the parent-child edge list, including `w`
itself (reflexivity). This replaces the earlier `>= w` proxy which treated sibling
worlds as accessible to one another. -/
def intTImpRule (φ ψ : Proposition Atom) (w : Nat) (edges : IEdges) (b : IBranch Atom) :
    List (ISF Atom) :=
  -- Get all worlds w' on the branch that are accessible from w (including w itself)
  let accessibleWorlds := (b.map (·.label)).eraseDups.filter (isAccessible edges w ·)
  accessibleWorlds.filterMap fun w' =>
    -- If T(φ) is at w' and T(ψ) is not yet at w', add T(ψ) at w'
    if b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w') then
      if b.any (fun sf => sf.sign == .pos && sf.formula == ψ && sf.label == w') then
        none  -- T(ψ) already present
      else
        some ⟨.pos, ψ, w'⟩
    else
      none  -- T(φ) not present at w', rule doesn't fire

/-! ## Intuitionistic Rule Application -/

/-- Apply intuitionistic propositional rules to a single signed formula.

For `T`-signed and `F`-signed formulas, applies the appropriate rule:
- `T(φ ∧ ψ)`: alpha-rule (linear) -- add T(φ) and T(ψ)
- `F(φ ∧ ψ)`: beta-rule (branching) -- branch to F(φ) or F(ψ)
- `T(φ ∨ ψ)`: beta-rule (branching) -- branch to T(φ) or T(ψ)
- `F(φ ∨ ψ)`: alpha-rule (linear) -- add F(φ) and F(ψ)
- `F(φ → ψ)`: world-creating (linear, increments world counter)
- `T(φ → ψ)`: persistent rule (handled separately via `intTImpRule`)
- `F(¬φ)` = `F(φ → ⊥)`: same as `F(φ → ψ)` with ψ = ⊥
- `T(¬φ)` = `T(φ → ⊥)`: same as `T(φ → ψ)` with ψ = ⊥

For intuitionistic tableau, ALL implications (including negation) use the implication rules,
matching directly on `.imp` since `¬φ` is represented as `φ → ⊥`. -/
def intApplyRule (sf : ISF Atom) (nextWorld : Nat) (b : IBranch Atom) :
    Option (List (ISF Atom) × Nat) :=
  let l := sf.label
  match sf.sign, sf.formula with
  -- T(φ ∧ ψ): add T(φ), T(ψ) at same world
  | .pos, .and φ ψ =>
    some ([⟨.pos, φ, l⟩, ⟨.pos, ψ, l⟩], nextWorld)
  -- F(φ ∧ ψ): branching -- but we handle by picking one branch (linearized)
  -- Actually the tableau branches; we return the list of options
  -- For the expansion loop, we need to handle branching separately
  -- T(φ ∨ ψ): branching
  -- F(φ ∨ ψ): add F(φ), F(ψ)
  | .neg, .or φ ψ =>
    some ([⟨.neg, φ, l⟩, ⟨.neg, ψ, l⟩], nextWorld)
  -- F(φ → ψ) including F(¬φ) = F(φ → ⊥): world-creating
  | .neg, .imp φ ψ =>
    let (newForms, nextWorld', _edge) := intFImpRule φ ψ l nextWorld b
    some (newForms, nextWorld')
  -- T(φ → ψ) including T(¬φ): persistent, handled by intTImpRule
  -- F(⊥): never fires (bot is always false in classical/int/min)
  -- Default: not applicable
  | _, _ => none

/-! ## Branching Rule Result -/

/-- Result of an intuitionistic expansion step.

- `linearResult newForms nextWorld' newEdge`: The rule added formulas linearly (alpha-rule
  or world-creation). `newEdge` carries the new parent-child edge from `intFImpRule`, or
  `none` for non-world-creating alpha rules.
- `branchingResult branches nextWorld'`: The rule branched (beta-rule for ∧F or ∨T).
- `notApplicable`: No rule fired. -/
inductive IntRuleResult (Atom : Type*) : Type _ where
  /-- Linear rule: add formulas to current branch. Optional new edge from world-creation. -/
  | linearResult : List (ISF Atom) → Nat → Option (Nat × Nat) → IntRuleResult Atom
  /-- Branching rule: split into multiple branches. -/
  | branchingResult : List (List (ISF Atom)) → Nat → IntRuleResult Atom
  /-- No rule applies. -/
  | notApplicable : IntRuleResult Atom

/-- Apply intuitionistic rules to a signed formula, handling both linear and branching cases. -/
def intApplyRuleFull (sf : ISF Atom) (nextWorld : Nat) (b : IBranch Atom) :
    IntRuleResult Atom :=
  let l := sf.label
  match sf.sign, sf.formula with
  -- T(φ ∧ ψ): alpha-rule
  | .pos, .and φ ψ =>
    .linearResult [⟨.pos, φ, l⟩, ⟨.pos, ψ, l⟩] nextWorld none
  -- F(φ ∧ ψ): beta-rule (branch to F(φ) or F(ψ))
  | .neg, .and φ ψ =>
    .branchingResult [[⟨.neg, φ, l⟩], [⟨.neg, ψ, l⟩]] nextWorld
  -- T(φ ∨ ψ): beta-rule (branch to T(φ) or T(ψ))
  | .pos, .or φ ψ =>
    .branchingResult [[⟨.pos, φ, l⟩], [⟨.pos, ψ, l⟩]] nextWorld
  -- F(φ ∨ ψ): alpha-rule
  | .neg, .or φ ψ =>
    .linearResult [⟨.neg, φ, l⟩, ⟨.neg, ψ, l⟩] nextWorld none
  -- F(φ → ψ) and F(¬φ) = F(φ → ⊥): world-creating alpha-rule
  | .neg, .imp φ ψ =>
    let (newForms, nextWorld', edge) := intFImpRule φ ψ l nextWorld b
    .linearResult newForms nextWorld' (some edge)
  -- T(φ → ψ) and T(¬φ): beta-rule (Fitting Ch. 4 split), branch to F(φ)@l or T(ψ)@l, at the
  -- SAME world `l = sf.label` this specific copy of T(φ → ψ) is labeled at. This coexists with
  -- (does not replace) the persistent positive-propagation rule `intTImpRule`/
  -- `applyAllTImpRules`, which now also copies T(φ → ψ) itself to every world accessible from
  -- `l` lacking its own copy (`applyAllTImpRules` below), so each accessible world eventually
  -- gets an independent reflexive resolution here -- realizing "for every w' accessible from w"
  -- without this rule itself needing an `edges` parameter. Guarded to fire at most once per
  -- (implication, world) pair for free: `intStepBranch`'s `expanded` set tracks the exact
  -- `⟨.pos, φ → ψ, l⟩` triple, and each accessible world's copy is a distinct triple.
  | .pos, .imp φ ψ =>
    .branchingResult [[⟨.neg, φ, l⟩], [⟨.pos, ψ, l⟩]] nextWorld
  -- T(⊥): closed by IntuitionisticClosure -- not expanded
  -- All others: atoms, bot, etc.
  | _, _ => .notApplicable

/-- Whether a signed formula's bare `(sign, formula)` shape carries an intuitionistic tableau
rule at all: true for `.and`/`.or` in either sign and `.imp` in either sign (world-creating
`F(φ → ψ)` included), false for atoms and `⊥` in either sign. Independent of `nextWorld`/`b` --
mirrors `intApplyRuleFull`'s match exactly, and `intApplyRuleFull_notApplicable_iff` below
confirms it characterizes `intApplyRuleFull`'s `.notApplicable` result precisely, for every
`nextWorld`/`b`. Used by the beta-priority freeze argument (plan Phase 5,
`Expansion.lean`'s `IFrozenBelow`): a formula outside this shape can never generate new branch
content, regardless of how many times it is (re-)considered. -/
def isRuleShape (sf : ISF Atom) : Bool :=
  match sf.sign, sf.formula with
  | .pos, .and _ _ | .neg, .and _ _ | .pos, .or _ _ | .neg, .or _ _
  | .neg, .imp _ _ | .pos, .imp _ _ => true
  | _, _ => false

omit [DecidableEq Atom] [Hashable Atom] in
/-- `intApplyRuleFull sf nextWorld b = .notApplicable` exactly when `sf`'s shape carries no
rule (`isRuleShape sf = false`), for every `nextWorld`/`b`: `intApplyRuleFull`'s six non-
`.notApplicable` clauses are exactly the six `isRuleShape`-true shapes, and none of them ever
returns `.notApplicable` (each constructs a `.linearResult` or `.branchingResult` outright). -/
lemma intApplyRuleFull_notApplicable_iff (sf : ISF Atom) (nextWorld : Nat) (b : IBranch Atom) :
    intApplyRuleFull sf nextWorld b = .notApplicable ↔ isRuleShape sf = false := by
  rcases sf with ⟨s, f, l⟩
  cases s <;> cases f <;> simp [intApplyRuleFull, isRuleShape]

end Cslib.Logic.PL

end
