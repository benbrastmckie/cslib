/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Tableau.Intuitionistic.Rules
public import Cslib.Foundations.Logic.Tableau.ClosureCondition
public import Cslib.Logics.Propositional.Subformula

/-! # Intuitionistic Propositional Tableau Expansion

This module implements the expansion loop for the intuitionistic propositional tableau.
The intuitionistic tableau uses `L = Nat` (Kripke world indices) and the
`IntuitionisticClosure` instance (closes on T(⊥) at any label, or on complementary
T(φ)/F(φ) pairs at the same label).

## Main Definitions

- `IntTableauResult`: Result of the intuitionistic expansion (closed or open).
- `intExpandBranches`/`propExpandBranches`: Fuel-based expansion loop, **parameterized by
  `closurePred`** — the generic workhorse. `intuitionisticTableau` instantiates it with
  `isIntuitionisticallyClosed`; `minimalTableau` instantiates it with `isMinimallyClosed`.
  `propExpandBranches` is an alias that emphasizes this generic, closure-predicate-parameterized
  design.
- `intuitionisticTableau`: Starting from `F(φ)` at world 0, closes iff `IValid φ`.
- `minimalTableau`: Same as above but uses `isMinimallyClosed`; closes iff `MValid φ`.

## Tableau Unification

The two divergence points between intuitionistic and minimal tableau are:
1. **Closure predicate**: `isIntuitionisticallyClosed` vs `isMinimallyClosed`.
2. **Bottom forcing in countermodel**: `fun _ _ => False` vs `minBranchBotForces b`.

Point 1 is handled here by the `closurePred` parameter.
Point 2 is handled in `Intuitionistic/Scheme.lean` via `IntMinScheme`.

There is no duplicate expansion function: both tableau variants are instances of
the single `intExpandBranches`/`propExpandBranches` loop.

## Design

The expansion loop processes one branch at a time. Within each branch:
1. First apply the persistent T(φ → ψ) rule for all T-implication formulas on the branch.
2. Then pick the first unexpanded formula and apply the appropriate rule.
3. For world-creating rules, add the new world's formulas, update the world counter,
   and extend the edge list with the new parent-child edge.
4. For branching rules, split the current branch into sub-branches (each inheriting
   the current edge list).

The fuel bound uses `2^(2 * complexity φ)` to account for the exponential blowup
possible in intuitionistic tableaux (due to world creation and persistence propagation).

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Section 2.2
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Intuitionistic Tableau Result -/

/-- The result of an intuitionistic (or minimal) propositional tableau computation.

- `closed`: Every branch is closed (the formula is valid).
- `openBranch b`: An open saturated branch `b` exists, providing a Kripke countermodel. -/
inductive IntTableauResult (Atom : Type*) : Type _ where
  /-- All branches close: the formula is valid in the logic. -/
  | closed : IntTableauResult Atom
  /-- An open saturated branch exists: the formula is not valid. -/
  | openBranch : IBranch Atom → IntTableauResult Atom

/-! ## Closure Check -/

/-- Check whether an intuitionistic branch is closed.

A branch is intuitionistically closed when either:
1. T(⊥) appears at any label (via the `IntuitionisticClosure` instance), or
2. T(φ) and F(φ) appear at the same label for some formula φ (complementary pair).

Note: complementary pairs DO close an intuitionistic branch. Although the intuitionistic
semantics does not close on complementary pairs for non-atomic formulas at the semantic
level, the tableau calculus uses both closure conditions for completeness. -/
def isIntuitionisticallyClosed (b : IBranch Atom) : Bool :=
  @ClosureCondition.isClosed _ _ IntuitionisticClosure.instClosureConditionOfBEqOfHasBot b ||
  Branch.hasContradiction b

/-- Check whether a minimal branch is closed.

A branch is minimally closed when it contains T(φ) and F(φ) at the same world for
ANY formula φ. This uses `Branch.hasContradiction`, which checks all complementary pairs
(not just atomic formulas). This is equivalent to classical closure minus the T(⊥) rule:
minimal logic does not close on T(⊥) alone, but it does close on any T(φ)/F(φ) pair.

NOTE: An atom-only closure criterion was previously used, but this is insufficient for
correctness -- for example, `⊥ → ⊥` is minimally valid but the atom-only criterion fails
to close the branch containing T(⊥)/F(⊥) at the created world. -/
def isMinimallyClosed (b : IBranch Atom) : Bool :=
  Branch.hasContradiction b

/-! ## Persistence Application -/

/-- Apply all pending T(φ → ψ) rules to the current branch state.

For each T(φ → ψ) formula at world w on the branch, and for each accessible world
w' (reachable via the edge list from w) with T(φ) at w', if T(ψ) is not yet at w',
add T(ψ) at w'.

**STEP 1 (task 574): the `T(φ → ψ)` self-copy channel has been removed.** A prior
revision of this def also copied `T(φ → ψ)` itself to every accessible world lacking its
own copy ("Deliverable 6"), intended to feed `intApplyRuleFull`'s `.pos, .imp` branching arm
at every accessible world. Task 574's Phase 1 divergence probe
(`specs/574_tableau_calculus_repair_ancestor_blocking/handoffs/01_variant-selection.md`,
Table 3, variant V3) measured that this self-copy is **not** the mechanism that bounds world
creation: with ancestor-directed loop-check blocking active (`intFImpReuseWitnessAnc?`, Phase
3 of that plan), removing the self-copy channel entirely reaches the *exact same* saturated
branch (`len=219, maxLabel=21, distinctLabels=22`) as keeping it. The self-copy was, at best,
redundant hygiene; at worst, a second unbounded-growth feed alongside `propagatePersistence`
(`Rules.lean`) — see D3 in the task's plan. `sat_timp` as an `IBranchSaturation` *field* is
unaffected by this removal: it is stated reflexively at the copy's own label and is already
discharged by `intApplyRuleFull`'s `.pos, .imp` branching arm via `expanded`-set guarding,
independently of whether a self-copy exists on the branch
(`Soundness.lean`'s `applyAllTImpRules_sat`, the `le_rfl` reflexive case). Whether
`sat_timp` can additionally be established *at accessible worlds* (not just reflexively) is
Gap 1 and remains out of scope for this task; `truthLemma`'s T-imp `sorry`
(`Scheme.lean:607`) is untouched by this change.

Termination of the overall expansion loop (`intExpandBranches`, below) is NOT currently
established, and the loop is known to diverge on some inputs: the `intUniverse φ0` bound this
docstring previously appealed to is itself refuted, not merely unproven. See the
*Divergence witness* note below in this file (`## Decision Procedures`, immediately preceding
`intFuel`) for the counterexample and its consequences.

Returns the updated branch with all pending persistence applications. -/
def applyAllTImpRules (b : IBranch Atom) (edges : IEdges) : IBranch Atom :=
  let newForms :=
    b.filterMap fun sf =>
      match sf.sign, sf.formula with
      | .pos, .imp φ ψ =>
        -- Get all accessible worlds w' with T(φ) at w' but not yet T(ψ)
        let toAdd := intTImpRule φ ψ sf.label edges b
        if toAdd.isEmpty then none else some toAdd
      | _, _ => none
  b ++ newForms.flatten

/-- Repeatedly apply persistence until fixpoint.

Since each application can create new T-formulas that may trigger more applications,
we iterate until no new formulas are added. Uses fuel to guarantee termination. -/
def applyPersistenceFixpoint (b : IBranch Atom) (edges : IEdges) (fuel : Nat) : IBranch Atom :=
  match fuel with
  | 0 => b
  | fuel' + 1 =>
    let b' := applyAllTImpRules b edges
    if b'.length == b.length then b  -- No new formulas added; fixpoint reached
    else applyPersistenceFixpoint b' edges fuel'

/-! ## One-Step Expansion -/

/-- One step of the intuitionistic tableau expansion on a single branch.

Finds the first formula on `b` that:
1. Is not in the `expanded` set, and
2. Has an applicable intuitionistic rule.

Returns `none` when the branch is saturated. -/
def intStepBranch (b : IBranch Atom) (expanded : List (ISF Atom)) (nextWorld : Nat) :
    Option (IntRuleResult Atom × List (ISF Atom)) :=
  b.findSome? fun sf =>
    if expanded.any (· == sf) then none
    else
      match intApplyRuleFull sf nextWorld b with
      | .notApplicable => none
      | result => some (result, expanded ++ [sf])

omit [Hashable Atom] in
/-- If `intStepBranch` returns `some (r, e')`, then `r ≠ .notApplicable`.
The definition maps every `.notApplicable` result of `intApplyRuleFull` to `none`,
so `.notApplicable` never appears as the first component of a `some` return value. -/
lemma intStepBranch_result_ne_notApplicable
    {b : IBranch Atom} {expanded : List (ISF Atom)} {nextWorld : Nat}
    {r : IntRuleResult Atom} {exp' : List (ISF Atom)}
    (h : intStepBranch b expanded nextWorld = some (r, exp')) : r ≠ .notApplicable := by
  simp only [intStepBranch] at h
  obtain ⟨sf, _, hsf⟩ := List.exists_of_findSome?_eq_some h
  by_cases hexp : (expanded.any (· == sf)) = true
  · simp [hexp] at hsf
  · simp only [Bool.not_eq_true] at hexp
    simp only [hexp, Bool.false_eq_true, ↓reduceIte] at hsf
    cases hint : intApplyRuleFull sf nextWorld b with
    | notApplicable => simp [hint] at hsf
    | linearResult fs nw' e =>
      simp only [hint, Option.some.injEq, Prod.mk.injEq] at hsf
      exact hsf.1.symm ▸ (by simp)
    | branchingResult bs nw' =>
      simp only [hint, Option.some.injEq, Prod.mk.injEq] at hsf
      exact hsf.1.symm ▸ (by simp)

/-! ## Sfor-Containment Loop-Check -/

/-- **SUPERSEDED (task 574, Phase 3):** this def searches **descendants**
(`isAccessible edges w x`), which is the defect task 574 repairs — a Fitting-style loop check
must search **ancestors**. See `intFImpReuseWitnessAnc?` below for the ancestor-direction
replacement; `intExpandBranches`'s call site (`:423`) still calls this def until Phase 4 swaps
it and retires this declaration. The rest of this docstring is retained verbatim as historical
record of the (superseded) descendant-direction design; do not treat it as current design intent.

The `Sfor`-containment loop-check (design settled, GO verdict). Wired into `go`'s
`some (.linearResult newForms nw' (some newEdge), newExp)` branch (see `intExpandBranches`
below).

Following the `Sfor`-containment termination technique of Garg, Genovese & Negri,
*Countermodels from Sequent Calculi in Multi-Modal Logics* (LICS 2012)
[`GargGenoveseNegri2012`], this helper will decide
whether the `F(φ → ψ)`-triggered world-creation in `go`'s
`some (.linearResult newForms nw' (some newEdge), newExp)` branch — the *only* world-creating
case, produced solely by `intApplyRuleFull`'s `F(φ → ψ)` clause via `intFImpRule` — can be
**reused** instead of performed, so that no two worlds on a branch ever end up with
containment-equal forced-sets (which is what makes the existing `2^(2·complexity+2)` fuel
bound, sized against the finite space of possible forced-sets, adequate).

**Which set.** `intFImpRule φ ψ w nextWorld b` returns
`newForms = [⟨.pos, φ, w'⟩, ⟨.neg, ψ, w'⟩] ++ propagatePersistence b w w'`, and
`propagatePersistence b w w' = (posFormulasAt b w).map (labeled w')`. So the prospective
forced-set at the would-be new world `w'`, `Sfor(w') = {φ} ∪ posFormulasAt bPers w`, is exactly
the `sign = .pos` sub-list of `newForms`; the obligation `ψ` is the unique `sign = .neg` entry.
Both are read directly off `newForms` — no need to thread `φ`/`ψ` separately.

**Where it fires.** Inside `go` (the `intExpandBranches` inner loop), in the
`some (.linearResult newForms nw' (some newEdge), newExp)` case, BEFORE
`Branch.extendMany bPers newForms` and BEFORE `newEdge` is appended to `edges`. At that point
`go` already has `bPers : IBranch Atom` and `edges : IEdges` (the pre-extension edge list) in
its own parameters, and the source world `w = newEdge.2` (`intFImpRule` returns edge
`(w', w)`). Consequently **no signature change to `intFImpRule`, `intApplyRuleFull`, or
`intStepBranch` is required**: those keep exactly their current parameters
(`φ ψ w nextWorld b` / `sf nextWorld b` / `b expanded nextWorld`); `edges` is available one
level up, exactly where the check needs to run, so the design threads no new parameter through
the rule layer at all.

**What it returns.** `some x` for a world label `x` (search order: e.g. first match under
`(bPers.map (·.label)).eraseDups`) such that:
- `isAccessible edges w x` — `x` is reachable from `w` in the existing Kripke pre-order
  (reuses `isAccessible` as-is; no new accessibility notion needed), AND
- `Sfor(w') ⊆ posFormulasAt bPers x` — containment: everything that would hold at the fresh
  world already holds at `x`, AND
- `ψ ∉ posFormulasAt bPers x` — the obligation is still open at `x` (no `T(ψ)@x`, so reusing
  `x` does not vacuously close the branch), AND
- **`F(ψ)@x` is already an explicit entry on `bPers`** (Option A fix). This is the load-bearing
  conjunct for soundness: `IBranchSaturation.sat_fimp`/
  `sfSatisfied`'s `.neg, .imp` case demands an *explicit* `F(ψ)@x` entry, not merely
  `ψ ∉ posFormulasAt bPers x` — an earlier investigation found a concrete counterexample where
  the latter alone holds but no `F(ψ)@x` entry exists, breaking the Hintikka condition at the
  reused witness.
  Requiring `F(ψ)@x` to already be *literally present* on `bPers` closes that gap for free,
  with NO branch modification on reuse (the alternative, Option B — appending a fresh `F(ψ)@x`
  entry unconditionally — was tried and found UNSOUND: `intExpandBranches_closed_unsat`
  (`Soundness.lean`) needs `intBranchSatisfied` for whatever branch `go` recurses on, and an
  arbitrary satisfying Kripke model has no obligation to falsify `ψ` at the model-world already
  assigned to `x` merely because `ψ` is not yet *forced on the branch* — that model-world's
  value was already pinned by earlier steps, unlike a genuinely fresh label. Requiring `F(ψ)@x`
  to pre-exist sidesteps this entirely: nothing new is asserted, so the already-established
  `intBranchSatisfied` witness for `bPers` continues to apply unchanged).

`some x` means do NOT create `w'` — mark `F(φ → ψ)@w` expanded
(already achieved via `newExp`) and continue on the SAME branch, calling `intExpandBranches`
with `bPers` (not `Branch.extendMany bPers newForms`) and unmodified `edges` (not
`edges ++ [newEdge]`). `none` means proceed exactly as today (create `w'` as normal).

**Why not the worlds-free G4ip weight** (Dyckhoff 1992 [`Dyckhoff1992`] / Negri–von Plato 2001
[`NegriVonPlato2001`] §5.5): that
measure requires every rule's active formula to be strictly lighter than its principal
formula, which `propagatePersistence` breaks by unconditionally copying ALL `T`-signed
formulas at `w` — including compounds not yet expanded there — onto `w'` regardless of
`complexity(φ → ψ)` (see blocker `R1-measure` in plan 03 / `.orchestrator-handoff.json`). The
`Sfor`-containment check sidesteps this: instead of a per-step-decreasing measure over branch
contents, it bounds the *number of distinct worlds* a branch can contain (`Sfor` takes values
only in the finite lattice of subsets of `Sub(φ)` and grows monotonically along
`isAccessible`), which is exactly the finite-model argument the `2^(2·complexity+2)` fuel bound
already assumes.

**GO verdict (R1 gate).** The check is fully expressible against the existing `IBranch`,
`IEdges`, `posFormulasAt`, `isAccessible` primitives, using only quantities already in scope
inside `go` (`bPers`, `edges`, `newForms`, `newEdge`). No new persistent field, no new
structure, and no signature change anywhere in the rule layer is required.

**Search order.** Candidates are the distinct world labels appearing on `bPers`
(`(bPers.map (·.label)).eraseDups`), in branch order; `List.findSome?` returns the first
label satisfying all three conditions, or `none` if no label does. -/
def intFImpReuseWitness? (bPers : IBranch Atom) (edges : IEdges)
    (newForms : List (ISF Atom)) (newEdge : Nat × Nat) : Option Nat :=
  -- `w` is the source world of the would-be world-creating edge (`intFImpRule` returns
  -- edge `(w', w)`, so `newEdge.2 = w`).
  let w := newEdge.2
  match newForms.findSome? (fun sf => if sf.sign == .neg then some sf.formula else none) with
  | none => none  -- malformed input: no obligation entry (should not happen for this rule)
  | some ψ =>
    -- Sfor(w') = {φ} ∪ posFormulasAt bPers w, read off newForms's sign = .pos sublist.
    let sfor : List (Proposition Atom) :=
      newForms.filterMap fun sf => if sf.sign == .pos then some sf.formula else none
    let candidates := (bPers.map (·.label)).eraseDups
    candidates.findSome? fun x =>
      let forcedAtX := posFormulasAt bPers x
      -- `w.ble x` (`w ≤ x`) is a cheap, purely computable, redundant-in-valid-runs check:
      -- `isAccessible edges w x` already semantically implies `w ≤ x` (descendants get
      -- strictly larger labels than ancestors), but proving that from `isAccessible`'s raw
      -- reachability definition would require threading a brand-new "edges are label-ordered"
      -- invariant through the whole expansion induction. Checking `w ≤ x` directly here makes
      -- the `sat_fimp`/`sfSatisfied` obligation `w ≤ w'` immediately available at the witness
      -- `x` with zero new invariant machinery.
      if isAccessible edges w x
          && w.ble x
          && sfor.all (forcedAtX.contains ·)
          && !(forcedAtX.contains ψ)
          && bPers.any (fun y => y.sign == .neg && y.formula == ψ && y.label == x) then
        some x
      else
        none

omit [Hashable Atom] in
/-- Specification lemma for `intFImpReuseWitness?`:
when it returns `some x` for the `.neg`-signed obligation `ψ` read off `newForms`, `x`
satisfies all five search conditions, including the load-bearing Option-A conjunct
`F(ψ)@x ∈ bPers` (an explicit branch entry, not merely "not forced"). This is the fact
`Scheme.lean`'s `intExpandBranches_openBranch_sat` reuse case needs to discharge
`sfSatisfied`/`sat_fimp` at the reused witness without any new invariant machinery. -/
lemma intFImpReuseWitness?_spec {bPers : IBranch Atom} {edges : IEdges}
    {newForms : List (ISF Atom)} {newEdge : Nat × Nat} {x : Nat} {ψ : Proposition Atom}
    (hψ : newForms.findSome? (fun sf => if sf.sign == .neg then some sf.formula else none)
        = some ψ)
    (h : intFImpReuseWitness? bPers edges newForms newEdge = some x) :
    isAccessible edges newEdge.2 x = true ∧
    newEdge.2 ≤ x ∧
    (newForms.filterMap fun sf => if sf.sign == .pos then some sf.formula else none).all
      ((posFormulasAt bPers x).contains ·) = true ∧
    ¬ (posFormulasAt bPers x).contains ψ ∧
    bPers.any (fun y => y.sign == .neg && y.formula == ψ && y.label == x) = true := by
  simp only [intFImpReuseWitness?, hψ] at h
  obtain ⟨x', _hx'mem, hif⟩ := List.exists_of_findSome?_eq_some h
  by_cases hcond : (isAccessible edges newEdge.2 x'
      && newEdge.2.ble x'
      && (newForms.filterMap fun sf => if sf.sign == .pos then some sf.formula else none).all
        ((posFormulasAt bPers x').contains ·)
      && !(posFormulasAt bPers x').contains ψ
      && bPers.any (fun y => y.sign == .neg && y.formula == ψ && y.label == x')) = true
  · simp only [hcond, if_true] at hif
    injection hif with hif
    subst hif
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hcond
    exact ⟨h1, Nat.le_of_ble_eq_true h2, h3, by simpa using h4, h5⟩
  · simp only [Bool.not_eq_true] at hcond
    simp only [hcond] at hif
    simp at hif

/-- The **ancestor-directed** `Sfor`-containment loop-check (task 574, Phase 3).

`intFImpReuseWitness?` above searches **descendants** of the world-creating source `w`
(`isAccessible edges w x`), which is the defect this task repairs: a Fitting-style loop check
must search **ancestors** instead, so that a formula obligation can be discharged by something
already forced earlier on the same accessibility path, not by something not-yet-created.

**Search direction and why.** Swap `isAccessible edges w x` → `isAccessible edges x w` and
`w.ble x` → `x.ble w` relative to `intFImpReuseWitness?`; every other conjunct (including the
`F(ψ)@x` explicit-entry conjunct) is unchanged. The rationale — `Sfor` (the forced-set at a
world) takes values in the finite subset lattice of `Sub(φ)` and grows monotonically along
accessibility, so an ancestor's forced-set is a subset of any descendant's — is attributed to
Garg, Genovese & Negri, *Countermodels from Sequent Calculi in Multi-Modal Logics* (LICS 2012)
[`GargGenoveseNegri2012`] and to Fitting, *Proof Methods for Modal and Intuitionistic Logics*
(1983) [`Fitting1983`] Ch. 4, as **provenance only**: neither source is readable from this
repository (BibTeX key only, no entry in the navigable literature corpus — see the plan's H3
honesty rule). The actual evidence for this design is
`specs/574_tableau_calculus_repair_ancestor_blocking/handoffs/01_variant-selection.md` Table 3:
real `#eval` measurement on the complexity-9 divergence witness shows the ancestor-directed
check (variant V1, conjunct retained) saturates at `fuel ≥ 120` (`maxLabel = 21`, stable across
four independent evaluations), where the descendant-directed `intFImpReuseWitness?` diverges
without bound on the same input.

**Search order.** Identical to `intFImpReuseWitness?`: candidates are the distinct world labels
appearing on `bPers` (`(bPers.map (·.label)).eraseDups`), in branch order; `List.findSome?`
returns the first label satisfying all four conditions, or `none` if no label does.

**Reuse contract.** `some x` means the ancestor `x` discharges the obligation: do NOT create
`w'`, recurse `intExpandBranches` on `bPers` **unmodified** (never Option B — appending a fresh
`F(ψ)@x` entry on reuse was tried and found UNSOUND, `Expansion.lean:256-264`), with `edges`
**unchanged** and the world counter **unconsumed**. `none` means proceed exactly as today
(create `w'` as normal). This mirrors `intFImpReuseWitness?`'s own contract exactly; only the
search direction differs.

This declaration is **additive**: `intExpandBranches`'s call site (`:423`) still calls
`intFImpReuseWitness?`, unchanged, in this phase. The swap is Phase 4's explicit acceptance
gate. -/
def intFImpReuseWitnessAnc? (bPers : IBranch Atom) (edges : IEdges)
    (newForms : List (ISF Atom)) (newEdge : Nat × Nat) : Option Nat :=
  -- `w` is the source world of the would-be world-creating edge (`intFImpRule` returns
  -- edge `(w', w)`, so `newEdge.2 = w`).
  let w := newEdge.2
  match newForms.findSome? (fun sf => if sf.sign == .neg then some sf.formula else none) with
  | none => none  -- malformed input: no obligation entry (should not happen for this rule)
  | some ψ =>
    -- Sfor(w') = {φ} ∪ posFormulasAt bPers w, read off newForms's sign = .pos sublist.
    let sfor : List (Proposition Atom) :=
      newForms.filterMap fun sf => if sf.sign == .pos then some sf.formula else none
    let candidates := (bPers.map (·.label)).eraseDups
    candidates.findSome? fun x =>
      let forcedAtX := posFormulasAt bPers x
      -- Ancestor direction: `x` is reachable *to* `w` (`isAccessible edges x w`), and carries
      -- a strictly smaller label (`x.ble w`) — the reverse of `intFImpReuseWitness?`'s
      -- descendant-direction checks.
      if isAccessible edges x w
          && x.ble w
          && sfor.all (forcedAtX.contains ·)
          && !(forcedAtX.contains ψ)
          && bPers.any (fun y => y.sign == .neg && y.formula == ψ && y.label == x) then
        some x
      else
        none

omit [Hashable Atom] in
/-- Specification lemma for `intFImpReuseWitnessAnc?`:
when it returns `some x` for the `.neg`-signed obligation `ψ` read off `newForms`, `x`
satisfies all five search conditions in **ancestor** direction, including the load-bearing
Option-A conjunct `F(ψ)@x ∈ bPers` (an explicit branch entry, not merely "not forced"). The
proof structure is `intFImpReuseWitness?_spec`'s, transferred verbatim with the two directional
conjuncts (`isAccessible`, `≤`) reversed. -/
lemma intFImpReuseWitnessAnc?_spec {bPers : IBranch Atom} {edges : IEdges}
    {newForms : List (ISF Atom)} {newEdge : Nat × Nat} {x : Nat} {ψ : Proposition Atom}
    (hψ : newForms.findSome? (fun sf => if sf.sign == .neg then some sf.formula else none)
        = some ψ)
    (h : intFImpReuseWitnessAnc? bPers edges newForms newEdge = some x) :
    isAccessible edges x newEdge.2 = true ∧
    x ≤ newEdge.2 ∧
    (newForms.filterMap fun sf => if sf.sign == .pos then some sf.formula else none).all
      ((posFormulasAt bPers x).contains ·) = true ∧
    ¬ (posFormulasAt bPers x).contains ψ ∧
    bPers.any (fun y => y.sign == .neg && y.formula == ψ && y.label == x) = true := by
  simp only [intFImpReuseWitnessAnc?, hψ] at h
  obtain ⟨x', _hx'mem, hif⟩ := List.exists_of_findSome?_eq_some h
  by_cases hcond : (isAccessible edges x' newEdge.2
      && x'.ble newEdge.2
      && (newForms.filterMap fun sf => if sf.sign == .pos then some sf.formula else none).all
        ((posFormulasAt bPers x').contains ·)
      && !(posFormulasAt bPers x').contains ψ
      && bPers.any (fun y => y.sign == .neg && y.formula == ψ && y.label == x')) = true
  · simp only [hcond, if_true] at hif
    injection hif with hif
    subst hif
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hcond
    exact ⟨h1, Nat.le_of_ble_eq_true h2, h3, by simpa using h4, h5⟩
  · simp only [Bool.not_eq_true] at hcond
    simp only [hcond] at hif
    simp at hif

/-! ## Expansion Loop -/

/-- Expand a list of intuitionistic tableau branches with a fuel counter.

For each open branch, applies persistence and then one expansion step.
Branches are processed sequentially; branching rules create new sub-branches.

The `edgeSets` parameter is a parallel list (one per branch) of parent-child edge lists
tracking the Kripke accessibility relation for each branch. When a world-creating rule
fires, the new edge is added to the current branch's edge set. When a branching rule
fires, both sub-branches inherit the current edge set. -/
def intExpandBranches
    (branches : List (IBranch Atom))
    (expandedSets : List (List (ISF Atom)))
    (nextWorlds : List Nat)
    (edgeSets : List IEdges)
    (fuel : Nat)
    (closurePred : IBranch Atom → Bool) :
    IntTableauResult Atom :=
  match fuel with
  | 0 =>
    -- Out of fuel: return first open branch as countermodel
    match branches.findSome? (fun b => if closurePred b then none else some b) with
    | some b => .openBranch b
    | none => .closed
  | fuel' + 1 =>
    -- Inner loop: apply persistence and expand the first open branch.
    -- Iterates through pending branches, skipping closed ones and expanding the first open one.
    let rec @[nolint docBlame] go (pending : List (IBranch Atom))
        (pendingExp : List (List (ISF Atom)))
        (pendingNW : List Nat)
        (pendingEdges : List IEdges)
        (done : List (IBranch Atom))
        (doneExp : List (List (ISF Atom)))
        (doneNW : List Nat)
        (doneEdges : List IEdges)
        : IntTableauResult Atom :=
      match pending, pendingExp, pendingNW, pendingEdges with
      | [], _, _, _ => .closed  -- All branches closed
      | b :: restBs, e :: restEs, nw :: restNW, edges :: restEdges =>
        -- First apply persistence to get all T(φ → ψ) consequences
        let bPers := applyPersistenceFixpoint b edges (fuel' + 1)
        if closurePred bPers then
          -- Branch is closed
          go restBs restEs restNW restEdges
            (done ++ [bPers]) (doneExp ++ [e]) (doneNW ++ [nw]) (doneEdges ++ [edges])
        else
          match intStepBranch bPers e nw with
          | none =>
            -- Branch is saturated and open: countermodel
            .openBranch bPers
          | some (.linearResult newForms nw' newEdge, newExp) =>
            -- Alpha-rule or world-creation: extend branch
            match newEdge with
            | none =>
              -- Alpha-rule: no new world, edges unchanged.
              intExpandBranches
                (done ++ [Branch.extendMany bPers newForms] ++ restBs)
                (doneExp ++ [newExp] ++ restEs)
                (doneNW ++ [nw'] ++ restNW)
                (doneEdges ++ [edges] ++ restEdges)
                fuel'
                closurePred
            | some e =>
              -- World-creating F(φ → ψ) rule: run the Sfor-containment loop-check
              -- before committing to a fresh world w' = e.1.
              match intFImpReuseWitness? bPers edges newForms e with
              | some _x =>
                -- Reuse: an accessible ancestor already contains Sfor(w') and lacks ψ, so
                -- F(φ → ψ)@w is discharged without creating w'. No new world, no new edge;
                -- the world counter is left at `nw` (unconsumed) since w' was never built.
                intExpandBranches
                  (done ++ [bPers] ++ restBs)
                  (doneExp ++ [newExp] ++ restEs)
                  (doneNW ++ [nw] ++ restNW)
                  (doneEdges ++ [edges] ++ restEdges)
                  fuel'
                  closurePred
              | none =>
                -- No reusable ancestor: create w' exactly as before.
                intExpandBranches
                  (done ++ [Branch.extendMany bPers newForms] ++ restBs)
                  (doneExp ++ [newExp] ++ restEs)
                  (doneNW ++ [nw'] ++ restNW)
                  (doneEdges ++ [edges ++ [e]] ++ restEdges)
                  fuel'
                  closurePred
          | some (.branchingResult branches' nw', newExp) =>
            -- Beta-rule: split into sub-branches (each inherits current edge set)
            intExpandBranches
              (done ++ branches'.map (Branch.extendMany bPers ·) ++ restBs)
              (doneExp ++ branches'.map (fun _ => newExp) ++ restEs)
              (doneNW ++ branches'.map (fun _ => nw') ++ restNW)
              (doneEdges ++ branches'.map (fun _ => edges) ++ restEdges)
              fuel'
              closurePred
          | some (.notApplicable, _) =>
            -- This case shouldn't happen (intStepBranch filters notApplicable)
            .openBranch bPers
      | _ :: restBs, _, _, _ =>
        go restBs [] [] [] done doneExp doneNW doneEdges
    go branches expandedSets nextWorlds edgeSets [] [] [] []

/-! ## Generic Alias -/

/-- `propExpandBranches` is the generic propositional tableau expansion loop,
parameterized by `closurePred : IBranch Atom → Bool`.

This is a documentation alias for `intExpandBranches`, emphasizing that the expansion loop
is closure-predicate-agnostic. The two concrete instantiations are:
- `intuitionisticTableau`: `closurePred = isIntuitionisticallyClosed`
- `minimalTableau`: `closurePred = isMinimallyClosed`

The `IntMinScheme` structure in `Scheme.lean` bundles both divergence points (closure
predicate and countermodel `botForces`) into a single parameterized interface. -/
@[inline] def propExpandBranches
    (branches : List (IBranch Atom))
    (expandedSets : List (List (ISF Atom)))
    (nextWorlds : List Nat)
    (edgeSets : List IEdges)
    (fuel : Nat)
    (closurePred : IBranch Atom → Bool) :
    IntTableauResult Atom :=
  intExpandBranches branches expandedSets nextWorlds edgeSets fuel closurePred

/-! ### Divergence witness: no world bound exists for this calculus -/

/-!
`intExpandBranches` does not terminate on every input: it diverges on a complexity-9 witness
formula, and no numeric world bound (of any size) can be substituted for the one
`intUniverse`/`intApplyRuleFull_outputs_subset` assume. This note is the durable, greppable
record of that fact, obtained by evaluating `intExpandBranches` on the witness formula below at
increasing fuel and observing the branch/world counts.

**Witness formula** (complexity 9):
`φ0 = (((a→b)→c) ∧ ((d→e)→f)) → ((u₁→v₁) ∨ (u₂→v₂))`

**Measured growth.** Evaluating `intExpandBranches [[⟨.neg, φ0, 0⟩]] [[]] [1] [[]] fuel
isIntuitionisticallyClosed` at increasing `fuel`, the maximum world label reached is:

| fuel         | 10 | 20 | 30 | 40 | 60 | 80 | 120 | 160 | 200 | 260 |
|--------------|----|----|----|----|----|----|-----|-----|-----|-----|
| max label    | 4  | 7  | 10 | 14 | 21 | 27 | 40  | 54  | 67  | 87  |

Growth is linear in fuel with no saturation: `intStepBranch` never returns `none` on this
input, so the loop consumes its entire fuel budget every time.

**Structural duplication.** From world 3 onward, every world is an exact structural duplicate
of its grandparent — identical T-set and F-set, period 2. The two T-implication rules
(`applyAllTImpRules`'s copy channel above and `intFImpRule` in `Rules.lean`) ping-pong forever
on identical content; only the label increments.

**Three consequences:**
(a) `intApplyRuleFull_outputs_subset`'s hypothesis `hnw : nextWorld ≤ φ0.complexity + 1`
(`Scheme.lean`) is FALSE, refuted by this direct counterexample.
(b) `intUniverse`'s label range `List.range (φ.complexity + 2)` (`Scheme.lean`) is false as an
invariant of branches actually produced by `intExpandBranches`.
(c) NO numeric world bound of any size exists for the current calculus: the world count is
unbounded in fuel on this input, so no `f(φ0)` satisfies `nextWorld ≤ f(φ0)`.

**Directive.** Do not attempt to prove `intExpandBranches_world_bound`, the `hnw` hypothesis, or
the `intUniverse` containment invariant (`hUniv`) as currently stated — they are refuted, not
merely hard. Any future progress on world-boundedness requires a calculus-level change (an
ancestor-directed loop-check/blocking rule that actually cuts the ping-pong above), not a proof
effort against the present statements.

**Method.** Obtained by evaluating `intExpandBranches` on `φ0` at increasing fuel and comparing
branch contents across worlds; re-verified directly in Lean on the unmodified library, not only
by an external harness.
-/

/-! ## Decision Procedures -/

/-- Fuel bound for the intuitionistic/minimal tableau expansion loop, as a function of
formula complexity. Set to `3 ^ (4 * (2 * φ.complexity + 1) * (φ.complexity + 2))` (doubling
the earlier exponent to mirror the Modal-K `modalFuel`'s built-in factor-of-2,
`FmpMeasure.lean:232-233`), replacing the earlier
`2 ^ (2 * φ.complexity + 2)` bound which was insufficient to guarantee saturation. The
earlier exponent (`2 * (2 * φ.complexity + 1) * (φ.complexity + 2)`, un-doubled) was verified
insufficient for `intExpMeasure_init_le_fuel`: the initial worklist measure scales as
`3 ^ (2 * |intUniverse φ| - 1)`, i.e. ~twice `intUniverse_length_le`'s bound, not once (see
`Scheme.lean`'s `intExpMeasure_init_le_fuel`). Shared by `intuitionisticTableau`,
`minimalTableau`, and by the fuel-pinned lemmas in `Scheme.lean` (`tableau_sound`,
`openBranch_countermodel`, `tableau_complete`) so that all fuel-dependent call sites stay in
sync. -/
def intFuel (φ : Proposition Atom) : Nat :=
  3 ^ (4 * (2 * φ.complexity + 1) * (φ.complexity + 2))

/-- The intuitionistic propositional tableau decision procedure.

Given `φ`, starts with `F(φ)` at world 0 and expands using `IntuitionisticClosure`.
- Returns `closed` iff `φ` is intuitionistically valid (IValid).
- Returns `openBranch b` iff `φ` is not intuitionistically valid, with `b` an open
  saturated branch giving a Kripke countermodel.

The fuel bound `intFuel φ` accounts for the exponential blowup possible in intuitionistic
proofs (finite model property gives this bound). -/
def intuitionisticTableau (φ : Proposition Atom) : IntTableauResult Atom :=
  let initialBranch : IBranch Atom := [⟨.neg, φ, 0⟩]
  let fuel := intFuel φ
  intExpandBranches [initialBranch] [[]] [1] [[]] fuel isIntuitionisticallyClosed

/-- The minimal propositional tableau decision procedure.

Identical to the intuitionistic tableau but uses `isMinimallyClosed` instead of
`isIntuitionisticallyClosed`: a branch closes when T(φ) and F(φ) coexist at the same
world for any formula φ (not only T(⊥)).

- Returns `closed` iff `φ` is minimally valid (MValid).
- Returns `openBranch b` iff `φ` is not minimally valid. -/
def minimalTableau (φ : Proposition Atom) : IntTableauResult Atom :=
  let initialBranch : IBranch Atom := [⟨.neg, φ, 0⟩]
  let fuel := intFuel φ
  intExpandBranches [initialBranch] [[]] [1] [[]] fuel isMinimallyClosed

end Cslib.Logic.PL

end
