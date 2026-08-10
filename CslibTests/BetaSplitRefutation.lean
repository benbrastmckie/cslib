/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
public meta import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
import Cslib.Logics.Propositional.Defs
public meta import Cslib.Logics.Propositional.Defs
import Cslib.Foundations.Logic.Tableau.Branch
public meta import Cslib.Foundations.Logic.Tableau.Branch
import Mathlib.Tactic.Ring
public meta import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
public meta import Mathlib.Tactic.NormNum

/-!
# Targeted beta-split refutation: the closure-asymmetry construction

`Gap1FixpointProbe.lean` established (empirically, `nonGenuine = 0` over every loop iteration of
seven candidates) that `applyPersistenceFixpoint b edges f` is a genuine `applyAllTImpRules`
fixpoint at every arm. Once that is granted, the reuse-time containment invariant strengthens
for free from "`l`'s positive content sits at `x`" to "the positive content of EVERY raw ancestor
of `l` sits at `x`", which discharges the copy arm, the alpha arm and the cross-world T-imp arm
of the post-reuse closure obligation. Exactly ONE arm survives: the positive-disjunction (beta)
arm, where `T(θ ∨ ρ)@x` and `T(θ ∨ ρ)@l` are two DISTINCT `ISF` entries that beta-split
independently and may resolve to different disjuncts.

Gate B2 searched for that shape by planting disjunctions into reuse-heavy formulas and found
nothing. This file searches differently: it engineers a **closure asymmetry** that FORCES the two
splits apart rather than hoping they diverge by accident.

The recipe (derived, not guessed):

1. `F(φ0)@0` with `φ0 = (Γ → pr)` mints world `1` carrying `F(pr)@1` and `T(Γ)@1`.
   World `1` is the intended reuse TARGET `x`.
2. `Γ` contains `pr ∨ ps` as a conjunct, so `T(pr ∨ ps)@1`. Its split has one child adding
   `T(pr)@1`, which closes immediately against `F(pr)@1`. So the surviving branch necessarily
   has `x = 1` resolving the disjunction to `ps` -- the choice is FORCED by closure, not left to
   chance.
3. `Γ` also contains `(ps → (ps → pr)) → pb`, whose T-imp reflexive branching arm yields
   `F(ps → (ps → pr))@1` as its FIRST child. That mints world `2` with `T(ps)@2` and
   `F(ps → pr)@2`. No reuse fires there: no world carries `F(ps → pr)`.
4. `F(ps → pr)@2` is then processed. Its obligation is `ψ = pr`, and world `1` carries
   `F(pr)@1`, is a raw ancestor of `2`, has the smaller label, and does not force `pr`. The
   containment conjunct holds because world `2`'s positive content is world `1`'s content plus
   `ps`, which world `1` already has. So **reuse fires with `(x, l) = (1, 2)`**, recording the
   loop-back edge `(1, 2)` and making worlds `1` and `2` equivalent in the augmented frame
   (raw `(2,1)` gives `1 ≤ 2`; the loop-back gives `2 ≤ 1`).
5. `genCopies` has already copied `T(pr ∨ ps)` from `1` to `2`. That copy is a distinct `ISF`
   entry, unexpanded, and it splits independently AFTER the reuse edge is recorded. Its
   `T(pr)@2` child does NOT close, because reuse suppressed the creation of a world carrying
   `F(pr)` below `2`, and `F(pr)@2` is absent.

Net: `T(pr)@2` on the returned open branch, `T(pr)@1` absent, with `1` and `2`
augmented-equivalent. That is an atom-level upward-closure violation over
`intAccessPreorder augEdges`.

This file is a promoted, CI-protected regression test (module mode, `#guard_msgs`-asserted); the
`goRaw` local recreation deliberately duplicates the private `intExpandBranches.go` (the
augmented edge list is a proof-side ghost with no runtime counterpart), and `branchesAgree` /
`minBranchesAgree` below are the guard keeping that recreation faithful to the real
`intuitionisticTableau` / `minimalTableau`. Do not de-privatise `intExpandBranches.go` to remove
this duplication -- that would widen `Cslib/`'s public surface to serve a test. -/

set_option autoImplicit false

open Cslib.Logic.PL
open Cslib.Logic.Tableau

namespace CslibTests.BetaSplitRefutation

/-- Result of the local `goRaw` recreation of `intExpandBranches`: either the branch closed, or
it stayed open with the returned branch plus the augmented and raw edge lists. -/
inductive AugRes where
  /-- The branch closed. -/
  | closed
  /-- The branch stayed open, with the final branch, augmented edges, and raw edges. -/
  | openBranch (b : IBranch Nat) (augEdges : IEdges) (rawEdges : IEdges)

/-- Termination-measure arithmetic: summing `3 ^ c` over a constant-`c` list collapses to
`length * 3 ^ c`. -/
private lemma sum_map_pow_const₄ {α : Type*} (l : List α) (c : Nat) :
    ((l.map (fun _ => c)).map (fun fl => 3 ^ fl)).sum = l.length * 3 ^ c := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    ring

/-- Termination-measure arithmetic: a non-increasing first component and a strictly-decreasing
second component gives a strict lexicographic decrease. -/
private lemma lex_lt_of_le_of_lt₄ {a a' b b' : Nat} (ha : a' ≤ a) (hb : b' < b) :
    Prod.Lex (· < ·) (· < ·) (a', b') (a, b) := by
  rcases Nat.eq_or_lt_of_le ha with heq | hlt
  · subst heq
    exact Prod.Lex.right a' hb
  · exact Prod.Lex.left _ _ hlt

/-- `BetaSplitProbe.goAug`, additionally returning the RAW edge list alongside the augmented one
so the loop-back edges can be isolated exactly (Gate B2's probe only had a heuristic proxy). -/
def goRaw
    (closurePred : IBranch Nat → Bool)
    (pending : List (IBranch Nat))
    (pendingExp : List (List (ISF Nat)))
    (pendingNW : List Nat)
    (pendingEdges : List IEdges)
    (pendingAug : List IEdges)
    (pendingFuels : List Nat)
    (done : List (IBranch Nat))
    (doneExp : List (List (ISF Nat)))
    (doneNW : List Nat)
    (doneEdges : List IEdges)
    (doneAug : List IEdges)
    (doneFuels : List Nat) :
    AugRes :=
  match pending, pendingExp, pendingNW, pendingEdges, pendingAug, pendingFuels with
  | [], _, _, _, _, _ => .closed
  | b :: restBs, e :: restEs, nw :: restNW, edges :: restEdges, augH :: augT, f :: restFs =>
    let bPers := applyPersistenceFixpoint b edges f
    if closurePred bPers then
      goRaw closurePred restBs restEs restNW restEdges augT restFs
        (done ++ [bPers]) (doneExp ++ [e]) (doneNW ++ [nw]) (doneEdges ++ [edges])
        (doneAug ++ [augH]) (doneFuels ++ [f])
    else
      match f with
      | 0 => .openBranch bPers augH edges
      | f' + 1 =>
        match _hstep : intStepBranchPrio bPers e nw with
        | none => .openBranch bPers augH edges
        | some (.linearResult newForms nw' newEdge, newExp) =>
          match newEdge with
          | none =>
            goRaw closurePred
              (done ++ [Branch.extendMany bPers newForms] ++ restBs)
              (doneExp ++ [newExp] ++ restEs)
              (doneNW ++ [nw'] ++ restNW)
              (doneEdges ++ [edges] ++ restEdges)
              (doneAug ++ [augH] ++ augT)
              (doneFuels ++ [f'] ++ restFs)
              [] [] [] [] [] []
          | some newE =>
            match intFImpReuseWitnessAnc? bPers edges newForms newE with
            | some x =>
              goRaw closurePred
                (done ++ [bPers] ++ restBs)
                (doneExp ++ [newExp] ++ restEs)
                (doneNW ++ [nw] ++ restNW)
                (doneEdges ++ [edges] ++ restEdges)
                (doneAug ++ [augH ++ [(x, newE.2)]] ++ augT)
                (doneFuels ++ [f'] ++ restFs)
                [] [] [] [] [] []
            | none =>
              goRaw closurePred
                (done ++ [Branch.extendMany bPers newForms] ++ restBs)
                (doneExp ++ [newExp] ++ restEs)
                (doneNW ++ [nw'] ++ restNW)
                (doneEdges ++ [edges ++ [newE]] ++ restEdges)
                (doneAug ++ [augH ++ [newE]] ++ augT)
                (doneFuels ++ [f'] ++ restFs)
                [] [] [] [] [] []
        | some (.branchingResult branches' nw', newExp) =>
          goRaw closurePred
            (done ++ branches'.map (Branch.extendMany bPers ·) ++ restBs)
            (doneExp ++ branches'.map (fun _ => newExp) ++ restEs)
            (doneNW ++ branches'.map (fun _ => nw') ++ restNW)
            (doneEdges ++ branches'.map (fun _ => edges) ++ restEdges)
            (doneAug ++ branches'.map (fun _ => augH) ++ augT)
            (doneFuels ++ branches'.map (fun _ => f') ++ restFs)
            [] [] [] [] [] []
        | some (.notApplicable, _) => .openBranch bPers augH edges
  | _ :: restBs, _pExp, _pNW, _pEdges, _pAug, _pFuels =>
    goRaw closurePred restBs [] [] [] [] [] done doneExp doneNW doneEdges doneAug doneFuels
termination_by
  (((pendingFuels ++ doneFuels).map (fun fl => 3 ^ fl)).sum, pending.length)
decreasing_by
  · have hsum : ((restFs ++ (doneFuels ++ [f])).map (fun fl => 3 ^ fl)).sum
        = (((f :: restFs) ++ doneFuels).map (fun fl => 3 ^ fl)).sum := by
      simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
        List.sum_cons, List.sum_nil]
      omega
    rw [hsum]
    exact Prod.Lex.right _ (by simp)
  · apply Prod.Lex.left
    have h1 : 1 ≤ (3 : Nat) ^ f' := Nat.one_le_pow _ _ (by norm_num)
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, List.append_nil]
    omega
  · apply Prod.Lex.left
    have h1 : 1 ≤ (3 : Nat) ^ f' := Nat.one_le_pow _ _ (by norm_num)
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, List.append_nil]
    omega
  · apply Prod.Lex.left
    have h1 : 1 ≤ (3 : Nat) ^ f' := Nat.one_le_pow _ _ (by norm_num)
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, List.append_nil]
    omega
  · apply Prod.Lex.left
    have hlen : branches'.length = 2 :=
      intStepBranch_branchingResult_length (intStepBranchPrio_some_exists _hstep)
    have hconst := sum_map_pow_const₄ branches' f'
    rw [hlen] at hconst
    have h1 : 1 ≤ (3 : Nat) ^ f' := Nat.one_le_pow _ _ (by norm_num)
    simp only [List.map_append, List.map_cons, List.sum_append,
      List.sum_cons, List.append_nil, hconst]
    omega
  · have hle : ((([] : List Nat) ++ doneFuels).map (fun fl => 3 ^ fl)).sum
        ≤ ((_pFuels ++ doneFuels).map (fun fl => 3 ^ fl)).sum := by
      simp only [List.nil_append, List.map_append, List.sum_append]
      omega
    exact lex_lt_of_le_of_lt₄ hle (by simp)

/-- Runs `goRaw` from the initial branch `[F(φ)@0]` on `φ` with the given fuel, under the
intuitionistic closure predicate. -/
def expandRaw (φ : Proposition Nat) (fuel : Nat) : AugRes :=
  goRaw isIntuitionisticallyClosed [[⟨.neg, φ, 0⟩]] [[]] [1] [[]] [[]] [fuel] [] [] [] [] [] []

/-- The distinct world labels appearing on `b`. -/
def branchLabels (b : IBranch Nat) : List Nat := (b.map (·.label)).eraseDups

/-- The distinct atom indices appearing on `b`. -/
def branchAtoms (b : IBranch Nat) : List Nat :=
  (b.filterMap fun sf => match sf.formula with | .atom p => some p | _ => none).eraseDups

/-- `true` iff `b` positively forces atom `p` at world `w`. -/
def forcesAtom (b : IBranch Nat) (p w : Nat) : Bool :=
  b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w)

/-- First atom-level upward-closure violation over the augmented frame: `(w, w', p)` with
`w` augmented-accessible to `w'`, `p` forced at `w` but not at `w'`. -/
def firstViolation (b : IBranch Nat) (augEdges : IEdges) : Option (Nat × Nat × Nat) :=
  let labels := branchLabels b
  let atoms := branchAtoms b
  labels.findSome? fun w =>
    labels.findSome? fun w' =>
      if isAccessible augEdges w w' then
        (atoms.findSome? fun p =>
          if forcesAtom b p w && !(forcesAtom b p w') then some p else none).map
            fun p => (w, w', p)
      else none

/-- Loop-back edges: augmented edges that are not raw edges. -/
def loopBackEdges (raw aug : IEdges) : IEdges := aug.filter (fun e => !(raw.contains e))

/-- `(verdict, branch length, max world label, raw edges, loop-back edges, first upward-closure
violation)` for the intuitionistic run of `φ0` at the given fuel. -/
def report (φ0 : Proposition Nat) (fuel : Nat) :
    String × Nat × Nat × IEdges × IEdges × Option (Nat × Nat × Nat) :=
  match expandRaw φ0 fuel with
  | .closed => ("CLOSED", 0, 0, [], [], none)
  | .openBranch b aug raw =>
    let maxLabel := (b.map (·.label)).foldl max 0
    ("OPEN", b.length, maxLabel, raw, loopBackEdges raw aug, firstViolation b aug)

/-- Positive atoms per world, for reading off the countermodel by hand. -/
def atomTable (φ0 : Proposition Nat) (fuel : Nat) : List (Nat × List Nat) :=
  match expandRaw φ0 fuel with
  | .closed => []
  | .openBranch b _ _ =>
    (branchLabels b).map fun w => (w, (branchAtoms b).filter (forcesAtom b · w))

/-- The atom `pa`. -/
def pa : Proposition Nat := .atom 0

/-- The atom `pb`. -/
def pb : Proposition Nat := .atom 1

/-- The atom `pr`, whose upward-closure failure this file exhibits. -/
def pr : Proposition Nat := .atom 2

/-- The atom `ps`. -/
def ps : Proposition Nat := .atom 3

/-- The atom `pc`, used only by the `phiRef4` robustness variant. -/
def pc : Proposition Nat := .atom 4

/-- **The targeted construction** (step 1-5 of the module docstring). -/
def phiRef1 : Proposition Nat :=
  ((pr ∨ ps) ∧ ((ps → (ps → pr)) → pb)) → pr

/-- Variant: the reuse-driving nested implication uses `pr ∨ ps` itself as the antecedent
(already positive at world `1`), giving a second route to the same containment. Deliberately
NOT promoted to an assertion below -- `report phiRef2 40` ends in `none`, i.e. this variant does
not exhibit the defect. -/
def phiRef2 : Proposition Nat :=
  ((pr ∨ ps) ∧ (((pr ∨ ps) → ((pr ∨ ps) → pr)) → pb)) → pr

/-- Variant: one more nesting level between the reuse target and the reused-into world. A
robustness variant, not cited by any annotation; kept interactively inspectable but not
promoted to an assertion. -/
def phiRef3 : Proposition Nat :=
  ((pr ∨ ps) ∧ ((ps → (ps → (ps → pr))) → pb)) → pr

/-- Variant: extra conjunct supplying an unrelated positive atom, so the containment check has
more to match on (tests robustness of the construction rather than its core). A robustness
variant, not cited by any annotation; kept interactively inspectable but not promoted to an
assertion. -/
def phiRef4 : Proposition Nat :=
  ((pr ∨ ps) ∧ (pc ∧ ((ps → (ps → pr)) → pb))) → pr

/-- info: ("OPEN", 17, 2, [(1, 0), (2, 1)], [(2, 2), (1, 2)], none) -/
#guard_msgs in
#eval report phiRef1 40

/-- info: [(2, [3]), (1, [3]), (0, [])] -/
#guard_msgs in
#eval atomTable phiRef1 40

/-! ## Fidelity check against the REAL `intuitionisticTableau`, and the closing argument

The local `goRaw` recreation exists only because `intExpandBranches.go` is `private` to
`Scheme.lean` and because the augmented edge list is a proof-side GHOST witness with no runtime
counterpart. Everything else is the real library. Checks below:

1. `intFuelExt phiRef1` is the fuel the real entry point actually uses; the refutation must hold
   at that exact value, not only at a hand-picked one.
2. The real `intuitionisticTableau phiRef1` must return `.openBranch b` with the SAME `b` the
   recreation returns at that fuel. If the branches agree, the only remaining difference is the
   ghost `augEdges` list, whose evolution is transcribed directly from the real `key` induction:
   `augH ++ [(x, l)]` at the reuse arm (`Scheme.lean`, the `hreuse_sat`/`refine ih` block),
   `augH ++ [newE]` at the mint arm, unchanged at every other arm.
3. `intExtractValuation b w p` unfolds to exactly `forcesAtom b p w` (`Soundness.lean`'s
   definition), so `firstViolation` tests the real valuation, not a proxy.
4. The closing step: the refutation kills the AUGMENTED-frame instantiation directly. To see that
   no OTHER edge list rescues the existential in `openBranch_countermodel`'s conjunct, note that
   any edge list supporting `IFimpAccess` for the reused obligation `F(ps -> pr)@2` must make some
   world `w'` with `T(ps)@w'` and `F(pr)@w'` accessible from `2`. `fimpWitnesses` below enumerates
   every such `w'` on `b`. If world `1` is the only one, then every admissible edge list has
   `2 <= 1`, and upward closure then demands `pr` at `1`, which fails.
-/

/-- The real fuel used by the real entry point. -/
def realFuel : Nat := intFuelExt phiRef1

/-- Refutation re-checked at the REAL fuel value: `(verdict, len, maxLabel, raw, loopbacks,
firstViolation)`. -/
def atRealFuel := report phiRef1 realFuel

/-- The real algorithm's returned branch for `f`, if open. -/
def realBranch (f : Proposition Nat) : Option (IBranch Nat) :=
  match intuitionisticTableau f with
  | .closed => none
  | .openBranch b => some b

/-- The `goRaw` recreation's returned branch for `f` at the given fuel, if open. -/
def recreatedBranch (f : Proposition Nat) (fuel : Nat) : Option (IBranch Nat) :=
  match expandRaw f fuel with
  | .closed => none
  | .openBranch b _ _ => some b

/-- `true` means the recreation reproduces the real algorithm's returned branch exactly. -/
def branchesAgree : Bool := realBranch phiRef1 == recreatedBranch phiRef1 realFuel

/-- Every world on `b` that could serve as an `IFimpAccess` witness for `F(ps -> pr)`:
it must carry `T(ps)` and `F(pr)`. -/
def fimpWitnesses : List Nat :=
  match realBranch phiRef1 with
  | none => []
  | some b =>
    (branchLabels b).filter fun w =>
      b.any (fun sf => sf.sign == .pos && sf.formula == ps && sf.label == w)
        && b.any (fun sf => sf.sign == .neg && sf.formula == pr && sf.label == w)

/-- The two decisive valuation facts, as `Bool`s: `pr` is forced at world `2` and not at world
`1` on the branch the REAL algorithm returns. -/
def decisiveFacts : Bool × Bool :=
  match realBranch phiRef1 with
  | none => (false, false)
  | some b => (forcesAtom b 2 2, forcesAtom b 2 1)

/-- Readable dump of the returned branch: `(sign-is-positive, formula, label)`. Interactively
inspectable; not promoted to an assertion (output is multi-page). -/
def branchDump : List (Bool × Proposition Nat × Nat) :=
  match realBranch phiRef1 with
  | none => []
  | some b => b.map fun sf => (sf.sign == .pos, sf.formula, sf.label)

/-- info: ("OPEN", 17, 2, [(1, 0), (2, 1)], [(2, 2), (1, 2)], none) -/
#guard_msgs in
#eval atRealFuel

/-- info: true -/
#guard_msgs in
#eval branchesAgree

/-- info: [1] -/
#guard_msgs in
#eval fimpWitnesses

/-- info: (false, false) -/
#guard_msgs in
#eval decisiveFacts

/-!
## Verdict: REFUTED (machine-verified)

`phiRef1 = ((pr | ps) & ((ps -> (ps -> pr)) -> pb)) -> pr` is not intuitionistically valid (take
`pr` false, `ps` true: the antecedent holds because `ps -> (ps -> pr)` is false), so
`.openBranch` is the correct verdict and this is not a soundness anomaly. The defect is in the
COUNTERMODEL the open branch yields:

- the real `intuitionisticTableau phiRef1` returns `.openBranch b` (branch reproduced exactly by
  the recreation, `branchesAgree = true`);
- the augmented edge list the `key` induction constructs on that path is
  `[(1,0), (2,1)] ++ [(1,2), (2,2)]`, whose `(1,2)` component is the recorded loop-back edge from
  the reuse event `(x, l) = (1, 2)`;
- `isAccessible aug 2 1 = true`, so `2 <= 1` in `intAccessPreorder aug`;
- `intExtractValuation b 2 pr` holds and `intExtractValuation b 1 pr` does not.

So upward closure of `intExtractValuation b` along `intAccessPreorder aug` is FALSE. World `1`
was forced onto the `ps` disjunct of `T(pr | ps)@1` by closure against `F(pr)@1`; the `genCopies`
copy `T(pr | ps)@2` is a distinct `ISF` entry that split independently AFTER the loop-back edge
was recorded, and its `T(pr)@2` child did not close because reuse had suppressed creation of any
world carrying `F(pr)` below `2`.
-/

/-! ## Minimal-closure variant (DP-4's calculus)

DP-4 lives on `minimalTableau`, whose closure predicate is `isMinimallyClosed` (closes when
`T(chi)` and `F(chi)` coexist at a world for ANY `chi`, not only `bot`). That is a STRICTLY
stronger closure test, so the refutation must be re-run under it rather than inferred from the
intuitionistic run. -/

/-- Runs `goRaw` from the initial branch `[F(f)@0]` on `f` with the given fuel, under the
minimal closure predicate. -/
def expandRawMin (f : Proposition Nat) (fuel : Nat) : AugRes :=
  goRaw isMinimallyClosed [[⟨.neg, f, 0⟩]] [[]] [1] [[]] [[]] [fuel] [] [] [] [] [] []

/-- `(verdict, branch length, max world label, raw edges, loop-back edges, first upward-closure
violation)` for the minimal-closure run of `f` at the given fuel. -/
def reportMin (f : Proposition Nat) (fuel : Nat) :
    String × Nat × Nat × IEdges × IEdges × Option (Nat × Nat × Nat) :=
  match expandRawMin f fuel with
  | .closed => ("CLOSED", 0, 0, [], [], none)
  | .openBranch b aug raw =>
    ("OPEN", b.length, (b.map (·.label)).foldl max 0, raw, loopBackEdges raw aug,
      firstViolation b aug)

/-- The real minimal-tableau algorithm's returned branch for `f`, if open. -/
def realBranchMin (f : Proposition Nat) : Option (IBranch Nat) :=
  match minimalTableau f with
  | .closed => none
  | .openBranch b => some b

/-- `true` means the minimal-closure recreation reproduces the real `minimalTableau`'s returned
branch exactly, at the real fuel. -/
def minBranchesAgree : Bool :=
  realBranchMin phiRef1 == (match expandRawMin phiRef1 realFuel with
    | .closed => none
    | .openBranch b _ _ => some b)

/-- Positive atoms per world for the minimal-closure run of `phiRef1` at the real fuel. -/
def minAtomTable : List (Nat × List Nat) :=
  match expandRawMin phiRef1 realFuel with
  | .closed => []
  | .openBranch b _ _ =>
    (branchLabels b).map fun w => (w, (branchAtoms b).filter (forcesAtom b · w))

/-- info: ("OPEN", 17, 2, [(1, 0), (2, 1)], [(2, 2), (1, 2)], none) -/
#guard_msgs in
#eval reportMin phiRef1 realFuel

/-- info: true -/
#guard_msgs in
#eval minBranchesAgree

/-- info: [(2, [3]), (1, [3]), (0, [])] -/
#guard_msgs in
#eval minAtomTable

end CslibTests.BetaSplitRefutation
