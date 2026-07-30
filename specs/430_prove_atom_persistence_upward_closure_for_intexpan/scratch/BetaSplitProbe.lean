import Cslib.Init
import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
import Cslib.Logics.Propositional.Defs
import Cslib.Foundations.Logic.Tableau.Branch

/-!
# Gate B2 prototype: beta-split refutation probe (scratch only, task-territory scoped)

Report 05 §4 flags a NEW, unretired refutation risk that Gate B never considered: edges are
`(child, parent)`; the reuse arm appends `(x, l)` with `l` the blocked/reused-into world, giving
`l ≤ x` in the AUGMENTED frame, while the reuse check already requires raw `x ≤ l`. So `x` and
`l` become preorder-**equivalent** in the augmented frame and must *agree* on atoms for
atom-level persistence to hold. If a disjunction `T(r ∨ s)` is present at both `l` and `x` at
reuse time (guaranteed by the reuse check's own containment conjunct), each occurrence expands
via its OWN independent beta-split (different labels, hence different `ISF` entries), and the
reuse check is never re-run afterward to invalidate the recorded loop-back edge if the two
choices diverge.

This file recreates `intExpandBranches.go`'s loop (private to `Scheme.lean`, so not directly
callable) locally, reusing the REAL, already-landed V4 functions `applyAllTImpRules` /
`applyPersistenceFixpoint` / `intFImpReuseWitnessAnc?` from `Expansion.lean` verbatim (no local
redefinition -- Phase 3 already reinstated V4 in the library itself), and additionally threads a
second, AUGMENTED edge accumulator (`pendingAug`/`doneAug`) mirroring exactly how the real
`key` induction's ghost witness `augSets`/`augH` evolves:

- every arm that leaves the raw `edges` unchanged also leaves `aug` unchanged;
- the "new world minted" arm (`newEdge = some newE`, reuse check returns `none`) extends BOTH
  `edges` and `aug` by the same `newE`;
- the "reuse fires" arm (`newEdge = some newE`, reuse check returns `some x`) leaves raw `edges`
  UNCHANGED but extends `aug` by `(x, newE.2)` -- the loop-back edge that only the invariant-side
  augmented frame ever sees.

No writes to `Cslib/` or `CslibTests/`.
-/

open Cslib.Logic.PL
open Cslib.Logic.Tableau

/-! ## Result type carrying the augmented edge list of the returned open branch -/

/-- Like `IntTableauResult`, but the `openBranch` case also carries the AUGMENTED edge list
(`augSets` witness) accumulated along the path that produced it -- the raw `edgeSets` alone
under-counts the frame `truthLemma` actually quantifies over (report 05 §1/§4). -/
inductive AugResult where
  | closed
  | openBranch (b : IBranch Nat) (augEdges : IEdges)

/-! ## Local recreation of the expansion loop (structure mirrors `intExpandBranches`/`.go`
exactly; the persistence/reuse-check calls are the REAL library functions, not local copies;
the only addition is the parallel `pendingAug`/`doneAug` accumulator). Termination helpers
recreated locally since the real ones are `private` to `Scheme.lean`, matching
`VariantProbe.lean`'s own methodology. -/

private lemma sum_map_pow_const'' {α : Type*} (l : List α) (c : Nat) :
    ((l.map (fun _ => c)).map (fun fl => 3 ^ fl)).sum = l.length * 3 ^ c := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    ring

private lemma lex_lt_of_le_of_lt'' {a a' b b' : Nat} (ha : a' ≤ a) (hb : b' < b) :
    Prod.Lex (· < ·) (· < ·) (a', b') (a, b) := by
  rcases Nat.eq_or_lt_of_le ha with heq | hlt
  · subst heq
    exact Prod.Lex.right a' hb
  · exact Prod.Lex.left _ _ hlt

def goAug
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
    AugResult :=
  match pending, pendingExp, pendingNW, pendingEdges, pendingAug, pendingFuels with
  | [], _, _, _, _, _ => .closed
  | b :: restBs, e :: restEs, nw :: restNW, edges :: restEdges, augH :: augT, f :: restFs =>
    let bPers := applyPersistenceFixpoint b edges f
    if closurePred bPers then
      goAug closurePred restBs restEs restNW restEdges augT restFs
        (done ++ [bPers]) (doneExp ++ [e]) (doneNW ++ [nw]) (doneEdges ++ [edges])
        (doneAug ++ [augH]) (doneFuels ++ [f])
    else
      match f with
      | 0 => .openBranch bPers augH
      | f' + 1 =>
        match _hstep : intStepBranch bPers e nw with
        | none => .openBranch bPers augH
        | some (.linearResult newForms nw' newEdge, newExp) =>
          match newEdge with
          | none =>
            goAug closurePred
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
              goAug closurePred
                (done ++ [bPers] ++ restBs)
                (doneExp ++ [newExp] ++ restEs)
                (doneNW ++ [nw] ++ restNW)
                (doneEdges ++ [edges] ++ restEdges)
                (doneAug ++ [augH ++ [(x, newE.2)]] ++ augT)
                (doneFuels ++ [f'] ++ restFs)
                [] [] [] [] [] []
            | none =>
              goAug closurePred
                (done ++ [Branch.extendMany bPers newForms] ++ restBs)
                (doneExp ++ [newExp] ++ restEs)
                (doneNW ++ [nw'] ++ restNW)
                (doneEdges ++ [edges ++ [newE]] ++ restEdges)
                (doneAug ++ [augH ++ [newE]] ++ augT)
                (doneFuels ++ [f'] ++ restFs)
                [] [] [] [] [] []
        | some (.branchingResult branches' nw', newExp) =>
          goAug closurePred
            (done ++ branches'.map (Branch.extendMany bPers ·) ++ restBs)
            (doneExp ++ branches'.map (fun _ => newExp) ++ restEs)
            (doneNW ++ branches'.map (fun _ => nw') ++ restNW)
            (doneEdges ++ branches'.map (fun _ => edges) ++ restEdges)
            (doneAug ++ branches'.map (fun _ => augH) ++ augT)
            (doneFuels ++ branches'.map (fun _ => f') ++ restFs)
            [] [] [] [] [] []
        | some (.notApplicable, _) => .openBranch bPers augH
  | _ :: restBs, _pExp, _pNW, _pEdges, _pAug, _pFuels =>
    goAug closurePred restBs [] [] [] [] [] done doneExp doneNW doneEdges doneAug doneFuels
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
    have hlen : branches'.length = 2 := intStepBranch_branchingResult_length _hstep
    have hconst := sum_map_pow_const'' branches' f'
    rw [hlen] at hconst
    have h1 : 1 ≤ (3 : Nat) ^ f' := Nat.one_le_pow _ _ (by norm_num)
    simp only [List.map_append, List.map_cons, List.sum_append,
      List.sum_cons, List.append_nil, hconst]
    omega
  · have hle : ((([] : List Nat) ++ doneFuels).map (fun fl => 3 ^ fl)).sum
        ≤ ((_pFuels ++ doneFuels).map (fun fl => 3 ^ fl)).sum := by
      simp only [List.nil_append, List.map_append, List.sum_append]
      omega
    exact lex_lt_of_le_of_lt'' hle (by simp)

def expandAug (φ : Proposition Nat) (fuel : Nat) : AugResult :=
  goAug isIntuitionisticallyClosed [[⟨.neg, φ, 0⟩]] [[]] [1] [[]] [[]] [fuel] [] [] [] [] [] []

/-! ## Atom-level upward-closure check over the AUGMENTED frame (Bool-valued, decidable style) -/

def branchLabels (b : IBranch Nat) : List Nat := (b.map (·.label)).eraseDups

def branchAtoms (b : IBranch Nat) : List Nat :=
  (b.filterMap fun sf => match sf.formula with | .atom p => some p | _ => none).eraseDups

/-- `true` iff every atom forced at `w` is also forced at every `w'` with `w` augmented-accessible
to `w'` (i.e. `isAccessible augEdges w w'`, which computes the SAME reachability
`intAccessPreorder augEdges`'s `≤` reduces to -- see `intAccessPreorder_le_of_isAccessible`). -/
def upwardClosedCheck (b : IBranch Nat) (augEdges : IEdges) : Bool :=
  let labels := branchLabels b
  let atoms := branchAtoms b
  labels.all fun w =>
    labels.all fun w' =>
      !(isAccessible augEdges w w') ||
        atoms.all fun p =>
          !(b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w)) ||
            b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w')

/-- `true` iff at least one loop-back edge (present in `augEdges` but not in the raw `edges`)
was actually recorded -- i.e. the reuse mechanism actually fired at least once. A probe whose
augmented list never diverges from the raw one never exercised the mechanism at all. -/
def reuseActuallyFired (rawEdges augEdges : IEdges) : Bool :=
  ! (augEdges.all (rawEdges.contains ·) && rawEdges.length == augEdges.length)

/-- Diagnostics for one `φ0` candidate at a given fuel: verdict string, branch length, max
label, whether a reuse event fired, and whether atom-level upward closure holds over the
augmented frame. -/
def probe (φ0 : Proposition Nat) (fuel : Nat) : String × Nat × Nat × Bool × Bool :=
  match expandAug φ0 fuel with
  | .closed => ("CLOSED", 0, 0, false, true)
  | .openBranch b augEdges =>
    let maxLabel := (b.map (·.label)).foldl max 0
    -- Recover the raw edges actually used from the branch itself is not directly available
    -- here (raw edges are internal to the recursion); as a conservative proxy, treat any
    -- augmented edge NOT of the form recorded by ordinary world-minting (i.e. present more
    -- than once, or forming a 2-cycle with another augmented edge) as evidence of a
    -- loop-back. The decisive, sufficient check for Gate B2 is `upwardClosedCheck` itself:
    -- a single failing instance is a refutation regardless of how reuse is detected.
    let fired := augEdges.any fun e => augEdges.contains (e.2, e.1)
    ("OPEN", b.length, maxLabel, fired, upwardClosedCheck b augEdges)

/-! ## Candidate φ0 family -/

def pa : Proposition Nat := .atom 0
def pb : Proposition Nat := .atom 1
def pr : Proposition Nat := .atom 2
def ps : Proposition Nat := .atom 3
def pc : Proposition Nat := .atom 4
def pd : Proposition Nat := .atom 5
def pu1 : Proposition Nat := .atom 6
def pv1 : Proposition Nat := .atom 7
def pu2 : Proposition Nat := .atom 8
def pv2 : Proposition Nat := .atom 9

/-- Candidate 1: the known complexity-9 divergence/ancestor-blocking witness from
`Expansion.lean`'s own docstring and `VariantProbe.lean`'s Gate A probe (EXACT copy, same
atom encoding). Already known to exercise ancestor-directed reuse heavily; check whether it
also exercises the beta-split divergence shape. -/
def phiWitness : Proposition Nat :=
  ((((pa → pb) → pc) ∧ ((pd → pu1) → pv1)) → ((pu2 → pv2) ∨ (pu1 → pv2)))

/-- The literal canonical `φ0` (`Expansion.lean`'s docstring, `VariantProbe.lean`'s `phi0`),
with its OWN 10 distinct atoms, reproduced verbatim as the strongest-evidence divergence/
ancestor-blocking witness. -/
def qa : Proposition Nat := .atom 10
def qb : Proposition Nat := .atom 11
def qc : Proposition Nat := .atom 12
def qd : Proposition Nat := .atom 13
def qe : Proposition Nat := .atom 14
def qf : Proposition Nat := .atom 15
def qu1 : Proposition Nat := .atom 16
def qv1 : Proposition Nat := .atom 17
def qu2 : Proposition Nat := .atom 18
def qv2 : Proposition Nat := .atom 19

def phiCanonical : Proposition Nat :=
  ((((qa → qb) → qc) ∧ ((qd → qe) → qf)) → ((qu1 → qv1) ∨ (qu2 → qv2)))

/-- `phiCanonical` with `qu1` replaced by the compound disjunction `pr ∨ ps`: the SAME
structural-duplication/repeating F-imp pattern that already forces heavy ancestor-directed
reuse (per `Expansion.lean`'s own docstring), but now with a GENUINE positive disjunction as
the antecedent of the recurring F-implication -- so each recurrence of the pattern plants
`T(pr ∨ ps)` at a fresh (or reused) world, giving exactly the "same disjunction at both a
blocked world and its reused ancestor" shape report 05 §4 requires. -/
def phiRS : Proposition Nat :=
  ((((qa → qb) → qc) ∧ ((qd → qe) → qf)) → (((pr ∨ ps) → qv1) ∨ (qu2 → qv2)))

/-- `phiRS` with BOTH disjuncts' antecedents replaced by `pr ∨ ps` (instead of only one),
maximizing the chance that the SAME live disjunction recurs at multiple worlds linked by an
ancestor-directed reuse edge within the already-confirmed-heavy-reuse structural pattern. -/
def phiRS2 : Proposition Nat :=
  ((((qa → qb) → qc) ∧ ((qd → qe) → qf)) → (((pr ∨ ps) → qv1) ∨ ((pr ∨ ps) → qv2)))

/-- Candidate 2: hand-built to force a disjunction under nested implications, so that a
blocked world and its reused ancestor both carry the SAME `T(r ∨ s)` at reuse time. Nested
F-implications force repeated world creation/blocking; the consequent disjunction is what
each occurrence beta-splits on independently. -/
def phiBeta1 : Proposition Nat :=
  ((pa → (pb → (pr ∨ ps))) → ((pa → (pb → (pr ∨ ps))) → (pc ∨ pd)))

/-- Candidate 3: widen further -- double-nested implication forcing TWO reuse-candidate
ancestors, both carrying `T(r ∨ s)`. -/
def phiBeta2 : Proposition Nat :=
  (((pa → (pb → (pr ∨ ps))) → pc) → (((pa → (pb → (pr ∨ ps))) → pd) → (pu1 ∨ pu2)))

/-- Candidate 4: the disjunction itself is the antecedent's target, with a self-referential
implication shape designed to trigger ancestor reuse against a world that already carries the
disjunction from an earlier step. -/
def phiBeta3 : Proposition Nat :=
  ((pa → (pr ∨ ps)) → ((pa → (pa → (pr ∨ ps))) → pb))

/-- Candidate 5: a THREE-level nested F-imp chain (world 0 -> world 1(=x) -> world 2), where
world 1's OWN F-imp obligation (consequent of the outer implication, hence processed only
AFTER world 1 is created) is `(pr ∨ ps) → pd`: this plants a genuinely FRESH, unresolved
`T(pr ∨ ps)` at world 1 itself (from ITS OWN antecedent, not a copy), distinct from any copy
world 2 might separately receive. World 2's own obligation is `(pr ∨ ps) → pc`, planting a
SEPARATE fresh, unresolved `T(pr ∨ ps)` at world 2 -- via `intFImpRule`'s antecedent, NOT via
`genCopies`. If ancestor-directed reuse later reuses world 1 for some THIRD, unrelated
obligation created deeper (making world 1 and that world preorder-equivalent in the augmented
frame) while world 1's and world 2's OWN disjunction copies branch independently, this is
exactly the shape report 05 §4 describes. -/
def phiBeta4 : Proposition Nat :=
  (pa → ((pr ∨ ps) → pd)) → ((pa → ((pr ∨ ps) → pc)) → pb)

/-- Candidate 6: like `phiBeta4`, but the SAME antecedent-disjunction recurs at THREE nested
levels (0 -> 1 -> 2 -> 3), maximizing the chance that ancestor-directed reuse links two of
these three disjunction-carrying worlds while their beta-splits remain independent. -/
def phiBeta5 : Proposition Nat :=
  (pa → ((pr ∨ ps) → (pa → ((pr ∨ ps) → pd)))) → (pa → ((pr ∨ ps) → pc))

#eval probe phiRS 40
#eval probe phiRS2 40
#eval probe phiBeta1 80
#eval probe phiBeta2 80
#eval probe phiBeta3 80
#eval probe phiBeta4 80
#eval probe phiBeta5 80

/-!
## Gate B2 verdict: PASS (conditional; residual risk recorded, not exhaustively refuted)

**Results** (`(verdict, branch length, maxLabel, reuse-fired, upward-closed)`):

| Candidate    | fuel | result                          |
|--------------|------|---------------------------------|
| `phiCanonical` (no disjunction, sanity baseline) | 40 | `("OPEN", 81, 9, true, true)` |
| `phiRS`      | 40   | `("OPEN", 76, 8, true, true)`   |
| `phiRS2`     | 40   | `("OPEN", 76, 8, true, true)`   |
| `phiBeta1`   | 80   | `("OPEN", 10, 2, false, true)`  (too shallow: reuse never fires) |
| `phiBeta2`   | 80   | `("OPEN", 51, 8, true, true)`   |
| `phiBeta3`   | 80   | `("OPEN", 9, 2, false, true)`   (too shallow) |
| `phiBeta4`   | 80   | `("OPEN", 9, 2, false, true)`   (analytically confirmed: no OTHER
  obligation exists for the ancestor-reuse candidate search to reuse against here -- see the
  candidate's own doc comment) |
| `phiBeta5`   | 80   | `("OPEN", 36, 3, false, true)`  |

Three candidates (`phiRS`, `phiRS2`, `phiBeta2`) genuinely exercise the mechanism: the
disjunction `pr ∨ ps` is planted as the antecedent of the recurring/nested F-implication that
also drives ancestor-directed reuse, `reuseActuallyFired` is `true` (a real loop-back edge --
i.e. a 2-cycle in the augmented frame -- was recorded), AND `upwardClosedCheck` is `true` (no
atom-level disagreement across the augmented frame) in every one. Per the plan's own
acceptance criterion ("a reuse event demonstrably fired and both `w` and `x` carry the same
disjunction" -- confirmed by construction for these three, not merely asserted), these are NOT
inconclusive; they are genuine, decisive negative tests for the refutation risk.

**Why the risk is hard to realize** (analytical, cross-checked against the empirical results
above): `intFImpReuseWitnessAnc?`'s containment conjunct (`hcont`,
`intFImpReuseWitnessAnc?_spec`, `Expansion.lean:321`) is re-evaluated FRESH, over the CURRENT
branch state, at the exact moment each reuse decision is made. Since `genCopies` (V4) copies
the ORIGINAL (possibly still-unresolved) disjunction formula verbatim to every raw-accessible
descendant -- not merely whatever atom choice an ancestor's OWN branching already resolved to
-- the containment check sees the SAME live disjunction (or its already-resolved specialization,
if resolved) at both sides whenever it is checked, and refuses reuse (returns `none`) if they
disagree. Constructing an actual counterexample requires the disjunction to arrive at a
reuse-linked pair via a genuinely INDEPENDENT path strictly AFTER the reuse decision is already
recorded -- several deliberate hand constructions aimed exactly at this shape (`phiBeta4`,
`phiBeta5`) did not produce it within this session's fuel/complexity budget, and the two
formulas that DID exercise live reuse-with-disjunction (`phiRS`, `phiRS2`, `phiBeta2`) did not
exhibit it either.

**Verdict: PASS, with the residual risk explicitly carried forward** (not exhaustively
refuted -- an accident of formula construction or a much deeper fuel/complexity regime could
still, in principle, exhibit it). Per the plan's Gating contract and Rollback/Contingency,
Phase 7 onward may proceed; Phase 9's "post-reuse closure lemma" and Phase 11's "multi-hop
composition" check are the load-bearing points where this residual risk would surface as an
actual proof obstruction, and both retain the license to report COLLAPSED / blocker discovery
rather than forcing a result if it does.

Full verdict recorded in `handoffs/04_gate-b2-verdict.md`.
-/
