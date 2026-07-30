import Cslib.Init
import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
import Cslib.Logics.Propositional.Defs
import Cslib.Foundations.Logic.Tableau.Branch

/-!
# Gap 1 fixpoint-completeness probe (scratch only)

Two questions, both instrumented on the SAME recreated `intExpandBranches.go` loop that
`BetaSplitProbe.lean` already validated (same shape, same real library functions
`applyPersistenceFixpoint`/`applyAllTImpRules`/`intFImpReuseWitnessAnc?`; only the outer
worklist loop is recreated locally because it is `private` to `Scheme.lean`).

**Q1 (Gap 1, operational).** Is `bPers := applyPersistenceFixpoint b edges f` a GENUINE fixpoint
of `applyAllTImpRules` at *every* iteration of the loop -- not merely at the terminal
`intStepBranch = none` arm? `applyAllTImpRules b e = b ++ newForms.flatten ++ genCopies.flatten`,
so length equality is equivalent to genuine fixpoint-ness
(`applyAllTImpRules_eq_self_of_length_eq`). The counter `nonGenuine` counts iterations where
`(applyAllTImpRules bPers edges).length ≠ bPers.length`, i.e. where `bPers` is NOT a genuine
fixpoint. `nonGenuine = 0` across a run means the fuel budget was never the binding constraint
on the persistence sub-recursion on that run.

**Q2 (sharpened beta-split precondition).** At each recorded reuse event `(x, l)`, is there a
positive `.or`-shaped formula `χ` with `T(χ)@l` on the branch, `⟨.pos, χ, x⟩` ALREADY in the
expanded set (so `x`'s copy has already been beta-split and resolved to one disjunct), and
`⟨.pos, χ, l⟩` NOT yet in the expanded set (so `l`'s copy will be split independently, later,
possibly picking the other disjunct)? That conjunction is the precondition for the
augmented-frame atom disagreement that `upwardClosedCheck` tests for. `riskyReuse` counts reuse
events satisfying it. This is a SHARPER target than Gate B2's family, which aimed at "the
disjunction arrives via an independent path strictly AFTER the reuse decision"; here the
disjunction is already at BOTH worlds at reuse time (so the containment conjunct is satisfied and
reuse fires), and the asymmetry is in the EXPANSION HISTORY, not in presence.

No writes to `Cslib/` or `CslibTests/`.
-/

open Cslib.Logic.PL
open Cslib.Logic.Tableau

/-- Instrumentation counters threaded through the loop. -/
structure Diag where
  /-- Iterations of the loop entered with a branch/fuel pair. -/
  iters : Nat
  /-- Iterations where `applyPersistenceFixpoint b edges f` is NOT a genuine
  `applyAllTImpRules` fixpoint (length still strictly increases on one more round). -/
  nonGenuine : Nat
  /-- Reuse (loop-back) events recorded. -/
  reuseEvents : Nat
  /-- Reuse events matching the sharpened beta-split precondition (see module docstring). -/
  riskyReuse : Nat
  deriving Repr

def Diag.empty : Diag := ⟨0, 0, 0, 0⟩

/-- Result type: like `IntTableauResult`, plus the augmented edge list and the diagnostics. -/
inductive DiagResult where
  | closed (d : Diag)
  | openBranch (b : IBranch Nat) (augEdges : IEdges) (d : Diag)

/-- `true` iff one more `applyAllTImpRules` round would still add entries. -/
def notGenuineFixpoint (b : IBranch Nat) (edges : IEdges) : Bool :=
  ! ((applyAllTImpRules b edges).length == b.length)

/-- The sharpened beta-split precondition at a reuse pair `(x, l)`: some positive `.or`-shaped
formula sits at BOTH `x` and `l`, `x`'s occurrence is already in the expanded set, `l`'s is not. -/
def riskyReusePair (b : IBranch Nat) (e : List (ISF Nat)) (x l : Nat) : Bool :=
  b.any fun sf =>
    match sf.sign, sf.formula with
    | .pos, .or _ _ =>
      sf.label == l
        && e.any (· == (⟨.pos, sf.formula, x⟩ : ISF Nat))
        && !(e.any (· == (⟨.pos, sf.formula, l⟩ : ISF Nat)))
    | _, _ => false

private lemma sum_map_pow_const₃ {α : Type*} (l : List α) (c : Nat) :
    ((l.map (fun _ => c)).map (fun fl => 3 ^ fl)).sum = l.length * 3 ^ c := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    ring

private lemma lex_lt_of_le_of_lt₃ {a a' b b' : Nat} (ha : a' ≤ a) (hb : b' < b) :
    Prod.Lex (· < ·) (· < ·) (a', b') (a, b) := by
  rcases Nat.eq_or_lt_of_le ha with heq | hlt
  · subst heq
    exact Prod.Lex.right a' hb
  · exact Prod.Lex.left _ _ hlt

/-- `BetaSplitProbe.goAug` with the two instrumentation counters threaded through. Structure is
otherwise identical, arm for arm. -/
def goDiag
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
    (doneFuels : List Nat)
    (d : Diag) :
    DiagResult :=
  match pending, pendingExp, pendingNW, pendingEdges, pendingAug, pendingFuels with
  | [], _, _, _, _, _ => .closed d
  | b :: restBs, e :: restEs, nw :: restNW, edges :: restEdges, augH :: augT, f :: restFs =>
    let bPers := applyPersistenceFixpoint b edges f
    let d := { d with
      iters := d.iters + 1,
      nonGenuine := d.nonGenuine + (if notGenuineFixpoint bPers edges then 1 else 0) }
    if closurePred bPers then
      goDiag closurePred restBs restEs restNW restEdges augT restFs
        (done ++ [bPers]) (doneExp ++ [e]) (doneNW ++ [nw]) (doneEdges ++ [edges])
        (doneAug ++ [augH]) (doneFuels ++ [f]) d
    else
      match f with
      | 0 => .openBranch bPers augH d
      | f' + 1 =>
        match _hstep : intStepBranch bPers e nw with
        | none => .openBranch bPers augH d
        | some (.linearResult newForms nw' newEdge, newExp) =>
          match newEdge with
          | none =>
            goDiag closurePred
              (done ++ [Branch.extendMany bPers newForms] ++ restBs)
              (doneExp ++ [newExp] ++ restEs)
              (doneNW ++ [nw'] ++ restNW)
              (doneEdges ++ [edges] ++ restEdges)
              (doneAug ++ [augH] ++ augT)
              (doneFuels ++ [f'] ++ restFs)
              [] [] [] [] [] [] d
          | some newE =>
            match intFImpReuseWitnessAnc? bPers edges newForms newE with
            | some x =>
              let d := { d with
                reuseEvents := d.reuseEvents + 1,
                riskyReuse := d.riskyReuse
                  + (if riskyReusePair bPers e x newE.2 then 1 else 0) }
              goDiag closurePred
                (done ++ [bPers] ++ restBs)
                (doneExp ++ [newExp] ++ restEs)
                (doneNW ++ [nw] ++ restNW)
                (doneEdges ++ [edges] ++ restEdges)
                (doneAug ++ [augH ++ [(x, newE.2)]] ++ augT)
                (doneFuels ++ [f'] ++ restFs)
                [] [] [] [] [] [] d
            | none =>
              goDiag closurePred
                (done ++ [Branch.extendMany bPers newForms] ++ restBs)
                (doneExp ++ [newExp] ++ restEs)
                (doneNW ++ [nw'] ++ restNW)
                (doneEdges ++ [edges ++ [newE]] ++ restEdges)
                (doneAug ++ [augH ++ [newE]] ++ augT)
                (doneFuels ++ [f'] ++ restFs)
                [] [] [] [] [] [] d
        | some (.branchingResult branches' nw', newExp) =>
          goDiag closurePred
            (done ++ branches'.map (Branch.extendMany bPers ·) ++ restBs)
            (doneExp ++ branches'.map (fun _ => newExp) ++ restEs)
            (doneNW ++ branches'.map (fun _ => nw') ++ restNW)
            (doneEdges ++ branches'.map (fun _ => edges) ++ restEdges)
            (doneAug ++ branches'.map (fun _ => augH) ++ augT)
            (doneFuels ++ branches'.map (fun _ => f') ++ restFs)
            [] [] [] [] [] [] d
        | some (.notApplicable, _) => .openBranch bPers augH d
  | _ :: restBs, _pExp, _pNW, _pEdges, _pAug, _pFuels =>
    goDiag closurePred restBs [] [] [] [] [] done doneExp doneNW doneEdges doneAug doneFuels d
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
    have hconst := sum_map_pow_const₃ branches' f'
    rw [hlen] at hconst
    have h1 : 1 ≤ (3 : Nat) ^ f' := Nat.one_le_pow _ _ (by norm_num)
    simp only [List.map_append, List.map_cons, List.sum_append,
      List.sum_cons, List.append_nil, hconst]
    omega
  · have hle : ((([] : List Nat) ++ doneFuels).map (fun fl => 3 ^ fl)).sum
        ≤ ((_pFuels ++ doneFuels).map (fun fl => 3 ^ fl)).sum := by
      simp only [List.nil_append, List.map_append, List.sum_append]
      omega
    exact lex_lt_of_le_of_lt₃ hle (by simp)

def expandDiag (φ : Proposition Nat) (fuel : Nat) : DiagResult :=
  goDiag isIntuitionisticallyClosed [[⟨.neg, φ, 0⟩]] [[]] [1] [[]] [[]] [fuel] [] [] [] [] [] []
    Diag.empty

/-! ## Upward-closure check with an explicit violation witness -/

def branchLabels (b : IBranch Nat) : List Nat := (b.map (·.label)).eraseDups

def branchAtoms (b : IBranch Nat) : List Nat :=
  (b.filterMap fun sf => match sf.formula with | .atom p => some p | _ => none).eraseDups

def forcesAtom (b : IBranch Nat) (p w : Nat) : Bool :=
  b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w)

/-- The FIRST atom-level upward-closure violation over the augmented frame, if any:
`(w, w', p)` with `w` augmented-accessible to `w'`, `p` forced at `w`, not forced at `w'`. -/
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

/-- Full diagnostic report for one candidate at a given fuel. -/
def report (φ0 : Proposition Nat) (fuel : Nat) :
    String × Nat × Nat × Diag × Option (Nat × Nat × Nat) :=
  match expandDiag φ0 fuel with
  | .closed d => ("CLOSED", 0, 0, d, none)
  | .openBranch b augEdges d =>
    let maxLabel := (b.map (·.label)).foldl max 0
    ("OPEN", b.length, maxLabel, d, firstViolation b augEdges)

/-! ## Candidate family (Gate B2's, verbatim, plus sharpened additions) -/

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

/-- Gate B2's canonical divergence witness (no disjunction; heavy reuse baseline). -/
def phiCanonical : Proposition Nat :=
  ((((qa → qb) → qc) ∧ ((qd → qe) → qf)) → ((qu1 → qv1) ∨ (qu2 → qv2)))

/-- Gate B2's `phiRS` (one antecedent slot replaced by `pr ∨ ps`). -/
def phiRS : Proposition Nat :=
  ((((qa → qb) → qc) ∧ ((qd → qe) → qf)) → (((pr ∨ ps) → qv1) ∨ (qu2 → qv2)))

/-- Gate B2's `phiRS2` (both antecedent slots replaced). -/
def phiRS2 : Proposition Nat :=
  ((((qa → qb) → qc) ∧ ((qd → qe) → qf)) → (((pr ∨ ps) → qv1) ∨ ((pr ∨ ps) → qv2)))

/-- Gate B2's `phiBeta2` (the third candidate that genuinely exercised reuse). -/
def phiBeta2 : Proposition Nat :=
  (((pa → (pb → (pr ∨ ps))) → pc) → (((pa → (pb → (pr ∨ ps))) → pd) → (pu1 ∨ pu2)))

/-- Sharpened candidate S1: a bare positive disjunction `pr ∨ ps` planted at world 0 (via the
outer F-implication's antecedent) so it is copied by `genCopies` to EVERY descendant, while the
heavy reuse machinery of the canonical witness runs underneath. The disjunction at world 0 is
expanded early (world 0's entries come first in branch order); its copies at later worlds are
appended late and expanded later, giving exactly the expansion-history asymmetry Q2 tests. -/
def phiS1 : Proposition Nat :=
  ((pr ∨ ps) ∧ (((qa → qb) → qc) ∧ ((qd → qe) → qf))) → ((qu1 → qv1) ∨ (qu2 → qv2))

/-- Sharpened candidate S2: as `phiS1` but with the disjunction also appearing as an antecedent
of the recurring F-implication, so it is planted freshly at each created world in addition to
being copied. -/
def phiS2 : Proposition Nat :=
  ((pr ∨ ps) ∧ (((qa → qb) → qc) ∧ ((qd → qe) → qf))) → (((pr ∨ ps) → qv1) ∨ (qu2 → qv2))

/-- Sharpened candidate S3: `phiBeta2` with a bare copied disjunction added at world 0. -/
def phiS3 : Proposition Nat :=
  ((pr ∨ ps) ∧ ((pa → (pb → (pr ∨ ps))) → pc)) → (((pa → (pb → (pr ∨ ps))) → pd) → (pu1 ∨ pu2))

#eval report phiCanonical 40
#eval report phiRS 40
#eval report phiRS2 40
#eval report phiBeta2 80
#eval report phiS1 40
#eval report phiS2 40
#eval report phiS3 60
