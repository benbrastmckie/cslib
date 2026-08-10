module

import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
public meta import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
import Cslib.Logics.Propositional.Defs
public meta import Cslib.Logics.Propositional.Defs
import Cslib.Foundations.Logic.Tableau.Branch
public meta import Cslib.Foundations.Logic.Tableau.Branch

/-!
Scratch probe: candidate calculus repairs for the never-re-validated loop-back containment
recorded by `intFImpReuseWitnessAnc?`.

Variants (all expressed as a `Cfg` over one recreated `go`, so the baseline is bit-identical
to `CslibTests/BetaSplitRefutation.goRaw` when `Cfg` is all-false):

* `betaPriority`  -- rule-selection reorder: the world-creating `F(φ→ψ)` rule fires only when
                     no other rule is applicable anywhere on the branch.
* `revalidate`    -- provisional reuse: every recorded loop-back is re-checked at each step;
                     on violation the edge is dropped and the discharged `F(φ→ψ)` entry is
                     removed from `expanded`, so the rule re-fires (and this time mints).
* `cyclicEdges`   -- the loop-back edge is appended to the ALGORITHM's own edge list, so the
                     copy channel maintains containment automatically.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

open Cslib.Logic.PL
open Cslib.Logic.Tableau

namespace ReuseProbe

/-- A recorded loop-back: reuse of ancestor `x` discharging `F(ante → cons)@w`, whose branch
entry is `sf`. -/
structure LB where
  /-- The reused ancestor. -/
  x : Nat
  /-- The source world whose obligation was discharged. -/
  w : Nat
  /-- Antecedent of the discharged implication. -/
  ante : Proposition Nat
  /-- Consequent (the obligation `ψ`). -/
  cons : Proposition Nat
  /-- The branch entry that was marked expanded by the discharge. -/
  sf : ISF Nat
deriving BEq

/-- Variant configuration. All-false reproduces the current library calculus exactly. -/
structure Cfg where
  /-- Defer the world-creating rule until no other rule applies. -/
  betaPriority : Bool
  /-- Re-check recorded loop-backs at every step; retract and re-fire on violation. -/
  revalidate : Bool
  /-- Put the loop-back edge into the algorithm's own edge list. -/
  cyclicEdges : Bool

/-- Expansion result carrying the augmented and raw edge lists plus surviving loop-backs. -/
inductive AugRes where
  /-- Every branch closed. -/
  | closed
  /-- Open branch, with augmented edges, raw edges, surviving loop-backs, retraction count. -/
  | openBranch (b : IBranch Nat) (aug : IEdges) (raw : IEdges) (lb : List LB) (retracts : Nat)

instance : Inhabited AugRes := ⟨.closed⟩

/-- `true` for the only world-creating rule shape. -/
def isWorldCreating (sf : ISF Nat) : Bool :=
  match sf.sign, sf.formula with
  | .neg, .imp _ _ => true
  | _, _ => false

/-- `intStepBranch` with world-creation deferred: a first pass ignores every `F(· → ·)` entry;
only if that pass finds nothing does the ordinary `intStepBranch` run. -/
def stepPrio (b : IBranch Nat) (expanded : List (ISF Nat)) (nw : Nat) :
    Option (IntRuleResult Nat × List (ISF Nat)) :=
  match b.findSome? fun sf =>
      if expanded.any (· == sf) || isWorldCreating sf then none
      else
        match intApplyRuleFull sf nw b with
        | .notApplicable => none
        | r => some (r, expanded ++ [sf]) with
  | some res => some res
  | none => intStepBranch b expanded nw

/-- The five reuse conditions, re-checked at the CURRENT branch state (the containment conjunct
is the one that can break as the branch grows). -/
def lbOK (b : IBranch Nat) (r : LB) : Bool :=
  let forcedAtX := posFormulasAt b r.x
  (r.ante :: posFormulasAt b r.w).all (forcedAtX.contains ·)
    && !(forcedAtX.contains r.cons)
    && b.any (fun y => y.sign == .neg && y.formula == r.cons && y.label == r.x)

/-- Antecedent/consequent of the `F(φ→ψ)` obligation behind a world-creating step, read off the
`newForms` list exactly as `intFImpReuseWitnessAnc?` does. -/
def obligationOf (newForms : List (ISF Nat)) : Option (Proposition Nat × Proposition Nat) :=
  match newForms.findSome? (fun sf => if sf.sign == .neg then some sf.formula else none),
        newForms.findSome? (fun sf => if sf.sign == .pos then some sf.formula else none) with
  | some ψ, some φ => some (φ, ψ)
  | _, _ => none

/-- Recreation of `intExpandBranches.go`, parameterised by `Cfg`, additionally threading the
raw edge list, the provisional loop-back list, and a retraction counter. `partial`: this is a
scratch probe, the measure is proved in `CslibTests/BetaSplitRefutation.lean` for the baseline. -/
partial def go
    (cfg : Cfg)
    (closurePred : IBranch Nat → Bool)
    (pending : List (IBranch Nat))
    (pExp : List (List (ISF Nat)))
    (pNW : List Nat)
    (pEdges : List IEdges)
    (pAug : List IEdges)
    (pLB : List (List LB))
    (pFuels : List Nat)
    (retracts : Nat)
    (done : List (IBranch Nat))
    (dExp : List (List (ISF Nat)))
    (dNW : List Nat)
    (dEdges : List IEdges)
    (dAug : List IEdges)
    (dLB : List (List LB))
    (dFuels : List Nat) :
    AugRes :=
  match pending, pExp, pNW, pEdges, pAug, pLB, pFuels with
  | [], _, _, _, _, _, _ => .closed
  | b :: restBs, e :: restEs, nw :: restNW, edges :: restEdges, augH :: augT, lbH :: lbT,
      f :: restFs =>
    let bPers := applyPersistenceFixpoint b edges f
    if closurePred bPers then
      go cfg closurePred restBs restEs restNW restEdges augT lbT restFs retracts
        (done ++ [bPers]) (dExp ++ [e]) (dNW ++ [nw]) (dEdges ++ [edges]) (dAug ++ [augH])
        (dLB ++ [lbH]) (dFuels ++ [f])
    else
      match f with
      | 0 => .openBranch bPers augH edges lbH retracts
      | f' + 1 =>
        -- Re-validation pass: drop every loop-back whose containment has broken, un-expand its
        -- discharged entry so the world-creating rule fires again.
        let bad := if cfg.revalidate then lbH.filter (fun r => !(lbOK bPers r)) else []
        if bad.isEmpty then
          match (if cfg.betaPriority then stepPrio bPers e nw else intStepBranch bPers e nw) with
          | none => .openBranch bPers augH edges lbH retracts
          | some (.linearResult newForms nw' newEdge, newExp) =>
            match newEdge with
            | none =>
              go cfg closurePred
                (done ++ [Branch.extendMany bPers newForms] ++ restBs)
                (dExp ++ [newExp] ++ restEs) (dNW ++ [nw'] ++ restNW)
                (dEdges ++ [edges] ++ restEdges) (dAug ++ [augH] ++ augT)
                (dLB ++ [lbH] ++ lbT) (dFuels ++ [f'] ++ restFs) retracts [] [] [] [] [] [] []
            | some newE =>
              match intFImpReuseWitnessAnc? bPers edges newForms newE with
              | some x =>
                let rec? := match obligationOf newForms with
                  | some (φ, ψ) =>
                    [({ x := x, w := newE.2, ante := φ, cons := ψ,
                        sf := ⟨.neg, .imp φ ψ, newE.2⟩ } : LB)]
                  | none => []
                go cfg closurePred
                  (done ++ [bPers] ++ restBs)
                  (dExp ++ [newExp] ++ restEs) (dNW ++ [nw] ++ restNW)
                  (dEdges ++ [if cfg.cyclicEdges then edges ++ [(x, newE.2)] else edges]
                    ++ restEdges)
                  (dAug ++ [augH ++ [(x, newE.2)]] ++ augT)
                  (dLB ++ [lbH ++ rec?] ++ lbT) (dFuels ++ [f'] ++ restFs) retracts
                  [] [] [] [] [] [] []
              | none =>
                go cfg closurePred
                  (done ++ [Branch.extendMany bPers newForms] ++ restBs)
                  (dExp ++ [newExp] ++ restEs) (dNW ++ [nw'] ++ restNW)
                  (dEdges ++ [edges ++ [newE]] ++ restEdges) (dAug ++ [augH ++ [newE]] ++ augT)
                  (dLB ++ [lbH] ++ lbT) (dFuels ++ [f'] ++ restFs) retracts [] [] [] [] [] [] []
          | some (.branchingResult branches' _nw', newExp) =>
            go cfg closurePred
              (done ++ branches'.map (Branch.extendMany bPers ·) ++ restBs)
              (dExp ++ branches'.map (fun _ => newExp) ++ restEs)
              (dNW ++ branches'.map (fun _ => nw) ++ restNW)
              (dEdges ++ branches'.map (fun _ => edges) ++ restEdges)
              (dAug ++ branches'.map (fun _ => augH) ++ augT)
              (dLB ++ branches'.map (fun _ => lbH) ++ lbT)
              (dFuels ++ branches'.map (fun _ => f') ++ restFs) retracts [] [] [] [] [] [] []
          | some (.notApplicable, _) => .openBranch bPers augH edges lbH retracts
        else
          let lb' := lbH.filter (fun r => lbOK bPers r)
          let aug' := augH.filter (fun edge => !(bad.any (fun r => (r.x, r.w) == edge)))
          let e' := e.filter (fun s => !(bad.any (fun r => r.sf == s)))
          let edges' :=
            if cfg.cyclicEdges then
              edges.filter (fun edge => !(bad.any (fun r => (r.x, r.w) == edge)))
            else edges
          go cfg closurePred (done ++ [bPers] ++ restBs) (dExp ++ [e'] ++ restEs)
            (dNW ++ [nw] ++ restNW) (dEdges ++ [edges'] ++ restEdges) (dAug ++ [aug'] ++ augT)
            (dLB ++ [lb'] ++ lbT) (dFuels ++ [f'] ++ restFs) (retracts + bad.length)
            [] [] [] [] [] [] []
  | _ :: restBs, _, _, _, _, _, _ =>
    go cfg closurePred restBs [] [] [] [] [] [] retracts done dExp dNW dEdges dAug dLB dFuels

/-- Run the recreation on `φ` at `fuel`, intuitionistic closure. -/
def expand (cfg : Cfg) (φ : Proposition Nat) (fuel : Nat) : AugRes :=
  go cfg isIntuitionisticallyClosed [[⟨.neg, φ, 0⟩]] [[]] [1] [[]] [[]] [[]] [fuel] 0
    [] [] [] [] [] [] []

/-! ### Metrics -/

/-- Distinct world labels on `b`. -/
def branchLabels (b : IBranch Nat) : List Nat := (b.map (·.label)).eraseDups

/-- Distinct atom indices on `b`. -/
def branchAtoms (b : IBranch Nat) : List Nat :=
  (b.filterMap fun sf => match sf.formula with | .atom p => some p | _ => none).eraseDups

/-- `b` positively forces atom `p` at `w`. -/
def forcesAtom (b : IBranch Nat) (p w : Nat) : Bool :=
  b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w)

/-- One-step successors of `w`. -/
def stepFrom (edges : IEdges) (w : Nat) : List Nat :=
  edges.filterMap fun edge => if edge.2 == w then some edge.1 else none

/-- Transitive-reflexive successor closure. -/
def succsAux (edges : IEdges) (acc : List Nat) (fuel : Nat) : List Nat :=
  match fuel with
  | 0 => acc
  | n + 1 =>
    let next := (acc ++ acc.flatMap (stepFrom edges)).eraseDups
    if next.length == acc.length then acc else succsAux edges next n

/-- Worlds reachable from `w` (reflexively). -/
def succs (edges : IEdges) (w : Nat) : List Nat := succsAux edges [w] (edges.length + 2)

/-- Decidable mirror of `IForces` over `intAccessPreorder edges` / `intExtractValuation b`. -/
def evalF (edges : IEdges) (b : IBranch Nat) : Nat → Proposition Nat → Bool
  | w, .atom p => forcesAtom b p w
  | _, .bot => false
  | w, .imp f g => (succs edges w).all fun w' => !(evalF edges b w' f) || evalF edges b w' g
  | w, .and f g => evalF edges b w f && evalF edges b w g
  | w, .or f g => evalF edges b w f || evalF edges b w g

/-- All worlds mentioned by `b` or `edges`. -/
def worldUniverse (b : IBranch Nat) (edges : IEdges) : List Nat :=
  (branchLabels b ++ edges.map (·.1) ++ edges.map (·.2)).eraseDups

/-- First FULL positive-formula persistence violation `(w, w')`: `w'` accessible from `w`, some
positive formula at `w` missing at `w'`. This is `truthLemma`'s `hpers`, not just its atomic
shadow. -/
def firstPosPersistViol (b : IBranch Nat) (edges : IEdges) : Option (Nat × Nat) :=
  (worldUniverse b edges).findSome? fun w =>
    (succs edges w).findSome? fun w' =>
      if (posFormulasAt b w).all ((posFormulasAt b w').contains ·) then none else some (w, w')

/-- `F(φ→ψ)` obligations at `w`. -/
def fimpObligations (b : IBranch Nat) (w : Nat) : List (Proposition Nat × Proposition Nat) :=
  b.filterMap fun sf =>
    if sf.sign == .neg && sf.label == w then
      match sf.formula with
      | .imp f g => some (f, g)
      | _ => none
    else none

/-- Worlds where `IFimpAccess edges b` fails. Empty = the frame carries `IFimpAccess`. -/
def fimpFailures (b : IBranch Nat) (edges : IEdges) : List Nat :=
  (worldUniverse b edges).filter fun w =>
    !((fimpObligations b w).all fun fg =>
      (succs edges w).any fun w' =>
        b.any (fun sf => sf.sign == .pos && sf.formula == fg.1 && sf.label == w') &&
        b.any (fun sf => sf.sign == .neg && sf.formula == fg.2 && sf.label == w'))

/-- Loop-back edges: augmented edges that are not raw. -/
def loopBackEdges (raw aug : IEdges) : IEdges := aug.filter (fun edge => !(raw.contains edge))

/-- Per-formula adequacy report over the AUGMENTED frame at the given fuel:
`(verdict, maxLabel, raw, loopBacks, retracts, IFimpAccess failures, first hpers violation,
forces φ at 0)`. A frame adequate for `truthLemma` has `[]`, `none` in the two middle slots and
`false` in the last. -/
def reportAug (cfg : Cfg) (φ : Proposition Nat) (fuel : Nat) :
    String × Nat × IEdges × IEdges × Nat × List Nat × Option (Nat × Nat) × Bool :=
  match expand cfg φ fuel with
  | .closed => ("CLOSED", 0, [], [], 0, [], none, false)
  | .openBranch b aug raw _lb r =>
    ("OPEN", (b.map (·.label)).foldl max 0, raw, loopBackEdges raw aug, r,
      fimpFailures b aug, firstPosPersistViol b aug, evalF aug b 0 φ)

/-- Verdict only (for conformance rows). -/
def verdict (cfg : Cfg) (φ : Proposition Nat) (fuel : Nat) : String :=
  match expand cfg φ fuel with
  | .closed => "CLOSED"
  | .openBranch _ _ _ _ _ => "OPEN"

/-- Max world label reached (divergence measurement). -/
def maxLabel (cfg : Cfg) (φ : Proposition Nat) (fuel : Nat) : String × Nat :=
  match expand cfg φ fuel with
  | .closed => ("CLOSED", 0)
  | .openBranch b _ _ _ _ => ("OPEN", (b.map (·.label)).foldl max 0)

/-! ### Formulas -/

/-- Atom `pa`. -/ def pa : Proposition Nat := .atom 0
/-- Atom `pb`. -/ def pb : Proposition Nat := .atom 1
/-- Atom `pr`. -/ def pr : Proposition Nat := .atom 2
/-- Atom `ps`. -/ def ps : Proposition Nat := .atom 3
/-- Atom `pc`. -/ def pc : Proposition Nat := .atom 4

/-- The targeted refutation formula. -/
def phiRef1 : Proposition Nat := ((pr ∨ ps) ∧ ((ps → (ps → pr)) → pb)) → pr
/-- Variant 2. -/
def phiRef2 : Proposition Nat := ((pr ∨ ps) ∧ (((pr ∨ ps) → ((pr ∨ ps) → pr)) → pb)) → pr
/-- Variant 3. -/
def phiRef3 : Proposition Nat := ((pr ∨ ps) ∧ ((ps → (ps → (ps → pr))) → pb)) → pr
/-- Variant 4. -/
def phiRef4 : Proposition Nat := ((pr ∨ ps) ∧ (pc ∧ ((ps → (ps → pr)) → pb))) → pr
/-- Excluded middle. -/
def exMiddle : Proposition Nat := pa ∨ (pa → .bot)
/-- Double negation elimination. -/
def dblNeg : Proposition Nat := ((pa → .bot) → .bot) → pa
/-- Peirce's law. -/
def peirce : Proposition Nat := ((pa → pb) → pa) → pa
/-- De Morgan. -/
def deMorgan : Proposition Nat := ((pa ∧ pb) → .bot) → ((pa → .bot) ∨ (pb → .bot))
/-- Dummett linearity. -/
def dummett : Proposition Nat := (pa → pb) ∨ (pb → pa)

/-- Divergence-witness atoms. -/
def da : Proposition Nat := .atom 0
/-- Divergence-witness atom. -/ def db : Proposition Nat := .atom 1
/-- Divergence-witness atom. -/ def dc : Proposition Nat := .atom 2
/-- Divergence-witness atom. -/ def dd : Proposition Nat := .atom 3
/-- Divergence-witness atom. -/ def de : Proposition Nat := .atom 4
/-- Divergence-witness atom. -/ def df : Proposition Nat := .atom 5
/-- Divergence-witness atom. -/ def du1 : Proposition Nat := .atom 6
/-- Divergence-witness atom. -/ def dv1 : Proposition Nat := .atom 7
/-- Divergence-witness atom. -/ def du2 : Proposition Nat := .atom 8
/-- Divergence-witness atom. -/ def dv2 : Proposition Nat := .atom 9

/-- The complexity-9 divergence witness. -/
def phi0 : Proposition Nat :=
  (((da → db) → dc) ∧ ((dd → de) → df)) → ((du1 → dv1) ∨ (du2 → dv2))

/-- Baseline configuration (bit-identical to the library calculus). -/
def V0 : Cfg := ⟨false, false, false⟩
/-- Beta-priority only. -/
def V1 : Cfg := ⟨true, false, false⟩
/-- Re-validation only. -/
def V2 : Cfg := ⟨false, true, false⟩
/-- Cyclic edges only. -/
def V3 : Cfg := ⟨false, false, true⟩
/-- Beta-priority + re-validation. -/
def V4 : Cfg := ⟨true, true, false⟩

/-- The eight-formula adequacy corpus. -/
def corpus : List (String × Proposition Nat) :=
  [("phiRef1", phiRef1), ("phiRef2", phiRef2), ("phiRef3", phiRef3), ("phiRef4", phiRef4),
   ("exMiddle", exMiddle), ("dblNeg", dblNeg), ("peirce", peirce), ("deMorgan", deMorgan),
   ("dummett", dummett)]

/-- Adequacy sweep over `corpus` at the real entry-point fuel. -/
def sweep (cfg : Cfg) :
    List (String × String × Nat × IEdges × IEdges × Nat × List Nat × Option (Nat × Nat) × Bool) :=
  corpus.map fun nf =>
    let r := reportAug cfg nf.2 (intFuelExt nf.2)
    (nf.1, r)

/-- Compact adequacy verdict per formula: `(name, IFimpAccess ok, hpers ok, ¬forces at 0)`. -/
def sweepCompact (cfg : Cfg) : List (String × Bool × Bool × Bool) :=
  corpus.map fun nf =>
    match expand cfg nf.2 (intFuelExt nf.2) with
    | .closed => (nf.1 ++ "[CLOSED]", true, true, true)
    | .openBranch b aug _raw _lb _r =>
      (nf.1, (fimpFailures b aug).isEmpty, (firstPosPersistViol b aug).isNone,
        !(evalF aug b 0 nf.2))

end ReuseProbe

section Driver
open ReuseProbe
#eval! sweepCompact V0
#eval! sweepCompact V1
#eval! sweepCompact V2
#eval! sweepCompact V3
#eval! sweepCompact V4
end Driver
