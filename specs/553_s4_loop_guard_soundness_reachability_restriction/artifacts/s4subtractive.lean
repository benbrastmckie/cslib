import Cslib.Logics.Modal.Tableau.LoopChecking

/-! # Route (3) probe: `Massacci2000` Technique 8.2 SUBTRACTIVE blocking

Definitions and `#eval` only -- no proofs, no `sorry`, no axioms.

Route (3) changes the blocked minting case of `modalApplyOneS4Keyed`
(`LoopChecking.lean:753`, `:758`) from

    (.linear [], acc.addEdge sf.label wBlock)      -- CSLib: additive (redirect edge)

to

    (.linear [], acc)                              -- Massacci Tech. 8.2: subtractive (no edge)

The guard itself (`blockingWorldS4Keyed`, `LoopChecking.lean:506`) is UNCHANGED: the same
blocking decisions are made, only the effect differs. Two sub-variants are measured, because
"withhold the pi-rule" admits two readings in the CSLib architecture:

* **S1 (consume)**: `(.linear [], acc)` -- the formula is retired into `e`, nothing is added.
* **S2 (withhold)**: `.notApplicable` -- the formula is never retired; `findSome?` skips it.

Measurements:

* **A (soundness)**: is `cex` (report 01 / `blockingWorldS4Keyed` docstring, node-size 19) OPEN?
* **B (validity)**: are the T, 4, K axiom instances CLOSED?
* **C (differential sweep)**: exhaustive 2-atom, size<=6, fuel-100 sweep against the shipped
  keyed driver, reporting `open -> closed` (must be 0) and `closed -> open`.
* **D (termination)**: max recorded-world count (`keys.length`), max DFS depth consumed, max
  out-degree, max edge count, and whether global `keysDistinct` breaks -- baseline vs both
  subtractive variants, over the same corpus.
* **E (completeness oracle)**: an INDEPENDENT semantic validity oracle over all reflexive-
  transitive frames of size <= 3 with 2 atoms. Every `closed -> open` formula is tested: if it
  has a countermodel, subtractive blocking CORRECTED an unsound baseline closure; if it has no
  countermodel of size <= 3 it is a completeness-loss SUSPECT and is printed for inspection.
  The oracle is validated on `cex` (must be falsifiable at size 3, per the docstring's explicit
  3-world countermodel) and on T/4/K (must not be falsifiable).
-/

set_option maxRecDepth 100000

open Cslib.Logic.Modal Cslib.Logic.Tableau Cslib.Logic.Modal.Tableau

abbrev P := Proposition Nat

partial def ppP : P → String
  | .atom n => s!"p{n}"
  | .bot => "⊥"
  | .imp x y => s!"({ppP x}→{ppP y})"
  | .and x y => s!"({ppP x}∧{ppP y})"
  | .or x y => s!"({ppP x}∨{ppP y})"
  | .box x => s!"□{ppP x}"
  | .diamond x => s!"◇{ppP x}"

abbrev Keys := List (WorldIndex × Finset (Sign × P))

/-! ## The two subtractive rule-application variants -/

/-- **S1 (consume)**: as `modalApplyOneS4Keyed` (`LoopChecking.lean:747`) but the blocked case
emits `(.linear [], acc)` -- NO EDGE. The formula is still retired into `e`. -/
def applyS1 (φ₀ : P) (keys : Keys) : SignedFormula P WorldIndex →
    List (SignedFormula P WorldIndex) → Accessibility →
    RuleResult P WorldIndex × Accessibility :=
  fun sf b acc =>
    match sf.sign, sf.formula with
    | .neg, .box φ =>
      match blockingWorldS4Keyed φ₀ b keys .neg φ sf.label with
      | some _ => (.linear [], acc)
      | none => modalApplyOne sf b acc
    | .pos, .diamond φ =>
      match blockingWorldS4Keyed φ₀ b keys .pos φ sf.label with
      | some _ => (.linear [], acc)
      | none => modalApplyOne sf b acc
    | _, _ => modalApplyOneS4 φ₀ sf b acc

/-- **S2 (withhold)**: the blocked case emits `.notApplicable` -- the pi-rule is literally
withheld, the formula is not retired, and the traversal moves past it. Closest to the letter of
`Massacci2000` Technique 8.2 ("before reducing a pi-formula, check whether the corresponding
prefix is not a copy of a shorter prefix"). -/
def applyS2 (φ₀ : P) (keys : Keys) : SignedFormula P WorldIndex →
    List (SignedFormula P WorldIndex) → Accessibility →
    RuleResult P WorldIndex × Accessibility :=
  fun sf b acc =>
    match sf.sign, sf.formula with
    | .neg, .box φ =>
      match blockingWorldS4Keyed φ₀ b keys .neg φ sf.label with
      | some _ => (.notApplicable, acc)
      | none => modalApplyOne sf b acc
    | .pos, .diamond φ =>
      match blockingWorldS4Keyed φ₀ b keys .pos φ sf.label with
      | some _ => (.notApplicable, acc)
      | none => modalApplyOne sf b acc
    | _, _ => modalApplyOneS4 φ₀ sf b acc

/-! ## Steppers (mirroring `modalStepBranchS4Keyed` / `modalStepBranchS4KeyedOrdered`) -/

abbrev StepRes :=
  List (List (SignedFormula P WorldIndex)) × List (List (SignedFormula P WorldIndex)) ×
    Accessibility × Keys

/-- Per-formula body, parametric in the rule-application variant. The `keys'` computation is
verbatim `modalStepBranchS4Keyed`'s (`LoopChecking.lean:966-976`): a blocked minting shape
records nothing, an unblocked one records `(modalNextWorld b, successorBirthContent ...)`. -/
def bodySub (app : P → Keys → SignedFormula P WorldIndex → List (SignedFormula P WorldIndex) →
      Accessibility → RuleResult P WorldIndex × Accessibility)
    (φ₀ : P) (b e : List (SignedFormula P WorldIndex)) (acc : Accessibility) (keys : Keys)
    (sf : SignedFormula P WorldIndex) : Option StepRes :=
  if e.any (· == sf) then none
  else
    let (result, newAcc) := app φ₀ keys sf b acc
    let keys' :=
      match sf.sign, sf.formula with
      | .neg, .box φ =>
        match blockingWorldS4Keyed φ₀ b keys .neg φ sf.label with
        | some _ => keys
        | none => keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .neg φ sf.label)]
      | .pos, .diamond φ =>
        match blockingWorldS4Keyed φ₀ b keys .pos φ sf.label with
        | some _ => keys
        | none => keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .pos φ sf.label)]
      | _, _ => keys
    match result with
    | .linear newForms => some ([newForms ++ b], [e ++ [sf]], newAcc, keys')
    | .branching branches =>
      some (branches.map (· ++ b), branches.map (fun _ => e ++ [sf]), newAcc, keys')
    | .persistent newForms => some ([newForms ++ b], [e], newAcc, keys')
    | .notApplicable => none

/-- Unordered stepper (mirrors `modalStepBranchS4Keyed`, `LoopChecking.lean:955`). -/
def stepSub (app : P → Keys → SignedFormula P WorldIndex → List (SignedFormula P WorldIndex) →
      Accessibility → RuleResult P WorldIndex × Accessibility)
    (φ₀ : P) (b e : List (SignedFormula P WorldIndex)) (acc : Accessibility) (keys : Keys) :
    Option StepRes :=
  b.findSome? (bodySub app φ₀ b e acc keys)

/-- Non-minting candidates under the given variant (mirrors `modalNonMintCandidates`,
`LoopChecking.lean:873`). -/
def nonMintSub (app : P → Keys → SignedFormula P WorldIndex → List (SignedFormula P WorldIndex) →
      Accessibility → RuleResult P WorldIndex × Accessibility)
    (φ₀ : P) (keys : Keys) (b e : List (SignedFormula P WorldIndex)) (acc : Accessibility) :
    List (SignedFormula P WorldIndex) :=
  b.filter (fun sf =>
    !modalMintShape sf && !(e.any (· == sf)) && (app φ₀ keys sf b acc).1.isApplicable)

/-- Ordered stepper (mirrors `modalStepBranchS4KeyedOrdered`, `LoopChecking.lean:1107`). -/
def stepSubOrdered (app : P → Keys → SignedFormula P WorldIndex →
      List (SignedFormula P WorldIndex) → Accessibility →
      RuleResult P WorldIndex × Accessibility)
    (φ₀ : P) (b e : List (SignedFormula P WorldIndex)) (acc : Accessibility) (keys : Keys) :
    Option StepRes :=
  match (nonMintSub app φ₀ keys b e acc).findSome? (bodySub app φ₀ b e acc keys) with
  | some r => some r
  | none => stepSub app φ₀ b e acc keys

/-! ## Termination instrumentation -/

structure TStats where
  maxWorlds : Nat := 1
  maxDepth : Nat := 0
  maxOutDeg : Nat := 0
  maxEdges : Nat := 0
  keysBroken : Bool := false
  deriving Inhabited

def combineT (a b : TStats) : TStats :=
  { maxWorlds := max a.maxWorlds b.maxWorlds
    maxDepth := max a.maxDepth b.maxDepth
    maxOutDeg := max a.maxOutDeg b.maxOutDeg
    maxEdges := max a.maxEdges b.maxEdges
    keysBroken := a.keysBroken || b.keysBroken }

def keysDistinctBroken (keys : Keys) : Bool :=
  keys.any (fun k1 => keys.any (fun k2 => (k1.1 != k2.1) && decide (k1.2 = k2.2)))

def maxOutDegree (acc : Accessibility) : Nat :=
  (acc.allWorlds.map (fun w => (acc.edges.filter (fun edg => edg.1 == w)).length)).foldl max 0

def leafT (depth : Nat) (acc : Accessibility) (keys : Keys) : TStats :=
  { maxWorlds := keys.length, maxDepth := depth, maxOutDeg := maxOutDegree acc
    maxEdges := acc.edges.length, keysBroken := keysDistinctBroken keys }

/-! ## Drivers -/

/-- Subtractive driver, verdict + termination stats. `depth` counts steps consumed on the
current path. -/
partial def dfsSub (app : P → Keys → SignedFormula P WorldIndex →
      List (SignedFormula P WorldIndex) → Accessibility →
      RuleResult P WorldIndex × Accessibility)
    (ordered : Bool) (φ₀ : P) (fuel depth : Nat) (b e : List (SignedFormula P WorldIndex))
    (acc : Accessibility) (keys : Keys) : Option Bool × TStats :=
  if isModalClosed b then (some true, leafT depth acc keys)
  else match fuel with
  | 0 => (none, leafT depth acc keys)
  | fuel' + 1 =>
    match (if ordered then stepSubOrdered app φ₀ b e acc keys
           else stepSub app φ₀ b e acc keys) with
    | none => (some false, leafT depth acc keys)
    | some (bs, es, acc', keys') =>
      let rec go (bs : List (List (SignedFormula P WorldIndex)))
          (es : List (List (SignedFormula P WorldIndex))) : Option Bool × TStats :=
        match bs, es with
        | [], _ => (some true, leafT depth acc' keys')
        | b2 :: rbs, e2 :: res =>
          match dfsSub app ordered φ₀ fuel' (depth + 1) b2 e2 acc' keys' with
          | (some true, s) => let (r2, s2) := go rbs res; (r2, combineT s s2)
          | (x, s) => (x, s)
        | _, _ => (some true, leafT depth acc' keys')
      go bs es

def runSub (app : P → Keys → SignedFormula P WorldIndex → List (SignedFormula P WorldIndex) →
      Accessibility → RuleResult P WorldIndex × Accessibility)
    (ordered : Bool) (φ₀ : P) (fuel : Nat) : Option Bool × TStats :=
  dfsSub app ordered φ₀ fuel 0 [⟨.neg, φ₀, 0⟩] [] Accessibility.empty
    [((0 : WorldIndex), (∅ : Finset (Sign × P)))]

/-- Baseline: the SHIPPED keyed driver `modalStepBranchS4Keyed` called directly (a genuine
control, not a reimplementation), instrumented with the same `TStats`. -/
partial def dfsBase (φ₀ : P) (fuel depth : Nat) (b e : List (SignedFormula P WorldIndex))
    (acc : Accessibility) (keys : Keys) : Option Bool × TStats :=
  if isModalClosed b then (some true, leafT depth acc keys)
  else match fuel with
  | 0 => (none, leafT depth acc keys)
  | fuel' + 1 =>
    match modalStepBranchS4Keyed φ₀ b e acc keys with
    | none => (some false, leafT depth acc keys)
    | some (bs, es, acc', keys') =>
      let rec go (bs : List (List (SignedFormula P WorldIndex)))
          (es : List (List (SignedFormula P WorldIndex))) : Option Bool × TStats :=
        match bs, es with
        | [], _ => (some true, leafT depth acc' keys')
        | b2 :: rbs, e2 :: res =>
          match dfsBase φ₀ fuel' (depth + 1) b2 e2 acc' keys' with
          | (some true, s) => let (r2, s2) := go rbs res; (r2, combineT s s2)
          | (x, s) => (x, s)
        | _, _ => (some true, leafT depth acc' keys')
      go bs es

def runBase (φ₀ : P) (fuel : Nat) : Option Bool × TStats :=
  dfsBase φ₀ fuel 0 [⟨.neg, φ₀, 0⟩] [] Accessibility.empty
    [((0 : WorldIndex), (∅ : Finset (Sign × P)))]

/-! ## Measurement E: an independent semantic validity oracle

Exhaustive over all reflexive-transitive (S4) frames on `n <= N` worlds and all valuations of
`natoms` atoms. `falsifiableUpTo` returns the least witnessing size, or `none`. Independent of
the tableau machinery: a direct `Bool` evaluator of the modal truth conditions. -/

def bitAt (m i : Nat) : Bool := (m / (2 ^ i)) % 2 == 1

def offDiag (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap (fun i =>
    (List.range n).filterMap (fun j => if i == j then none else some (i, j)))

/-- Reflexive relation on `range n` determined by off-diagonal bitmask `m`. -/
def relOfMask (n m : Nat) : Nat → Nat → Bool :=
  let od := offDiag n
  fun i j => i == j || (decide ((od.idxOf (i, j)) < od.length) && bitAt m (od.idxOf (i, j)))

def relIsTrans (n : Nat) (r : Nat → Nat → Bool) : Bool :=
  (List.range n).all (fun i => (List.range n).all (fun j => (List.range n).all (fun k =>
    !(r i j && r j k) || r i k)))

def valOfMask (natoms m : Nat) : Nat → Nat → Bool := fun w a => bitAt m (w * natoms + a)

partial def evalP (n : Nat) (r : Nat → Nat → Bool) (v : Nat → Nat → Bool) : P → Nat → Bool
  | .atom a, w => v w a
  | .bot, _ => false
  | .imp x y, w => !evalP n r v x w || evalP n r v y w
  | .and x y, w => evalP n r v x w && evalP n r v y w
  | .or x y, w => evalP n r v x w || evalP n r v y w
  | .box x, w => (List.range n).all (fun u => !r w u || evalP n r v x u)
  | .diamond x, w => (List.range n).any (fun u => r w u && evalP n r v x u)

def falsifiableAtSize (natoms n : Nat) (φ : P) : Bool :=
  (List.range (2 ^ (n * (n - 1)))).any (fun fm =>
    let r := relOfMask n fm
    relIsTrans n r && (List.range (2 ^ (n * natoms))).any (fun vm =>
      let v := valOfMask natoms vm
      (List.range n).any (fun w => !evalP n r v φ w)))

/-- Least `n <= N` at which `φ` has an S4 countermodel, or `none`. `none` means "no
countermodel of size <= N" -- NOT a validity proof, but a strong signal. -/
def falsifiableUpTo (natoms N : Nat) (φ : P) : Option Nat :=
  (List.range N).findSome? (fun i =>
    if falsifiableAtSize natoms (i + 1) φ then some (i + 1) else none)

/-! ## Corpus (verbatim from report 01 / `blockingWorldS4Keyed`'s docstring) -/

def p0 : P := .atom 0
def p1 : P := .atom 1
def nt (x : P) : P := .imp x .bot
def alphaA : P := .or (.box p0) (nt (nt (.diamond p1)))
def alphaL : P := .or (.box p0) (nt (.box p1))
def cex : P := .or (.box alphaA) (.box alphaL)
def tAxiom : P := .imp (.box p0) p0
def fourAxiom : P := .imp (.box p0) (.box (.box p0))
def kAxiom : P := .imp (.box (.imp p0 p1)) (.imp (.box p0) (.box p1))

#eval IO.println s!"cex = {ppP cex}"

/-! ### Oracle validation -/

#eval IO.println
  s!"E0: oracle(cex)={falsifiableUpTo 2 3 cex} (expect some 3)  oracle(T)={falsifiableUpTo 2 3 tAxiom} oracle(4)={falsifiableUpTo 2 3 fourAxiom} oracle(K)={falsifiableUpTo 2 3 kAxiom} (expect none,none,none)"

/-! ### Measurement A: soundness -- cex must be OPEN under both subtractive variants -/

#eval IO.println
  s!"A: baseline(cex,400)={(runBase cex 400).1}  S1-unord={(runSub applyS1 false cex 400).1}  S1-ord={(runSub applyS1 true cex 400).1}  S2-unord={(runSub applyS2 false cex 400).1}  S2-ord={(runSub applyS2 true cex 400).1}  (expect subtractive = some false)"

/-! ### Measurement B: validity -- T, 4, K must be CLOSED -/

#eval IO.println
  s!"B: T   base={(runBase tAxiom 400).1} S1u={(runSub applyS1 false tAxiom 400).1} S1o={(runSub applyS1 true tAxiom 400).1} S2u={(runSub applyS2 false tAxiom 400).1} S2o={(runSub applyS2 true tAxiom 400).1}"
#eval IO.println
  s!"B: 4   base={(runBase fourAxiom 400).1} S1u={(runSub applyS1 false fourAxiom 400).1} S1o={(runSub applyS1 true fourAxiom 400).1} S2u={(runSub applyS2 false fourAxiom 400).1} S2o={(runSub applyS2 true fourAxiom 400).1}"
#eval IO.println
  s!"B: K   base={(runBase kAxiom 400).1} S1u={(runSub applyS1 false kAxiom 400).1} S1o={(runSub applyS1 true kAxiom 400).1} S2u={(runSub applyS2 false kAxiom 400).1} S2o={(runSub applyS2 true kAxiom 400).1}"

/-! ### Formula enumeration (verbatim from `s4probe.lean` / `s4ancestor.lean`) -/

def atomsList (natoms : Nat) : List P := (List.range natoms).map (fun i => .atom i)

partial def gen (natoms : Nat) : Nat → List P
  | 0 => []
  | 1 => .bot :: atomsList natoms
  | n + 1 =>
    let unary := (gen natoms n).flatMap (fun x => [Proposition.box x, Proposition.diamond x])
    let binary := (List.range n).filterMap (fun i => if i == 0 then none else some i) |>.flatMap
      (fun i =>
        let l := gen natoms i
        let r := gen natoms (n - i)
        l.flatMap (fun x => r.flatMap (fun y => [Proposition.imp x y, .and x y, .or x y])))
    unary ++ binary

def allUpTo (natoms sz : Nat) : List P :=
  (List.range sz).flatMap (fun i => gen natoms (i + 1))

/-! ### Measurements C + D (one combined pass) -/

structure Row where
  f : P
  base : Option Bool
  s1 : Option Bool
  s2 : Option Bool
  bT : TStats
  s1T : TStats
  s2T : TStats

/-- Ordered variants are used for the S1/S2 columns, matching `s4ancestor.lean`'s convention of
reporting the settled-context-scheduled successor; the unordered column is spot-checked in
Measurement A/B above. -/
def sweepRows (natoms sz fuel : Nat) : List Row :=
  (allUpTo natoms sz).map (fun f =>
    let (b, bT) := runBase f fuel
    let (r1, s1T) := runSub applyS1 true f fuel
    let (r2, s2T) := runSub applyS2 true f fuel
    { f := f, base := b, s1 := r1, s2 := r2, bT := bT, s1T := s1T, s2T := s2T })

def rBaseClosed (r : Row) : Bool := r.base == some true
def rBaseOpen (r : Row) : Bool := r.base == some false
def rBaseFuel (r : Row) : Bool := r.base == none
def rS1Closed (r : Row) : Bool := r.s1 == some true
def rS1Open (r : Row) : Bool := r.s1 == some false
def rS1Fuel (r : Row) : Bool := r.s1 == none
def rS2Closed (r : Row) : Bool := r.s2 == some true
def rS2Open (r : Row) : Bool := r.s2 == some false
def rS2Fuel (r : Row) : Bool := r.s2 == none
def rS1OpenToClosed (r : Row) : Bool := r.base == some false && r.s1 == some true
def rS1ClosedToOpen (r : Row) : Bool := r.base == some true && r.s1 == some false
def rS2OpenToClosed (r : Row) : Bool := r.base == some false && r.s2 == some true
def rS2ClosedToOpen (r : Row) : Bool := r.base == some true && r.s2 == some false
def rS1S2Differ (r : Row) : Bool := !(r.s1 == r.s2)
def rBW (r : Row) : Nat := r.bT.maxWorlds
def rBD (r : Row) : Nat := r.bT.maxDepth
def rBO (r : Row) : Nat := r.bT.maxOutDeg
def rBE (r : Row) : Nat := r.bT.maxEdges
def rBK (r : Row) : Bool := r.bT.keysBroken
def r1W (r : Row) : Nat := r.s1T.maxWorlds
def r1D (r : Row) : Nat := r.s1T.maxDepth
def r1O (r : Row) : Nat := r.s1T.maxOutDeg
def r1E (r : Row) : Nat := r.s1T.maxEdges
def r1K (r : Row) : Bool := r.s1T.keysBroken
def r2W (r : Row) : Nat := r.s2T.maxWorlds
def r2D (r : Row) : Nat := r.s2T.maxDepth
def r2K (r : Row) : Bool := r.s2T.keysBroken
def rFormula (r : Row) : P := r.f
def rWorldsGrew (r : Row) : Bool := decide (r.s1T.maxWorlds > r.bT.maxWorlds)
def rDepthGrew (r : Row) : Bool := decide (r.s1T.maxDepth > r.bT.maxDepth)

/-! Named top-level helpers for the Measurement E aggregation. Inline lambdas over tuple fields
inside a `#eval do` block leave the binder's type unresolved during elaboration (the same issue
`s4ancestor.lean` records); named functions sidestep it. -/

def oracleRow (f : P) : P × Option Nat := (f, falsifiableUpTo 2 3 f)
def orIsRefuted (pr : P × Option Nat) : Bool := !(pr.2 == none)
def orIsSuspect (pr : P × Option Nat) : Bool := pr.2 == none
def orPP (pr : P × Option Nat) : String := ppP pr.1
def hasCexSize2 (f : P) : Bool := !(falsifiableUpTo 2 2 f == none)
def hasCexSize3 (f : P) : Bool := !(falsifiableUpTo 2 3 f == none)

#eval do
  let rows := sweepRows 2 6 100
  let total := rows.length
  IO.println s!"C: total={total}"
  IO.println s!"C: baseline (closed={(rows.filter rBaseClosed).length}, open={(rows.filter rBaseOpen).length}, fuelExhausted={(rows.filter rBaseFuel).length})  (expect 1650/6882/0)"
  IO.println s!"C: S1-ord  (closed={(rows.filter rS1Closed).length}, open={(rows.filter rS1Open).length}, fuelExhausted={(rows.filter rS1Fuel).length})"
  IO.println s!"C: S2-ord  (closed={(rows.filter rS2Closed).length}, open={(rows.filter rS2Open).length}, fuelExhausted={(rows.filter rS2Fuel).length})"
  IO.println s!"C: S1 vs baseline: openToClosed(MUST BE 0)={(rows.filter rS1OpenToClosed).length}  closedToOpen={(rows.filter rS1ClosedToOpen).length}"
  IO.println s!"C: S2 vs baseline: openToClosed(MUST BE 0)={(rows.filter rS2OpenToClosed).length}  closedToOpen={(rows.filter rS2ClosedToOpen).length}"
  IO.println s!"C: S1 vs S2 verdict disagreements = {(rows.filter rS1S2Differ).length}"
  IO.println s!"D: baseline maxWorlds={(rows.map rBW).foldl max 0} maxDepth={(rows.map rBD).foldl max 0} maxOutDeg={(rows.map rBO).foldl max 0} maxEdges={(rows.map rBE).foldl max 0} keysBrokenCount={(rows.filter rBK).length}"
  IO.println s!"D: S1       maxWorlds={(rows.map r1W).foldl max 0} maxDepth={(rows.map r1D).foldl max 0} maxOutDeg={(rows.map r1O).foldl max 0} maxEdges={(rows.map r1E).foldl max 0} keysBrokenCount={(rows.filter r1K).length}"
  IO.println s!"D: S2       maxWorlds={(rows.map r2W).foldl max 0} maxDepth={(rows.map r2D).foldl max 0} keysBrokenCount={(rows.filter r2K).length}"
  IO.println s!"D: formulas where S1 maxWorlds EXCEEDS baseline = {(rows.filter rWorldsGrew).length}  where S1 maxDepth EXCEEDS baseline = {(rows.filter rDepthGrew).length}"
  -- Measurement E: run the semantic oracle on the closed->open differential.
  let diff := (rows.filter rS1ClosedToOpen).map rFormula
  IO.println s!"E: closed->open differential size = {diff.length}"
  let orc := diff.map oracleRow
  let refuted := orc.filter orIsRefuted
  let suspects := orc.filter orIsSuspect
  IO.println s!"E: of these, HAVE an S4 countermodel of size <=3 (baseline was UNSOUND here) = {refuted.length}"
  IO.println s!"E: of these, NO countermodel of size <=3 (COMPLETENESS-LOSS SUSPECTS) = {suspects.length}"
  IO.println s!"E: suspects (first 40): {(suspects.take 40).map orPP}"
  -- Cross-check: how many closures of each driver are outright unsound on this corpus?
  let bclosed := (rows.filter rBaseClosed).map rFormula
  IO.println s!"E: baseline-closed with a countermodel of size <=2 (UNSOUND closures) = {(bclosed.filter hasCexSize2).length} / {bclosed.length}"
  let s1closed := (rows.filter rS1Closed).map rFormula
  IO.println s!"E: S1-closed      with a countermodel of size <=2 (UNSOUND closures) = {(s1closed.filter hasCexSize2).length} / {s1closed.length}"
  let s2closed := (rows.filter rS2Closed).map rFormula
  IO.println s!"E: S2-closed      with a countermodel of size <=2 (UNSOUND closures) = {(s2closed.filter hasCexSize2).length} / {s2closed.length}"
  -- Completeness cross-check in the other direction: formulas with NO countermodel of size <=3
  -- (i.e. very likely S4-valid) that each driver nonetheless leaves OPEN.
  let baseOpenF := (rows.filter rBaseOpen).map rFormula
  IO.println s!"E: baseline-OPEN with NO countermodel of size <=3 (completeness suspects) = {(baseOpenF.filter (fun f => !hasCexSize3 f)).length} / {baseOpenF.length}"
  let s1OpenF := (rows.filter rS1Open).map rFormula
  IO.println s!"E: S1-OPEN      with NO countermodel of size <=3 (completeness suspects) = {(s1OpenF.filter (fun f => !hasCexSize3 f)).length} / {s1OpenF.length}"
