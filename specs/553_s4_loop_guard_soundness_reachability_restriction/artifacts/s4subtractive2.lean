import Cslib.Logics.Modal.Tableau.LoopChecking

/-! # Route (3) probe, part 2: does blocking actually FIRE, and does the differential stay empty
on a deeper corpus?

`s4subtractive.lean` established that over the 2-atom, size<=6, fuel-100 corpus (8532 formulas)
the subtractive variants S1/S2 agree with the shipped keyed driver on **every** formula
(1650 closed / 6882 open / 0 fuel-exhausted, 0 `open->closed`, 0 `closed->open`), while `cex`
flips from CLOSED (unsound) to OPEN. Two gaps remain in that measurement, both closed here:

* **Gap 1 — vacuity.** If the loop guard never fires on the size<=6 corpus, verdict agreement is
  uninformative. Here every step of the SHIPPED driver is classified: a blocked step is exactly
  one where `acc` gains an edge while `keys` does not gain a world (a mint gains BOTH; a
  non-minting shape gains NEITHER). This gives an exact per-formula count of redirect edges laid
  down by the shipped driver.
* **Gap 2 — corpus depth.** `cex` has node-size 19, far outside size<=6. Two deeper corpora are
  swept here: 1 atom / size<=8 (95730 formulas) and 2 atoms / size<=7 (55299 formulas).
-/

set_option maxRecDepth 100000

open Cslib.Logic.Modal Cslib.Logic.Tableau Cslib.Logic.Modal.Tableau

abbrev P := Proposition Nat
abbrev Keys := List (WorldIndex × Finset (Sign × P))

partial def ppP : P → String
  | .atom n => s!"p{n}"
  | .bot => "⊥"
  | .imp x y => s!"({ppP x}→{ppP y})"
  | .and x y => s!"({ppP x}∧{ppP y})"
  | .or x y => s!"({ppP x}∨{ppP y})"
  | .box x => s!"□{ppP x}"
  | .diamond x => s!"◇{ppP x}"

/-- S1 (consume): the blocked case emits `(.linear [], acc)` -- no edge. -/
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

abbrev StepRes :=
  List (List (SignedFormula P WorldIndex)) × List (List (SignedFormula P WorldIndex)) ×
    Accessibility × Keys

def bodyS1 (φ₀ : P) (b e : List (SignedFormula P WorldIndex)) (acc : Accessibility) (keys : Keys)
    (sf : SignedFormula P WorldIndex) : Option StepRes :=
  if e.any (· == sf) then none
  else
    let (result, newAcc) := applyS1 φ₀ keys sf b acc
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

def stepS1 (φ₀ : P) (b e : List (SignedFormula P WorldIndex)) (acc : Accessibility)
    (keys : Keys) : Option StepRes :=
  b.findSome? (bodyS1 φ₀ b e acc keys)

/-- Verdict only. -/
partial def dfsS1 (φ₀ : P) (fuel : Nat) (b e : List (SignedFormula P WorldIndex))
    (acc : Accessibility) (keys : Keys) : Option Bool :=
  if isModalClosed b then some true
  else match fuel with
  | 0 => none
  | fuel' + 1 =>
    match stepS1 φ₀ b e acc keys with
    | none => some false
    | some (bs, es, acc', keys') =>
      let rec go (bs : List (List (SignedFormula P WorldIndex)))
          (es : List (List (SignedFormula P WorldIndex))) : Option Bool :=
        match bs, es with
        | [], _ => some true
        | b2 :: rbs, e2 :: res =>
          match dfsS1 φ₀ fuel' b2 e2 acc' keys' with
          | some true => go rbs res
          | x => x
        | _, _ => some true
      go bs es

def runS1 (φ₀ : P) (fuel : Nat) : Option Bool :=
  dfsS1 φ₀ fuel [⟨.neg, φ₀, 0⟩] [] Accessibility.empty
    [((0 : WorldIndex), (∅ : Finset (Sign × P)))]

/-! ## Baseline with EXACT blocked-step classification

The shipped `modalStepBranchS4Keyed` (`LoopChecking.lean:955`) returns `(bs, es, acc', keys')`.
Exactly one of three things happened at the selected formula:

* **unblocked mint** — `modalApplyOne` at a minting shape: `acc` gains one edge AND `keys` gains
  one world (`LoopChecking.lean:971`, `:975`);
* **blocked mint** — `modalApplyOneS4Keyed`'s blocked arm (`LoopChecking.lean:753`, `:758`):
  `acc` gains one edge, `keys` is UNCHANGED;
* **non-minting shape** — neither `acc` nor `keys` changes (no S4/K non-minting rule calls
  `addEdge`).

So `acc'.edges.length > acc.edges.length && keys'.length == keys.length` classifies a blocked
step exactly. `blocks` accumulates the max over the explored paths. -/
partial def dfsBaseBlocks (φ₀ : P) (fuel blocks : Nat) (b e : List (SignedFormula P WorldIndex))
    (acc : Accessibility) (keys : Keys) : Option Bool × Nat :=
  if isModalClosed b then (some true, blocks)
  else match fuel with
  | 0 => (none, blocks)
  | fuel' + 1 =>
    match modalStepBranchS4Keyed φ₀ b e acc keys with
    | none => (some false, blocks)
    | some (bs, es, acc', keys') =>
      let wasBlock :=
        decide (acc'.edges.length > acc.edges.length) && (keys'.length == keys.length)
      let blocks' := if wasBlock then blocks + 1 else blocks
      let rec go (bs : List (List (SignedFormula P WorldIndex)))
          (es : List (List (SignedFormula P WorldIndex))) : Option Bool × Nat :=
        match bs, es with
        | [], _ => (some true, blocks')
        | b2 :: rbs, e2 :: res =>
          match dfsBaseBlocks φ₀ fuel' blocks' b2 e2 acc' keys' with
          | (some true, k) => let (r2, k2) := go rbs res; (r2, max k k2)
          | (x, k) => (x, k)
        | _, _ => (some true, blocks')
      go bs es

def runBaseBlocks (φ₀ : P) (fuel : Nat) : Option Bool × Nat :=
  dfsBaseBlocks φ₀ fuel 0 [⟨.neg, φ₀, 0⟩] [] Accessibility.empty
    [((0 : WorldIndex), (∅ : Finset (Sign × P)))]

/-! ## Corpus -/

def p0 : P := .atom 0
def p1 : P := .atom 1
def nt (x : P) : P := .imp x .bot
def alphaA : P := .or (.box p0) (nt (nt (.diamond p1)))
def alphaL : P := .or (.box p0) (nt (.box p1))
def cex : P := .or (.box alphaA) (.box alphaL)

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

/-! ## Sweep -/

structure Row2 where
  f : P
  base : Option Bool
  blocks : Nat
  s1 : Option Bool

def sweep2 (natoms sz fuel : Nat) : List Row2 :=
  (allUpTo natoms sz).map (fun f =>
    let (b, k) := runBaseBlocks f fuel
    { f := f, base := b, blocks := k, s1 := runS1 f fuel })

def q2Closed (r : Row2) : Bool := r.base == some true
def q2Open (r : Row2) : Bool := r.base == some false
def q2Fuel (r : Row2) : Bool := r.base == none
def q2S1Closed (r : Row2) : Bool := r.s1 == some true
def q2S1Open (r : Row2) : Bool := r.s1 == some false
def q2S1Fuel (r : Row2) : Bool := r.s1 == none
def q2OpenToClosed (r : Row2) : Bool := r.base == some false && r.s1 == some true
def q2ClosedToOpen (r : Row2) : Bool := r.base == some true && r.s1 == some false
def q2Blocked (r : Row2) : Bool := decide (r.blocks > 0)
def q2BlockedClosed (r : Row2) : Bool := decide (r.blocks > 0) && r.base == some true
def q2BlockedDisagree (r : Row2) : Bool := decide (r.blocks > 0) && !(r.base == r.s1)
def q2Blocks (r : Row2) : Nat := r.blocks
def q2F (r : Row2) : P := r.f

def reportSweep (label : String) (natoms sz fuel : Nat) : IO Unit := do
  let rows := sweep2 natoms sz fuel
  IO.println s!"{label}: total={rows.length} fuel={fuel}"
  IO.println s!"{label}: baseline (closed={(rows.filter q2Closed).length}, open={(rows.filter q2Open).length}, fuelExhausted={(rows.filter q2Fuel).length})"
  IO.println s!"{label}: S1       (closed={(rows.filter q2S1Closed).length}, open={(rows.filter q2S1Open).length}, fuelExhausted={(rows.filter q2S1Fuel).length})"
  IO.println s!"{label}: openToClosed(MUST BE 0)={(rows.filter q2OpenToClosed).length}  closedToOpen={(rows.filter q2ClosedToOpen).length}"
  IO.println s!"{label}: GUARD FIRED on {(rows.filter q2Blocked).length} formulas; max redirect edges on one path = {(rows.map q2Blocks).foldl max 0}"
  IO.println s!"{label}: of the guard-fired formulas, baseline CLOSED on {(rows.filter q2BlockedClosed).length}; baseline/S1 DISAGREE on {(rows.filter q2BlockedDisagree).length}"
  let dis := (rows.filter q2BlockedDisagree).map q2F
  IO.println s!"{label}: disagreements (first 20): {(dis.take 20).map ppP}"

/-! ### cex control: the guard must fire there, and the verdict must flip -/

#eval IO.println
  s!"cex: baseline={(runBaseBlocks cex 400).1} redirectEdges={(runBaseBlocks cex 400).2} S1={runS1 cex 400}"

/-! ### Sweep 1: 2 atoms, size<=6 (the established 8532-formula corpus), with guard-firing counts -/

#eval reportSweep "S6.2" 2 6 100

/-! ### Sweep 2: 1 atom, size<=8 (95730 formulas) -/

#eval reportSweep "S8.1" 1 8 100

/-! ### Sweep 3: 2 atoms, size<=7 (55299 formulas) -/

#eval reportSweep "S7.2" 2 7 100
