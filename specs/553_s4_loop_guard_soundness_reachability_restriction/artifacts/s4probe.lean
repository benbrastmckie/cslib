import Cslib.Logics.Modal.Tableau.LoopChecking

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

def ppSF (sf : SignedFormula P WorldIndex) : String :=
  (match sf.sign with | .pos => "T" | .neg => "F") ++ s!"({ppP sf.formula})@{sf.label}"

def ppB (b : List (SignedFormula P WorldIndex)) : String :=
  String.intercalate ", " (b.map ppSF)

structure St where
  b : List (SignedFormula P WorldIndex)
  e : List (SignedFormula P WorldIndex)
  acc : Accessibility
  keys : List (WorldIndex × Finset (Sign × P))

def initSt (φ₀ : P) : St :=
  ⟨[⟨.neg, φ₀, 0⟩], [], Accessibility.empty, [((0 : WorldIndex), (∅ : Finset (Sign × P)))]⟩

/-- `some true` = subtree all closed; `some false` = open saturated branch found;
    `none` = step budget exhausted (unknown). Driven by the UNORDERED (shipped) keyed
    stepper `modalStepBranchS4Keyed`. -/
partial def dfsKeyed (φ₀ : P) (fuel : Nat) (st : St) : Option Bool :=
  if isModalClosed st.b then some true
  else match fuel with
  | 0 => none
  | fuel'+1 =>
    match modalStepBranchS4Keyed φ₀ st.b st.e st.acc st.keys with
    | none => some false
    | some (bs, es, acc', keys') =>
      let rec go (bs : List (List (SignedFormula P WorldIndex)))
                 (es : List (List (SignedFormula P WorldIndex))) : Option Bool :=
        match bs, es with
        | [], _ => some true
        | b :: rbs, e :: res =>
          match dfsKeyed φ₀ fuel' ⟨b, e, acc', keys'⟩ with
          | some true => go rbs res
          | x => x
        | _, _ => some true
      go bs es

def tabClosesKeyed (φ₀ : P) (fuel : Nat) : Option Bool :=
  dfsKeyed φ₀ fuel (initSt φ₀)

/-- The ORDERED-stepper analogue of `dfsKeyed`, driven by `modalStepBranchS4KeyedOrdered`
(settled-context scheduling: non-minting candidates first, minting fallback only once the
branch has settled). Same worklist shape as `dfsKeyed`, only the stepper differs. -/
partial def dfsOrdered (φ₀ : P) (fuel : Nat) (st : St) : Option Bool :=
  if isModalClosed st.b then some true
  else match fuel with
  | 0 => none
  | fuel'+1 =>
    match modalStepBranchS4KeyedOrdered φ₀ st.b st.e st.acc st.keys with
    | none => some false
    | some (bs, es, acc', keys') =>
      let rec go (bs : List (List (SignedFormula P WorldIndex)))
                 (es : List (List (SignedFormula P WorldIndex))) : Option Bool :=
        match bs, es with
        | [], _ => some true
        | b :: rbs, e :: res =>
          match dfsOrdered φ₀ fuel' ⟨b, e, acc', keys'⟩ with
          | some true => go rbs res
          | x => x
        | _, _ => some true
      go bs es

def tabClosesOrdered (φ₀ : P) (fuel : Nat) : Option Bool :=
  dfsOrdered φ₀ fuel (initSt φ₀)

/-- LIVE-set (non-keyed) driver, kept for the original three-way comparison. -/
partial def dfsLive (φ₀ : P) (fuel : Nat)
    (b e : List (SignedFormula P WorldIndex)) (acc : Accessibility) : Option Bool :=
  if isModalClosed b then some true
  else match fuel with
  | 0 => none
  | fuel'+1 =>
    match modalStepBranchS4 φ₀ b e acc with
    | none => some false
    | some (bs, es, acc') =>
      let rec go (bs : List (List (SignedFormula P WorldIndex)))
                 (es : List (List (SignedFormula P WorldIndex))) : Option Bool :=
        match bs, es with
        | [], _ => some true
        | b2 :: rbs, e2 :: res =>
          match dfsLive φ₀ fuel' b2 e2 acc' with
          | some true => go rbs res
          | x => x
        | _, _ => some true
      go bs es

def tabClosesLive (φ₀ : P) (fuel : Nat) : Option Bool :=
  dfsLive φ₀ fuel [⟨.neg, φ₀, 0⟩] [] Accessibility.empty

/-! ### Formula enumeration -/

def atomsList (natoms : Nat) : List P := (List.range natoms).map (fun i => .atom i)

partial def gen (natoms : Nat) : Nat → List P
  | 0 => []
  | 1 => .bot :: atomsList natoms
  | n+1 =>
    let unary := (gen natoms n).flatMap (fun x => [Proposition.box x, Proposition.diamond x])
    let binary := (List.range n).filterMap (fun i => if i == 0 then none else some i) |>.flatMap (fun i =>
      let l := gen natoms i
      let r := gen natoms (n - i)
      l.flatMap (fun x => r.flatMap (fun y => [Proposition.imp x y, .and x y, .or x y])))
    unary ++ binary

def allUpTo (natoms sz : Nat) : List P :=
  (List.range sz).flatMap (fun i => gen natoms (i+1))

/-! ### The counterexample and controls -/

def p0 : P := .atom 0
def p1 : P := .atom 1
def nt (x : P) : P := .imp x .bot
def alphaA : P := .or (.box p0) (nt (nt (.diamond p1)))
def alphaL : P := .or (.box p0) (nt (.box p1))
def cex : P := .or (.box alphaA) (.box alphaL)
def bAxiom : P := .imp p0 (.box (.diamond p0))
def tAxiom : P := .imp (.box p0) p0

#eval IO.println s!"cex = {ppP cex}"
#eval IO.println s!"KEYED (unordered) closes cex, fuel 400 = {tabClosesKeyed cex 400}"
#eval IO.println s!"KEYED (ordered)   closes cex, fuel 400 = {tabClosesOrdered cex 400}"
#eval IO.println s!"LIVE              closes cex, fuel 400 = {tabClosesLive cex 400}"
#eval IO.println s!"B axiom: unordered={tabClosesKeyed bAxiom 400} ordered={tabClosesOrdered bAxiom 400}"
#eval IO.println s!"T axiom: unordered={tabClosesKeyed tAxiom 400} ordered={tabClosesOrdered tAxiom 400}"

/-! ### Phase 8 empirical gate: exhaustive size<=6, 2-atom sweep, unordered vs. ordered

Reproduces the Phase 1 baseline methodology (report section 3.3 / plan Phase 8): keyed driver,
`allUpTo 2 6`, fuel 100. The pre-change baseline (unordered driver alone) is 8532 formulas: 1650
closed, 6882 open, 0 fuel-exhausted. This sweep computes BOTH drivers' verdicts on every formula
in one pass and censuses every verdict change. Every change must be closed-to-open; a single
open-to-closed change is a completeness regression. -/

def sweepRows (natoms sz fuel : Nat) : List (P × Option Bool × Option Bool) :=
  (allUpTo natoms sz).map (fun f => (f, tabClosesKeyed f fuel, tabClosesOrdered f fuel))

def isOldClosed (r : P × Option Bool × Option Bool) : Bool := r.2.1 == some true
def isOldOpen (r : P × Option Bool × Option Bool) : Bool := r.2.1 == some false
def isOldFuel (r : P × Option Bool × Option Bool) : Bool := r.2.1 == none
def isNewClosed (r : P × Option Bool × Option Bool) : Bool := r.2.2 == some true
def isNewOpen (r : P × Option Bool × Option Bool) : Bool := r.2.2 == some false
def isNewFuel (r : P × Option Bool × Option Bool) : Bool := r.2.2 == none
def isClosedToOpen (r : P × Option Bool × Option Bool) : Bool := r.2.1 == some true && r.2.2 == some false
def isOpenToClosed (r : P × Option Bool × Option Bool) : Bool := r.2.1 == some false && r.2.2 == some true
def isFuelInvolved (r : P × Option Bool × Option Bool) : Bool := r.2.1 == none || r.2.2 == none

#eval do
  let rows : List (P × Option Bool × Option Bool) := sweepRows 2 6 100
  let total := rows.length
  let oldClosed := (rows.filter isOldClosed).length
  let oldOpen := (rows.filter isOldOpen).length
  let oldFuel := (rows.filter isOldFuel).length
  let newClosed := (rows.filter isNewClosed).length
  let newOpen := (rows.filter isNewOpen).length
  let newFuel := (rows.filter isNewFuel).length
  let closedToOpen := rows.filter isClosedToOpen
  let openToClosed := rows.filter isOpenToClosed
  let fuelInvolved := rows.filter isFuelInvolved
  IO.println s!"total={total}"
  IO.println s!"unordered(closed={oldClosed}, open={oldOpen}, fuelExhausted={oldFuel})"
  IO.println s!"ordered  (closed={newClosed}, open={newOpen}, fuelExhausted={newFuel})"
  IO.println s!"closedToOpen (sound fix, expected>0)={closedToOpen.length}"
  IO.println s!"openToClosed (COMPLETENESS REGRESSION if >0)={openToClosed.length}"
  IO.println s!"fuelInvolved (TERMINATION REGRESSION if newFuel>oldFuel)={fuelInvolved.length}"
  if openToClosed.length > 0 then
    IO.println "-- open-to-closed regressions --"
    for r in openToClosed do
      IO.println s!"  {ppP r.1}"
  if closedToOpen.length > 0 && closedToOpen.length <= 20 then
    IO.println "-- closed-to-open fixes --"
    for r in closedToOpen do
      IO.println s!"  {ppP r.1}"
