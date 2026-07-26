import Cslib.Logics.Modal.Tableau.LoopChecking

/-! Phase 13 divergence audit: executable **boxed-key** variant of the keyed S4 guard.

The audited defect is that `successorBirthContent` records the box-context *unwrapped*
(`(pos, ψ)` for `T(□ψ)@w`), which is exactly the information loss that makes redirect-inertness
unprovable. This file implements the alternative in executable form only (no proofs):

* `sbcBoxed` -- birth content records the **boxed** pair `(pos, □ψ)` / `(neg, ◇ψ)`.
* `mintBoxed` -- the mint payload transmits the **boxed** forms `T(□ψ)@w'` / `F(◇ψ)@w'`
  (sound in S4 by transitivity; the driver already derives exactly these one step later via
  `modalFourBoxProp`/`modalFourDiaNegProp`). Keeping payload and key in step is what preserves
  `keyLowerBd`.

Under this pairing, redirect-inertness is definitional: guard match gives
`key(wBlock) = sbcBoxed ... v`, which contains `(pos, □ψ)` for every `T(□ψ)@v ∈ b`, and
`keyLowerBd` turns that into `T(□ψ)@wBlock ∈ b` directly -- no origin-edge invariant, no
mint-readiness, no witness-collision case.

Purpose here: measure the two things a proof cannot tell us -- does the boxed variant keep the
known counterexample `cex` OPEN (soundness), and does it change any verdict on the size<=6
2-atom corpus (completeness/termination)?
-/

open Cslib.Logic.Modal Cslib.Logic.Tableau Cslib.Logic.Modal.Tableau

abbrev P := Proposition Nat
abbrev SF := SignedFormula P WorldIndex

partial def ppP : P → String
  | .atom n => s!"p{n}"
  | .bot => "⊥"
  | .imp x y => s!"({ppP x}→{ppP y})"
  | .and x y => s!"({ppP x}∧{ppP y})"
  | .or x y => s!"({ppP x}∨{ppP y})"
  | .box x => s!"□{ppP x}"
  | .diamond x => s!"◇{ppP x}"

/-! ### Boxed birth content and boxed guard -/

/-- `true` when `q` is a boxed-shape pair whose instantiation at `w` is present on `b`:
`(pos, □ψ)` with `T(□ψ)@w ∈ b`, or `(neg, ◇ψ)` with `F(◇ψ)@w ∈ b`. -/
def boxedShapeAt (b : List SF) (w : WorldIndex) (q : Sign × P) : Bool :=
  (match q.1, q.2 with
   | .pos, .box _ => true
   | .neg, .diamond _ => true
   | _, _ => false)
  && b.any (· == (⟨q.1, q.2, w⟩ : SF))

/-- Boxed analogue of `successorBirthContent`: the witness pair together with the box-context
recorded in its **boxed** form. -/
def sbcBoxed (φ₀ : P) (b : List SF) (s : Sign) (φ : P) (w : WorldIndex) :
    Finset (Sign × P) :=
  insert (s, φ) ((signedSubfmls φ₀).filter (fun q => boxedShapeAt b w q = true))

/-- Boxed analogue of `blockingWorldS4Keyed`: identical shape, `sbcBoxed` substituted. The
comparison remains plain key equality, so `blockingWorldS4Keyed_none_fresh` -- and hence
`keysDistinct` and the pigeonhole world bound -- transfers verbatim. -/
def bwBoxed (φ₀ : P) (b : List SF) (keys : List (WorldIndex × Finset (Sign × P)))
    (s : Sign) (φ : P) (w : WorldIndex) : Option WorldIndex :=
  ((keys.filter (fun wk => decide (wk.2 = sbcBoxed φ₀ b s φ w))).map Prod.fst).min?

/-- Boxed mint payload: witness (unwrapped, as before) plus the box-context in boxed form. -/
def mintBoxed (b : List SF) (s : Sign) (φ : P) (w : WorldIndex) : List SF :=
  let w' := modalNextWorld b
  (⟨s, φ, w'⟩ : SF) ::
    ((boxPositivesOf b).filterMap (fun (ψ, src) =>
      if src == w then
        let sf' : SF := ⟨.pos, .box ψ, w'⟩
        if b.any (· == sf') then none else some sf'
      else none) ++
     b.filterMap (fun sf' =>
      if sf'.sign == .neg && sf'.label == w then
        match sf'.formula with
        | .diamond ψ =>
          let pr : SF := ⟨.neg, .diamond ψ, w'⟩
          if b.any (· == pr) then none else some pr
        | _ => none
      else none))

/-- Boxed analogue of `modalApplyOneS4Keyed`. -/
def applyBoxed (φ₀ : P) (keys : List (WorldIndex × Finset (Sign × P))) : RuleApply Nat :=
  fun sf b acc =>
    match sf.sign, sf.formula with
    | .neg, .box φ =>
      match bwBoxed φ₀ b keys .neg φ sf.label with
      | some wBlock => (.linear [], acc.addEdge sf.label wBlock)
      | none => (.linear (mintBoxed b .neg φ sf.label), acc.addEdge sf.label (modalNextWorld b))
    | .pos, .diamond φ =>
      match bwBoxed φ₀ b keys .pos φ sf.label with
      | some wBlock => (.linear [], acc.addEdge sf.label wBlock)
      | none => (.linear (mintBoxed b .pos φ sf.label), acc.addEdge sf.label (modalNextWorld b))
    | _, _ => modalApplyOneS4 φ₀ sf b acc

/-- Boxed analogue of `modalStepBranchS4KeyedBody`. -/
def bodyBoxed (φ₀ : P) (b e : List SF) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × P))) (sf : SF) :
    Option (List (List SF) × List (List SF) × Accessibility ×
            List (WorldIndex × Finset (Sign × P))) :=
  if e.any (· == sf) then none
  else
    let (result, newAcc) := applyBoxed φ₀ keys sf b acc
    let keys' :=
      match sf.sign, sf.formula with
      | .neg, .box φ =>
        match bwBoxed φ₀ b keys .neg φ sf.label with
        | some _ => keys
        | none => keys ++ [(modalNextWorld b, sbcBoxed φ₀ b .neg φ sf.label)]
      | .pos, .diamond φ =>
        match bwBoxed φ₀ b keys .pos φ sf.label with
        | some _ => keys
        | none => keys ++ [(modalNextWorld b, sbcBoxed φ₀ b .pos φ sf.label)]
      | _, _ => keys
    match result with
    | .linear newForms => some ([newForms ++ b], [e ++ [sf]], newAcc, keys')
    | .branching branches =>
      some (branches.map (· ++ b), branches.map (fun _ => e ++ [sf]), newAcc, keys')
    | .persistent newForms => some ([newForms ++ b], [e], newAcc, keys')
    | .notApplicable => none

def nonMintCandBoxed (φ₀ : P) (keys : List (WorldIndex × Finset (Sign × P)))
    (b e : List SF) (acc : Accessibility) : List SF :=
  b.filter (fun sf =>
    !modalMintShape sf && !(e.any (· == sf)) && (applyBoxed φ₀ keys sf b acc).1.isApplicable)

/-- Boxed UNORDERED stepper (plain `b.findSome?`, no settled-context scheduling). -/
def stepBoxed (φ₀ : P) (b e : List SF) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × P))) :=
  b.findSome? (bodyBoxed φ₀ b e acc keys)

/-- Boxed ORDERED stepper (Route P scheduling on top of the boxed guard). -/
def stepBoxedOrdered (φ₀ : P) (b e : List SF) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × P))) :=
  match (nonMintCandBoxed φ₀ keys b e acc).findSome? (bodyBoxed φ₀ b e acc keys) with
  | some r => some r
  | none => stepBoxed φ₀ b e acc keys

/-! ### Drivers -/

structure St where
  b : List SF
  e : List SF
  acc : Accessibility
  keys : List (WorldIndex × Finset (Sign × P))

def initSt (φ₀ : P) : St :=
  ⟨[⟨.neg, φ₀, 0⟩], [], Accessibility.empty, [((0 : WorldIndex), (∅ : Finset (Sign × P)))]⟩

/-- `some true` = closed, `some false` = open saturated branch, `none` = fuel exhausted. -/
partial def dfsBoxed (ordered : Bool) (φ₀ : P) (fuel : Nat) (st : St) : Option Bool :=
  if isModalClosed st.b then some true
  else match fuel with
  | 0 => none
  | fuel'+1 =>
    match (if ordered then stepBoxedOrdered φ₀ st.b st.e st.acc st.keys
           else stepBoxed φ₀ st.b st.e st.acc st.keys) with
    | none => some false
    | some (bs, es, acc', keys') =>
      let rec go (bs : List (List SF)) (es : List (List SF)) : Option Bool :=
        match bs, es with
        | [], _ => some true
        | b :: rbs, e :: res =>
          match dfsBoxed ordered φ₀ fuel' ⟨b, e, acc', keys'⟩ with
          | some true => go rbs res
          | x => x
        | _, _ => some true
      go bs es

def closesBoxed (ordered : Bool) (φ₀ : P) (fuel : Nat) : Option Bool :=
  dfsBoxed ordered φ₀ fuel (initSt φ₀)

/-- Reference drivers from the shipped file, for the comparison columns. -/
partial def dfsRef (ordered : Bool) (φ₀ : P) (fuel : Nat) (st : St) : Option Bool :=
  if isModalClosed st.b then some true
  else match fuel with
  | 0 => none
  | fuel'+1 =>
    match (if ordered then modalStepBranchS4KeyedOrdered φ₀ st.b st.e st.acc st.keys
           else modalStepBranchS4Keyed φ₀ st.b st.e st.acc st.keys) with
    | none => some false
    | some (bs, es, acc', keys') =>
      let rec go (bs : List (List SF)) (es : List (List SF)) : Option Bool :=
        match bs, es with
        | [], _ => some true
        | b :: rbs, e :: res =>
          match dfsRef ordered φ₀ fuel' ⟨b, e, acc', keys'⟩ with
          | some true => go rbs res
          | x => x
        | _, _ => some true
      go bs es

def closesRef (ordered : Bool) (φ₀ : P) (fuel : Nat) : Option Bool :=
  dfsRef ordered φ₀ fuel (initSt φ₀)

/-! ### The known counterexample and the audit's own witness formula -/

def p0 : P := .atom 0
def p1 : P := .atom 1
def nt (x : P) : P := .imp x .bot
def alphaA : P := .or (.box p0) (nt (nt (.diamond p1)))
def alphaL : P := .or (.box p0) (nt (.box p1))
/-- The machine-checked unsoundness counterexample (`CslibTests/S4LoopGuardRegression.lean`):
NOT `s4Valid`, so every sound driver must report it OPEN. -/
def cex : P := .or (.box alphaA) (.box alphaL)
/-- This audit's witness-collision formula: `¬(◇p ∧ ◇(□p ∧ ◇p))`. -/
def phiW : P := nt (.and (.diamond p0) (.diamond (.and (.box p0) (.diamond p0))))
def tAxiom : P := .imp (.box p0) p0
def fourAxiom : P := .imp (.box p0) (.box (.box p0))
def kAxiom : P := .imp (.box (.imp p0 p1)) (.imp (.box p0) (.box p1))

#eval do
  IO.println s!"cex  = {ppP cex}   (NOT s4Valid: must be OPEN)"
  IO.println s!"  keyed unordered      = {closesRef false cex 400}"
  IO.println s!"  keyed ordered        = {closesRef true cex 400}"
  IO.println s!"  BOXED unordered      = {closesBoxed false cex 400}"
  IO.println s!"  BOXED ordered        = {closesBoxed true cex 400}"
  IO.println ""
  for (nm, f) in [("T", tAxiom), ("4", fourAxiom), ("K", kAxiom)] do
    IO.println s!"{nm} axiom (VALID: must be CLOSED): unord={closesRef false f 400} ord={closesRef true f 400} boxedUnord={closesBoxed false f 400} boxedOrd={closesBoxed true f 400}"
  IO.println ""
  IO.println s!"phiW = {ppP phiW}   (NOT s4Valid: must be OPEN)"
  IO.println s!"  keyed ordered = {closesRef true phiW 400}   BOXED ordered = {closesBoxed true phiW 400}"

/-! ### Corpus sweep: does the boxed variant change any verdict? -/

def atomsList (natoms : Nat) : List P := (List.range natoms).map (fun i => .atom i)

partial def gen (natoms : Nat) : Nat → List P
  | 0 => []
  | 1 => .bot :: atomsList natoms
  | n+1 =>
    let unary := (gen natoms n).flatMap (fun x => [Proposition.box x, Proposition.diamond x])
    let binary := (List.range n).filterMap (fun i => if i == 0 then none else some i)
      |>.flatMap (fun i =>
        let l := gen natoms i
        let r := gen natoms (n - i)
        l.flatMap (fun x => r.flatMap (fun y => [Proposition.imp x y, .and x y, .or x y])))
    unary ++ binary

def allUpTo (natoms sz : Nat) : List P :=
  (List.range sz).flatMap (fun i => gen natoms (i+1))

def rows (natoms sz fuel : Nat) : List (P × Option Bool × Option Bool) :=
  (allUpTo natoms sz).map (fun f => (f, closesRef true f fuel, closesBoxed true f fuel))

def rowsUnord (natoms sz fuel : Nat) : List (P × Option Bool × Option Bool) :=
  (allUpTo natoms sz).map (fun f => (f, closesRef false f fuel, closesBoxed false f fuel))

def report (label : String) (rs : List (P × Option Bool × Option Bool)) : IO Unit := do
  let aClosed := (rs.filter (fun r => r.2.1 == some true)).length
  let bClosed := (rs.filter (fun r => r.2.2 == some true)).length
  let aFuel := (rs.filter (fun r => r.2.1 == none)).length
  let bFuel := (rs.filter (fun r => r.2.2 == none)).length
  let openToClosed := rs.filter (fun r => r.2.1 == some false && r.2.2 == some true)
  let closedToOpen := rs.filter (fun r => r.2.1 == some true && r.2.2 == some false)
  IO.println s!"-- {label} (total={rs.length})"
  IO.println s!"   reference: closed={aClosed} fuelExhausted={aFuel}"
  IO.println s!"   BOXED    : closed={bClosed} fuelExhausted={bFuel}"
  IO.println s!"   ref-OPEN -> BOXED-CLOSED (soundness regression if >0) = {openToClosed.length}"
  IO.println s!"   ref-CLOSED -> BOXED-OPEN (completeness change)        = {closedToOpen.length}"
  for r in openToClosed.take 10 do IO.println s!"     OPEN->CLOSED {ppP r.1}"
  for r in closedToOpen.take 10 do IO.println s!"     CLOSED->OPEN {ppP r.1}"

#eval do
  report "ORDERED: keyed vs boxed, 2 atoms, size<=6, fuel 100" (rows 2 6 100)
  report "UNORDERED: keyed vs boxed, 2 atoms, size<=6, fuel 100" (rowsUnord 2 6 100)

/-! ### Does the boxed variant avoid the witness-collision redirect? -/

def ppSF (sf : SF) : String :=
  (match sf.sign with | .pos => "T" | .neg => "F") ++ s!"({ppP sf.formula})@{sf.label}"

def ppAcc (acc : Accessibility) : String :=
  String.intercalate " " (acc.edges.map (fun e => s!"{e.1}→{e.2}"))

partial def traceBoxed (boxed : Bool) (φ₀ : P) (fuel : Nat) (st : St) (n : Nat) : IO Unit := do
  IO.println s!"[{n}] worlds={(modalKnownWorlds st.b).length} acc=[{ppAcc st.acc}] nkeys={st.keys.length}"
  if isModalClosed st.b then IO.println "     CLOSED" else
  match fuel with
  | 0 => IO.println "     FUEL EXHAUSTED"
  | fuel'+1 =>
    match (if boxed then stepBoxedOrdered φ₀ st.b st.e st.acc st.keys
           else modalStepBranchS4KeyedOrdered φ₀ st.b st.e st.acc st.keys) with
    | none => IO.println "     SATURATED OPEN"
    | some (bs, es, acc', keys') =>
      match bs, es with
      | [b'], [e'] => traceBoxed boxed φ₀ fuel' ⟨b', e', acc', keys'⟩ (n+1)
      | _, _ => IO.println s!"     BRANCHED ({bs.length})"

#eval do
  IO.println "REFERENCE ordered driver on phiW (expect redirect edge 2→1 to appear):"
  traceBoxed false phiW 40 (initSt phiW) 0
  IO.println ""
  IO.println "BOXED ordered driver on phiW (expect NO 2→1 edge):"
  traceBoxed true phiW 40 (initSt phiW) 0
