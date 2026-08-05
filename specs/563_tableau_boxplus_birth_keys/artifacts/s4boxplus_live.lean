import Cslib.Logics.Modal.Tableau.LoopChecking

/-! Task E probe 2: does enriching `successorBirthContent` **in place** perturb the LIVE-set
driver (`modalApplyOneS4` / `modalExpandBranchesS4`)?

`blockingWorldS4` (the live guard) is defined against `successorBirthContent`, so an in-place
enrichment changes `modalApplyOneS4`, `modalTableauS4`, and the `modalExpandBranchesS4` row of
`CslibTests/S4LoopGuardRegression.lean` (asserted "OPEN" on `cex`). The keyed track is measured
separately in `s4boxplus.lean`.

Unlike the keyed track, the live driver's mint payload is `modalApplyOneS4Rules` (K+T+4) and is
NOT changed here: `keyLowerBd` does not apply to the live guard, so there is no reason to
front-load the boxed forms. The measurement is therefore "enriched key vs unchanged live mint".
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

def bothShapeAt (b : List SF) (w : WorldIndex) (q : Sign × P) : Bool :=
  ((match q.1 with
    | .pos => b.any (· == (⟨.pos, .box q.2, w⟩ : SF))
    | .neg => b.any (· == (⟨.neg, .diamond q.2, w⟩ : SF))))
  || (match q.1, q.2 with
      | .pos, .box _ => b.any (· == (⟨q.1, q.2, w⟩ : SF))
      | .neg, .diamond _ => b.any (· == (⟨q.1, q.2, w⟩ : SF))
      | _, _ => false)

def sbcPlus (φ₀ : P) (b : List SF) (s : Sign) (φ : P) (w : WorldIndex) : Finset (Sign × P) :=
  insert (s, φ) ((signedSubfmls φ₀).filter (fun q => bothShapeAt b w q = true))

/-- Enriched LIVE guard: `blockingWorldS4` with `sbcPlus` substituted. -/
def bwLivePlus (φ₀ : P) (b : List SF) (s : Sign) (φ : P) (w : WorldIndex) : Option WorldIndex :=
  ((modalKnownWorlds b).filter
    (fun w' => decide (relevantSetFinset φ₀ b w' = sbcPlus φ₀ b s φ w))).min?

/-- Enriched `modalApplyOneS4`: same shape, enriched live guard, UNCHANGED mint payload. -/
def applyLivePlus (φ₀ : P) : RuleApply Nat :=
  fun sf b acc =>
    match sf.sign, sf.formula with
    | .neg, .box φ =>
      match bwLivePlus φ₀ b .neg φ sf.label with
      | some wBlock => (.linear [], acc.addEdge sf.label wBlock)
      | none => modalApplyOneS4Rules sf b acc
    | .pos, .diamond φ =>
      match bwLivePlus φ₀ b .pos φ sf.label with
      | some wBlock => (.linear [], acc.addEdge sf.label wBlock)
      | none => modalApplyOneS4Rules sf b acc
    | _, _ => modalApplyOneS4Rules sf b acc

structure St where
  b : List SF
  e : List SF
  acc : Accessibility

def initSt (φ₀ : P) : St := ⟨[⟨.neg, φ₀, 0⟩], [], Accessibility.empty⟩

partial def dfsLive (apply : RuleApply Nat) (φ₀ : P) (fuel : Nat) (st : St) : Option Bool :=
  if isModalClosed st.b then some true
  else match fuel with
  | 0 => none
  | fuel'+1 =>
    match modalStepBranchGen apply st.b st.e st.acc with
    | none => some false
    | some (bs, es, acc') =>
      let rec go (bs : List (List SF)) (es : List (List SF)) : Option Bool :=
        match bs, es with
        | [], _ => some true
        | b :: rbs, e :: res =>
          match dfsLive apply φ₀ fuel' ⟨b, e, acc'⟩ with
          | some true => go rbs res
          | x => x
        | _, _ => some true
      go bs es

def closesLiveRef (φ₀ : P) (fuel : Nat) : Option Bool :=
  dfsLive (modalApplyOneS4 φ₀) φ₀ fuel (initSt φ₀)

def closesLivePlus (φ₀ : P) (fuel : Nat) : Option Bool :=
  dfsLive (applyLivePlus φ₀) φ₀ fuel (initSt φ₀)

def p0 : P := .atom 0
def p1 : P := .atom 1
def nt (x : P) : P := .imp x .bot
def alphaA : P := .or (.box p0) (nt (nt (.diamond p1)))
def alphaL : P := .or (.box p0) (nt (.box p1))
def cex : P := .or (.box alphaA) (.box alphaL)
def tAxiom : P := .imp (.box p0) p0
def fourAxiom : P := .imp (.box p0) (.box (.box p0))
def kAxiom : P := .imp (.box (.imp p0 p1)) (.imp (.box p0) (.box p1))
def bAxiom : P := .imp p0 (.box (.diamond p0))

#eval do
  IO.println s!"cex (regression row asserts OPEN for the live driver):"
  IO.println s!"  live reference = {closesLiveRef cex 400}"
  IO.println s!"  live BOXPLUS   = {closesLivePlus cex 400}"
  for (nm, f) in [("T", tAxiom), ("4", fourAxiom), ("K", kAxiom), ("B", bAxiom)] do
    IO.println s!"{nm}: liveRef={closesLiveRef f 400} livePlus={closesLivePlus f 400}"

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

def liveRows (natoms sz fuel : Nat) : List (P × Option Bool × Option Bool) :=
  (allUpTo natoms sz).map (fun f => (f, closesLiveRef f fuel, closesLivePlus f fuel))

def liveReport (rs : List (P × Option Bool × Option Bool)) : IO Unit := do
  let aClosed := (rs.filter (fun r => r.2.1 == some true)).length
  let bClosed := (rs.filter (fun r => r.2.2 == some true)).length
  let aFuel := (rs.filter (fun r => r.2.1 == none)).length
  let bFuel := (rs.filter (fun r => r.2.2 == none)).length
  let openToClosed := rs.filter (fun r => r.2.1 == some false && r.2.2 == some true)
  let closedToOpen := rs.filter (fun r => r.2.1 == some true && r.2.2 == some false)
  IO.println s!"-- LIVE driver, 2 atoms, size<=6, fuel 100 (total={rs.length})"
  IO.println s!"   reference: closed={aClosed} fuelExhausted={aFuel}"
  IO.println s!"   BOXPLUS  : closed={bClosed} fuelExhausted={bFuel}"
  IO.println s!"   ref-OPEN -> PLUS-CLOSED = {openToClosed.length}"
  IO.println s!"   ref-CLOSED -> PLUS-OPEN = {closedToOpen.length}"
  for r in openToClosed.take 10 do IO.println s!"     OPEN->CLOSED {ppP r.1}"
  for r in closedToOpen.take 10 do IO.println s!"     CLOSED->OPEN {ppP r.1}"

#eval liveReport (liveRows 2 6 100)
