import Cslib.Logics.Modal.Tableau.LoopChecking

/-! Task E probe: executable **box-plus (both-members)** variant of the keyed S4 guard.

Distinct from `specs/553_.../artifacts/s4boxed.lean`, which measured the *boxed-only* variant
(`sbcBoxed` replaces `(pos, ψ)` by `(pos, □ψ)`). This file measures the variant Task E actually
specifies: the key records **BOTH** members of each pair, `{(pos, ψ), (pos, □ψ)}` for every
`T(□ψ)@w ∈ b` and `{(neg, ψ), (neg, ◇ψ)}` for every `F(◇ψ)@w ∈ b`.

Correspondingly the mint payload is the current `modalApplyOne` payload **plus** the boxed forms,
appended on the right (`mintPlus = modalApplyOne's list ++ boxPlusExtra`) -- the additive shape,
chosen so every existing `List.mem_append_left` membership proof into the original payload
survives with one extra wrapper.

Measured questions:
1. Does the box-plus driver keep the known counterexample `cex` OPEN (soundness)?
2. Do the T/4/K axioms still CLOSE?
3. Does any verdict change on the 2-atom size<=6 corpus (the gate proxy for
   `modalTableauS4Keyed_complete`)?
4. Does it remove the offending `2 → 1` redirect on the witness formula `phiW`?
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

/-! ### Box-plus birth content -/

/-- The box-plus partner of a signed pair: `(pos, ψ) ↦ (pos, □ψ)`, `(neg, ψ) ↦ (neg, ◇ψ)`. -/
def boxPlusPair (p : Sign × P) : Sign × P :=
  match p.1 with
  | .pos => (.pos, .box p.2)
  | .neg => (.neg, .diamond p.2)

/-- `true` when `q` is transmitted to a successor of `w` under the BOTH-members reading:
either `q = (pos, ψ)` with `T(□ψ)@w ∈ b` (the current, unwrapped member), or `q = (pos, □ψ)`
with `T(□ψ)@w ∈ b` (the added box-plus member); dually for `neg`/`◇`. -/
def bothShapeAt (b : List SF) (w : WorldIndex) (q : Sign × P) : Bool :=
  -- unwrapped member (exactly the current `successorBirthContent` filter)
  ((match q.1 with
    | .pos => b.any (· == (⟨.pos, .box q.2, w⟩ : SF))
    | .neg => b.any (· == (⟨.neg, .diamond q.2, w⟩ : SF))))
  -- box-plus member: q is itself boxed/diamonded and present at w
  || (match q.1, q.2 with
      | .pos, .box _ => b.any (· == (⟨q.1, q.2, w⟩ : SF))
      | .neg, .diamond _ => b.any (· == (⟨q.1, q.2, w⟩ : SF))
      | _, _ => false)

/-- Box-plus analogue of `successorBirthContent`. -/
def sbcPlus (φ₀ : P) (b : List SF) (s : Sign) (φ : P) (w : WorldIndex) : Finset (Sign × P) :=
  insert (s, φ) ((signedSubfmls φ₀).filter (fun q => bothShapeAt b w q = true))

/-- Box-plus analogue of `blockingWorldS4Keyed`: identical shape, `sbcPlus` substituted, so the
comparison remains plain key equality and `blockingWorldS4Keyed_none_fresh` transfers verbatim. -/
def bwPlus (φ₀ : P) (b : List SF) (keys : List (WorldIndex × Finset (Sign × P)))
    (s : Sign) (φ : P) (w : WorldIndex) : Option WorldIndex :=
  ((keys.filter (fun wk => decide (wk.2 = sbcPlus φ₀ b s φ w))).map Prod.fst).min?

/-- The extra (box-plus) half of the mint payload: the boxed/diamonded forms. -/
def boxPlusExtra (b : List SF) (w : WorldIndex) : List SF :=
  let w' := modalNextWorld b
  (boxPositivesOf b).filterMap (fun (ψ, src) =>
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
    else none)

/-- Additive box-plus mint payload: `modalApplyOne`'s own payload, `++ boxPlusExtra`. -/
def mintPlus (b : List SF) (acc : Accessibility) (sf : SF) : List SF :=
  match (modalApplyOne sf b acc).1 with
  | .linear nf => nf ++ boxPlusExtra b sf.label
  | _ => []

/-- Box-plus analogue of `modalApplyOneS4Keyed`. -/
def applyPlus (φ₀ : P) (keys : List (WorldIndex × Finset (Sign × P))) : RuleApply Nat :=
  fun sf b acc =>
    match sf.sign, sf.formula with
    | .neg, .box φ =>
      match bwPlus φ₀ b keys .neg φ sf.label with
      | some wBlock => (.linear [], acc.addEdge sf.label wBlock)
      | none => (.linear (mintPlus b acc sf), acc.addEdge sf.label (modalNextWorld b))
    | .pos, .diamond φ =>
      match bwPlus φ₀ b keys .pos φ sf.label with
      | some wBlock => (.linear [], acc.addEdge sf.label wBlock)
      | none => (.linear (mintPlus b acc sf), acc.addEdge sf.label (modalNextWorld b))
    | _, _ => modalApplyOneS4 φ₀ sf b acc

/-- Box-plus analogue of `modalStepBranchS4KeyedBody`. -/
def bodyPlus (φ₀ : P) (b e : List SF) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × P))) (sf : SF) :
    Option (List (List SF) × List (List SF) × Accessibility ×
            List (WorldIndex × Finset (Sign × P))) :=
  if e.any (· == sf) then none
  else
    let (result, newAcc) := applyPlus φ₀ keys sf b acc
    let keys' :=
      match sf.sign, sf.formula with
      | .neg, .box φ =>
        match bwPlus φ₀ b keys .neg φ sf.label with
        | some _ => keys
        | none => keys ++ [(modalNextWorld b, sbcPlus φ₀ b .neg φ sf.label)]
      | .pos, .diamond φ =>
        match bwPlus φ₀ b keys .pos φ sf.label with
        | some _ => keys
        | none => keys ++ [(modalNextWorld b, sbcPlus φ₀ b .pos φ sf.label)]
      | _, _ => keys
    match result with
    | .linear newForms => some ([newForms ++ b], [e ++ [sf]], newAcc, keys')
    | .branching branches =>
      some (branches.map (· ++ b), branches.map (fun _ => e ++ [sf]), newAcc, keys')
    | .persistent newForms => some ([newForms ++ b], [e], newAcc, keys')
    | .notApplicable => none

def nonMintCandPlus (φ₀ : P) (keys : List (WorldIndex × Finset (Sign × P)))
    (b e : List SF) (acc : Accessibility) : List SF :=
  b.filter (fun sf =>
    !modalMintShape sf && !(e.any (· == sf)) && (applyPlus φ₀ keys sf b acc).1.isApplicable)

def stepPlus (φ₀ : P) (b e : List SF) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × P))) :=
  b.findSome? (bodyPlus φ₀ b e acc keys)

def stepPlusOrdered (φ₀ : P) (b e : List SF) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × P))) :=
  match (nonMintCandPlus φ₀ keys b e acc).findSome? (bodyPlus φ₀ b e acc keys) with
  | some r => some r
  | none => stepPlus φ₀ b e acc keys

/-! ### Drivers -/

structure St where
  b : List SF
  e : List SF
  acc : Accessibility
  keys : List (WorldIndex × Finset (Sign × P))

def initSt (φ₀ : P) : St :=
  ⟨[⟨.neg, φ₀, 0⟩], [], Accessibility.empty, [((0 : WorldIndex), (∅ : Finset (Sign × P)))]⟩

/-- `some true` = closed, `some false` = open saturated branch, `none` = fuel exhausted. -/
partial def dfsPlus (ordered : Bool) (φ₀ : P) (fuel : Nat) (st : St) : Option Bool :=
  if isModalClosed st.b then some true
  else match fuel with
  | 0 => none
  | fuel'+1 =>
    match (if ordered then stepPlusOrdered φ₀ st.b st.e st.acc st.keys
           else stepPlus φ₀ st.b st.e st.acc st.keys) with
    | none => some false
    | some (bs, es, acc', keys') =>
      let rec go (bs : List (List SF)) (es : List (List SF)) : Option Bool :=
        match bs, es with
        | [], _ => some true
        | b :: rbs, e :: res =>
          match dfsPlus ordered φ₀ fuel' ⟨b, e, acc', keys'⟩ with
          | some true => go rbs res
          | x => x
        | _, _ => some true
      go bs es

def closesPlus (ordered : Bool) (φ₀ : P) (fuel : Nat) : Option Bool :=
  dfsPlus ordered φ₀ fuel (initSt φ₀)

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
/-- The machine-checked unsoundness counterexample: NOT `s4Valid`, must be OPEN. -/
def cex : P := .or (.box alphaA) (.box alphaL)
/-- The redirect witness-collision formula `¬(◇p ∧ ◇(□p ∧ ◇p))`. -/
def phiW : P := nt (.and (.diamond p0) (.diamond (.and (.box p0) (.diamond p0))))
def tAxiom : P := .imp (.box p0) p0
def fourAxiom : P := .imp (.box p0) (.box (.box p0))
def kAxiom : P := .imp (.box (.imp p0 p1)) (.imp (.box p0) (.box p1))

#eval do
  IO.println s!"cex  = {ppP cex}   (NOT s4Valid: must be OPEN)"
  IO.println s!"  keyed unordered      = {closesRef false cex 400}"
  IO.println s!"  keyed ordered        = {closesRef true cex 400}"
  IO.println s!"  BOXPLUS unordered    = {closesPlus false cex 400}"
  IO.println s!"  BOXPLUS ordered      = {closesPlus true cex 400}"
  IO.println ""
  for (nm, f) in [("T", tAxiom), ("4", fourAxiom), ("K", kAxiom)] do
    IO.println s!"{nm} axiom (VALID: must be CLOSED): unord={closesRef false f 400} ord={closesRef true f 400} plusUnord={closesPlus false f 400} plusOrd={closesPlus true f 400}"
  IO.println ""
  IO.println s!"phiW = {ppP phiW}   (NOT s4Valid: must be OPEN)"
  IO.println s!"  keyed ordered = {closesRef true phiW 400}   BOXPLUS ordered = {closesPlus true phiW 400}"

/-! ### Corpus sweep -/

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
  (allUpTo natoms sz).map (fun f => (f, closesRef true f fuel, closesPlus true f fuel))

def rowsUnord (natoms sz fuel : Nat) : List (P × Option Bool × Option Bool) :=
  (allUpTo natoms sz).map (fun f => (f, closesRef false f fuel, closesPlus false f fuel))

def report (label : String) (rs : List (P × Option Bool × Option Bool)) : IO Unit := do
  let aClosed := (rs.filter (fun r => r.2.1 == some true)).length
  let bClosed := (rs.filter (fun r => r.2.2 == some true)).length
  let aFuel := (rs.filter (fun r => r.2.1 == none)).length
  let bFuel := (rs.filter (fun r => r.2.2 == none)).length
  let openToClosed := rs.filter (fun r => r.2.1 == some false && r.2.2 == some true)
  let closedToOpen := rs.filter (fun r => r.2.1 == some true && r.2.2 == some false)
  IO.println s!"-- {label} (total={rs.length})"
  IO.println s!"   reference: closed={aClosed} fuelExhausted={aFuel}"
  IO.println s!"   BOXPLUS  : closed={bClosed} fuelExhausted={bFuel}"
  IO.println s!"   ref-OPEN -> PLUS-CLOSED (soundness regression if >0) = {openToClosed.length}"
  IO.println s!"   ref-CLOSED -> PLUS-OPEN (completeness change)        = {closedToOpen.length}"
  for r in openToClosed.take 10 do IO.println s!"     OPEN->CLOSED {ppP r.1}"
  for r in closedToOpen.take 10 do IO.println s!"     CLOSED->OPEN {ppP r.1}"

#eval do
  report "ORDERED: keyed vs boxplus, 2 atoms, size<=6, fuel 100" (rows 2 6 100)
  report "UNORDERED: keyed vs boxplus, 2 atoms, size<=6, fuel 100" (rowsUnord 2 6 100)

/-! ### Redirect trace -/

def ppSF (sf : SF) : String :=
  (match sf.sign with | .pos => "T" | .neg => "F") ++ s!"({ppP sf.formula})@{sf.label}"

def ppAcc (acc : Accessibility) : String :=
  String.intercalate " " (acc.edges.map (fun e => s!"{e.1}→{e.2}"))

partial def tracePlus (plus : Bool) (φ₀ : P) (fuel : Nat) (st : St) (n : Nat) : IO Unit := do
  IO.println s!"[{n}] worlds={(modalKnownWorlds st.b).length} acc=[{ppAcc st.acc}] nkeys={st.keys.length}"
  if isModalClosed st.b then IO.println "     CLOSED" else
  match fuel with
  | 0 => IO.println "     FUEL EXHAUSTED"
  | fuel'+1 =>
    match (if plus then stepPlusOrdered φ₀ st.b st.e st.acc st.keys
           else modalStepBranchS4KeyedOrdered φ₀ st.b st.e st.acc st.keys) with
    | none => IO.println "     SATURATED OPEN"
    | some (bs, es, acc', keys') =>
      match bs, es with
      | [b'], [e'] => tracePlus plus φ₀ fuel' ⟨b', e', acc', keys'⟩ (n+1)
      | _, _ => IO.println s!"     BRANCHED ({bs.length})"

#eval do
  IO.println "REFERENCE ordered driver on phiW (expect redirect edge 2→1):"
  tracePlus false phiW 40 (initSt phiW) 0
  IO.println ""
  IO.println "BOXPLUS ordered driver on phiW:"
  tracePlus true phiW 40 (initSt phiW) 0
