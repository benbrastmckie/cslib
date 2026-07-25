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

/-- `some true` = subtree all closed; `some false` = open saturated branch found;
    `none` = step budget exhausted (unknown). -/
partial def dfs (φ₀ : P) (fuel : Nat) (st : St) : Option Bool :=
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
          match dfs φ₀ fuel' ⟨b, e, acc', keys'⟩ with
          | some true => go rbs res
          | x => x
        | _, _ => some true
      go bs es

def tabCloses (φ₀ : P) (fuel : Nat) : Option Bool :=
  dfs φ₀ fuel ⟨[⟨.neg, φ₀, 0⟩], [], Accessibility.empty,
    [((0:WorldIndex), (∅ : Finset (Sign × P)))]⟩

/-! ### Brute-force S4 countermodel search -/

partial def sat (n : Nat) (rel : Nat → Nat → Bool) (val : Nat → Nat → Bool)
    (w : Nat) : P → Bool
  | .atom p => val w p
  | .bot => false
  | .imp x y => !(sat n rel val w x) || sat n rel val w y
  | .and x y => sat n rel val w x && sat n rel val w y
  | .or x y => sat n rel val w x || sat n rel val w y
  | .box x => (List.range n).all (fun v => !(rel w v) || sat n rel val v x)
  | .diamond x => (List.range n).any (fun v => rel w v && sat n rel val v x)

def bit (m i : Nat) : Bool := (m >>> i) % 2 == 1

def isS4 (n m : Nat) : Bool :=
  let rel := fun i j => bit m (i * n + j)
  (List.range n).all (fun i => rel i i) &&
  (List.range n).all (fun i => (List.range n).all (fun j => (List.range n).all (fun k =>
    !(rel i j && rel j k) || rel i k)))

/-- `true` if a countermodel of size exactly `n` over `natoms` atoms exists. -/
def hasCountermodel (φ : P) (n natoms : Nat) : Bool :=
  (List.range (2 ^ (n * n))).any (fun m =>
    isS4 n m &&
    (let rel := fun i j => bit m (i * n + j)
     (List.range (2 ^ (n * natoms))).any (fun v =>
       let val := fun w p => bit v (w * natoms + p)
       (List.range n).any (fun w => !(sat n rel val w φ)))))

def notS4Valid (φ : P) (maxN natoms : Nat) : Bool :=
  (List.range maxN).any (fun i => hasCountermodel φ (i+1) natoms)

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

#eval IO.println s!"formula count (2 atoms, size<=5): {(allUpTo 2 5).length}"

/-! ### Redirect instrumentation -/

def reach (edges : List (WorldIndex × WorldIndex)) (src : WorldIndex) : List WorldIndex :=
  let step (vs : List WorldIndex) : List WorldIndex :=
    (vs ++ edges.filterMap (fun e => if vs.contains e.1 then some e.2 else none)).eraseDups
  (List.range (edges.length + 2)).foldl (fun vs _ => step vs) [src]

/-- classify new edges added by one step. returns (numRedirects, numUnsoundRedirects) -/
def classify (b : List (SignedFormula P WorldIndex)) (acc acc' : Accessibility) : Nat × Nat :=
  let known := modalKnownWorlds b
  let newEdges := acc'.edges.filter (fun e => !(acc.edges.contains e))
  newEdges.foldl (fun (c : Nat × Nat) e =>
    if known.contains e.2 then
      (c.1 + 1, if (reach acc.edges e.1).contains e.2 then c.2 else c.2 + 1)
    else c) (0, 0)

partial def dfsR (f0 : P) (fuel : Nat) (st : St) : Nat × Nat :=
  if isModalClosed st.b then (0,0)
  else match fuel with
  | 0 => (0,0)
  | fuel'+1 =>
    match modalStepBranchS4Keyed f0 st.b st.e st.acc st.keys with
    | none => (0,0)
    | some (bs, es, acc', keys') =>
      let here := classify st.b st.acc acc'
      let rec go (bs : List (List (SignedFormula P WorldIndex)))
                 (es : List (List (SignedFormula P WorldIndex))) : Nat × Nat :=
        match bs, es with
        | [], _ => (0,0)
        | b :: rbs, e :: res =>
          let x := dfsR f0 fuel' ⟨b, e, acc', keys'⟩
          let y := go rbs res
          (x.1 + y.1, x.2 + y.2)
        | _, _ => (0,0)
      let sub := go bs es
      (here.1 + sub.1, here.2 + sub.2)

def redirectStats (natoms sz fuel : Nat) : String :=
  let rs := (allUpTo natoms sz).map (fun f =>
    dfsR f fuel ⟨[⟨.neg, f, 0⟩], [], Accessibility.empty,
      [((0:WorldIndex), (∅ : Finset (Sign × P)))]⟩)
  let tot := rs.foldl (fun (c : Nat × Nat) x => (c.1 + x.1, c.2 + x.2)) (0,0)
  let withUnsound := (rs.filter (fun x => x.2 > 0)).length
  s!"redirects={tot.1} unsoundRedirects={tot.2} formulasWithUnsoundRedirect={withUnsound}"

def unsoundRedirectFormulas (natoms sz fuel : Nat) : List P :=
  (allUpTo natoms sz).filter (fun f =>
    (dfsR f fuel ⟨[⟨.neg, f, 0⟩], [], Accessibility.empty,
      [((0:WorldIndex), (∅ : Finset (Sign × P)))]⟩).2 > 0)

def p0 : P := .atom 0
def p1 : P := .atom 1
def nt (x : P) : P := .imp x .bot

-- candidate counterexample
def alphaA : P := .or (.box p0) (nt (nt (.diamond p1)))
def alphaL : P := .or (.box p0) (nt (.box p1))
def cex : P := .or (.box alphaA) (.box alphaL)

-- LIVE-set (non-keyed) driver
partial def dfsL (f0 : P) (fuel : Nat)
    (b e : List (SignedFormula P WorldIndex)) (acc : Accessibility) : Option Bool :=
  if isModalClosed b then some true
  else match fuel with
  | 0 => none
  | fuel'+1 =>
    match modalStepBranchS4 f0 b e acc with
    | none => some false
    | some (bs, es, acc') =>
      let rec go (bs : List (List (SignedFormula P WorldIndex)))
                 (es : List (List (SignedFormula P WorldIndex))) : Option Bool :=
        match bs, es with
        | [], _ => some true
        | b2 :: rbs, e2 :: res =>
          match dfsL f0 fuel' b2 e2 acc' with
          | some true => go rbs res
          | x => x
        | _, _ => some true
      go bs es

def tabClosesL (f0 : P) (fuel : Nat) : Option Bool :=
  dfsL f0 fuel [⟨.neg, f0, 0⟩] [] Accessibility.empty

def p0 : P := .atom 0
def p1 : P := .atom 1
def nt (x : P) : P := .imp x .bot
def alphaA : P := .or (.box p0) (nt (nt (.diamond p1)))
def alphaL : P := .or (.box p0) (nt (.box p1))
def cex : P := .or (.box alphaA) (.box alphaL)

#eval IO.println s!"KEYED closes cex = {tabCloses cex 400}"
#eval IO.println s!"LIVE  closes cex = {tabClosesL cex 400}"

-- broad search against the LIVE-set driver
def badL (natoms sz fuel maxN : Nat) : List P :=
  ((allUpTo natoms sz).filter (fun f => tabClosesL f fuel == some true)).filter
    (fun f => notS4Valid f maxN natoms)
def statsL (natoms sz fuel : Nat) : String :=
  let rs := (allUpTo natoms sz).map (fun f => tabClosesL f fuel)
  s!"total={(allUpTo natoms sz).length} closed={(rs.filter (· == some true)).length} open={(rs.filter (· == some false)).length} unknown={(rs.filter (· == none)).length}"
#eval IO.println ("LIVE " ++ statsL 2 5 100)
#eval IO.println s!"LIVE UNSOUND(size<=5): {((badL 2 5 100 3).map ppP)}"
