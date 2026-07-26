import Cslib.Logics.Modal.Tableau.LoopChecking

/-! # Route (3) probe, part 3: is the completeness construction recoverable?

Under subtractive blocking the redirect edge is gone, so `modalHintikkaSetS4`'s box-negative
conjunct (`LoopChecking.lean:6557-6559`)

    ∀ φ w, ⟨.neg, .box φ, w⟩ ∈ b → ∃ w', acc.hasEdge w w' = true ∧ ⟨.neg, φ, w'⟩ ∈ b

loses its only source. The repair candidate is to thread the blocking decisions in a SEPARATE
completeness-only channel `red` (so soundness, which quantifies over `acc.hasEdge`, never sees
them) and to extract the countermodel over `ReflTransGen (acc ∪ red)`. For that to feed
`modalTruthLemmaS4` (`FrameCompleteness.lean:232-394`) the recorded `(src, wBlock, s, ψ)` must
satisfy FOUR conditions at every TERMINAL OPEN leaf:

* **(a) witness**   — the blocked witness formula is present at `wBlock`:
  `⟨s, ψ, wBlock⟩ ∈ b`. (Corresponds to the surviving asset
  `modalStepBranchS4Keyed_blocked_witness_mem`, `LoopChecking.lean:8806-8824`.)
* **(b) box wrapped** — `∀χ, T(□χ)@src ∈ b → T(□χ)@wBlock ∈ b`. Needed because the extracted
  relation is `ReflTransGen`, so box facts must keep travelling PAST `wBlock`
  (`FrameCompleteness.lean:87`, `:150-153`).
* **(c) box unwrapped** — `∀χ, T(□χ)@src ∈ b → T(χ)@wBlock ∈ b`. This one is implied by
  `S4LoopInv.keyLowerBd` + the guard, since `successorBirthContent`
  (`LoopChecking.lean:384-391`) puts `(pos, χ)` — UNWRAPPED — into the key.
* **(d) diamond dual** — `∀χ, F(◇χ)@src ∈ b → F(◇χ)@wBlock ∈ b`.

`(b)` is the load-bearing one: it is the wrapped form that `successorBirthContent` does NOT put
in the key, and it is the same obligation report 02's removed `blockedRedirect_boxctx_mem`
asserted.

Also measured: the SHIPPED ordered driver (`modalStepBranchS4KeyedOrdered`,
`LoopChecking.lean:1107`) on `cex`, as a control on whether settled-context scheduling alone
already changes the empirical verdict.
-/

set_option maxRecDepth 100000

open Cslib.Logic.Modal Cslib.Logic.Tableau Cslib.Logic.Modal.Tableau

abbrev P := Proposition Nat
abbrev Keys := List (WorldIndex × Finset (Sign × P))
/-- A recorded blocking decision: `(src, wBlock, witnessSign, witnessFormula)`. -/
abbrev Reds := List (WorldIndex × WorldIndex × Sign × P)

partial def ppP : P → String
  | .atom n => s!"p{n}"
  | .bot => "⊥"
  | .imp x y => s!"({ppP x}→{ppP y})"
  | .and x y => s!"({ppP x}∧{ppP y})"
  | .or x y => s!"({ppP x}∨{ppP y})"
  | .box x => s!"□{ppP x}"
  | .diamond x => s!"◇{ppP x}"

/-! ## Subtractive rule application (S1: consume, no edge) -/

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

structure St where
  b : List (SignedFormula P WorldIndex)
  e : List (SignedFormula P WorldIndex)
  acc : Accessibility
  keys : Keys
  red : Reds

abbrev StepRes := List (List (SignedFormula P WorldIndex)) ×
  List (List (SignedFormula P WorldIndex)) × Accessibility × Keys × Reds

def bodyS1 (φ₀ : P) (b e : List (SignedFormula P WorldIndex)) (acc : Accessibility) (keys : Keys)
    (red : Reds) (sf : SignedFormula P WorldIndex) : Option StepRes :=
  if e.any (· == sf) then none
  else
    let (result, newAcc) := applyS1 φ₀ keys sf b acc
    let (keys', red') :=
      match sf.sign, sf.formula with
      | .neg, .box φ =>
        match blockingWorldS4Keyed φ₀ b keys .neg φ sf.label with
        | some wB => (keys, red ++ [(sf.label, wB, Sign.neg, φ)])
        | none =>
          (keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .neg φ sf.label)], red)
      | .pos, .diamond φ =>
        match blockingWorldS4Keyed φ₀ b keys .pos φ sf.label with
        | some wB => (keys, red ++ [(sf.label, wB, Sign.pos, φ)])
        | none =>
          (keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .pos φ sf.label)], red)
      | _, _ => (keys, red)
    match result with
    | .linear nf => some ([nf ++ b], [e ++ [sf]], newAcc, keys', red')
    | .branching brs =>
      some (brs.map (· ++ b), brs.map (fun _ => e ++ [sf]), newAcc, keys', red')
    | .persistent nf => some ([nf ++ b], [e], newAcc, keys', red')
    | .notApplicable => none

def nonMintS1 (φ₀ : P) (keys : Keys) (b e : List (SignedFormula P WorldIndex))
    (acc : Accessibility) : List (SignedFormula P WorldIndex) :=
  b.filter (fun sf =>
    !modalMintShape sf && !(e.any (· == sf)) && (applyS1 φ₀ keys sf b acc).1.isApplicable)

/-- Ordered (settled-context-scheduled) subtractive stepper. -/
def stepS1O (φ₀ : P) (st : St) : Option StepRes :=
  match (nonMintS1 φ₀ st.keys st.b st.e st.acc).findSome?
      (bodyS1 φ₀ st.b st.e st.acc st.keys st.red) with
  | some r => some r
  | none => st.b.findSome? (bodyS1 φ₀ st.b st.e st.acc st.keys st.red)

/-! ## The four completeness conditions, evaluated at a TERMINAL OPEN leaf -/

/-- Every `□`-formula and `◇`-formula that can occur, via `modalSubfmls φ₀` (the same
computable superset technique `s4ancestor.lean`/`s4witness.lean` use). -/
def probeFmls (φ₀ : P) : List P := modalSubfmls φ₀

def condA (b : List (SignedFormula P WorldIndex)) (r : WorldIndex × WorldIndex × Sign × P) : Bool :=
  b.any (· == (⟨r.2.2.1, r.2.2.2, r.2.1⟩ : SignedFormula P WorldIndex))

def condB (φ₀ : P) (b : List (SignedFormula P WorldIndex))
    (r : WorldIndex × WorldIndex × Sign × P) : Bool :=
  (probeFmls φ₀).all (fun χ =>
    !(b.any (· == (⟨.pos, .box χ, r.1⟩ : SignedFormula P WorldIndex))) ||
      b.any (· == (⟨.pos, .box χ, r.2.1⟩ : SignedFormula P WorldIndex)))

def condC (φ₀ : P) (b : List (SignedFormula P WorldIndex))
    (r : WorldIndex × WorldIndex × Sign × P) : Bool :=
  (probeFmls φ₀).all (fun χ =>
    !(b.any (· == (⟨.pos, .box χ, r.1⟩ : SignedFormula P WorldIndex))) ||
      b.any (· == (⟨.pos, χ, r.2.1⟩ : SignedFormula P WorldIndex)))

def condD (φ₀ : P) (b : List (SignedFormula P WorldIndex))
    (r : WorldIndex × WorldIndex × Sign × P) : Bool :=
  (probeFmls φ₀).all (fun χ =>
    !(b.any (· == (⟨.neg, .diamond χ, r.1⟩ : SignedFormula P WorldIndex))) ||
      b.any (· == (⟨.neg, .diamond χ, r.2.1⟩ : SignedFormula P WorldIndex)))

/-- **(e)** the UNWRAPPED diamond dual: `∀χ, F(◇χ)@src ∈ b → F(χ)@wBlock ∈ b`. This is the one
`successorBirthContent` (`LoopChecking.lean:390-391`) actually puts in the key, so it should be
free from `S4LoopInv.keyLowerBd`. Measured separately from (d) to localise which half of the
diamond-negative obligation is the real gap. -/
def condE (φ₀ : P) (b : List (SignedFormula P WorldIndex))
    (r : WorldIndex × WorldIndex × Sign × P) : Bool :=
  (probeFmls φ₀).all (fun χ =>
    !(b.any (· == (⟨.neg, .diamond χ, r.1⟩ : SignedFormula P WorldIndex))) ||
      b.any (· == (⟨.neg, χ, r.2.1⟩ : SignedFormula P WorldIndex)))

/-! ### The EXACT truth-lemma obligations (f) and (g)

Conditions (b)-(e) are proxies. What `modalTruthLemmaS4` actually needs, once the extracted
relation is `ReflTransGen (acc ∪ red)` (`FrameCompleteness.lean:87`, `:150-153`), is that the
propagation payload of `src` is already correct at EVERY world `acc`-reachable from `wBlock`,
not merely at `wBlock`:

* **(g)** `∀χ, T(□χ)@src ∈ b → ∀u, ReflTransGen(acc) wBlock u → T(χ)@u ∈ b`
* **(f)** `∀χ, F(◇χ)@src ∈ b → ∀u, ReflTransGen(acc) wBlock u → F(χ)@u ∈ b`

These are the box-positive / diamond-negative halves of `modalHintikkaSetS4` conjunct 2
restricted to the redirect target's forward cone, and they are exactly what
`hintikkaS4_box_pos_reflTransGen` / `hintikkaS4_dia_neg_reflTransGen`
(`LoopChecking.lean:6985-6998`, `:7001-7013`) would have to yield across a redirect edge. -/

/-- `acc`-reachable set from `w` (reflexive), by saturation over the finite world list. -/
partial def reachFrom (acc : Accessibility) (w : WorldIndex) : List WorldIndex :=
  let rec grow (seen frontier : List WorldIndex) (budget : Nat) : List WorldIndex :=
    match budget with
    | 0 => seen
    | budget' + 1 =>
      let next := (frontier.flatMap (fun v => acc.successorsOf v)).filter
        (fun u => !(seen.any (· == u)))
      match next with
      | [] => seen
      | _ => grow (seen ++ next) next budget'
  grow [w] [w] (acc.edges.length + 1)

def condG (φ₀ : P) (b : List (SignedFormula P WorldIndex)) (acc : Accessibility)
    (r : WorldIndex × WorldIndex × Sign × P) : Bool :=
  (probeFmls φ₀).all (fun χ =>
    !(b.any (· == (⟨.pos, .box χ, r.1⟩ : SignedFormula P WorldIndex))) ||
      (reachFrom acc r.2.1).all (fun u =>
        b.any (· == (⟨.pos, χ, u⟩ : SignedFormula P WorldIndex))))

def condF (φ₀ : P) (b : List (SignedFormula P WorldIndex)) (acc : Accessibility)
    (r : WorldIndex × WorldIndex × Sign × P) : Bool :=
  (probeFmls φ₀).all (fun χ =>
    !(b.any (· == (⟨.neg, .diamond χ, r.1⟩ : SignedFormula P WorldIndex))) ||
      (reachFrom acc r.2.1).all (fun u =>
        b.any (· == (⟨.neg, χ, u⟩ : SignedFormula P WorldIndex))))

/-! ### (F*)/(G*): the FULL obligation, closed under redirect CHAINS

(f)/(g) cover ONE redirect hop followed by `acc`-reachability. The extracted relation is
`ReflTransGen (acc ∪ red)`, so a path may alternate: `src ->red wB ->acc v ->red wB2 ->acc u`.
Since sweeps observe up to 39 recorded redirects on a single path, multi-hop chains certainly
occur. (F*)/(G*) test the obligation over reachability in the FULL augmented relation
`acc ∪ red`, which is exactly what `modalTruthLemmaS4`'s box-positive / diamond-negative cases
need via `hintikkaS4_box_pos_reflTransGen` / `hintikkaS4_dia_neg_reflTransGen`
(`LoopChecking.lean:6985-6998`, `:7001-7013`). -/

/-- Reachable set over a raw edge list (reflexive closure of the list's transitive closure). -/
partial def reachEdges (edges : List (WorldIndex × WorldIndex)) (w : WorldIndex) :
    List WorldIndex :=
  let rec grow (seen frontier : List WorldIndex) (budget : Nat) : List WorldIndex :=
    match budget with
    | 0 => seen
    | budget' + 1 =>
      let next := (frontier.flatMap (fun v =>
        (edges.filter (fun ed => ed.1 == v)).map Prod.snd)).filter
          (fun u => !(seen.any (· == u)))
      match next with
      | [] => seen
      | _ => grow (seen ++ next) next budget'
  grow [w] [w] (edges.length + 1)

/-- `acc ∪ red`, as a raw edge list. -/
def augEdges (acc : Accessibility) (red : Reds) : List (WorldIndex × WorldIndex) :=
  acc.edges ++ red.map (fun r => (r.1, r.2.1))

def condGStar (φ₀ : P) (b : List (SignedFormula P WorldIndex)) (acc : Accessibility) (red : Reds)
    (r : WorldIndex × WorldIndex × Sign × P) : Bool :=
  (probeFmls φ₀).all (fun χ =>
    !(b.any (· == (⟨.pos, .box χ, r.1⟩ : SignedFormula P WorldIndex))) ||
      (reachEdges (augEdges acc red) r.2.1).all (fun u =>
        b.any (· == (⟨.pos, χ, u⟩ : SignedFormula P WorldIndex))))

def condFStar (φ₀ : P) (b : List (SignedFormula P WorldIndex)) (acc : Accessibility) (red : Reds)
    (r : WorldIndex × WorldIndex × Sign × P) : Bool :=
  (probeFmls φ₀).all (fun χ =>
    !(b.any (· == (⟨.neg, .diamond χ, r.1⟩ : SignedFormula P WorldIndex))) ||
      (reachEdges (augEdges acc red) r.2.1).all (fun u =>
        b.any (· == (⟨.neg, χ, u⟩ : SignedFormula P WorldIndex))))

/-- Additionally: is the blocked source's obligation *already* discharged by a genuine `acc`
edge (i.e. did the source independently acquire a real successor)? If so the redirect channel is
not even needed at that world. -/
def condSelfSat (b : List (SignedFormula P WorldIndex)) (acc : Accessibility)
    (r : WorldIndex × WorldIndex × Sign × P) : Bool :=
  (acc.successorsOf r.1).any (fun u =>
    b.any (· == (⟨r.2.2.1, r.2.2.2, u⟩ : SignedFormula P WorldIndex)))

structure CStats where
  redirects : Nat := 0
  failA : Nat := 0
  failB : Nat := 0
  failC : Nat := 0
  failD : Nat := 0
  failE : Nat := 0
  failF : Nat := 0
  failG : Nat := 0
  failFStar : Nat := 0
  failGStar : Nat := 0
  selfSat : Nat := 0
  openLeaves : Nat := 0
  /-- Human-readable descriptions of the first few condition-(d) failures. -/
  dEx : List String := []
  deriving Inhabited

def combineC (x y : CStats) : CStats :=
  { redirects := x.redirects + y.redirects, failA := x.failA + y.failA
    failB := x.failB + y.failB, failC := x.failC + y.failC, failD := x.failD + y.failD
    failE := x.failE + y.failE
    failF := x.failF + y.failF, failG := x.failG + y.failG
    failFStar := x.failFStar + y.failFStar, failGStar := x.failGStar + y.failGStar
    selfSat := x.selfSat + y.selfSat, openLeaves := x.openLeaves + y.openLeaves
    dEx := (x.dEx ++ y.dEx).take 6 }

/-- The offending `χ`s for a condition-(d) failure, rendered. -/
def dWitnesses (φ₀ : P) (b : List (SignedFormula P WorldIndex))
    (r : WorldIndex × WorldIndex × Sign × P) : String :=
  let bad := (probeFmls φ₀).filter (fun χ =>
    b.any (· == (⟨.neg, .diamond χ, r.1⟩ : SignedFormula P WorldIndex)) &&
      !(b.any (· == (⟨.neg, χ, r.2.1⟩ : SignedFormula P WorldIndex)) ||
        b.any (· == (⟨.neg, .diamond χ, r.2.1⟩ : SignedFormula P WorldIndex))))
  let bad2 := (probeFmls φ₀).filter (fun χ =>
    b.any (· == (⟨.neg, .diamond χ, r.1⟩ : SignedFormula P WorldIndex)) &&
      !(b.any (· == (⟨.neg, .diamond χ, r.2.1⟩ : SignedFormula P WorldIndex))))
  s!"φ₀={ppP φ₀} src={r.1} wBlock={r.2.1} unwrappedAlsoMissing={bad.map ppP} wrappedMissing={bad2.map ppP}"

def openLeafStats (φ₀ : P) (st : St) : CStats :=
  { redirects := st.red.length
    failA := (st.red.filter (fun r => !condA st.b r)).length
    failB := (st.red.filter (fun r => !condB φ₀ st.b r)).length
    failC := (st.red.filter (fun r => !condC φ₀ st.b r)).length
    failD := (st.red.filter (fun r => !condD φ₀ st.b r)).length
    failE := (st.red.filter (fun r => !condE φ₀ st.b r)).length
    failF := (st.red.filter (fun r => !condF φ₀ st.b st.acc r)).length
    failG := (st.red.filter (fun r => !condG φ₀ st.b st.acc r)).length
    failFStar := (st.red.filter (fun r => !condFStar φ₀ st.b st.acc st.red r)).length
    failGStar := (st.red.filter (fun r => !condGStar φ₀ st.b st.acc st.red r)).length
    selfSat := (st.red.filter (fun r => condSelfSat st.b st.acc r)).length
    openLeaves := 1
    dEx := ((st.red.filter (fun r => !condD φ₀ st.b r)).map (dWitnesses φ₀ st.b)).take 3 }

/-- DFS that aggregates the four conditions over EVERY terminal open leaf. Unlike the shipped
drivers this does NOT short-circuit on the first non-closed child -- every open leaf a
countermodel could be extracted from is visited, since completeness must hold at all of them. -/
partial def dfsC (φ₀ : P) (fuel : Nat) (st : St) : Option Bool × CStats :=
  if isModalClosed st.b then (some true, {})
  else match fuel with
  | 0 => (none, {})
  | fuel' + 1 =>
    match stepS1O φ₀ st with
    | none => (some false, openLeafStats φ₀ st)
    | some (bs, es, acc', keys', red') =>
      let rec go (bs : List (List (SignedFormula P WorldIndex)))
          (es : List (List (SignedFormula P WorldIndex))) : Option Bool × CStats :=
        match bs, es with
        | [], _ => (some true, {})
        | b2 :: rbs, e2 :: res =>
          let (r1, s1) := dfsC φ₀ fuel' ⟨b2, e2, acc', keys', red'⟩
          let (r2, s2) := go rbs res
          -- verdict: closed iff every child closed; stats aggregated over ALL children
          ((if r1 == some true then r2 else r1), combineC s1 s2)
        | _, _ => (some true, {})
      go bs es

def runC (φ₀ : P) (fuel : Nat) : Option Bool × CStats :=
  dfsC φ₀ fuel ⟨[⟨.neg, φ₀, 0⟩], [], Accessibility.empty,
    [((0 : WorldIndex), (∅ : Finset (Sign × P)))], []⟩

/-! ## Control: the SHIPPED ordered driver on cex -/

partial def dfsShippedOrdered (φ₀ : P) (fuel : Nat) (b e : List (SignedFormula P WorldIndex))
    (acc : Accessibility) (keys : Keys) : Option Bool :=
  if isModalClosed b then some true
  else match fuel with
  | 0 => none
  | fuel' + 1 =>
    match modalStepBranchS4KeyedOrdered φ₀ b e acc keys with
    | none => some false
    | some (bs, es, acc', keys') =>
      let rec go (bs : List (List (SignedFormula P WorldIndex)))
          (es : List (List (SignedFormula P WorldIndex))) : Option Bool :=
        match bs, es with
        | [], _ => some true
        | b2 :: rbs, e2 :: res =>
          match dfsShippedOrdered φ₀ fuel' b2 e2 acc' keys' with
          | some true => go rbs res
          | x => x
        | _, _ => some true
      go bs es

def runShippedOrdered (φ₀ : P) (fuel : Nat) : Option Bool :=
  dfsShippedOrdered φ₀ fuel [⟨.neg, φ₀, 0⟩] [] Accessibility.empty
    [((0 : WorldIndex), (∅ : Finset (Sign × P)))]

partial def dfsShipped (φ₀ : P) (fuel : Nat) (b e : List (SignedFormula P WorldIndex))
    (acc : Accessibility) (keys : Keys) : Option Bool :=
  if isModalClosed b then some true
  else match fuel with
  | 0 => none
  | fuel' + 1 =>
    match modalStepBranchS4Keyed φ₀ b e acc keys with
    | none => some false
    | some (bs, es, acc', keys') =>
      let rec go (bs : List (List (SignedFormula P WorldIndex)))
          (es : List (List (SignedFormula P WorldIndex))) : Option Bool :=
        match bs, es with
        | [], _ => some true
        | b2 :: rbs, e2 :: res =>
          match dfsShipped φ₀ fuel' b2 e2 acc' keys' with
          | some true => go rbs res
          | x => x
        | _, _ => some true
      go bs es

def runShipped (φ₀ : P) (fuel : Nat) : Option Bool :=
  dfsShipped φ₀ fuel [⟨.neg, φ₀, 0⟩] [] Accessibility.empty
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

/-! ## Semantic validity oracle (as in `s4subtractive.lean`), for the deeper-corpus differential

`s4subtractive2.lean` found exactly FOUR `closed -> open` disagreements over the 1-atom,
size<=8 corpus (95730 formulas). Each is adjudicated here: a countermodel means the SHIPPED
driver was unsound there and subtractive blocking corrected it; no countermodel up to size 4
would make it a completeness-loss suspect. -/

def bitAt (m i : Nat) : Bool := (m / (2 ^ i)) % 2 == 1

def offDiag (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap (fun i =>
    (List.range n).filterMap (fun j => if i == j then none else some (i, j)))

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

def falsifiableUpTo (natoms N : Nat) (φ : P) : Option Nat :=
  (List.range N).findSome? (fun i =>
    if falsifiableAtSize natoms (i + 1) φ then some (i + 1) else none)

/-- The four `closed -> open` disagreements from the 1-atom size<=8 sweep, verbatim. -/
def d1 : P := .diamond (.box (.diamond (.box (.diamond (.box (.diamond .bot))))))
def d2 : P := .diamond (.box (.diamond (.box (.diamond (.box (.diamond p0))))))
def d3 : P := .diamond (.box (.box (.imp p0 (.box (.diamond p0)))))
def d4 : P := .diamond (.box (.box (.imp (.diamond (.box p0)) p0)))

#eval IO.println s!"ORACLE on the 4 deeper-corpus disagreements (least countermodel size, <=4):"
#eval IO.println s!"  {ppP d1} -> {falsifiableUpTo 1 4 d1}"
#eval IO.println s!"  {ppP d2} -> {falsifiableUpTo 1 4 d2}"
#eval IO.println s!"  {ppP d3} -> {falsifiableUpTo 1 4 d3}"
#eval IO.println s!"  {ppP d4} -> {falsifiableUpTo 1 4 d4}"
#eval IO.println s!"  (a size = the shipped driver was UNSOUND there; `none` = completeness-loss suspect)"
#eval IO.println s!"  verdicts: shipped={[runShipped d1 100, runShipped d2 100, runShipped d3 100, runShipped d4 100]} subtractive={[runC d1 100 |>.1, runC d2 100 |>.1, runC d3 100 |>.1, runC d4 100 |>.1]}"

/-! ## Control measurements -/

#eval IO.println
  s!"M1: cex  shipped-unordered={runShipped cex 400}  shipped-ORDERED={runShippedOrdered cex 400}  subtractive-ordered={(runC cex 400).1}"

#eval IO.println s!"M2: cex subtractive-ordered redirect stats = {repr (runC cex 400).2.redirects}, failA={(runC cex 400).2.failA}, failB={(runC cex 400).2.failB}, failC={(runC cex 400).2.failC}, failD={(runC cex 400).2.failD}, selfSat={(runC cex 400).2.selfSat}, openLeaves={(runC cex 400).2.openLeaves}"

/-! ## Sweep: the four conditions over every terminal open leaf of the whole corpus -/

def cRow (fuel : Nat) (f : P) : CStats := (runC f fuel).2

def sumC (xs : List CStats) : CStats := xs.foldl combineC {}

def reportC (label : String) (natoms sz fuel : Nat) : IO Unit := do
  let fs := allUpTo natoms sz
  let s := sumC (fs.map (cRow fuel))
  IO.println s!"{label}: formulas={fs.length} openLeavesVisited={s.openLeaves} recordedRedirects={s.redirects}"
  IO.println s!"{label}: (a) witness present at wBlock      -- FAILURES = {s.failA}"
  IO.println s!"{label}: (b) T(□χ)@src -> T(□χ)@wBlock      -- FAILURES = {s.failB}   <-- LOAD-BEARING"
  IO.println s!"{label}: (c) T(□χ)@src -> T(χ)@wBlock       -- FAILURES = {s.failC}"
  IO.println s!"{label}: (d) F(◇χ)@src -> F(◇χ)@wBlock      -- FAILURES = {s.failD}"
  IO.println s!"{label}: (e) F(◇χ)@src -> F(χ)@wBlock       -- FAILURES = {s.failE}"
  IO.println s!"{label}: (g) T(□χ)@src -> T(χ)@u for ALL u acc-reachable from wBlock -- FAILURES = {s.failG}   <-- EXACT TRUTH-LEMMA OBLIGATION"
  IO.println s!"{label}: (f) F(◇χ)@src -> F(χ)@u for ALL u acc-reachable from wBlock -- FAILURES = {s.failF}   <-- EXACT TRUTH-LEMMA OBLIGATION"
  IO.println s!"{label}: (G*) box obligation over ALL u reachable in acc UNION red -- FAILURES = {s.failGStar}   <-- FULL OBLIGATION"
  IO.println s!"{label}: (F*) dia obligation over ALL u reachable in acc UNION red -- FAILURES = {s.failFStar}   <-- FULL OBLIGATION"
  IO.println s!"{label}: redirects whose source ALREADY had a genuine acc-successor witness = {s.selfSat}"
  for x in s.dEx do IO.println s!"{label}:   (d)-failure example: {x}"

#eval reportC "C6.2" 2 6 100
#eval reportC "C7.1" 1 7 100
#eval reportC "C7.2" 2 7 100
