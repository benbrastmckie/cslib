import Cslib.Logics.Modal.Tableau.LoopChecking

/-! Phase 13 divergence audit probe: is the witness-collision configuration of
`blockedRedirect_boxctx_mem` reachable by the ORDERED driver?

Candidate formula: `φ₀ = ¬(◇p ∧ ◇(□p ∧ ◇p))`, `¬X := X → ⊥`.

Intended trace:
  * `F(φ₀)@0` decomposes to `T(◇p)@0`, `T(◇(□p∧◇p))@0` -- world 0 has NO box-positives.
  * mint `T(◇p)@0`  -> world 1, key `{(pos,p)}`, edge 0→1, branch gets `T(p)@1` only.
  * mint `T(◇(□p∧◇p))@0` -> world 2, key `{(pos,□p∧◇p)}`, edge 0→2.
  * non-mint saturation at 2 gives `T(□p)@2`, `T(◇p)@2`, `T(p)@2`.
  * mint attempt `T(◇p)@2`: prospective birth content = `insert (pos,p) {(pos,p)}` = `{(pos,p)}`
    == key(1). Guard REDIRECTS 2→1, but `T(□p)@1 ∉ b`.
-/

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

def ppPair (p : Sign × P) : String :=
  (match p.1 with | .pos => "+" | .neg => "-") ++ ppP p.2

/-- Computable stand-in for `Finset.toList` (noncomputable): probe membership of every
signed subformula pair of `φ₀`, which is a superset of every key the driver ever records
(`S4LoopInv.keysInUniverse`). -/
def probePairs (φ₀ : P) : List (Sign × P) :=
  (modalSubfmls φ₀).flatMap (fun f => [(Sign.pos, f), (Sign.neg, f)])

def ppKeyIn (φ₀ : P) (k : Finset (Sign × P)) : String :=
  "{" ++ String.intercalate "," (((probePairs φ₀).filter (fun q => decide (q ∈ k))).map ppPair)
    ++ "}"

def ppKeys (φ₀ : P) (keys : List (WorldIndex × Finset (Sign × P))) : String :=
  String.intercalate " " (keys.map (fun wk => s!"{wk.1}↦{ppKeyIn φ₀ wk.2}"))

def ppAcc (acc : Accessibility) : String :=
  String.intercalate " " (acc.edges.map (fun e => s!"{e.1}→{e.2}"))

structure St where
  b : List (SignedFormula P WorldIndex)
  e : List (SignedFormula P WorldIndex)
  acc : Accessibility
  keys : List (WorldIndex × Finset (Sign × P))

def initSt (φ₀ : P) : St :=
  ⟨[⟨.neg, φ₀, 0⟩], [], Accessibility.empty, [((0 : WorldIndex), (∅ : Finset (Sign × P)))]⟩

def p : P := .atom 0
def nt (x : P) : P := .imp x .bot

/-- `φ₀ = ¬(◇p ∧ ◇(□p ∧ ◇p))` -/
def phiW : P := nt (.and (.diamond p) (.diamond (.and (.box p) (.diamond p))))

/-- Linear (single-branch) trace of the ORDERED stepper, printing the full state each step.
Aborts if the stepper ever branches (this probe's formula is disjunction-free). -/
partial def trace (φ₀ : P) (fuel : Nat) (st : St) (n : Nat) : IO Unit := do
  IO.println s!"[{n}] b = {ppB st.b}"
  IO.println s!"      acc = [{ppAcc st.acc}]   keys = {ppKeys φ₀ st.keys}"
  IO.println s!"      e   = [{ppB st.e}]"
  IO.println s!"      nonMintCandidates = [{ppB (modalNonMintCandidates φ₀ st.keys st.b st.e st.acc)}]"
  IO.println s!"      guard(pos,p0,@2) = {blockingWorldS4Keyed φ₀ st.b st.keys .pos p 2}"
  IO.println s!"      T(box p0)@1 ∈ b = {st.b.any (· == (⟨.pos, .box p, 1⟩ : SignedFormula P WorldIndex))}"
  IO.println s!"      eBoxOnlyNeg = {st.e.all (fun sf => match sf.formula, sf.sign with | .box _, .pos => false | _, _ => true)}"
  IO.println s!"      keys(0) = ∅ : {st.keys.all (fun wk => if wk.1 == 0 then decide (wk.2 = (∅ : Finset (Sign × P))) else true)}"
  IO.println s!"      eDiaOnlyPos = {st.e.all (fun sf => match sf.formula, sf.sign with | .diamond _, .neg => false | _, _ => true)}"
  if isModalClosed st.b then
    IO.println "      CLOSED"
    return
  match fuel with
  | 0 => IO.println "      FUEL EXHAUSTED"
  | fuel'+1 =>
    match modalStepBranchS4KeyedOrdered φ₀ st.b st.e st.acc st.keys with
    | none => IO.println "      SATURATED OPEN"
    | some (bs, es, acc', keys') =>
      if bs.length != 1 then
        IO.println s!"      BRANCHED into {bs.length} -- probe expects 1"
      else
        match bs, es with
        | [b'], [e'] => trace φ₀ fuel' ⟨b', e', acc', keys'⟩ (n+1)
        | _, _ => IO.println "      shape mismatch"

#eval IO.println s!"phiW = {ppP phiW}"
#eval trace phiW 40 (initSt phiW) 0
