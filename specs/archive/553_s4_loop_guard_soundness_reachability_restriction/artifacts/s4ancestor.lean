import Cslib.Logics.Modal.Tableau.LoopChecking

/-! Phase 1 (plan v3, ancestor-only blocking) empirical probe.

Definitions and `#eval` only -- no proofs, no `sorry`, no axioms. Builds an executable
spine-tracking state and an ancestor-restricted guard `bwAnc` (as `blockingWorldS4Keyed` but
the candidate list is filtered to the source world's own spine-ancestor chain), together with
unordered and ordered stepper variants mirroring the shipped `modalStepBranchS4Keyed` /
`modalStepBranchS4KeyedOrdered`. Records four measurements:

* **A (soundness)**: is `cex` (the report-01 counterexample) OPEN under the ancestor-ordered
  driver?
* **B (validity)**: are the T, 4, K axiom instances CLOSED under the ancestor-ordered driver?
* **C (differential sweep)**: exhaustive size<=6, 2-atom, fuel-100 sweep, both ancestor
  orderings, against the established 1650-closed/6882-open/0-fuel-exhausted baseline for the
  shipped unordered keyed driver (recomputed here as a control, not merely cited).
* **D (invariant damage)**: does global `keysDistinct` actually break; observed max spine
  depth; observed max out-degree; and the upward box-propagation test on every blocked
  redirect (`∀ψ, T(□ψ)@src ∈ b → T(□ψ)@wBlock ∈ b`), aggregated over the same sweep corpus
  using the ordered driver.
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

/-! ### Spine tracking

`Spine` records, for every minted world, the (child, parent) edge created at mint time: the
child is `modalNextWorld b` and the parent is the label of the minting formula. Root world `0`
has no entry. Ancestor chains terminate because `modalNextWorld_gt` (LoopChecking's own,
`Branch.lean`) guarantees every child index is strictly greater than every world already on the
branch, in particular its parent -- so the parent chain has strictly decreasing indices and
must reach a world with no recorded parent (the root) in at most `spine.length` steps. This
probe does not prove that fact; it only needs `partial def` to compute with it. -/

abbrev Spine := List (WorldIndex × WorldIndex)

/-- The direct parent of `w` in `spine`, if any. -/
def spineParentOf (spine : Spine) (w : WorldIndex) : Option WorldIndex :=
  (spine.find? (fun e => e.1 == w)).map Prod.snd

/-- The strict ancestor chain of `w` (parent, grandparent, ..., root), NOT including `w`
itself. -/
partial def spineAncestors (spine : Spine) (w : WorldIndex) : List WorldIndex :=
  match spineParentOf spine w with
  | none => []
  | some p => p :: spineAncestors spine p

/-! ### The ancestor-restricted guard -/

/-- `bwAnc`: as `blockingWorldS4Keyed` but the candidate list is filtered to `w` itself plus
its spine ancestors -- the mandated ancestor-only-blocking restriction. Returns the least such
world whose recorded key equals the prospective successor's birth content, or `none` if no
ancestor (or `w` itself) matches. -/
def bwAnc (φ₀ : P) (b : List (SignedFormula P WorldIndex))
    (keys : List (WorldIndex × Finset (Sign × P))) (spine : Spine)
    (s : Sign) (φ : P) (w : WorldIndex) : Option WorldIndex :=
  let candidates := w :: spineAncestors spine w
  ((keys.filter (fun wk =>
      candidates.any (· == wk.1) && decide (wk.2 = successorBirthContent φ₀ b s φ w))).map
    Prod.fst).min?

/-! ### Rule application and non-mint candidates over `bwAnc` -/

/-- As `modalApplyOneS4Keyed` but consulting `bwAnc` (ancestor-restricted) instead of
`blockingWorldS4Keyed` (globally-restricted) at the two minting shapes. Falls through to the
ordinary S4 rule set (`modalApplyOneS4`, hence to `modalApplyOne`'s raw K rules) exactly as the
shipped keyed driver does. -/
def modalApplyOneS4Anc (φ₀ : P) (keys : List (WorldIndex × Finset (Sign × P))) (spine : Spine) :
    SignedFormula P WorldIndex → List (SignedFormula P WorldIndex) → Accessibility →
    RuleResult P WorldIndex × Accessibility :=
  fun sf b acc =>
    match sf.sign, sf.formula with
    | .neg, .box φ =>
      match bwAnc φ₀ b keys spine .neg φ sf.label with
      | some wBlock => (.linear [], acc.addEdge sf.label wBlock)
      | none => modalApplyOne sf b acc
    | .pos, .diamond φ =>
      match bwAnc φ₀ b keys spine .pos φ sf.label with
      | some wBlock => (.linear [], acc.addEdge sf.label wBlock)
      | none => modalApplyOne sf b acc
    | _, _ => modalApplyOneS4 φ₀ sf b acc

/-- `true` at the two minting shapes (mirrors `modalMintShape`). -/
def modalMintShapeAnc (sf : SignedFormula P WorldIndex) : Bool :=
  match sf.sign, sf.formula with
  | .neg, .box _ => true
  | .pos, .diamond _ => true
  | _, _ => false

/-- Non-minting, not-yet-expanded, currently-applicable candidates under the ancestor guard
(mirrors `modalNonMintCandidates`). Consulted first by the ordered stepper. -/
def nonMintCandidatesAnc (φ₀ : P) (keys : List (WorldIndex × Finset (Sign × P))) (spine : Spine)
    (b e : List (SignedFormula P WorldIndex)) (acc : Accessibility) :
    List (SignedFormula P WorldIndex) :=
  b.filter (fun sf =>
    !modalMintShapeAnc sf && !(e.any (· == sf)) &&
      (modalApplyOneS4Anc φ₀ keys spine sf b acc).1.isApplicable)

/-! ### State, per-formula body, unordered and ordered steppers -/

structure StAnc where
  b : List (SignedFormula P WorldIndex)
  e : List (SignedFormula P WorldIndex)
  acc : Accessibility
  keys : List (WorldIndex × Finset (Sign × P))
  spine : Spine
  /-- `(src, wBlock)` pairs recorded along THIS path (branch-local, per DFS convention). -/
  redirects : List (WorldIndex × WorldIndex)

def initStAnc (φ₀ : P) : StAnc :=
  ⟨[⟨.neg, φ₀, 0⟩], [], Accessibility.empty, [((0 : WorldIndex), (∅ : Finset (Sign × P)))], [], []⟩

abbrev StepResult :=
  List (List (SignedFormula P WorldIndex)) × List (List (SignedFormula P WorldIndex)) ×
    Accessibility × List (WorldIndex × Finset (Sign × P)) × Spine ×
    List (WorldIndex × WorldIndex)

/-- The per-formula rule-application body shared by the unordered and ordered ancestor
steppers (mirrors `modalStepBranchS4KeyedBody`): same `modalApplyOneS4Anc` call, plus threading
of `keys`/`spine` on a genuine mint and of `redirects` on a block. -/
def stepBodyAnc (φ₀ : P) (b e : List (SignedFormula P WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × P))) (spine : Spine)
    (redirects : List (WorldIndex × WorldIndex)) (sf : SignedFormula P WorldIndex) :
    Option StepResult :=
  if e.any (· == sf) then none
  else
    let (result, newAcc) := modalApplyOneS4Anc φ₀ keys spine sf b acc
    let (keys', spine', redirects') :=
      match sf.sign, sf.formula with
      | .neg, .box φ =>
        match bwAnc φ₀ b keys spine .neg φ sf.label with
        | some wBlock => (keys, spine, redirects ++ [(sf.label, wBlock)])
        | none =>
          (keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .neg φ sf.label)],
            spine ++ [(modalNextWorld b, sf.label)], redirects)
      | .pos, .diamond φ =>
        match bwAnc φ₀ b keys spine .pos φ sf.label with
        | some wBlock => (keys, spine, redirects ++ [(sf.label, wBlock)])
        | none =>
          (keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .pos φ sf.label)],
            spine ++ [(modalNextWorld b, sf.label)], redirects)
      | _, _ => (keys, spine, redirects)
    match result with
    | .linear newForms => some ([newForms ++ b], [e ++ [sf]], newAcc, keys', spine', redirects')
    | .branching branches =>
      some (branches.map (· ++ b), branches.map (fun _ => e ++ [sf]), newAcc, keys', spine',
        redirects')
    | .persistent newForms => some ([newForms ++ b], [e], newAcc, keys', spine', redirects')
    | .notApplicable => none

/-- Unordered ancestor stepper: plain `b.findSome?` traversal (mirrors
`modalStepBranchS4Keyed`). -/
def stepAnc (φ₀ : P) (b e : List (SignedFormula P WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × P))) (spine : Spine)
    (redirects : List (WorldIndex × WorldIndex)) : Option StepResult :=
  b.findSome? (stepBodyAnc φ₀ b e acc keys spine redirects)

/-- Ordered (settled-context-scheduling) ancestor stepper: non-minting candidates first,
falling back to the plain traversal once settled (mirrors `modalStepBranchS4KeyedOrdered`). -/
def stepAncOrdered (φ₀ : P) (b e : List (SignedFormula P WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × P))) (spine : Spine)
    (redirects : List (WorldIndex × WorldIndex)) : Option StepResult :=
  match (nonMintCandidatesAnc φ₀ keys spine b e acc).findSome?
      (stepBodyAnc φ₀ b e acc keys spine redirects) with
  | some r => some r
  | none => stepAnc φ₀ b e acc keys spine redirects

/-! ### Measurement D instrumentation -/

/-- `true` iff two DIFFERENT recorded worlds share an equal key -- i.e. global `keysDistinct`
is actually violated at this state. -/
def keysDistinctBroken (keys : List (WorldIndex × Finset (Sign × P))) : Bool :=
  keys.any (fun wk1 => keys.any (fun wk2 => (wk1.1 != wk2.1) && decide (wk1.2 = wk2.2)))

/-- Max spine-ancestor-chain length over every recorded key's world. -/
def maxSpineDepth (spine : Spine) (keys : List (WorldIndex × Finset (Sign × P))) : Nat :=
  (keys.map (fun wk => (spineAncestors spine wk.1).length)).foldl max 0

/-- Max out-degree over every world mentioned in `acc`. -/
def maxOutDegree (acc : Accessibility) : Nat :=
  (acc.allWorlds.map (fun w => (acc.edges.filter (fun e => e.1 == w)).length)).foldl max 0

/-- The upward box-propagation test for a blocked redirect `src -> wBlock`: for every signed
subformula `□ψ` of `φ₀`, `T(□ψ)@src ∈ b → T(□ψ)@wBlock ∈ b`. Restricted to `modalSubfmls φ₀`
(a computable superset of every box formula that can appear, mirroring `s4witness.lean`'s
`probePairs` technique). -/
def boxUpwardHolds (φ₀ : P) (b : List (SignedFormula P WorldIndex)) (src wBlock : WorldIndex) :
    Bool :=
  (modalSubfmls φ₀).all (fun ψ =>
    !(b.any (· == (⟨.pos, .box ψ, src⟩ : SignedFormula P WorldIndex))) ||
      b.any (· == (⟨.pos, .box ψ, wBlock⟩ : SignedFormula P WorldIndex)))

structure DStats where
  maxDepth : Nat := 0
  maxOutDeg : Nat := 0
  keysBroken : Bool := false
  redirectPass : Nat := 0
  redirectFail : Nat := 0
  deriving Inhabited

def combineStats (a b : DStats) : DStats :=
  { maxDepth := max a.maxDepth b.maxDepth
    maxOutDeg := max a.maxOutDeg b.maxOutDeg
    keysBroken := a.keysBroken || b.keysBroken
    redirectPass := a.redirectPass + b.redirectPass
    redirectFail := a.redirectFail + b.redirectFail }

def leafStats (φ₀ : P) (st : StAnc) : DStats :=
  { maxDepth := maxSpineDepth st.spine st.keys
    maxOutDeg := maxOutDegree st.acc
    keysBroken := keysDistinctBroken st.keys
    redirectPass := (st.redirects.filter (fun r => boxUpwardHolds φ₀ st.b r.1 r.2)).length
    redirectFail := (st.redirects.filter (fun r => !boxUpwardHolds φ₀ st.b r.1 r.2)).length }

/-! ### Drivers -/

/-- Unordered ancestor driver, verdict only (used for the C sweep's unordered column; no stats
tracked to keep the large sweep fast). -/
partial def dfsAncVerdict (φ₀ : P) (fuel : Nat) (st : StAnc) : Option Bool :=
  if isModalClosed st.b then some true
  else match fuel with
  | 0 => none
  | fuel' + 1 =>
    match stepAnc φ₀ st.b st.e st.acc st.keys st.spine st.redirects with
    | none => some false
    | some (bs, es, acc', keys', spine', redirects') =>
      let rec go (bs : List (List (SignedFormula P WorldIndex)))
          (es : List (List (SignedFormula P WorldIndex))) : Option Bool :=
        match bs, es with
        | [], _ => some true
        | b' :: rbs, e' :: res =>
          match dfsAncVerdict φ₀ fuel' ⟨b', e', acc', keys', spine', redirects'⟩ with
          | some true => go rbs res
          | x => x
        | _, _ => some true
      go bs es

def tabClosesAncUnordered (φ₀ : P) (fuel : Nat) : Option Bool :=
  dfsAncVerdict φ₀ fuel (initStAnc φ₀)

/-- Ordered ancestor driver, verdict AND aggregated `DStats` (max over/along the explored
paths, matching the existing drivers' short-circuit-on-first-non-closed-child semantics: only
visited leaves contribute to the aggregate). -/
partial def dfsAncOrdered (φ₀ : P) (fuel : Nat) (st : StAnc) : Option Bool × DStats :=
  if isModalClosed st.b then (some true, leafStats φ₀ st)
  else match fuel with
  | 0 => (none, leafStats φ₀ st)
  | fuel' + 1 =>
    match stepAncOrdered φ₀ st.b st.e st.acc st.keys st.spine st.redirects with
    | none => (some false, leafStats φ₀ st)
    | some (bs, es, acc', keys', spine', redirects') =>
      let rec go (bs : List (List (SignedFormula P WorldIndex)))
          (es : List (List (SignedFormula P WorldIndex))) : Option Bool × DStats :=
        match bs, es with
        | [], _ => (some true, {})
        | b' :: rbs, e' :: res =>
          match dfsAncOrdered φ₀ fuel' ⟨b', e', acc', keys', spine', redirects'⟩ with
          | (some true, s) =>
            let (r2, s2) := go rbs res
            (r2, combineStats s s2)
          | (x, s) => (x, s)
        | _, _ => (some true, {})
      go bs es

def tabClosesAncOrdered (φ₀ : P) (fuel : Nat) : Option Bool × DStats :=
  dfsAncOrdered φ₀ fuel (initStAnc φ₀)

/-- Baseline: the shipped, unrestricted keyed driver (`modalStepBranchS4Keyed`), called
directly -- NOT reimplemented -- so it is a genuine control, not a second copy of the same
logic. Mirrors `s4probe.lean`'s `dfsKeyed`/`tabClosesKeyed`. -/
partial def dfsBaseline (φ₀ : P) (fuel : Nat) (b e : List (SignedFormula P WorldIndex))
    (acc : Accessibility) (keys : List (WorldIndex × Finset (Sign × P))) : Option Bool :=
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
          match dfsBaseline φ₀ fuel' b2 e2 acc' keys' with
          | some true => go rbs res
          | x => x
        | _, _ => some true
      go bs es

def tabClosesBaseline (φ₀ : P) (fuel : Nat) : Option Bool :=
  dfsBaseline φ₀ fuel [⟨.neg, φ₀, 0⟩] [] Accessibility.empty
    [((0 : WorldIndex), (∅ : Finset (Sign × P)))]

/-! ### The counterexample and axiom instances (verbatim from report 01 / `s4probe.lean`) -/

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

/-! ### Measurement A: soundness -- cex must be OPEN under the ancestor-ordered driver -/

#eval IO.println
  s!"A: baseline(cex,fuel400)={tabClosesBaseline cex 400}  ancestor-ordered(cex,fuel400)={(tabClosesAncOrdered cex 400).1}  (expect ancestor-ordered = some false)"

/-! ### Measurement B: validity -- T, 4, K axiom instances must be CLOSED -/

#eval IO.println
  s!"B: T axiom ancestor-ordered(fuel400)={(tabClosesAncOrdered tAxiom 400).1}  (expect some true)"
#eval IO.println
  s!"B: 4 axiom ancestor-ordered(fuel400)={(tabClosesAncOrdered fourAxiom 400).1}  (expect some true)"
#eval IO.println
  s!"B: K axiom ancestor-ordered(fuel400)={(tabClosesAncOrdered kAxiom 400).1}  (expect some true)"

/-! ### Formula enumeration (verbatim from `s4probe.lean`) -/

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

/-! ### Measurement C (differential sweep) and D (invariant damage), one combined pass -/

structure SweepRow where
  base : Option Bool
  ancU : Option Bool
  ancO : Option Bool
  stats : DStats

def sweepRowsAnc (natoms sz fuel : Nat) : List SweepRow :=
  (allUpTo natoms sz).map (fun f =>
    let base := tabClosesBaseline f fuel
    let ancU := tabClosesAncUnordered f fuel
    let (ancO, stats) := tabClosesAncOrdered f fuel
    { base := base, ancU := ancU, ancO := ancO, stats := stats })

/-! Named predicates/projections (not inline lambdas) for the aggregation below -- inline
lambdas over `SweepRow` fields inside a `#eval do` block leave `r`'s type unresolved during
elaboration (observed directly while developing this probe); named top-level functions sidestep
it, matching `s4probe.lean`'s established pattern (`isOldClosed` etc.). -/

def rowBaseClosed (r : SweepRow) : Bool := r.base == some true
def rowBaseOpen (r : SweepRow) : Bool := r.base == some false
def rowBaseFuel (r : SweepRow) : Bool := r.base == none
def rowAncUClosed (r : SweepRow) : Bool := r.ancU == some true
def rowAncUOpen (r : SweepRow) : Bool := r.ancU == some false
def rowAncUFuel (r : SweepRow) : Bool := r.ancU == none
def rowAncOClosed (r : SweepRow) : Bool := r.ancO == some true
def rowAncOOpen (r : SweepRow) : Bool := r.ancO == some false
def rowAncOFuel (r : SweepRow) : Bool := r.ancO == none
def rowUOpenToClosed (r : SweepRow) : Bool := r.base == some false && r.ancU == some true
def rowUClosedToOpen (r : SweepRow) : Bool := r.base == some true && r.ancU == some false
def rowOOpenToClosed (r : SweepRow) : Bool := r.base == some false && r.ancO == some true
def rowOClosedToOpen (r : SweepRow) : Bool := r.base == some true && r.ancO == some false
def rowKeysBroken (r : SweepRow) : Bool := r.stats.keysBroken
def rowMaxDepth (r : SweepRow) : Nat := r.stats.maxDepth
def rowMaxOutDeg (r : SweepRow) : Nat := r.stats.maxOutDeg
def rowRedirectPass (r : SweepRow) : Nat := r.stats.redirectPass
def rowRedirectFail (r : SweepRow) : Nat := r.stats.redirectFail

#eval do
  let rows := sweepRowsAnc 2 6 100
  let total := rows.length
  let baseClosed := (rows.filter rowBaseClosed).length
  let baseOpen := (rows.filter rowBaseOpen).length
  let baseFuel := (rows.filter rowBaseFuel).length
  let ancUClosed := (rows.filter rowAncUClosed).length
  let ancUOpen := (rows.filter rowAncUOpen).length
  let ancUFuel := (rows.filter rowAncUFuel).length
  let ancOClosed := (rows.filter rowAncOClosed).length
  let ancOOpen := (rows.filter rowAncOOpen).length
  let ancOFuel := (rows.filter rowAncOFuel).length
  let uOpenToClosed := (rows.filter rowUOpenToClosed).length
  let uClosedToOpen := (rows.filter rowUClosedToOpen).length
  let oOpenToClosed := (rows.filter rowOOpenToClosed).length
  let oClosedToOpen := (rows.filter rowOClosedToOpen).length
  let keysBrokenCount := (rows.filter rowKeysBroken).length
  let overallMaxDepth := (rows.map rowMaxDepth).foldl max 0
  let overallMaxOutDeg := (rows.map rowMaxOutDeg).foldl max 0
  let totalRedirectPass := (rows.map rowRedirectPass).foldl (· + ·) 0
  let totalRedirectFail := (rows.map rowRedirectFail).foldl (· + ·) 0
  IO.println s!"C: total={total}"
  IO.println s!"C: baseline        (closed={baseClosed}, open={baseOpen}, fuelExhausted={baseFuel})  (expect 1650/6882/0)"
  IO.println s!"C: ancestor-unord. (closed={ancUClosed}, open={ancUOpen}, fuelExhausted={ancUFuel})"
  IO.println s!"C: ancestor-ord.   (closed={ancOClosed}, open={ancOOpen}, fuelExhausted={ancOFuel})"
  IO.println s!"C: unordered vs baseline: openToClosed(COMPLETENESS-only, ok)={uOpenToClosed}  closedToOpen(MUST BE 0)={uClosedToOpen}"
  IO.println s!"C: ordered   vs baseline: openToClosed(COMPLETENESS-only, ok)={oOpenToClosed}  closedToOpen(MUST BE 0)={oClosedToOpen}"
  IO.println s!"D(i): formulas where global keysDistinct is broken = {keysBrokenCount} / {total}"
  IO.println s!"D(ii): overall max spine depth observed = {overallMaxDepth}"
  IO.println s!"D(iii): overall max out-degree observed = {overallMaxOutDeg}"
  IO.println s!"D(iv): blocked-redirect upward box-propagation test: pass={totalRedirectPass} fail={totalRedirectFail}"
