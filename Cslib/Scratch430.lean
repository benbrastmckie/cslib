import Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion
import Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness

open Cslib.Logic.PL
open Cslib.Logic.Tableau

namespace Scratch430

/-- atoms -/
def A : Proposition Nat := .atom 0
def B : Proposition Nat := .atom 1
def C : Proposition Nat := .atom 2
def D : Proposition Nat := .atom 3
def E : Proposition Nat := .atom 4

/-- Per-branch saturator: identical rule pipeline to `intExpandBranches`
    (same `applyPersistenceFixpoint`, `intStepBranch`, `closurePred`, edge bookkeeping),
    but DFS over beta-splits, returning EVERY open saturated leaf together with its edge set. -/
partial def satBranch (b : IBranch Nat) (expanded : List (ISF Nat)) (nw : Nat) (edges : IEdges)
    (fuel : Nat) (closurePred : IBranch Nat → Bool) : List (IBranch Nat × IEdges) :=
  match fuel with
  | 0 => if closurePred b then [] else [(b, edges)]
  | fuel' + 1 =>
    let bPers := applyPersistenceFixpoint b edges (fuel' + 1)
    if closurePred bPers then []
    else match intStepBranch bPers expanded nw with
      | none => [(bPers, edges)]
      | some (.linearResult newForms nw' newEdge, newExp) =>
        let edges' := match newEdge with | none => edges | some ed => edges ++ [ed]
        satBranch (Branch.extendMany bPers newForms) newExp nw' edges' fuel' closurePred
      | some (.branchingResult branches' nw', newExp) =>
        (branches'.map (Branch.extendMany bPers ·)).flatMap (fun b' =>
          satBranch b' newExp nw' edges fuel' closurePred)
      | some (.notApplicable, _) => [(bPers, edges)]

def allOpenInt (φ : Proposition Nat) : List (IBranch Nat × IEdges) :=
  satBranch [⟨.neg, φ, 0⟩] [] 1 [] (2 ^ (2 * φ.complexity + 2)) isIntuitionisticallyClosed

/-- worlds occurring on a branch -/
def worldsOf (b : IBranch Nat) : List Nat := (b.map (·.label)).eraseDups

/-- atoms occurring on a branch -/
def atomsOf (b : IBranch Nat) : List Nat :=
  (b.filterMap (fun sf => match sf.formula with | .atom p => some p | _ => none)).eraseDups

/-- raw valuation as a Bool (matches `intExtractValuation` definitionally) -/
def rawval (b : IBranch Nat) (w p : Nat) : Bool :=
  b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w)

/-- Readable summary: edges, plus per-world list of positive atoms. -/
def summary (be : IBranch Nat × IEdges) : IEdges × List (Nat × List Nat) :=
  let (b, edges) := be
  (edges, (worldsOf b).map (fun w =>
    (w, (atomsOf b).filter (fun p => rawval b w p))))

/-- Find EDGE-upward-closure violations on a single (branch, edges):
    triples (p, w, w') with `isAccessible edges w w'` (i.e. w ≤ w'), rawval@w true, rawval@w' false. -/
def edgeUCViolations (be : IBranch Nat × IEdges) : List (Nat × Nat × Nat) :=
  let (b, edges) := be
  let ws := worldsOf b
  let ps := atomsOf b
  ps.flatMap (fun p =>
    ws.flatMap (fun w =>
      ws.filterMap (fun w' =>
        if isAccessible edges w w' && rawval b w p && !(rawval b w' p)
        then some (p, w, w') else none)))

/-- ≤-on-ℕ upward-closure violations (the seed's naive order), for contrast. -/
def natUCViolations (be : IBranch Nat × IEdges) : List (Nat × Nat × Nat) :=
  let (b, _) := be
  let ws := worldsOf b
  let ps := atomsOf b
  ps.flatMap (fun p =>
    ws.flatMap (fun w =>
      ws.filterMap (fun w' =>
        if w ≤ w' && rawval b w p && !(rawval b w' p) then some (p, w, w') else none)))

/-! ## Experiment 1 cases -/

/-- A's counterexample: (a→b) ∨ (c→d) -- expect siblings, ≤-on-ℕ fails, edge-UC should hold. -/
def phi1 : Proposition Nat := .or (.imp A B) (.imp C D)

/-- Disjunct under an implication antecedent that creates a child:
    ((c∨d) → (e → bot))  -- world 1 gets T(c∨d), then child world 2. -/
def phi2 : Proposition Nat := .imp (.or C D) (.imp E .bot)

/-- Nested: a→b with a disjunctive antecedent landing in a created world, plus a deeper child. -/
def phi3 : Proposition Nat := .imp (.imp (.or C D) E) (.imp A B)

/-- ENGINEERED to break edge-UC: at world 1 (born), the antecedent `a ∧ (a → (c∨d))`
    yields T(a)@1 and T(a→(c∨d))@1; an F(→) consequent `g→h` creates child world 2 which
    copies the (possibly unsplit) `c∨d`; worlds 1 and 2 then split `c∨d` INDEPENDENTLY,
    so a branch with T(c)@1 and T(d)@2 (edge 1≤2) would violate edge-UC. -/
def G : Proposition Nat := .atom 5
def H : Proposition Nat := .atom 6
def phi4 : Proposition Nat :=
  .imp (.and A (.imp A (.or C D))) (.imp G H)

/-- Variant: disjunction directly as born antecedent but with the child creator first in a
    nested consequent so the split might lag. ((g→h) is forced false creating a child). -/
def phi5 : Proposition Nat :=
  .imp (.imp A (.or C D)) (.imp G H)

def report (name : String) (φ : Proposition Nat) : String :=
  let opens := allOpenInt φ
  let summaries := opens.map summary
  let edgeV := opens.map edgeUCViolations
  let natV := opens.map natUCViolations
  s!"{name}: #open={opens.length}\n  summaries={summaries}\n  edgeUC_violations={edgeV}\n  natUC_violations={natV}"

#eval report "phi1 (a→b)∨(c→d)" phi1
#eval report "phi2 (c∨d)→(e→⊥)" phi2
#eval report "phi3 ((c∨d)→e)→(a→b)" phi3
#eval report "phi4 engineered split-after-child" phi4
#eval report "phi5 (a→(c∨d))→(g→h)" phi5

/-! ## Experiment 2 — Route A closure valuation (Bool) and Route C containment order -/

/-- Closure valuation as Bool: `p` holds at `w` iff some edge-ancestor `w0` (w0 ≤ w) has raw `p`. -/
def rawvalUC (b : IBranch Nat) (edges : IEdges) (w p : Nat) : Bool :=
  (worldsOf b).any (fun w0 => isAccessible edges w0 w && rawval b w0 p)

/-- Closure-valuation edge-UC violations (should be EMPTY everywhere by construction). -/
def closureUCViolations (be : IBranch Nat × IEdges) : List (Nat × Nat × Nat) :=
  let (b, edges) := be
  let ws := worldsOf b
  let ps := atomsOf b
  ps.flatMap (fun p =>
    ws.flatMap (fun w =>
      ws.filterMap (fun w' =>
        if isAccessible edges w w' && rawvalUC b edges w p && !(rawvalUC b edges w' p)
        then some (p, w, w') else none)))

/-- Containment order (Route C) as Bool: w ⊑ w' iff every pos atom at w is also at w'. -/
def subseteqAtoms (b : IBranch Nat) (w w' : Nat) : Bool :=
  (atomsOf b).all (fun p => !(rawval b w p) || rawval b w' p)

/-- For each open branch: list the sat_fimp/world-creating EDGES (child,parent) that FAIL
    containment, i.e. parent ⋢ child. Nonempty ⇒ Route C's imp-F witness is broken. -/
def containmentBadEdges (be : IBranch Nat × IEdges) : List (Nat × Nat) :=
  let (b, edges) := be
  edges.filterMap (fun (child, parent) =>
    if subseteqAtoms b parent child then none else some (parent, child))

/-- raw NEGATIVE atom occurrence: F(atom p)@w on branch. -/
def rawvalNeg (b : IBranch Nat) (w p : Nat) : Bool :=
  b.any (fun sf => sf.sign == .neg && sf.formula == .atom p && sf.label == w)

/-- KEY Route-A residual risk: F(p)@w on branch AND some edge-ancestor of w carries T(p).
    Nonempty ⇒ closure valuation forces p at w while branch says F(p)@w ⇒ truthLemma F-atom breaks. -/
def closureFatomConflicts (be : IBranch Nat × IEdges) : List (Nat × Nat) :=
  let (b, edges) := be
  let ws := worldsOf b
  let ps := atomsOf b
  ps.flatMap (fun p =>
    ws.filterMap (fun w =>
      if rawvalNeg b w p && rawvalUC b edges w p then some (p, w) else none))

#eval "phi1/2/3/4/5 closure F-atom conflicts (nonempty ⇒ Route A truthLemma F-atom breaks):"
#eval ([phi1, phi2, phi3, phi4, phi5].map (fun φ => (allOpenInt φ).map closureFatomConflicts))

#eval "=== Experiment 2 ==="
#eval "phi4 closure-valuation edge-UC violations (expect all []):"
#eval (allOpenInt phi4).map closureUCViolations
#eval "phi4 containment-bad edges per branch (parent ⋢ child); nonempty ⇒ Route C imp-F broken:"
#eval (allOpenInt phi4).map containmentBadEdges
#eval "phi1 containment-bad edges (siblings; edges 1,2 both children of 0):"
#eval (allOpenInt phi1).map containmentBadEdges

/-! ## Route A type-level checks: Preorder via ReflTransGen, IValid instantiation -/

/-- Edge accessibility as a Prop preorder relation. -/
def IAccessibleP (edges : IEdges) : Nat → Nat → Prop :=
  Relation.ReflTransGen (fun p c => (c, p) ∈ edges)

/-- It forms a Preorder (refl + trans are free from ReflTransGen). -/
def edgePreorder (edges : IEdges) : Preorder Nat where
  le := IAccessibleP edges
  lt := fun a b => IAccessibleP edges a b ∧ ¬ IAccessibleP edges b a
  le_refl := fun _ => Relation.ReflTransGen.refl
  le_trans := fun _ _ _ h1 h2 => Relation.ReflTransGen.trans h1 h2
  lt_iff_le_not_ge := fun _ _ => Iff.rfl

/-- Closure valuation (Prop), upward-closed by transitivity of ReflTransGen. -/
def valUCProp (b : IBranch Nat) (edges : IEdges) (w : Nat) (p : Nat) : Prop :=
  ∃ w0, IAccessibleP edges w0 w ∧ intExtractValuation b w0 p

theorem valUCProp_upward (b : IBranch Nat) (edges : IEdges) {w w' p}
    (h : IAccessibleP edges w w') :
    valUCProp b edges w p → valUCProp b edges w' p := by
  rintro ⟨w0, hw0, hv⟩
  exact ⟨w0, hw0.trans h, hv⟩

/-- IValid-style instantiation typechecks at World = ℕ with the edge Preorder. -/
example (b : IBranch Nat) (edges : IEdges) (w : Nat) (φ : Proposition Nat) : Prop :=
  letI : Preorder Nat := edgePreorder edges
  IForces (fun w p => valUCProp b edges w p) (fun _ => False) w φ

end Scratch430
