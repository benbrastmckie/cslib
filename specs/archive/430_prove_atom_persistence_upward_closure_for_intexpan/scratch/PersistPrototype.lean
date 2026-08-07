import Cslib.Init
import Cslib.Logics.Propositional.Tableau.Intuitionistic.Rules
import Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion

/-!
# Gate B prototype: single loop-back hop persistence (scratch only, task-territory scoped)

No algorithm change. Tests whether the `Sfor`-containment established at a reuse-blocking
event (real code: `Scheme.lean`'s `key` induction, the reuse arm around `intFImpReuseWitnessAnc?`)
survives from the blocking-time branch snapshot to the FINAL branch, for a single recorded
loop-back pair `(x, l)`.
-/

open Cslib.Logic.PL

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-- Forest/chain comparability along RAW edges: any two raw-ancestors of a common world are
comparable. NOT proved here -- already available, in substance, from `Scheme.lean`'s PRIVATE
`IWorldHist` machinery (`par : Nat → Nat`, `parAncestor`, `parAncestor_le`; landed for DP-2).
Phase 5 needs to export a public corollary of this shape rather than re-derive it from scratch:
`par` being a genuine total function (each created world has exactly one parent) makes any two
`parAncestor`-ancestors of a common world comparable for free, and `IWorldHist`'s (H1-acc)
clause already links `parAncestor` to `isAccessible`. -/
def ForestComparable (edges : IEdges) : Prop :=
  ∀ w x l : Nat, isAccessible edges w l = true → isAccessible edges x l = true →
    isAccessible edges w x = true ∨ isAccessible edges x w = true

/-- One round of T-imp-rule successor persistence: `χ` is added to `posFormulasAt b l` by
firing `T(φ → χ)@w ∈ b` (`w` raw-accessible to `l`) against `T(φ)@l ∈ b`. Mirrors `intTImpRule`'s
own firing condition. -/
def TImpSuccessor (b : IBranch Atom) (edges : IEdges) (l : Nat) (χ : Proposition Atom) : Prop :=
  ∃ φ w, (⟨.pos, .imp φ χ, w⟩ : ISF Atom) ∈ b ∧ isAccessible edges w l = true ∧
    (⟨.pos, φ, l⟩ : ISF Atom) ∈ b

/-- Self-copy-reach: `T(φ → χ)@w`'s own positive-formula content reaches every raw-descendant
of `w`. This is exactly what Phase 3's reinstated self-copy channel (V1/V4) gives at a genuine
`applyAllTImpRules` fixpoint (Phase 4's deliverable) -- NOT proved here (no algorithm change in
this Gate), taken as a documented hypothesis standing in for the Phase-3/4 result. -/
def SelfCopyReach (b : IBranch Atom) (edges : IEdges) : Prop :=
  ∀ φ χ w w', (⟨.pos, .imp φ χ, w⟩ : ISF Atom) ∈ b → isAccessible edges w w' = true →
    (⟨.pos, .imp φ χ, w'⟩ : ISF Atom) ∈ b

/-- Origin-traceability: every positive formula present at any world `w` traces back to an
"origin" world `w0` raw-accessible to `w` (`isAccessible edges w0 w`) at which the SAME formula
was either (a) part of the initial decomposition, or (b) the target of a `TImpSuccessor` step
from a STRICTLY-earlier occurrence. This is exactly the provenance shape `IWorldHist`'s
`fire`/`par`/`obl` witness functions already record for MINT events (task 585, DP-2) --
Phase 5's job is to repurpose that landed machinery for positive-formula content generally,
not just for the mint obligations it currently tracks. NOT proved here; recorded as the
precise shape of the remaining Phase 5 obligation this prototype could not discharge from
`SelfCopyReach` alone. -/
def OriginTraceable (b : IBranch Atom) (edges : IEdges) : Prop :=
  ∀ ψ w, (⟨.pos, ψ, w⟩ : ISF Atom) ∈ b →
    ∃ w0, isAccessible edges w0 w = true ∧ isAccessible edges w0 w = true  -- placeholder shape

/-- **Gate B core step**: given the blocking-time containment `hcont`, chain comparability, and
the fixpoint-level self-copy-reach fact, a SINGLE `TImpSuccessor` addition to `l` survives to
`x` in the `w ≤ x` sub-case (`w` raw-descendant of `x`); the `x ≤ w` sub-case (`x` a raw-
ancestor of `w`) is the genuine remaining difficulty -- see the doc comment and the `sorry`
below, which marks EXACTLY the gap this prototype could not close from `SelfCopyReach` alone
(it requires `OriginTraceable`, not just forward self-copy, since content does not flow
backward from `w` to its ancestor `x`). -/
theorem gateB_single_hop_successor
    (edges : IEdges) (b : IBranch Atom) (x l : Nat)
    (hcomp : ForestComparable edges)
    (hacc : isAccessible edges x l = true)
    (hcont : ∀ ψ, (⟨.pos, ψ, l⟩ : ISF Atom) ∈ b → (⟨.pos, ψ, x⟩ : ISF Atom) ∈ b)
    (hcopy : SelfCopyReach b edges)
    (horigin : OriginTraceable b edges)
    (χ : Proposition Atom)
    (hsucc : TImpSuccessor b edges l χ) :
    (⟨.pos, χ, x⟩ : ISF Atom) ∈ b ∨
      ∃ φ, (⟨.pos, .imp φ χ, x⟩ : ISF Atom) ∈ b ∧ (⟨.pos, φ, x⟩ : ISF Atom) ∈ b := by
  obtain ⟨φ, w, himp, hwl, hφl⟩ := hsucc
  have hφx : (⟨.pos, φ, x⟩ : ISF Atom) ∈ b := hcont φ hφl
  rcases hcomp w x l hwl hacc with hwx | hxw
  · -- w ≤ x: T(φ→χ)@w reaches x directly via SelfCopyReach (descendant sub-case, clean).
    right
    exact ⟨φ, hcopy φ χ w x himp hwx, hφx⟩
  · -- x ≤ w: w is a raw-descendant of x. `SelfCopyReach` alone does not place a copy of
    -- `T(φ→χ)` at x from w's occurrence (persistence is forward-only; content at a
    -- descendant does not flow back to an ancestor). Closing this case needs
    -- `T(φ→χ)`'s OWN origin `w0` (via `OriginTraceable`) to satisfy `isAccessible edges w0 x`,
    -- at which point `SelfCopyReach` (fired from `w0`, not `w`) delivers the copy to `x`
    -- directly. `OriginTraceable`'s placeholder shape above is not yet strong enough to
    -- supply that fact syntactically -- recording this as the concrete, precise remaining
    -- Phase 5 obligation rather than papering over it.
    sorry

/-!
## Gate B verdict

**Not refuted.** No counterexample was found (contrast Option 2 / the quotient route, which
carries a CONCRETE, proven counterexample -- `intBlockRep`'s non-monotonicity). The descendant
sub-case (`w ≤ x`) closes cleanly from `SelfCopyReach` alone. The ancestor sub-case (`x ≤ w`)
requires origin-tracing: `T(φ→χ)`'s OWN provenance must be shown raw-accessible to `x`, not
just checked against `w`. This is NOT a fresh, unbuilt requirement -- `Scheme.lean`'s private
`IWorldHist` invariant (task 585, DP-2) already threads exactly this shape of provenance data
(`par`/`obl`/`fire`/`sfor` witness functions, one per created world) through the SAME forward
induction Phase 5 must extend. The likely Phase 5 route is therefore to EXTEND `IWorldHist`'s
existing witness functions (or a sibling invariant threaded alongside it) to cover arbitrary
positive-formula content, not to invent new provenance machinery from nothing.

**Verdict: PASS (conditional).** Proceed to Phase 3. The remaining gap is real, substantial,
and comparable in scope to the existing `IWorldHist`/`IAllAccessConsistent` threading -- not a
quick corollary -- but it is a BUILD task, not a refutation.
-/
