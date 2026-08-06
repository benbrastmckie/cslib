/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Logics.Modal.Tableau.LoopChecking
public meta import Cslib.Logics.Modal.Tableau.LoopChecking
import Cslib.Logics.Modal.Tableau.FrameCompleteness
public meta import Cslib.Logics.Modal.Tableau.FrameCompleteness

/-! # S4 Keyed Loop-Check Guard Regression Corpus

Executable regression corpus witnessing that `modalTableauS4Keyed_sound` is false as stated
for the shipped keyed S4 driver: a node-size-19 formula closes under
`modalExpandBranchesS4Keyed` while having an explicit 3-world reflexive-transitive
countermodel, so the formula is not `s4Valid`. `#eval` **does** reduce (it uses the compiler,
not the kernel) but only works from `CslibTests/`, not from inside
`Cslib/Logics/Modal/Tableau/` itself -- this is why the corpus lives here rather than beside
the driver, mirroring `CslibTests/TableauConformance.lean`'s rationale for the same idiom.

## The counterexample

Over two atoms `p0`, `p1`, with `¬X := X → ⊥`:

```
αA := □p0 ∨ ¬¬◇p1
αL := □p0 ∨ ¬□p1
cex := □αA ∨ □αL
```

`cex` has a 3-world reflexive-transitive countermodel: `R = {(0,0), (0,1), (0,2), (1,1),
(2,2)}`, with `p1` true at world `1` only and `p0` false everywhere. World `2`'s only
successor is itself, where `p1` is false, so `□p0` and `¬¬◇p1` are both false at `2`, making
`αA` false at `2` and hence `□αA` false at `0`. World `1`'s only successor is itself, where
`p1` holds, so `□p0` is false and `¬□p1` is false at `1`, making `αL` false at `1` and hence
`□αL` false at `0`. So `cex` is false at world `0` of a genuine S4 (reflexive-transitive)
model, and is therefore not `s4Valid`.

Nonetheless the shipped keyed driver closes `cex`. The refutation trace mints world `1` from
`F(□αA)@0`, then mints world `2` from `F(□p0)@1` with recorded key `{(neg, p0)}` before world
`1`'s `F(¬¬◇p1)@1` has expanded. World `2` subsequently accumulates `F(p1)@2` from world `1`'s
later expansion, but its **recorded key never updates** ("staleness"). Separately, world `3`
(minted from `F(□αL)@0`) computes a prospective birth content of `{(neg, p0)}` from
`F(□p0)@3`, which matches world `2`'s **stale** recorded key, so `blockingWorldS4Keyed` returns
`some 2` and adds the edge `3 → 2` -- **with no reachability restriction ensuring `2` is
actually accessible from `3`** ("no reachability restriction"). `F(¬□p1)@3` then expands to
`T(□p1)@3`, which is `.persistent` and so transmits along the unjustified edge `3 → 2`, adding
`T(p1)@2` alongside the pre-existing `F(p1)@2`. The branch closes -- spuriously, since world `2`
cannot simultaneously satisfy `¬p1` (required as world `1`'s successor) and `p1` (required as
world `3`'s successor).

Both defects are independently real (staleness: the live-set guard `blockingWorldS4` would
correctly reject this specific block; no-reachability-restriction: the redirect edge asserts
`m.r (f 3) (f 2)`, which nothing in an arbitrary reflexive-transitive model supplies), and this
counterexample exercises both at once. See `blockingWorldS4Keyed`'s docstring
(`LoopChecking.lean`) for the corrected account of both defects.

## KNOWN-UNSOUND row, historical

The row asserting `modalExpandBranchesS4Keyed cex ... = CLOSED` below records the **current,
unsound** verdict of the shipped (unordered) driver, not the semantically correct verdict
(`OPEN`, since `cex` is not `s4Valid`). This row is kept exactly as-is -- `modalStepBranchS4Keyed`
/ `modalExpandBranchesS4Keyed` are not touched or retired until the destructive Phase 15, so
their behaviour on `cex` remains what it always was and this row still correctly documents it.
Any future change to `modalStepBranchS4Keyed`/`blockingWorldS4Keyed` that silently reopens this
exact closure is caught immediately.

**The successor driver fixes this.** `modalExpandBranchesS4KeyedOrdered` (settled-context
scheduling: non-minting candidates are exhausted before any minting fallback fires) does **not**
close `cex` -- see the "Ordered driver" section below. It is the sound-on-this-example successor
that the rest of this task's soundness line is built against. -/

namespace CslibTests.S4LoopGuardRegression

open Cslib.Logic.Modal Cslib.Logic.Tableau Cslib.Logic.Modal.Tableau

/-- The atom type used throughout this corpus. -/
abbrev P := Proposition Nat

/-- `String`-valued verdict adapter for `ModalTableauResult`: neither `Repr` nor `BEq` is
derived for the result type, so a direct `#guard` is unusable; rendering to `String` makes
`#guard_msgs in #eval` the assertion route, exactly as `TableauConformance.lean`'s
`temporalVerdict`/`intVerdict`. Test-only: intentionally not exposed from `Cslib/`. -/
def s4Verdict : ModalTableauResult Nat → String
  | .closed => "CLOSED"
  | .openBranch _ _ => "OPEN"

/-- The first counterexample atom. -/
def p0 : P := .atom 0

/-- The second counterexample atom. -/
def p1 : P := .atom 1

/-- Propositional negation via `X → ⊥`, test-local sugar matching the research report's
notation. -/
def nt (x : P) : P := .imp x .bot

/-- `αA := □p0 ∨ ¬¬◇p1`, false at world `2` of the countermodel. -/
def alphaA : P := .or (.box p0) (nt (nt (.diamond p1)))

/-- `αL := □p0 ∨ ¬□p1`, false at world `1` of the countermodel. -/
def alphaL : P := .or (.box p0) (nt (.box p1))

/-- `cex := □αA ∨ □αL`, the node-size-19 formula that closes under the shipped keyed driver
despite having a 3-world reflexive-transitive countermodel. See the file docstring for the
countermodel and the closing trace. -/
def cex : P := .or (.box alphaA) (.box alphaL)

/-- The initial signed branch for `cex` at world `0`. -/
def cexInitBranch : List (SignedFormula P WorldIndex) := [⟨.neg, cex, 0⟩]

/-- The initial keys list for the keyed driver: world `0` born with the empty relevant set.
An empty `keys` list would violate `S4LoopInv.keysTotal` (see `LoopChecking.lean`'s entry-point
note), so the singleton `[(0, ∅)]` is required, matching `modalTableauS4Keyed`'s own entry. -/
def cexInitKeys : List (WorldIndex × Finset (Sign × P)) :=
  [((0 : WorldIndex), (∅ : Finset (Sign × P)))]

/-! ## KNOWN-UNSOUND: the shipped keyed driver closes `cex`

See the file docstring's "KNOWN-UNSOUND row, historical" section: this is the shipped
(unordered) driver's current, unsound verdict, recorded deliberately so the checkpoint stays
green while the defect stays locked under test. `modalStepBranchS4Keyed`/
`modalExpandBranchesS4Keyed` are unchanged and unretired, so this row still correctly documents
their behaviour. -/

/-- info: "CLOSED" -/
#guard_msgs in
#eval s4Verdict (modalExpandBranchesS4Keyed cex [cexInitBranch] [[]] [Accessibility.empty]
  [cexInitKeys] 400)

/-! ## Ordered driver: `modalExpandBranchesS4KeyedOrdered` does not close `cex`

The Phase 8 empirical gate. Settled-context scheduling (`modalStepBranchS4KeyedOrdered`:
non-minting candidates are exhausted before any minting fallback fires) means world `3`'s
`F(¬¬◇p1)@1`-driven expansion of world `1`'s box context is no longer deferred behind a minting
race -- see the file docstring's "expected mechanism" note in the Phase 8 plan section. The
prospective birth content computed for `F(□p0)@3` therefore already reflects world `1`'s `p1`,
so it no longer matches world `2`'s recorded key, no redirect edge is created, and the branch
stays open. This is the fixed, sound-on-this-example successor named in the "KNOWN-UNSOUND row,
historical" section above. -/

/-- info: "OPEN" -/
#guard_msgs in
#eval s4Verdict (modalExpandBranchesS4KeyedOrdered cex [cexInitBranch] [[]] [Accessibility.empty]
  [cexInitKeys] 400)

/-! ## The live-set (non-keyed) driver does not close `cex`

Confirms empirically that this counterexample is specific to the keyed guard's staleness
defect: the live-set guard `blockingWorldS4` compares against each world's *current* relevant
set, so it would have rejected the same block. -/

/-- info: "OPEN" -/
#guard_msgs in
#eval s4Verdict (modalExpandBranchesS4 cex [cexInitBranch] [[]] [Accessibility.empty] 400)

/-! ## Controls

The B axiom is not S4-valid (S4 frames need not be symmetric) and correctly stays open. The T
axiom is S4-valid (reflexivity alone suffices) and correctly closes. Both controls confirm the
harness itself -- and the keyed driver's ordinary behaviour -- is unaffected by the
counterexample construction above. -/

/-- The B axiom `p0 → □◇p0`, not S4-valid. -/
def bAxiom : P := .imp p0 (.box (.diamond p0))

/-- The T axiom `□p0 → p0`, S4-valid. -/
def tAxiom : P := .imp (.box p0) p0

/-- info: "OPEN" -/
#guard_msgs in
#eval s4Verdict (modalExpandBranchesS4Keyed bAxiom [[⟨.neg, bAxiom, 0⟩]] [[]]
  [Accessibility.empty] [[((0 : WorldIndex), (∅ : Finset (Sign × P)))]] 400)

/-- info: "CLOSED" -/
#guard_msgs in
#eval s4Verdict (modalExpandBranchesS4Keyed tAxiom [[⟨.neg, tAxiom, 0⟩]] [[]]
  [Accessibility.empty] [[((0 : WorldIndex), (∅ : Finset (Sign × P)))]] 400)

/-! ## Controls, ordered driver

The same B/T-axiom controls against `modalExpandBranchesS4KeyedOrdered`: reordering must not
change completeness on valid/invalid axiom schemas. Both rows must agree with their unordered
counterparts immediately above. -/

/-- info: "OPEN" -/
#guard_msgs in
#eval s4Verdict (modalExpandBranchesS4KeyedOrdered bAxiom [[⟨.neg, bAxiom, 0⟩]] [[]]
  [Accessibility.empty] [[((0 : WorldIndex), (∅ : Finset (Sign × P)))]] 400)

/-- info: "CLOSED" -/
#guard_msgs in
#eval s4Verdict (modalExpandBranchesS4KeyedOrdered tAxiom [[⟨.neg, tAxiom, 0⟩]] [[]]
  [Accessibility.empty] [[((0 : WorldIndex), (∅ : Finset (Sign × P)))]] 400)

/-! ## Soundness capstone, ordered driver

Permanent type-level witness that `modalTableauS4KeyedOrdered_sound`
(`Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`) is stated over the correct
driver/entry-point pairing for this file's own `tAxiom`/`s4Valid` vocabulary. `h` is an
unproved parameter (not independently established here -- `decide`/`native_decide`/`rfl` all
stall on the fuel driver's `WellFounded.fix`, per the file docstring above and
`CslibTests/TableauConformance.lean`'s documented blocker), so this is a compile-time API/shape
regression, not a computational one: it would fail to type-check if the capstone's statement
ever drifted from `modalTableauS4KeyedOrdered φ₀ = .closed → s4Valid φ₀`. The `#eval` control
immediately above independently confirms `modalTableauS4KeyedOrdered tAxiom` actually evaluates
to `.closed`, so this hypothesis is non-vacuously satisfiable, not just well-typed. -/
example (h : modalTableauS4KeyedOrdered tAxiom = .closed) : s4Valid tAxiom :=
  modalTableauS4KeyedOrdered_sound tAxiom h

end CslibTests.S4LoopGuardRegression
