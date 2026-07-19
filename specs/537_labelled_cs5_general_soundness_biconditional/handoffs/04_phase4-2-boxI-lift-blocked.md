# Phase 4.2 [BLOCKED] Handoff: `boxI_lift` recursive tree-cascade

- **Task**: 537 - direct-route general labelled CS5 soundness (`plans/02_direct-route.md`)
- **Phase**: 4.2 ("Iterate the raise over the finite tree; close the boxI case")
- **Outcome**: `[BLOCKED]`, sanctioned per the plan's own blocked-honesty gate (not a `sorry`,
  not an undirected retry). Zero debt: build green, no `sorry`, no new axiom, `cs5FCIncest`
  unweakened, all Preserved Assets (Phases 1-4.1) unregressed.
- **What landed this dispatch**: `boxI_lift_star` (`Soundness.lean:563-654` approx, see file for
  exact lines after this commit), sorry-free, axiom-clean (`propext`/`Classical.choice`/
  `Quot.sound` only, verified via `lake env lean` on `#print axioms
  Cslib.Logic.Modal.Labelled.boxI_lift_star`).

## The exact blocker (machine-checked analysis, not hand-waving)

The plan's Phase 4.2 goal is: iterate `boxI_raise_step` (Phase 4.1, the single-neighbour raise)
"node-by-node over the finite derivation tree" to get a fully general `boxI_lift`, usable to
close the `NIK.boxI` case (`Deduction.lean:297-300`) for an ARBITRARY `Graph`. This dispatch
worked out precisely what that recursion requires and where it stops being free:

1. **Why the cascade is unavoidable.** `cs5FCIncest`'s conjuncts (`hfour`/`hsymbox`/`hincest`,
   `CS5Canonical.lean:255-260`) have no "raise-source-only, keep-target-exact" (or dually
   target-only) clause — raising one endpoint of an `r`-edge ALWAYS raises the other endpoint too
   (to some `≥`-successor, never the same value). Consequently, raising `ρ x` to an adversarial
   `w' ≥ ρ x` forces every raw-`R`-neighbour of `x` to move, and if that neighbour has neighbours
   of its own, the raise cascades recursively through the whole raw-connected component of `x` —
   confirmed necessary (not merely convenient) because `Γ`-cond survives raising "for free" via
   `ckforces_persistence`, but raw edge-cond (`∀ a b, G.R a b → r (ρ a) (ρ b)`) does NOT — it is a
   flat fact about `r`, not about `CKForces`, so it cannot be "topped up" after the fact.
2. **Why a FULLY GENERAL cascade (arbitrary finite `Graph`) is unsound without an extra
   invariant.** I constructed a concrete counterexample: the 3-cycle `x → a → b → x` (i.e.
   `G.R x a`, `G.R a b`, `G.R b x`) satisfies "each label has at most one raw-edge SOURCE per
   target" (`∀ a₁ a₂ b, G.R a₁ b → G.R a₂ b → a₁ = a₂` — a natural-looking "unique parent"
   condition) with NO violation (each of `a`, `b`, `x` has exactly one inbound edge). Yet once the
   cascade raises `x` then `a`, the newly-discovered node `b` is simultaneously constrained by
   BOTH `a → b` (raised `a`, F1-style) AND `b → x` (raised `x`, F2-style reversed) — two
   independent existential raises that are not guaranteed to coincide. Ruling this out needs a
   genuine acyclicity/rank invariant (e.g. a graded rank function `ht : Label Atom → ℕ` with
   `∀ a b, G.R a b → ht b = ht a + 1`, PLUS the unique-parent condition above, together making `G`
   a rooted forest) — not just "unique parent," which the 3-cycle shows is insufficient alone.
3. **This invariant does not exist yet anywhere in the codebase.** `Graph` (`Syntax.lean:110`)
   carries no finiteness or acyclicity field. The module's OWN docstring (`Soundness.lean`,
   "What remains", item 1: "The tree-shape invariant") already flags this exact gap as separate,
   not-yet-established work belonging to the MAIN induction (Phase 5) — "the main soundness
   induction must always instantiate this cofinite premise at a label fresh to the WHOLE
   derivation so far... This needs its own lemma/invariant, threaded through the main induction."
   Establishing a rank/depth function and unique-parent property for `Graph`, and proving it is
   maintained across every `NIK` constructor (not just `boxI`), is graph/forest formalization
   work with no existing Mathlib or CSLib scaffolding — genuinely out of Phase 4.2's single-file,
   node-level scope, and larger than this phase's ~150-300 line budget on its own.

## What IS landed and safe to build on

`boxI_lift_star` generalizes Phase 4.1's `boxI_raise_step` from ONE raw-neighbour of `x` to a
**finite `Finset` of `x`'s direct raw-neighbours** (either direction), chaining
`cs5FCIncest_lift`/`cs5FCIncest_raise` via `Finset.induction`, holding `x`'s target fixed at the
ORIGINAL raise fact throughout. This needs NO acyclicity hypothesis (it never looks past `x`'s
immediate neighbours, so no cascade/conflict can arise) and is genuine forward progress: it is
the natural finite generalization Phase 4.2's mission asked for, sorry-free and axiom-clean. It
does **not** by itself close `boxI_lift` (a neighbour's OWN further neighbours are left
unraised), which is exactly the residual gap above.

## Recommended follow-up (for the routed task)

Scoped narrowly to the `boxI` tree-lifting recursion, building on `boxI_lift_star` +
`boxI_raise_step` + `box_iff_base`/`dia_iff_base`/`box_iff_TClosure`/`dia_iff_TClosure`/
`box_gives_here` (all landed, Preserved Assets):

1. Establish a rank/depth invariant on `Graph` (or thread one through the eventual Phase 5
   induction directly, generalizing the induction's own motive to carry
   `∃ ht : Label Atom → ℕ, (∀ a b, G.R a b → ht b = ht a + 1) ∧ (∀ a₁ a₂ b, G.R a₁ b → G.R a₂ b →
   a₁ = a₂)` alongside the raw edge-cond / Γ-cond invariants already in place) — this is
   substantial, separate infrastructure, likely its own re-plan-scale phase.
2. Given that invariant, prove `boxI_lift` by well-founded induction on the finite raw-connected
   component of `x` (a `Finset (Label Atom)`-based cascade, exactly as this dispatch's analysis
   worked out step-by-step, but now sound because the rank+unique-parent invariant rules out the
   3-cycle-style conflict).
3. Close the `NIK.boxI` case using `boxI_lift` + `Function.update _ y u` (map the fresh
   eigenvariable to the adversarial witness exactly, Simpson §8.1.2, chunk 0156) — mechanically
   straightforward once `boxI_lift` exists.

## Verification evidence (this dispatch)

- `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness` — green.
- `grep -n '\bsorry\b' Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean` —
  zero tactic-level `sorry` (only prose mentions in historical dispatch notes, pre-existing).
- `lake env lean` on `#print axioms Cslib.Logic.Modal.Labelled.boxI_lift_star` —
  `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`, no new axiom).
- No Preserved Asset (`box_iff_base`, `dia_iff_base`, `box_iff_TClosure`, `dia_iff_TClosure`,
  `cs5FCIncest_lift`, `cs5FCIncest_raise`, `box_gives_here`, `boxI_raise_step`) was edited.
- `cs5FCIncest` definition (`CS5Canonical.lean:255`) untouched/unweakened.
