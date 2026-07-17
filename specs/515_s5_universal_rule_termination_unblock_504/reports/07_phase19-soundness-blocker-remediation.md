# Phase 19 Soundness Blocker — Remediation Research

**Task**: 515 (`s5_universal_rule_termination_unblock_504`)
**Scope**: Decide the remediation route for the Phase 19 `modalTableauFive_sound` design-soundness gap. Research/decision only — no Lean written.

## Verdict

**Adopt Route (1): make the propagation helpers root/non-root asymmetric.** It is the correct
fix (not a relocation of the unsoundness), it is bounded, it does not cascade into the termination
proof, and it reuses exactly the Phase 16-17 substrate that was sequenced first to serve it. Route
(2) (completeness cross-check) **converges** with Route (1) rather than competing — a strong
correctness signal. Route (c) / Fallback 4 (S5-only) is **not** warranted: the fix is bounded.

## Root cause (confirmed against landed code)

The S5 soundness discharge `accReachableInv_related_s5` (`FrameSoundness.lean:1385`) is built on
`reachable_imp_related_s5` (`:1378`), whose induction **base case is `hFC.1.refl (f 0)`** — it
consumes frame **reflexivity** (`Std.Refl m.r`, the first conjunct of `s5FC`) to obtain
`m.r (f 0) (f 0)`. `fiveFC := fun r => Relation.RightEuclidean r` (`:1282`) has **no reflexivity
conjunct**, so this base case is unavailable, and it is genuinely false at the frame level: the
committed `Fin 3` counterexample `r = {(0,1),(1,1),(1,2),(2,1),(2,2)}` is `RightEuclidean` with
`¬ r 0 2`. Root-relatedness to a 2nd-generation cluster member does not follow from
`RightEuclidean` alone.

The current helpers `modalFiveBoxAll`/`modalFiveDiaNegAll` (`FiveSimplification.lean:74,85`)
`filterMap` over `modalKnownWorlds b` excluding only world `0`, **ignoring the trigger `_w`**. That
uniform shape is sound for `s5FC` (equivalence relation) but unsound for `fiveFC` when the trigger
is the root.

## Why Route (1) closes the gap (adversarial check passed)

Split by trigger:

- **Root trigger (`w == 0`)**: propagate a box-positive only to genuine direct successors
  `acc.successorsOf 0`. Sound by the standard K argument — those edges are realized in any model
  (`hacc : acc.hasEdge w w' → m.r (f w) (f w')`), so `m.r (f 0) (f w')` holds directly. This is the
  same discipline the base rule already uses (`Rules.lean:93`, "K-SOUND: propagate only to
  successorsOf w"; `boxPropagation` at `acc.successorsOf w`).

- **Non-root trigger (`w ≠ 0`)**: keep universal propagation across the non-root cluster. Sound
  because the **codomain of `m.r` carries an equivalence relation** even without frame reflexivity
  — `Relation.rooted_cluster_isEquiv : IsEquiv (cod r) r` (landed Phase 17). Every non-root known
  world is the target of a mint edge, hence `f w ∈ cod m.r` (`Relation.rooted_mem_cod`), and any
  non-root world reachable from a direct root successor `s` gets `m.r (f s) (f w)` by
  `RightEuclidean.rightEuclidean` steps **inside `cod`**, where reflexivity is recovered from the
  cod-equivalence (`rooted_cluster_isEquiv.refl`), not assumed of the frame. Two non-root known
  worlds are then related by one more Euclidean composition — mirroring
  `accReachableInv_related_s5`'s final `rightEuclidean`, but discharged via the cod-equivalence
  instead of `hFC.1`.

The suspected relocation does **not** happen: the non-root direction is justified with the trigger
itself (or a common root successor) as the Euclidean source; the root direction is restricted to
realized edges. Neither leans on the false `m.r (f 0) (f w2)`.

## Convergence with completeness (Route 2)

`EuclGen`'s `eucl` constructor only combines two derivations **sharing the same first argument**,
so `EuclGen r` never manufactures `EuclGen r 0 2` from `EuclGen r 0 1` and `EuclGen r 1 2` — it
relates `0` only to its `base`-case direct successors, exactly the root/non-root split above. So
the same asymmetric shape Route (1) needs for soundness is **also** the shape Phase 20's
`extractModelFive`/`modalTruthLemmaFive` will need. Route (1) is the right shape for both halves,
not a soundness-only patch.

## Blast radius (bounded)

- **`FiveSimplification.lean`**:
  - Give `modalFiveBoxAll`/`modalFiveDiaNegAll` an `acc` parameter; add a single guard so the root
    trigger keeps only `w'` with `acc.hasEdge 0 w'`. Keep the `filterMap over modalKnownWorlds b`
    skeleton (root case = same list filtered by an extra `hasEdge 0 w'` predicate) so the emitted
    set stays a **subset** of the current one. Membership lemmas `modalFiveBoxAll_mem`/`_mem`
    keep their conclusion (`x.label ∈ modalKnownWorlds b ∧ x.label ≠ 0 ∧ x ∉ b`) verbatim; one
    extra `by_cases` on the new guard.
  - Thread `acc` through `modalApplyOneFiveProp`.
  - Re-verify `modalApplyOneFive_specCore`. The world-bound / catalog-membership fields
    (`hOutputsSubsetUniverse`, the `modalKnownWorlds` fields) get **easier**, not harder — output
    is a subset. **Mint-arm fields are untouched** (route (1) changes only the two propagation
    arms, which emit `.persistent` formulas and add no edges).
- **`FrameSoundness.lean`**: add `reachable_imp_cod_related_five` + `accReachableInv_related_five`
  (the root/non-root discharge) and `modalTableauFive_sound`. Reuse the landed `accReachableInv`
  definition, `accReachableInv_initial`, and its step-preservation unchanged (edge-tracking is
  frame-condition-independent). New proof is well inside the plan's 400-line KILL budget.
- **`GenericDriver.lean`**: **not touched.** `RuleApplicationSpecCore.freshLocal`'s one-edge
  contract is about the **mint** arm, which route (1) leaves alone; the propagation arms add no
  edges. The earlier-rejected "redirect mint edges to the root" idea (which *would* have broken
  `freshLocal`) is a different, discarded option — not route (1).

## Termination: no cascade

The termination machinery (`modalOps`/`mintTags`/`S5wTagInv`/`usedTags`/`S5wWorldInv`/
`modalMaxWorld_lt_worldBound_of_S5w`) depends only on the **mint arms** (the counting crux), which
route (1) does not touch. Restricting propagation output to a subset cannot raise the world count.
Termination is unaffected.

## Recommended plan action

Revise Phase 18's helpers per Route (1), re-verify `modalApplyOneFive_specCore`, then land Phase 19
soundness via the cod-equivalence discharge. Un-block Phases 20-23 (they consume the corrected
shape, which also matches `EuclGen`). Do **not** invoke Fallback 4.
