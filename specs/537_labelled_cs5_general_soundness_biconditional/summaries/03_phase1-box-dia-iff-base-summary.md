# Task 537 -- Phase 1 Implementation Summary: box_iff_base, dia_iff_base

## Status

`implemented` (Phase 1 of 7 in direct-route plan v2, `plans/02_direct-route.md`)

## What Was Proven

Two base forcing-equivalence biconditionals landed in
`Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`, directly after the
existing `cs5FCIncest_lift` theorem:

- `box_iff_base {World} [Preorder World] {r} (hfc : cs5FCIncest r) {a b} (hab : r a b)
  {P : World → Prop} : (∀ w' ≥ a, ∀ u, r w' u → P u) ↔ (∀ w' ≥ b, ∀ u, r w' u → P u)`
  -- forward via `hfour`; backward (the ex-"Wall A" `.symm` direction) via `hincest` then
  `hfour`.
- `dia_iff_base {World} [Preorder World] {r} (hfc : cs5FCIncest r) {a b} (hab : r a b)
  {Q : World → Prop} : (∀ w' ≥ a, ∃ u, r w' u ∧ Q u) ↔ (∀ w' ≥ b, ∃ u, r w' u ∧ Q u)`
  -- forward via `hsymbox`+`htrans`; backward via `hincest`+`hsymbox`+`htrans`.

Both are proved by destructuring `cs5FCIncest`'s five conjuncts (`hrefl`, `htrans`, `hfour`,
`hsymbox`, `hincest`, `CS5Canonical.lean:255`) and chasing raised witnesses -- no induction, no
tree-lifting machinery, and critically **no exact-`r`-symmetry lemma** (the lemma that killed
four prior dispatches at GATE-C, see the module's "Fourth dispatch" section). `P`/`Q` are
arbitrary predicates, matching `CKForces_box`/`CKForces_diamond`'s exact clause shapes
(`Forcing.lean:106,112`), so both lemmas apply directly to real `CKForces (_) (□A)` /
`CKForces (_) (◇A)` forcing goals.

## Why This Works (the crux, per report 02 §4(A))

The prior blocked direction tried to derive an **exact** fact `r b a` from `r a b` plus
`cs5FCIncest` -- provably not obtainable in general (GATE-C, task 537 v1 dispatch). This phase
sidesteps that entirely: `boxE`/`diaI` soundness only needs the `CKForces` clause to be
**forcing-equivalent** across an `r`-related pair `(a, b)`, not an exact symmetric edge. Both
directions of both lemmas discharge purely from raised witnesses (`hfour`/`hsymbox`/`hincest`),
composed via `htrans`/`≤`-transitivity -- never pinning down an exact point.

## Verification

- `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness` -- green.
- `lake exe checkInitImports` -- passes (exit 0).
- `lean_verify` on `box_iff_base`: `axioms: []` (fully constructive).
- `lean_verify` on `dia_iff_base`: `axioms: []` (fully constructive).
- `grep -n '\bsorry\b'` on `Soundness.lean` -- zero tactic-level matches (only historical
  narrative mentions of the word "sorry" in prose, e.g. "no `sorry`... was introduced").
- Regression check: `lean_verify` on the Preserved Asset `nik_TS5_consistent` still reports
  only the standard `[propext, Classical.choice, Quot.sound]` axiom set -- unchanged from
  before this phase.

## Plan Deviations

None. All three Phase 1 checklist items executed exactly as specified (statement, proof
routing via the named conjuncts, and clause-shape confirmation against
`CKForces_box`/`CKForces_diamond`).

## Files Touched

- `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean` (+~35 lines: two new
  theorems plus a section docstring)
- `specs/537_labelled_cs5_general_soundness_biconditional/plans/02_direct-route.md` (Phase 1
  heading `[IN PROGRESS]` -> `[COMPLETED]`; three checklist items checked off)

## Next Step

Phase 2 (`box_iff_TClosure`, `dia_iff_TClosure`): extend these two base biconditionals over the
entire `TClosure {T, B, Four}` class by induction on the `TClosure` derivation (`base` -> this
phase's lemmas; `refl` -> `Iff.rfl`; `symm` -> `Iff.symm`; `trans` -> `Iff.trans`; `eucl` ->
`False.elim` since `Five ∉ TS5`). Depends only on this phase.

## Commit

`54b05950 task 537 phase 1: box_iff_base + dia_iff_base`
