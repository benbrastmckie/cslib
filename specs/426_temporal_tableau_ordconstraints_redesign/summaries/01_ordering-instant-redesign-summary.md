# Implementation Summary: Task #426 — Temporal Tableau Time-Ordering Redesign

- **Task**: 426 - Redesign the temporal tableau time-ordering scheme so ordering invariants hold
- **Status**: PARTIAL (phases 1, 2, 4, 5 complete; phase 3 BLOCKED)
- **Artifacts**: plans/01_ordering-instant-redesign.md (plan), summaries/01_ordering-instant-redesign-summary.md (this file)
- **Type**: cslib

## What Was Delivered

All deliverable phases completed sorry-free:

- **Phase 1** [COMPLETED]: Augmented `TimeOrdering` with an integer `instant : Nat → ℤ` field.
  `empty` initializes it to `fun _ => 0`; `addFuture` sets `instant tNew = instant t + 1`;
  `addPast` sets `instant tNew = instant t - 1`. Uses `Function.update` from Mathlib.

- **Phase 2** [COMPLETED]: Defined `InstantStrict` and proved edge-by-edge preservation lemmas
  sorry-free in `TimeOrdering.lean`:
  - `InstantStrict.empty` (vacuously true)
  - `InstantStrict.addFuture` (freshness from `∉ allTimes` + `Function.update` + `omega`)
  - `InstantStrict.addPast` (symmetrically)

- **Phase 3** [BLOCKED]: The run-level induction threading `InstantStrict` through
  `temporalExpandBranches`/`processNext` is blocked. `processNext` is a `let rec` inside a
  `do`-style match in Saturation.lean — Lean 4 does not generate standalone recursion principles
  for `let rec` bindings, preventing standard induction tactics. Needs factoring out of
  `processNext` as a top-level `def` before this phase can proceed. Zero-debt: no `sorry`
  introduced.

- **Phase 4** [COMPLETED]: Added `extractModelℤ : TemporalModel ℤ Atom` keyed on `ord.instant`
  and proved four re-keyed atom lemmas sorry-free:
  - `extractModelℤ_atom_sat_iff`
  - `extractModelℤ_atomPos_sat`
  - `extractModelℤ_bot_false`
  - `extractModelℤ_atom_neg_notSat`

- **Phase 5** [COMPLETED]: Removed the false `ordConstraints_strict` comment block, replaced
  with design explanation. Updated `openBranch_branchSat` sketch to document the D=ℤ/f=instant
  design and the order-preservation component (unlocked). The full `openBranch_branchSat`
  remains BLOCKED on FMP (the Until/Since truth lemmas), documented as comments only.

## Plan Deviations

- **Phase 3 blocked**: The run-level threading was known to be the highest-risk phase. The plan's
  zero-debt fallback was taken exactly: edge-by-edge preservation lemmas delivered, phase marked
  BLOCKED, no `sorry` introduced. The documented Option A (Mathlib `LinearExtension`) remains
  available as a heavier alternative.

## Verification Results

| Check | Result |
|-------|--------|
| `lake build` (full) | Green (only task 427's pre-existing sorry at Completeness.lean:433) |
| `lake test` | All 9152 jobs pass |
| `lake exe checkInitImports` | Pass |
| Active sorries introduced by task 426 | 0 |
| `ordConstraints_strict` revived | No (referenced only in comments explaining why it was false) |

## Files Modified

- `Cslib/Logics/Temporal/Tableau/TimeOrdering.lean` — `instant` field, `InstantStrict`, preservation lemmas
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — `extractModelℤ`, atom lemmas, design notes, false block replaced

## Sorry Inventory

| Sorry | File | Line | Owner | Status |
|-------|------|------|-------|--------|
| `temporalTruthLemma_propositional_aux` imp case | Completeness.lean | 433 | Task 427 | Pre-existing, not introduced by task 426 |

Task 426 introduced zero new sorries.
