# Implementation Summary: Task #439 — `processNext` mutual refactor + run-level `InstantStrict`

- **Task**: 439 - refactor_processnext_to_mutual_def_and_prove_instantstrict_t (Phase 3 of parent task 426)
- **Status**: Implemented (all 4 phases complete, green, sorry-free)
- **Plan**: specs/439_refactor_processnext_to_mutual_def_and_prove_instantstrict_t/plans/01_processnext-mutual-instantstrict.md

## What Was Done

### Phase 1 — Mutual refactor (`Saturation.lean`)
Lifted the nested `let rec processNext` out of `temporalExpandBranches` into a top-level
`mutual … end` block containing both `temporalExpandBranches` and `processNext` as ordinary
`def`s, with `processNext` taking the fuel `fuel'` as an explicit parameter. Supplied
`termination_by (fuel, 0)` / `termination_by (fuel', pending.length)` (Lean's tuple-measure
lexicographic termination). Behaviour-preserving: same match arms, same signatures. Verified
`lean_local_search`-confirmed that this now yields `temporalExpandBranches.induct` /
`processNext.induct` recursion principles that did not exist for the `let rec` form (though the
final proof used a hand-rolled strong-induction argument instead — see Phase 3).

### Phase 2 — Single-step preservation (`Saturation.lean`)
Added `temporalStepBranch_preserves`, proving that one `temporalStepBranch` expansion step
preserves `TimeOrdering.InstantStrict` and the `OrdFreshWRT` branch/ordering coupling invariant.
This packages the already-existing `temporalApplyOne_preserves` (Rules.lean, landed under task
180 phase 8, ahead of this task) via `List.exists_of_findSome?_eq_some` and a case split on the
`RuleResult`.

### Phase 3 — Run-level threading (`Saturation.lean`)
Introduced `WorklistInv` (parallel-list invariant: `InstantStrict` + `OrdFreshWRT` per
branch/ordering position) and `ResultInv` (`.closed ↦ True`, `.openBranch _ ord ↦
InstantStrict ord`) as the induction motives. Proved `run_level_P1 : ∀ fuel, P1 fuel` by
`Nat.strong_induction_on` on `fuel`, with a nested `induction pending` establishing `P2 fuel'`
inside the `fuel'+1` case (citing the outer strong-induction hypothesis at the *same* `fuel'`
for the processNext → temporalExpandBranches cross-call). Added `processNext_mismatch_closed`
to dispatch `processNext`'s three defensive length-mismatch fallback arms (always drain to
`.closed`, unconditionally). Instantiated at the `temporalTableau` entry point as
`temporalTableau_instantStrict : temporalTableau φ = .openBranch b ord → InstantStrict ord`.

### Phase 4 — Wire into `Completeness.lean` + finalize
Updated the `openBranch_branchSat` documentation block: the order-preservation component
(`hInst`) is no longer an assumed hypothesis — it is the concrete, sorry-free
`temporalTableau_instantStrict`. The full `openBranch_branchSat` lemma remains a documented
comment sketch (not real code) because `temporalTruthLemma` for Until/Since is still
FMP-blocked (requires PTL's Finite Model Property, not yet formalized) and `branchSat`'s
existential witness needs both components simultaneously. No `sorry` introduced.

## Verification

- `lake build` (full project): green, 3188/3188.
- `lake test`: green, 9179/9179 (`CslibTests` suite).
- `lake exe checkInitImports`: pass.
- `lake exe lint-style`: pass.
- `lake lint`: no new findings in `Saturation.lean`/`Completeness.lean` (2 pre-existing,
  unrelated `defsWithUnderscore` errors in `Temporal/Theorems.lean`, not touched by this task).
- `lake shake --add-public --keep-implied --keep-prefix`: one pre-existing import-minimization
  suggestion for `Completeness.lean` (predates this task's changes — confirmed via `git stash`
  isolation test), not acted on (out of this task's scope).
- `lake exe mk_all --module`: no update necessary.
- `grep -n "\bsorry\b"`: zero real `sorry` in touched files (only prose/doc-comment mentions and
  the pre-existing, unchanged FMP-blocked comment-sketch bodies).
- Vacuous-definition scan: zero matches.
- Axiom count: unchanged (22 in `Cslib/`, no new `axiom` declarations).
- `lean_verify` on `temporalTableau_instantStrict`, `processNext_mismatch_closed`,
  `temporalStepBranch_preserves`: `axioms: [propext, Quot.sound]` only (standard), no `sorry`.

## Plan Deviations

- **Phase 2**: The branch/ordering coupling predicate (`OrdFreshWRT`) and the edge-case
  preservation lemma (`temporalApplyOne_preserves`) already existed in `Rules.lean` (landed
  under task 180 phase 8, ahead of this task's dispatch). Reused directly rather than
  redefining; `temporalStepBranch_preserves` is a thin wrapper around them.
- **Phase 3**: Confirmed Lean auto-generates `temporalExpandBranches.induct`/`processNext.induct`
  for the `mutual` well-founded pair (verified via `#check`), but used a hand-rolled
  `Nat.strong_induction_on` + nested `induction pending` proof instead, since the auto-generated
  principle's raw case shapes (dependent-if encodings of the `fuel=0` `findSome?` search) were
  more awkward to discharge directly than the manual unfold-based approach already proven out in
  Phase 2. Also added `processNext_mismatch_closed` (not anticipated in the plan) to dispatch the
  three defensive length-mismatch fallback arms without needing extra length-matching hypotheses.
- No phase was blocked; no `sorry` or vacuous placeholder was introduced at any point.

## Files Modified

- `Cslib/Logics/Temporal/Tableau/Saturation.lean` — mutual refactor (Phase 1); single-step
  preservation lemma (Phase 2); `WorklistInv`/`ResultInv`/`processNext_mismatch_closed`/
  `run_level_P1`/`temporalTableau_instantStrict` (Phase 3).
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — updated blocker documentation to reflect
  the resolved order-preservation component (Phase 4).
- `specs/state.json` — task 439 → implemented; parent task 426 → completed.

## Commits

- `task 439 phase 1: lift processNext into mutual block (green refactor)`
- `task 439 phase 2: single-step InstantStrict preservation + coupling (green, sorry-free)`
- `task 439 phase 3: run-level InstantStrict threaded through saturation (green, sorry-free)`
- `task 439: complete (426 phase 3 — run-level InstantStrict threaded and wired)` (this commit)

## Remaining Work (Out of Scope, FMP-Blocked)

- `temporalTruthLemma` for Until/Since (requires PTL's Finite Model Property).
- `openBranch_branchSat`, `temporalTableau_complete`, `instDecidableValid` — all depend
  transitively on the above; documented as blocked comment sketches, no `sorry`.
