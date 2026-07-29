# Phase 6 Summary: R1 Restatement of `intExpandBranches_openBranch_sat` + Fuel-0 Discharge + Call-Site Repair

- **Task**: 317
- **Plan**: plans/14_fuel-materialization-repair.md (v14, binding)
- **Phase**: 6 (single dispatch)
- **Session**: sess_1785294636_11f932
- **Status**: [COMPLETED]

## What Was Proven / Built

All changes land in `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`.

### New `hFuel` infrastructure

A new section ("`hFuel` Threading Invariant, Phase 6, R1 restatement"), inserted right
before `intExpandBranches.go`'s definition:

1. **`IAllFuel φ0 bs es fuels`**: a per-branch parallel-list invariant defined by
   simultaneous recursion over three lists (mirrors `IAllConsistent`'s shape exactly):
   `intWork (intUniverseExt φ0) bᵢ eᵢ < fuelsᵢ` for every `i`. This is the per-branch
   form the plan mandates — never the retired global `intExpMeasure ≤ fuel` form.
2. **`IAllFuel_append`/`IAllFuel_map`**: combinators mirroring `IAllConsistent_append`/
   `IAllConsistent_map`, used identically at every induction case.
3. **`intWork_persistence_le`**: persistence only ever ADDS formulas to a branch, and
   `intWork`'s branch-side term is antitone in branch-membership growth, so
   `intWork U (applyPersistenceFixpoint b edges fuel) e ≤ intWork U b e`. Bridges the
   threaded `hFuel` (stated relative to the raw pending branch `bh`) to the persisted
   branch `bPers` that `intStepBranch` actually consumes.
4. **`intStepBranch_some_exists_fuel`**: `intStepBranch_some_exists` widened to also
   expose the `e.any (· == sf) = false` witness that `intWork_drop` needs but the
   original lemma consumes internally without surfacing. Kept as a separate lemma
   rather than widening the existing one, to avoid touching its other call sites.

### R1 restatement

`intExpandBranches_openBranch_sat` gains a new first explicit parameter `φ0 : Proposition
Atom` and three new hypotheses: `hUniv : IAllUniv φ0 branches`, `hNW : IAllNW φ0
nextWorlds` (both Phase 5's invariants, consumed as-is), and `hFuel : IAllFuel φ0
branches expandedSets fuels` (this phase's). The internal `key` suffices-statement gains
six new universally-quantified hypotheses (`IAllUniv`/`IAllNW`/`IAllFuel` for both
`pending` and `done`), threaded through all 10 cases of the `intExpandBranches.go.induct`
functional induction exactly as `IAllConsistent`/`IAllAccessConsistent` already were:

- **case1, case9**: vacuous (list-shape absurdities) — no threading needed.
- **case4**: the saturated-leaf success arm — no recursion, new hypotheses unused
  (discarded with `_`).
- **case10**: the list-mismatch skip arm — already proved absurd from `hPending`'s own
  simultaneous-recursion shape before `ih` is ever reached — no threading needed.
- **case2** (closed-branch skip), **case5** (ALPHA), **case6** (ancestor-reuse
  world-creating), **case7** (fresh-mint world-creating), **case8** (BETA): all
  recursive arms. Each derives `hUniv_bPers`/`hFuel_bPers` from the pending-level facts
  via `applyPersistenceFixpoint_subset_ext`/`intWork_persistence_le`, re-establishes the
  child-level facts via Phase 5's step-preservation lemmas (`hUniv`/`hNW`) and
  `intWork_drop` + `omega` (`hFuel`), then combines the old `done` + new child(ren) +
  old `pending` tail into the recursive call's `IAllUniv`/`IAllNW`/`IAllFuel` arguments
  via the SAME double-`_append` pattern the pre-existing `IAllConsistent`/
  `IAllAccessConsistent` threading already used.
  - **case7's `hNW` forward preservation** (the fresh-mint arm) consumes the
    pre-existing DP-2 strategic sorry `intFreshMint_preserves_nw` (line 2515,
    follow-up task 585) as a black box — untouched, not re-proved, not re-opened.

### Fuel-0 discharge

Case3 (the `f = 0` exhaustion arm, formerly the bare `sorry` at the old line 4732) now
extracts `hFuel`'s head component (`intWork (intUniverseExt φ0) bh eH < 0`) and closes
by `omega` — impossible for a `Nat`. The counter-instance comment block is retained
(re-worded to mark it explicitly PRE-R1) as the durable record of why the `hFuel`
hypothesis had to be added.

### Call-site repair

`openBranch_countermodel` now passes `φ` as `φ0` and discharges the three new
hypotheses: `hUniv` via `mem_intUniverseExt_of (Nat.zero_le _) (intSubfmls_self_mem φ)`
at the singleton entry branch, `hNW` via `WBound_pos`, `hFuel` via
`intWork_init_lt_intFuelExt` (Phase 4A). `tableau_complete`'s statement is unchanged
(it only calls `openBranch_countermodel`, not the restated lemma directly).

## Verification

- Scoped build: green (`lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme`).
- Full build: green, 3311/3311 jobs. Both `Completeness.lean` files (Intuitionistic,
  Minimal) and both `DecisionProcedure.lean` files build unchanged — confirmed untouched
  by `git status --short`.
- `lake exe checkInitImports`: exit 0.
- Bare-sorry census in the subtree: **4** (was 5) — `Scheme.lean:514` (`truthLemma`
  T-imp, Phase 7's target), `Scheme.lean:2515` (`intFreshMint_preserves_nw`, DP-2, task
  585), `Intuitionistic/Completeness.lean:133` (DP-3, task 430),
  `Minimal/Completeness.lean:125` (DP-4, task 430). The fuel-0 sorry is GONE.
- `lean_verify` on `openBranch_countermodel`: axioms `{propext, Classical.choice,
  Quot.sound, sorryAx}` — `sorryAx` present only via `truthLemma`'s pre-existing T-imp
  sorry (unaffected by this phase; Phase 7's job), not from any new gap this phase
  introduced.

## Plan Deviations

None. All four Phase 6 task-list items (hypothesis threading, fuel-0 discharge,
succ-case re-establishment, call-site repair, comment cleanup) were completed exactly
as specified in plan v14. No design decision was re-opened; the per-branch `hFuel` form
was used throughout (never the retired global-measure form).

## Sorry Inventory (unchanged by this phase, for accounting continuity)

| File | Line | Strategic | Follow-up |
|------|------|-----------|-----------|
| `Scheme.lean` | 514 | true | Phase 7 (this plan) |
| `Scheme.lean` | 2515 | true | task 585 |
| `Intuitionistic/Completeness.lean` | 133 | true | task 430 |
| `Minimal/Completeness.lean` | 125 | true | task 430 |

## Next Phase

Phase 7: `truthLemma` T-imp discharge via persistence fixpoint sufficiency
(`Scheme.lean:514`), consuming the same `hUniv`/`hNW`/per-branch `hFuel` invariants this
phase landed.
