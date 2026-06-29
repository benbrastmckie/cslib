# Implementation Summary: Task #385

- **Task**: 385 - Complete Parked Tableau Interpolation FMP
- **Status**: [PR READY]
- **Phases Completed**: 5 of 5 (Phase 4 deferred via research-or-defer gate; Phase 5 documentation-only)
- **Build**: repo-wide `lake build` GREEN (3153 jobs)
- **CI Pipeline**: All checks clean
- **New Sorries Introduced**: 0
- **New Axioms Introduced**: 0

## Outcome Summary

Task 385 had two sub-parts: (1) eliminating the repo-wide build blocker from the commented-out
`IntFMPSpike.lean` import, and (2) closing structural sorries in `Scheme.lean`. Both are resolved
at the level 385 can address without task 317's parametric truth lemma.

## Phase Outcomes

### Phase 1: Apply verified build-blocker patch + clear lint [COMPLETED]

Applied the 7-edit build-verified patch from `intfmpspike-verified-patch.diff` to
`Cslib/Logics/Propositional/Metalogic/IntFMPSpike.lean`. The patch:
- Added `public import Mathlib.Data.Finset.Powerset`
- Renamed `Σ`-identifier hypothesis names at 5 sites (`hψ'Σ`/`hab_Σ` → `hψ'mem`/`hab_sub`)
- Rewrote `intFinWorld_propConsistent` with the world-polymorphic `suffices ∀ u, ...` term form
- Fixed `Set.mem_coe` → `Finset.mem_coe.mpr` coercion
- Dropped `private` from `intFinWorld_carrier_injective`
- Cleared ~8 lint warnings (unused simp args, flexible simp, line-length)

Scoped build of `IntFMPSpike.lean` reached EXIT 0, sorry-free.

Also delivered as part of this phase: the structural lemmas `intExpandBranches_openBranch_closed`
and `intExpandBranches_openBranch_initial_mem` (the Phase 3 obligations) were included in the
verified diff.

### Phase 2: Rename + rewire + mk_all + full build verify [COMPLETED]

- `git mv IntFMPSpike.lean → IntDecidability.lean`
- Stripped spike/specs-370 framing from module docstring and section headers (no decl renames)
- Re-enabled the `Cslib.lean:420-422` import as
  `public import Cslib.Logics.Propositional.Metalogic.IntDecidability`
- Ran `lake exe mk_all --module` to regenerate the barrel
- Verified repo-wide `lake build` GREEN

This eliminated the build blocker: the import was previously commented out because
`IntFMPSpike.lean` did not compile.

### Phase 3: Close Scheme.lean :296 then :280 (structural sorries) [COMPLETED]

Both structural lemmas were delivered by the Phase 1 diff:

- `intExpandBranches_openBranch_closed` (Scheme.lean:267-352): proves that
  `intExpandBranches ... = .openBranch b → closurePred b = false` by induction on fuel
  + the `go` accumulator.

- `intExpandBranches_openBranch_initial_mem` (Scheme.lean:354-465): proves that any
  formula present in every initial branch is preserved in the returned open branch, by
  induction on fuel + `go` with `applyPersistenceFixpoint` and `Branch.extendMany`
  monotonicity.

The Phase 3 agent fixed proof errors in the original diff (wrong `ih_inner` arg orderings,
`split_ifs` → `cases heq : closurePred b₀`, `if_neg` explicit proof, nil-case contradiction,
`List.mem_cons_self _ _` → `List.mem_cons_self`). After fixes: scoped and repo-wide builds clean.

### Phase 4: Attempt Scheme.lean :288 (sat) — research-or-defer gate [BLOCKED]

Research outcome: the formulation bridge is **unbridgeable** at task 385's scope.

The `hsat : ∀ sf ∈ b, intStepBranch b [] 0 = none` hypothesis in `openBranch_countermodel`
requires `intStepBranch` to return `none` with the **empty expanded set** and **world 0**.
The loop returns `.openBranch bPers` when `intStepBranch bPers e nw = none` for the
**accumulated expanded set `e`** and a **positive next-world `nw`**.

These two statements are not equivalent because:
- `expanded` set `e` skips already-applied formulas; `[]` skips nothing — different rule-firing
  behavior
- `nextWorld nw ≠ 0` for world-creating rules — different branching conditions

Bridging requires either (a) showing saturation is independent of `e` and `nw`
(false in general), or (b) reformulating `hsat` to use the accumulated-set form that
the loop actually provides. Option (b) requires changing `truthLemma`'s signature, which
is task 317's core obligation.

Result: the sorry at Scheme.lean:519 remains as a pre-existing obligation, deferred to
task 317. No new sorry or axiom was introduced. Documentation comments added near the sorry
explain the bridge gap and sequence it after task 317.

### Phase 5: Coordinate :242 (truthLemma) + Completeness.lean:112 with task 317 [COMPLETED]

Documentation comments added to:
- `Scheme.lean:246` (truthLemma sorry): references task 317 parametric Kripke truth lemma
  (formula induction + persistence/monotonicity + parametric `modelBot`/`S.bot_truth`)
- `Completeness.lean:113` (IValid bridge sorry): references task 317 IValid→forcing bridge
  with upward closure of `intExtractValuation b`

Both sorries are clearly sequenced after task 317.

## CI Verification Results

| Check | Result |
|-------|--------|
| `lake build` (repo-wide) | GREEN (3153 jobs, 0 errors) |
| `lake exe checkInitImports` | CLEAN |
| `lake exe lint-style` | CLEAN |
| `lake shake --add-public --keep-implied --keep-prefix` | Pre-existing Temporal/* suggestions only (unrelated to task 385) |
| `grep sorry` in modified files | 3 sorries: Scheme.lean:246, Scheme.lean:519, Completeness.lean:113 — all pre-existing, task-317-deferred |
| New axioms | 0 |

## Files Modified

| File | Change |
|------|--------|
| `Cslib/Logics/Propositional/Metalogic/IntFMPSpike.lean` | Phase 1: applied 7-edit patch |
| `Cslib/Logics/Propositional/Metalogic/IntDecidability.lean` | Phase 2: renamed from IntFMPSpike, stripped spike framing |
| `Cslib.lean` | Phase 2: re-enabled import at line 420-422 |
| `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` | Phase 1/3: structural lemmas; Phase 4/5: defer documentation |
| `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` | Phase 5: task-317 sequencing comment |

## Sorry Inventory

| Location | Sorry | Disposition |
|----------|-------|-------------|
| `Scheme.lean:246` | `truthLemma` parametric Kripke truth | deferred-to-317 |
| `Scheme.lean:519` | `hsat` (`intStepBranch b [] 0 = none`) | deferred-to-317 (Phase 4 gate: formulation bridge unbridgeable) |
| `Completeness.lean:113` | IValid→forcing bridge + upward closure | deferred-to-317 |

## Plan Deviations

- **Phase 3 via Phase 1**: The Phase 3 structural lemmas (`intExpandBranches_openBranch_closed`,
  `intExpandBranches_openBranch_initial_mem`) were delivered as part of the Phase 1 verified diff
  rather than as a separate Phase 3 effort. Phase 3 became a proof-error-fixing phase for the
  diff-introduced lemmas rather than from-scratch authoring.

- **Phase 4 deferred (expected)**: The research-or-defer gate triggered: the `hsat` formulation
  in `openBranch_countermodel` cannot be bridged from the loop's accumulated-set return without
  reformulating `truthLemma`'s interface (task 317 obligation). No sorry was introduced; the
  pre-existing sorry remains.

- **Phase 5 folded into Phase 4 commit**: The task-317 sequencing documentation for `:242` and
  `:112` was added in the same commit as the Phase 4 gate-outcome documentation.
