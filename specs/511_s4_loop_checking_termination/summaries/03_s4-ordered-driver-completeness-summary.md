# Implementation Summary: Task #511

- **Task**: 511 - S4 loop checking termination (close the termination bound and complete decidability)
- **Plan**: `plans/03_s4-ordered-driver-completeness.md`
- **Status**: Implemented (all 5 phases COMPLETED)

## Overview

Closed S4 decidability by finishing the completeness half for the ordered keyed driver
`modalTableauS4KeyedOrdered`, whose soundness was already proved sorry-free and axiom-free at
HEAD. This is the last of the classical-cube decidability corners.

## Phases Completed

- **Phase 1 — Ordered saturation lemma** (`LoopChecking.lean`): added
  `modalStepBranchS4KeyedOrdered_none_saturated`, transferring the saturated-leaf characterisation
  from the unordered stepper via `modalStepBranchS4KeyedOrdered_eq_none_iff`.
- **Phase 2 — Relocate `_newExps_eq_map`** (`LoopChecking.lean` + `FrameCompleteness.lean`, atomic
  batch): moved `modalStepBranchS4KeyedOrdered_newExps_eq_map` from `FrameCompleteness.lean` into
  `LoopChecking.lean` (pure relocation, byte-identical proof) so it is available to Phase 3's
  lemma, which lives below `FrameCompleteness` in import order.
- **Phase 3 — `modalExpandBranchesS4KeyedOrdered_hintikka`** (`LoopChecking.lean`, ~365 lines):
  structural port of the unordered top-loop Hintikka lemma, using the bundled `S4OrderedFuelInv`
  as the per-index hypothesis and `modalStepBranchS4KeyedOrdered_preserves_S4OrderedFuelInv` as
  the single step lemma — simpler than the unordered original's four-way conjunct reassembly.
- **Phase 4 — `modalExpandBranchesS4KeyedOrdered_openBranch_initial_mem`** (`LoopChecking.lean`,
  ~141 lines): structural port of the initial-branch membership persistence lemma, substituting
  `modalStepBranchS4KeyedOrdered_branch_superset` and the Phase 2 relocated lemma.
- **Phase 5 — Completeness and the decidability capstone** (`FrameCompleteness.lean`): landed
  `modalTableauS4KeyedOrdered_complete`, `s4Valid_decides`, `instDecidableS4Valid` (mirroring the
  KB5 template), and corrected the two stale prose notes asserting S4 decidability was out of
  scope (`FrameCompleteness.lean`'s S4Keyed-completeness-section note, and `LoopChecking.lean`'s
  `modalTableauS4Keyed` docstring).

## Correctness Constraint Honored

All new work targets the **ordered** driver `modalTableauS4KeyedOrdered` exclusively. The
unordered keyed driver's soundness is machine-checked false (countermodel in
`CslibTests/S4LoopGuardRegression.lean`), so `instDecidableS4Valid` is built strictly from
`modalTableauS4KeyedOrdered_sound` + `modalTableauS4KeyedOrdered_complete` — never from the
unordered driver or the live-guard `modalTableauS4`. Every new declaration name in Phases 1-4
contains `Ordered`; each phase's finished body was grepped for unqualified (non-`Ordered`)
references to the unordered keyed driver/stepper and none were found in code (only expected
docstring cross-references naming the unordered originals by name).

## Verification

- `lake build Cslib.Logics.Modal.Tableau.LoopChecking`: 876/876, exit 0.
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness`: 910 jobs, exit 0.
- Full repository `lake build`: 3323 jobs, exit 0.
- `lake exe checkInitImports`: pass (no output).
- `lake lint`: zero warnings attributable to `LoopChecking.lean` / `FrameCompleteness.lean`
  (pre-existing warnings elsewhere in the repo, e.g. `Logics/Temporal/`, are unrelated).
- `lake exe lint-style`: exit 0.
- `lake shake --add-public --keep-implied --keep-prefix`: neither scope file appears in the
  suggested-changes summary (imports remain minimal); pre-existing suggestions elsewhere in the
  repo are unrelated to this task.
- `lake exe mk_all --module`: "No update necessary" (no new files added).
- `lake test`: exit 0 (full `CslibTests/` suite, including
  `CslibTests.S4LoopGuardRegression` — the ordered-driver soundness smoke row still builds).
- Sorry census over `Cslib/Logics/Modal/Tableau/` (README's two-pattern command): **zero**,
  unchanged from baseline.
- `#print axioms` (via `lean_run_code`, authoritative fresh compile) on
  `modalTableauS4KeyedOrdered_complete`, `s4Valid_decides`, and `instDecidableS4Valid`: all report
  only the standard `propext`/`Classical.choice`/`Quot.sound` triple, matching the
  `modalTableauS4Keyed_complete` control. `modalTableauS4KeyedOrdered_sound`'s axiom list is
  unchanged (still only the standard triple).
- `git diff --stat`: only `Cslib/Logics/Modal/Tableau/LoopChecking.lean` and
  `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` were touched; zero changes under
  `Cslib/Logics/Modal/Tableau/S4/`.

## Note: transient `lean_verify` MCP tool false positive

The `lean_verify` MCP tool reported `sorryAx` for `instDecidableS4Valid` on first check, despite
`modalTableauS4KeyedOrdered_complete`, `s4Valid_decides`, and `modalTableauS4KeyedOrdered_sound`
each independently reporting a clean standard triple through the same tool. A direct, fresh
`#print axioms` via `lean_run_code` on `instDecidableS4Valid` confirmed the clean standard triple
with no `sorryAx`, consistent with all its dependencies being individually clean. This is recorded
as a `lean_verify` tool-caching/staleness false positive, not a real finding — the authoritative
fresh-compile check is what the final metadata's `verification` block relies on.

## Plan Deviations

None. All five phases were executed exactly as specified, including the deliberate
`S4OrderedFuelInv`-bundle simplification named in Phase 3's plan text (rather than widening the
unordered proof's four-way per-index conjunction to five). The only judgment call not pinned down
by the plan was the exact insertion point for Phase 5's new declarations within
`FrameCompleteness.lean` (the plan named the file but not a precise line); they were placed
immediately after `modalTableauS4KeyedOrdered_sound` at the end of the file, pairing the
soundness/completeness/decidability trio together, which does not affect correctness or scope.

## Roadmap Note (informational, not applied by this task)

Per the plan's Roadmap Alignment section, no `roadmap_path`/`roadmap_flag` was passed to this
task, so `specs/ROADMAP.md` was not modified. Two lines there are now stale and should be
annotated by whoever next runs `/todo`: line 153 ("S4 ... loop-checking termination bound +
decidability ... the last classical-cube decidability corner" — now closed) and line 114
("Decidability instances: K, T, B, S5, 5/Euclidean, KB5 (all sorry-free)" — S4 should be added to
this list).

## Files Modified

- `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`
- `specs/511_s4_loop_checking_termination/plans/03_s4-ordered-driver-completeness.md` (phase
  status markers, checklist items, plan-level status)
