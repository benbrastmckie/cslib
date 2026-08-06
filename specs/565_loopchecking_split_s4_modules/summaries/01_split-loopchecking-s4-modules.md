# Implementation Summary: Split `LoopChecking.lean` into an `S4/` Module Cluster

- **Task**: 565 - Split LoopChecking.lean along the real S4 seams and update ORGANISATION.md
- **Status**: [COMPLETED]
- **Started**: 2026-08-06T00:00:00Z
- **Completed**: 2026-08-06T00:00:00Z
- **Effort**: ~19 hours estimated; all 15 phases executed
- **Dependencies**: 553, 563, 564, 566, 586 (all landed)
- **Artifacts**: `specs/565_loopchecking_split_s4_modules/plans/01_split-loopchecking-s4-modules.md`
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

`Cslib/Logics/Modal/Tableau/LoopChecking.lean` was split from a single 11,393-line / 241-declaration
file into eleven new `S4/*.lean` modules along the research-verified acyclic dependency layering,
leaving `LoopChecking.lean` as a 20-declaration / 1,723-line `public import` barrel plus the S4
driver's entry points, termination measure, and two end-to-end capstones. This is a move-only
refactor: no declaration's statement or proof content changed, except removing `private` from the
26 declarations whose consumers ended up in a different module. Zero downstream `.lean` files
changed across the entire task.

## What Changed

- Extracted eleven modules bottom-up: `S4/Universe.lean` (32 decls), `S4/BirthKey.lean` (17),
  `S4/Guard.lean` (12), `S4/Driver.lean` (88, across two phases), `S4/Hintikka.lean` (15),
  `S4/Redirect.lean` (16), `S4/InvariantKeys.lean` (14), `S4/InvariantAcc.lean` (12),
  `S4/Invariant.lean` (7), `S4/HintikkaInvariant.lean` (8). Total 221 declarations moved.
- Registered all eleven modules in `Cslib.lean`, alphabetically positioned.
- Rewrote `LoopChecking.lean`'s module docstring: barrel description, ASCII layering diagram,
  one-line summary of each of the eleven modules, and the 20-declaration residue rationale.
- Created `Cslib/Logics/Modal/Tableau/README.md`, receiving the re-homed `## Measured Baseline`
  subsystem-wide census section, with `LoopChecking.lean`'s stale `10,540`/`230` figures
  corrected to the verified `11,393`/`241` (pre-split) and `1,723`/`20` (post-split) values.
- Updated `ORGANISATION.md`: expanded the undifferentiated `Tableau/` tree line into a subtree
  naming `Support/` and the `S4/` cluster with its layering; added a `## Module Size` guidance
  section.
- Added one `-- shake: keep` annotation, on `LoopChecking.lean`'s `public import S4.Redirect`.
- Updated `scripts/shake-residue-baseline.txt` (Phase 2): added `S5Simplification.lean`,
  `FiveSimplification.lean`, `TDriver.lean` -- a downstream-consumer shake-precision knock-on of
  moving declarations out of the barrel (see Decisions below).

## Decisions

- **A seventh module, `S4/Driver.lean`, was structurally forced** (research option A): the
  invariant material makes ~248 references into the driver definitions, so leaving them in
  `LoopChecking.lean` would create an import cycle. Recorded as a deviation from the task
  description's six-family list, not drift.
- **The invariant material was split four ways** (`InvariantKeys`, `InvariantAcc`, `Invariant`,
  `HintikkaInvariant`) rather than kept as one ~4,445-line module.
- **Four non-obvious research corrections were applied and verified**: `keysUpdate_preserves_keysDistinct`
  in `Guard` (not `BirthKey`); `modalNonMintCandidates` in `Driver` (not `Guard`);
  `successorBirthContent_{boxNeg,diamondPos}_subset_relevantSetFinset` in `InvariantKeys` (not
  `BirthKey`); `modalS4Saturated_addEdge_of_blocked` in `Redirect` (not `Hintikka`).
- **`lake shake` downstream-consumer false positives were resolved via the sanctioned baseline
  registry escape hatch, never by re-pointing a downstream file's import.** Moving a declaration
  out of the barrel makes `lake shake` prefer the more specific new `S4/` module for any file
  that directly imports `LoopChecking.lean` (`S5Simplification.lean`, `FrameCompleteness.lean`).
  Re-pointing those imports is forbidden by this plan's own Non-Goal and by the zero-downstream-
  churn invariant, so `check-shake-residue.sh --update` was used instead, with justification
  recorded in each commit message (Phase 2). This recurred once more at Phase 8, resolved instead
  by a `-- shake: keep` annotation on `LoopChecking.lean`'s own re-export once that became the
  more precise fix.
- **A real extraction-tooling bug was found and fixed mid-task** (Phase 8): the declaration-graph
  regeneration script records a bare keyword line, not any preceding `@[attr]` line, and the
  span-extraction algorithm did not independently check for one either. This could have silently
  dropped an attribute (`@[nolint unusedArguments]` on `Reds`) when its immediate predecessor
  wasn't co-moved in the same phase. Audited the two earlier `@[simp]` occurrences (Phase 4) and
  confirmed no corruption there (self-healed by concatenation order); fixed the tool for all
  subsequent phases.
- **A recurring two-level heading-attribution gap was identified, understood, and worked around
  explicitly rather than automated away.** A heading followed by a *separate* docstring block
  two levels above a declaration is not reached by the span algorithm's single-absorption rule --
  deliberately, since unconditional two-level absorption would misattribute genuinely-shared
  headings (Phase 4's "Mint-Readiness" case). Every occurrence (Phases 2, 5, 7, 8, 10, 11, 12)
  was caught by the standard post-move orphan check and fixed via either an explicit
  `start_overrides` entry or a manual relocation, never silently.
- **`pre-pr-check.sh`'s repo-wide `--wfail` gate (step 5) does not pass**, but this predates the
  task: it fails on warnings in five files this task never touched at all (byte-identical to the
  pre-task baseline) plus three pre-existing warnings verbatim-moved into `S4/Driver.lean`. See
  the Reasoned Exclusions table in the plan's Phase 15 section.

## Impacts

- **Zero downstream file changes**: `S5Simplification.lean`, `FrameCompleteness.lean`,
  `FrameSoundness.lean`, `FiveSimplification.lean`, `CslibTests/S4LoopGuardRegression.lean` are
  byte-identical to the pre-task baseline commit `11607e0f` (confirmed via
  `git diff --stat 11607e0f -- <five files>`, empty).
- **Job count**: 3313 (baseline) -> 3323 (final), delta +10, exactly the ten new
  `.olean`-producing modules (`Driver` counts once despite being built across two phases).
- **Future maintainers** get a coherent, dependency-ordered module cluster instead of an
  11,393-line file, plus module-size guidance in `ORGANISATION.md` intended to prevent recurrence.

## Final Gate Reconciliation

| Gate | Phase 1 baseline | Final (Phase 15) | Status |
|---|---|---|---|
| `lake build Cslib` job count | 3313 | 3323 | Green; delta +10 explained (ten new modules) |
| `Modal/Tableau` sorry census | 1 (`branchSatisfiableIn_s4FC_ancestor_redirect`) | 1 (same lemma) | Unchanged |
| `check-axiom-census.sh` | 43 sorryAx-tainted | 43 | Unchanged |
| `check-shake-residue.sh` | 9 findings, none in `Modal/Tableau/` | 12 findings (baseline updated Phase 2), none in `Modal/Tableau/` | Ratchet-compliant; +3 downstream-consumer entries justified and recorded |
| `check-lint-suppressions.sh` | 19 | 19 | Unchanged |
| `checkInitImports` | exit 0 | exit 0 | Green |
| `mk_all --check` | exit 0 | exit 0 | Green |
| `lint-style` | exit 0 | exit 0 | Green |
| `lake test` | green | green | Green |
| `check-boneyard-quarantine.sh` | exit 0 (5/5) | exit 0 (5/5) | Green |
| `pre-pr-check.sh` | N/A (not run at baseline) | 9/10 steps green | Step 5 fails on pre-existing, out-of-scope warnings -- see Decisions |
| Downstream `.lean` files | -- | 0 changed | Confirmed against `11607e0f` |

## Follow-ups

- **Boneyard candidates, deferred by design** (this task's declared non-goal): three
  zero-consumer `private` declarations were carried unchanged into their new homes --
  `foldl_max_le_of_forall_le` (`S4/Universe.lean`),
  `modalApplyOneS4Rules_boxPos_not_notApplicable_of_fourBoxProp_ne_nil` and
  `modalApplyOneS4Rules_diaNeg_not_notApplicable_of_fourDiaNegProp_ne_nil` (both
  `S4/Driver.lean`). A future, separately-committed task should decide whether to archive them to
  `Boneyard/`.
- **`pre-pr-check.sh` step 5** (repo-wide `--wfail` build) remains red for reasons outside this
  task's scope (see Decisions/Reasoned Exclusions). A future task addressing
  `FrameCompleteness.lean`/`FrameSoundness.lean`/`Propositional/Tableau/*` `simp_all`
  flexible-tactic warnings and sorry declarations could close this gap; out of scope here.
- **Optional downstream import optimization** (explicitly out of scope per this plan's Non-Goals):
  `S5Simplification.lean` and `FrameCompleteness.lean` could import the specific `S4/` modules
  they use instead of the barrel, which would let the three shake-baseline entries added in
  Phase 2 be removed. Left as a follow-up with its own verification cost.

## References

- `specs/565_loopchecking_split_s4_modules/plans/01_split-loopchecking-s4-modules.md` (all 15
  phases, each annotated with actual outcomes vs. hypotheses)
- `specs/565_loopchecking_split_s4_modules/artifacts/baseline.md` (Phase 1 baseline capture)
- `specs/565_loopchecking_split_s4_modules/artifacts/decl-graph.json`,
  `module-assignment.md` (declaration-level dependency graph and family assignment)
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean`, `Cslib/Logics/Modal/Tableau/S4/*.lean`,
  `Cslib/Logics/Modal/Tableau/README.md`, `Cslib.lean`, `ORGANISATION.md`
