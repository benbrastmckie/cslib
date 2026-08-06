# Implementation Summary: Create `Boneyard/` and Move Re-Verified Zero-Consumer Declarations

- **Task**: 566 - Create Boneyard/ with its convention and move only re-verified zero-consumer declarations
- **Status**: [COMPLETED]
- **Plan**: `specs/566_boneyard_creation_eligible_moves/plans/01_boneyard-creation-eligible-moves.md`
- **Research**: `specs/566_boneyard_creation_eligible_moves/reports/01_boneyard-convention-and-consumer-reaudit.md`

## Outcome

All 6 phases completed. A root-level `Boneyard/` quarantine directory now exists with a
documented convention, and exactly three re-verified zero-consumer declaration units (142 lines
total) were moved out of `Cslib/Logics/Modal/Tableau/LoopChecking.lean`:

- `blockedRedirect_boxctx_mem_of_boxOrigin` and `blockedRedirect_diaNeg_mem_of_diaOrigin`
  -> `Boneyard/ModalTableauS4Keyed/RedirectOriginTransfer.lean` (106 lines)
- `keysRootEmpty` and `keysRootEmpty_entry` -> `Boneyard/ModalTableauS4Keyed/KeysRootEmpty.lean`
  (36 lines)

Nothing was deleted. Both mandatory carve-outs (`branchSatisfiableIn_s4FC_ancestor_redirect` in
`FrameSoundness.lean`, and `keysOriginS4`/relatives in `LoopChecking.lean`) remain untouched and
were confirmed intact at Phase 6. The `outDegEq` non-goal was never touched (no phase mentioned
it).

## Phase-by-Phase Results

**Phase 1 — Quarantine skeleton**: Created `Boneyard/README.md` (archival criterion, build
policy, `#exit`/`ARCHIVED` convention, Directory Inventory table, three standing invariants, two
repo-wide scanner constraints, root-placement rationale) and
`Boneyard/ModalTableauS4Keyed/README.md`. Ran the full gate set before and after directory
creation: every figure matched exactly (3313 build jobs, 43 sorryAx-tainted, 9 shake-flagged, 19
lint suppressions, 18/28 sorry suppressions, `checkInitImports` exit 0). Zero config files
touched. Scope hypothesis (creating `Boneyard/` perturbs nothing) confirmed empirically.

**Phase 2 — Move `blockedRedirect_*_of_*Origin` pair**: Re-verified zero-consumer status by
word-boundary grep before excising (0 code consumers, matching the research report exactly).
Excised the contiguous ~85-line block into `RedirectOriginTransfer.lean` under the
`#exit`/`ARCHIVED` convention. Redirected the one surviving prose reference ("Witness Disjunct
(Gate)" section) to point at the archive; the sibling docstring reference was self-resolving
(moved with the block). Post-move grep confirmed zero remaining code hits for both names. Build
green at 3313 jobs, unchanged.

**Phase 3 — Move `keysRootEmpty` pair, split section comment**: Re-verified zero-consumer status
(`keysRootEmpty_entry` is the pair's only consumer, travels with it). The ~40-line section
comment was split: the `keysOriginS4` retraction paragraphs (about a live, pervasively-consumed
declaration) were re-homed under a new `### keysOriginS4 Consumer Audit -- Retraction of an
Earlier Hedge` heading and kept live in `LoopChecking.lean`; the `keysRootEmpty`-specific
paragraphs travelled verbatim to `Boneyard/ModalTableauS4Keyed/README.md`. Two surviving
references (`BoxPlusClosed` docstring, "Redirect-Inertness Assembly -- REMOVED" section) were
redirected, not deleted. Post-edit grep confirmed the retraction's distinguishing sentence ("Any
future claim that `keysOriginS4` was deleted is false...") is still present in live code, and
`keysOriginS4` remains pervasively referenced (42 hits, order-40+ as required). Build green,
unchanged.

**Phase 4 — Reconcile falsified/incomplete prose**: Replaced the now-falsified "There is no
`Boneyard/` directory" assertion in `LoopChecking.lean`'s measured-figures block with a true,
checkable statement. Added `Boneyard/` to `ORGANISATION.md`'s Top-Level Structure section.
Confirmed every redirected reference from Phases 2-3 names a path that actually exists.
Repo-wide grep for "Boneyard" (excluding `specs/`) confirmed every remaining mention is true.

**Phase 5 — Defensive quarantine self-test**: Added `scripts/check-boneyard-quarantine.sh`
(five checks: directory exists; zero `Boneyard` references in `Cslib.lean`; zero in
`lakefile.toml`; no live `TODO:`/`FIXME:`-family markers under `Boneyard/`; a `B0`-style mirror
asserting the directory count matches a hard-coded expectation of 1). Wired as step 10 of
`scripts/pre-pr-check.sh`. Documented in `scripts/README.md`. Shellcheck clean (`--severity=warning`).
Positive test passed; two independent negative tests (count mismatch, injected TODO marker) both
correctly failed the check, confirming it is live rather than vacuously green.

**Phase 6 — Full CI gate and closeout**: All explicitly required gates passed and matched
baseline exactly:

| Gate | Result | Baseline | Verdict |
|---|---|---|---|
| `lake build Cslib` | 3313 jobs, green | 3313 | MATCHES |
| Modal/Tableau sorry census | exactly 1 (`FrameSoundness.lean:1251`) | 1 | MATCHES |
| `check-shake-residue.sh` | 9 flagged, exit 0 | 9 | MATCHES |
| `check-axiom-census.sh` | 43 tainted, exit 0, sole Modal/Tableau row is the carve-out | 43 | MATCHES |
| `checkInitImports` | exit 0 | exit 0 | MATCHES |
| `check-lint-suppressions.sh` | 19 (ceiling 19), exit 0 | 19 | MATCHES |
| `check-sorry-suppressions.sh` | markers 18, sorries 28, exit 0 | 18/28 | MATCHES |
| `lake test` | green, 9378 jobs including `CslibTests.S4LoopGuardRegression` | green | MATCHES |
| `lake exe mk_all --check` | green, no `Boneyard.lean` aggregator demanded | green | MATCHES |
| Baseline files (5) grepped for the 3 moved names | zero hits in all five; `git status` confirms untouched | zero | MATCHES |
| Directory Inventory table | 2 files, 142 lines (106 + 36), measured | -- | confirmed |
| Carve-out 1 | `branchSatisfiableIn_s4FC_ancestor_redirect` still in `FrameSoundness.lean:1227` | -- | intact |
| Carve-out 2 | `keysOriginS4`/`_entry`/`_mono_branch`/`_mono_acc` still in `LoopChecking.lean` | -- | intact |

**One item could not be reproduced locally**: `lint-style` (mechanism 3), invoked directly via
`lake env lean --run .lake/packages/mathlib/scripts/lint-style.lean`, hits a pre-existing Lean
interpreter environment limitation (`LEAN ASSERTION VIOLATION` / `ir_interpreter.cpp:928`,
`'unreachable' code was reached`) unrelated to this task's changes -- CI invokes it via the
`leanprover-community/lint-style-action` composite action rather than this bare invocation, which
was not reproducible in this environment. This is not a Non-Goal violation (no lint-style config
was touched) and mechanism 3's blindness to a root-level `Boneyard/` was already established
analytically in the research report (import-reachability scoped, §4.2 row 3) and is unaffected by
this task's comment-only and declaration-relocation edits.

## Plan Deviations

None. All six phases were executed exactly as planned, with no altered, skipped, or deferred
tasks. The one notable finding during execution -- `keysOriginS4` count of 42 (vs. the research
report's 43) after the section-comment split -- is expected and within tolerance: the plan's own
verification only required "order 40+ ... must not have shrunk to near zero," which it clearly
satisfies; the small delta reflects wording changes in the redirected references themselves, not
a change in `keysOriginS4`'s actual consumer set.

## Files Changed

- `Boneyard/README.md` (new)
- `Boneyard/ModalTableauS4Keyed/README.md` (new)
- `Boneyard/ModalTableauS4Keyed/RedirectOriginTransfer.lean` (new)
- `Boneyard/ModalTableauS4Keyed/KeysRootEmpty.lean` (new)
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (three declaration units removed; falsified
  assertion corrected; `keysOriginS4` retraction re-homed and kept live; four prose references
  redirected)
- `ORGANISATION.md` (documented `Boneyard/` under Top-Level Structure)
- `scripts/check-boneyard-quarantine.sh` (new)
- `scripts/pre-pr-check.sh` (added step 10)
- `scripts/README.md` (documented the new script)

## Commits

- `08a8308a` — task 566 phase 1: create quarantine skeleton and prove exclusion empirically
- `170c2e5b` — task 566 phase 2: move blockedRedirect_*_of_*Origin lemmas to Boneyard
- `4386e3c0` — task 566 phase 3: move keysRootEmpty pair, split section comment
- `85d6c163` — task 566 phase 4: reconcile falsified no-Boneyard assertion and document ORGANISATION.md
- `029e8329` — task 566 phase 5: add Boneyard quarantine self-test (B0-style)
- `62284df8` — task 566 phase 6: full CI gate and closeout

## AI Tools Used

This work was prepared with the assistance of Claude Code (Anthropic). The AI tool was used for:
- Excising and relocating the three eligible declaration units under the Boneyard convention
- Drafting the `Boneyard/README.md` convention documentation and the quarantine self-test script
- Running CI verification commands and re-verifying consumer status by grep at each phase boundary
- Drafting this summary

All Lean code was verified to compile cleanly against the full CI gate set described above.
