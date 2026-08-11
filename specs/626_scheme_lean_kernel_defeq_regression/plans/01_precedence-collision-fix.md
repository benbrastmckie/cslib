# Implementation Plan: Precedence-Collision Fix for Scheme.lean Non-Termination
- **Task**: 626 - Root-cause and fix the Scheme.lean build non-termination introduced by the Connectives/Operators migration
- **Status**: [NOT STARTED]
- **Effort**: 2 hours (dominated by build wall time; edit surface is ~10 lines)
- **Dependencies**: None (task 619 phase 8 is blocked ON this task, not the reverse)
- **Research Inputs**:
  - specs/626_scheme_lean_kernel_defeq_regression/reports/02_defeq-mechanism-and-fix.md (PRIMARY — mechanism + end-to-end-verified fix; adversarially verified)
  - specs/626_scheme_lean_kernel_defeq_regression/reports/01_scheme-defeq-regression-findings.md (superseded on mechanism by report 02; localization and control experiment confirmed and reused)
- **Artifacts**: plans/01_precedence-collision-fix.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/context/standards/status-markers.md
  - .claude/rules/no-task-references-in-deliverables.md (binding on all Lean-file comments/docstrings this plan touches)
- **Type**: cslib

## Overview

`Cslib/Foundations/Logic/Operators.lean` declares `scoped infixr:30 " ∨ " => HasOr.or` and
`scoped infixr:25 " → " => HasImp.imp` — exact token+precedence+associativity collisions with
core `Or` (infixr:30) and the core function arrow (infixr:25). Phase 8 of the
Connectives/Operators migration (branch `task-619-phase8-wip`, commit `1e88ad3e`) adds
`public import Cslib.Foundations.Logic.Operators` to `Connectives.lean`, activating these scoped
notations across all of `Cslib.Logic.*`. Every Prop-level `→`/`∨` then parses as a two-way
`choice` node, and nested chains cost Θ(2^n) elaborator backtracking; per-alternative
deterministic-timeout exceptions are swallowed by `observing` in choice elaboration, so no
heartbeat budget bounds the walk (report 02 §2-3). `Scheme.lean:8410` has a 29-arrow chain
(≈25-50 min walk, observed as >34 min DNF); `intExpandBranches_closed_unsat`
(`Scheme.lean:6264`) is a second, previously hidden casualty.

**The verified fix is two precedence digits** — `infixr:30 " ∨ "` → `infixr:31`,
`infixr:25 " → "` → `infixr:26` — mirroring `HasAnd`'s existing collision-free `infixr:36` vs
core 35 (report 02 §5, E8-E11). With the fix, Scheme.lean builds in 29s and the full library is
green (3331/3331 jobs, 6m55s) **including the `Cslib` barrel that is broken on `main`**. The
phase-8 `set_option maxHeartbeats 1000000` band-aid in `LoopChecking.lean` becomes unnecessary
(E12: green at default budget without it) and is deleted along with its misattributing comment.

Definition of done: the fix, band-aid removal, and a cheap regression guard are committed on
`task-619-phase8-wip`; full `lake build` on that branch is green including the barrel; the E9
formula-semantics gates (rfl grouping tests) pass; task artifacts (summary, metadata, handoff)
written on `main`.

### Branch and Worktree Execution Model (SETTLED — read before phase 1)

The current checkout at `/home/benjamin/Projects/cslib` is on `main` and MUST stay on `main`
(all `specs/**` artifacts live there). The fix targets the phase-8 migration, which lives ONLY
on branch `task-619-phase8-wip` (commit `1e88ad3e`; merge-base with main = `e39a75f5`).
`Operators.lean` is textually identical on `main` and the branch — the collision is latent on
`main` (nothing activates the scoped notations there) and detonates only with phase 8's
Connectives import — so the fix lands where the detonator is: **as commits on
`task-619-phase8-wip`**.

**Recommended default (adopt unless the user intervenes)**: commit the fix + band-aid removal +
regression guard directly on `task-619-phase8-wip`. Do NOT rebase the branch onto `main`, do NOT
merge it to `main`, and do NOT cherry-pick to `main` — landing the branch on `main` is task
619 phase 8's job after this task completes. No pushes, no PRs (pr-prohibition rule).

**Execution site**: the branch is checked out in an existing git worktree at
`/tmp/claude-1000/-home-benjamin-Projects-cslib/622a4407-4dc9-4cb5-b6f8-f7c190e5bbfe/scratchpad/wt`
(verified live at plan time). That worktree ALREADY CONTAINS the verified fix as uncommitted
changes: `Cslib/Foundations/Logic/Operators.lean` (2-line precedence change, verified
`infixr:31`/`infixr:26` in the working tree) and `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
(5-line band-aid deletion). It also has a warm `.lake` build directory. Phases 1-4 run inside
this worktree via `git -C <wt>` / `cd <wt>`; commits made there land on the branch and persist
in the main repository's object store even if the worktree is later removed. Because the branch
is checked out in the worktree, it CANNOT be committed to from the main checkout — do not try.

**Contingency if the worktree is gone at implement time**: `git worktree prune`, then
`git worktree add <scratchpad>/wt task-619-phase8-wip`, re-apply the two edits from report 02 §5
(two precedence digits + one 5-line deletion — trivial), and copy `.lake` from the old worktree
if salvageable, else from the main checkout (mathlib oleans reused; branch-code oleans rebuild —
expect the first build to take ~10-30 min instead of seconds; this is NOT a hang).

### Preserved Assets

The following work is complete and must not regress:

| Component | File/Ref | Status | Verified |
|-----------|----------|--------|----------|
| Phase-8 migration (barrel fix + 22 downstream repairs) | branch `task-619-phase8-wip` @ `1e88ad3e` | [COMPLETED, preserved] | 2026-08-10 |
| Verified fix (uncommitted) | worktree `wt`: Operators.lean + LoopChecking.lean working-tree changes | [VERIFIED, uncommitted] | 2026-08-11 (report 02 E8-E12) |
| Research reports 01 + 02 | specs/626_.../reports/ on `main` | [COMPLETED] | 2026-08-11 |
| `HasAnd`'s collision-free `infixr:36` | Operators.lean (both branches) | [EXISTING] | report 02 E7 |

The uncommitted worktree changes ARE the verified artifact — phase 1's first job is to commit
them, not recreate them. No destructive git (`reset --hard`, `checkout --`, `clean`) in the
worktree before they are committed.

### Source-to-Implementation Mapping (H3, Tier 3: implementation-backed)

| Load-bearing decision | Source | Phase |
|----------------------|--------|-------|
| Fix = `∨` 30→31, `→` 25→26 (nothing else) | report 02 §5 recipe; safety arguments verified (relative order preserved, repo grep at 26/31 clean, constant-cost single-use ambiguity ≡ existing `∧` situation) | 1 |
| Sentinel = Scheme.lean module build, ~29s | report 02 E10 | 1 |
| Band-aid deletion safe at default budget | report 02 E12 (module green, 13.5s, budget 200000) | 2 |
| Band-aid comment misattributes cost to instance projections | report 02 §5 follow-through; refutation in §2-3 + E7 | 2 |
| Semantics-unchanged gates = E9 rfl/grouping tests | report 02 E9 + adversarial table row "fix does not change formula parsing/semantics" | 3 |
| Docstring guard sentence in Connectives.lean Standing Invariant | report 02 §5 follow-through (performance reason added to existing Ambiguous-term reason) | 3 |
| Full gate = `lake build` 3331/3331 incl. barrel, ~7 min | report 02 §8 / E11 | 4 |
| Do NOT re-litigate kernel-defeq mechanism | report 02 §2 + adversarial self-verification table (refutes report 01 §4) | all |

## Postmortem Constraints

Binding rules for all implementation dispatches. Derived from report 02's refutation of report
01 and from the migration's own history.

**Do NOT**:
- Re-diagnose or re-investigate the mechanism. It is SETTLED: parser choice-node exponential
  backtracking from exact notation collision — NOT kernel defeq, NOT instance-projection
  unfolding (report 02 §2, adversarial table). Zero diagnostic dispatches are budgeted.
- Add or raise `set_option maxHeartbeats` anywhere. Heartbeat budgets cannot bound the choice
  walk (`observing` swallows per-alternative timeouts — report 02 §2.1); a bump masks the
  symptom and was the exact band-aid this plan deletes.
- Restore the deleted `Defs.lean` constructor-bound notations (causes Ambiguous-term errors and
  does not touch the Prop-level collision — report 02 adversarial table, last-but-two row).
- Add `@[reducible]`/`@[irreducible]`, instance priorities, or simp lemmas for this issue —
  all target the refuted mechanism (report 02 §5 "What the fix is NOT").
- Edit `Scheme.lean` at all. It is a victim, not a cause.
- Pick precedence values other than 31/26 without re-running the collision grep (26 and 31 are
  verified unoccupied by interacting tokens — report 02 §5).
- Rebase `task-619-phase8-wip` onto `main`, merge it to `main`, or cherry-pick to `main`.
- Push, or create PRs (pr-prohibition rule).
- Run destructive git in the worktree while the verified fix is uncommitted.
- Treat multi-minute builds as hangs — expected durations are stated per phase below. Only a
  Scheme-module build exceeding 10 minutes indicates regression.
- Cite task numbers in any Lean file, comment, docstring, or test name (deliverables rule
  no-task-references-in-deliverables.md). Reference the mechanism ("exact core-notation
  precedence collision causes exponential choice-node backtracking"), never "task 626".

**MUST preserve**: everything in Preserved Assets above; `HasAnd`'s `infixr:36`; the relative
precedence order `¬(40) > ∧(36) > ∨(31) > →(26) > ↔(20)`.

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):
- Mechanism: choice-node backtracking (kernel-defeq claim of report 01 is refuted).
- Fix: precedence offset mirroring `HasAnd`, exactly `∨→31`, `→→26`.
- Landing site: commits on `task-619-phase8-wip`; merge-to-main deferred to the phase-8 task.
- Band-aid: deleted, not retained "just in case" (E12 proves it unnecessary).

## Goals & Non-Goals

- **Goals**:
  - Commit the verified 2-line precedence fix on `task-619-phase8-wip`.
  - Delete the LoopChecking `maxHeartbeats 1000000` band-aid and its misattributing comment.
  - Add a cheap, durable regression guard (docstring sentence + small notation test file).
  - Prove the branch fully green: `lake build` 3331/3331 including the `Cslib` barrel.
- **Non-Goals**:
  - Merging/rebasing the branch to `main` (task 619 phase 8's job).
  - Any upstream PR (report 02 notes the fix is upstream-PR-worthy; out of scope here).
  - Fixing the `↔`/`¬` latent collisions (acceptable today; documented in the docstring guard).
  - Any change to `Scheme.lean`, `Defs.lean`, class declarations, instances, or bridge lemmas.

## Risks & Mitigations

- Risk: worktree vanished (scratchpad is session-scoped). Mitigation: contingency recipe above;
  the fix is 2 digits + 5-line deletion, re-applied from report 02 §5 in under a minute; only
  build time is lost.
- Risk: implementer mistakes a 7-minute full build (or 10-30 min cold-cache rebuild) for the
  original hang. Mitigation: expected durations stated in every phase; the pathological
  signature is specifically the *Scheme module* exceeding 10 min.
- Risk: test-file namespace/type names guessed wrong at plan time. Mitigation: marked as Scope
  Hypothesis in phase 3; implementer confirms against `Defs.lean` on the branch before writing.
- Risk: racing commits on the branch if phases were parallelized. Mitigation: waves are
  declared fully sequential (shared worktree, shared `.lake`, same branch — see below).

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases 2 and 3 are logically independent of each other (disjoint file territory), but all
phases share one worktree, one `.lake` build directory, and one branch head — parallel dispatch
would race builds and commits, so execution is deliberately fully sequential. There are no
parallel opportunities in this plan.

### Phase 1: Commit the precedence fix on the wip branch [NOT STARTED]

- **Goal:** The 2-line `Operators.lean` precedence fix is committed on `task-619-phase8-wip`,
  with the Scheme.lean sentinel build proving the non-termination is gone.
- **Territory (H7):** `Cslib/Foundations/Logic/Operators.lean` in the worktree ONLY. (The
  LoopChecking working-tree change stays uncommitted until phase 2 — stage the single file.)
- **Tasks:**
  - [ ] Verify worktree exists and its `Operators.lean` diff is exactly the report 02 §5
        recipe: `scoped infixr:31 " ∨ " => HasOr.or` and `scoped infixr:26 " → " => HasImp.imp`
        (content-anchored; expected at lines 38/45). If the worktree is gone, run the
        contingency recipe (Overview) first.
  - [ ] Sentinel build in the worktree:
        `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme`.
  - [ ] Commit ONLY `Cslib/Foundations/Logic/Operators.lean` on the branch
        (`git -C <wt> add Cslib/Foundations/Logic/Operators.lean && git -C <wt> commit`),
        message per git-workflow.md (`task 626 phase 1: ...` + Session line).
- **Timing:** sentinel build ~29s warm (report 02 E10); tolerate up to 10 min; beyond 10 min =
  regression signal, stop and report (do not wait out a 2^29 walk). Cold-cache contingency:
  10-30 min, announced in advance in the dispatch log.
- **Done when:** sentinel build exits 0 in bounded time AND `git -C <wt> log -1` shows the
  commit containing exactly the 2-line change AND `git -C <wt> status` shows `Operators.lean`
  clean (LoopChecking.lean still dirty is expected).
- **Scope Hypothesis:** the edit sits at Operators.lean lines 38 and 45 (report 02 §5) —
  confirm by content match at implementation time, not by line number.
- **Estimated output:** ~10 lines of diff + 1 commit.
- **Depends on:** none
- **Verification Tier:** local

### Phase 2: Remove the LoopChecking heartbeat band-aid [NOT STARTED]

- **Goal:** The `set_option maxHeartbeats 1000000 in` block and its misattributing 4-line
  comment (which blames "a typeclass-projection layer that `isDefEq` must unfold" — the exact
  misdiagnosis report 02 refutes) are deleted, and the module is proven green at the default
  200000-heartbeat budget.
- **Territory (H7):** `Cslib/Logics/Modal/Tableau/LoopChecking.lean` in the worktree ONLY.
- **Tasks:**
  - [ ] Verify the worktree working-tree change is exactly the 5-line deletion of the block at
        branch lines 1209-1213 (`set_option maxHeartbeats 1000000 in` + the 4 comment lines
        beginning "`maxHeartbeats` raised: Phase 8's move to upstream ..."). Nothing replaces
        it — the comment is deleted, not rewritten, because its claim is false and the default
        budget suffices (report 02 E12).
  - [ ] Build the module at default budget in the worktree:
        `lake build Cslib.Logics.Modal.Tableau.LoopChecking`.
  - [ ] Commit ONLY `LoopChecking.lean` on the branch, message
        `task 626 phase 2: ...` + Session line.
- **Timing:** module build ~15s-1 min warm (report 02 E12: 13.5s); tolerate up to 10 min.
- **Done when:** module builds green with NO `maxHeartbeats` occurrence remaining in the file
  (`grep -c maxHeartbeats` on the file returns 0) AND the commit exists AND worktree is clean.
- **Scope Hypothesis:** the block is 5 lines at branch lines 1209-1213 and is the file's only
  `maxHeartbeats` occurrence — confirm both by grep at implementation time.
- **Estimated output:** ~5 lines of diff + 1 commit.
- **Depends on:** 1
- **Verification Tier:** local

### Phase 3: Regression guard — docstring sentence and notation test [NOT STARTED]

- **Goal:** A silent-catastrophic recurrence of this bug class (a `scoped` notation exactly
  colliding with core notation in token+precedence+associativity) is guarded by (a) one
  documentation sentence at the established invariant site and (b) a small compile-time test
  whose failure mode is loud. Deliberately cheap: one docstring edit + one ~40-60 line test
  file. No linter, no metaprogram, no sub-project.
- **Territory (H7):** worktree `Cslib/Foundations/Logic/Connectives.lean` (docstring only),
  new file `CslibTests/OperatorPrecedenceRegression.lean`, and the import list in
  `CslibTests.lean`.
- **Tasks:**
  - [ ] Append 1-2 sentences to the END of the existing
        `## Standing Invariant: Notation Collision Risk` section of `Connectives.lean` (section
        exists on the branch at ~line 65): an *exact* token+precedence+associativity collision
        with a core notation turns every use into a parser `choice` node with Θ(2^n) elaborator
        backtracking on nested chains (heartbeat-unbounded, since per-alternative timeouts are
        swallowed); therefore every scoped notation here must stay offset by one from the core
        precedence (`∧` 36 vs 35, `∨` 31 vs 30, `→` 26 vs 25), and the latent `↔` (20 vs 20) /
        `¬` (identical shape) collisions are acceptable only while no instance activates them on
        chain-prone types. NO task numbers in the text.
  - [ ] Create `CslibTests/OperatorPrecedenceRegression.lean` (naming precedent:
        `S4LoopGuardRegression.lean`) containing, inside a namespace where the scoped
        `Cslib.Logic` notation is active (the research probes used
        `import Cslib.Logics.Propositional.Defs` + `namespace Cslib.Logic.PL`):
        - a 24-arrow Prop chain `example : True → True → ... → True := by intros; trivial`
          (flat-time with offset precedences; Θ(2^24) walk + eventual timeout error if an exact
          `→` collision regresses — report 02 E5/E8);
        - a 24-`∨` Prop chain `example : True ∨ True ∨ ... ∨ True := Or.inl trivial`
          (right-associated, so `Or.inl trivial` closes it; same guard for `∨` — E6/E8);
        - the two E9 formula-level grouping pins, e.g.
          `example (a b c : Proposition _) : (a ∧ b ∨ c → a) = HasImp.imp (HasOr.or (HasAnd.and a b) c) a := rfl` and
          `example (a b c : Proposition _) : (a → b → c) = a.imp (b.imp c) := rfl`
          — these are the named semantics-unchanged gates.
        - File docstring explains the guard mechanically (collision → choice nodes → 2^n), no
          task numbers.
  - [ ] Register the new module in `CslibTests.lean`'s import list.
  - [ ] Build the test module in the worktree; run the four examples green.
  - [ ] Commit the three files on the branch, message `task 626 phase 3: ...` + Session line.
- **Timing:** test-module build seconds-to-~2 min warm.
- **Done when:** the new test module builds green in the worktree, `CslibTests.lean` imports
  it, the docstring sentence is present, and the commit exists with exactly these three files.
- **Scope Hypothesis:** exact namespace (`Cslib.Logic.PL`), formula type name/arity
  (`Proposition _`), projection spellings (`a.imp`), and the test-build invocation
  (`lake build CslibTests.OperatorPrecedenceRegression` vs building the `CslibTests` driver
  target — check `lakefile.toml`, which declares `testDriver = "CslibTests"`) are plan-time
  guesses from report 02 E9's probe shapes — confirm all against branch `Defs.lean` /
  `lakefile.toml` before writing.
- **Estimated output:** ~60-80 lines across three files + 1 commit.
- **Depends on:** 2
- **Verification Tier:** local

### Phase 4: Full-library gate and wrap-up [NOT STARTED]

- **Goal:** The branch (now = `1e88ad3e` + 3 fix commits) is proven fully green, and task
  artifacts are written on `main`.
- **Territory (H7):** no Lean edits. Writes only under `specs/626_scheme_lean_kernel_defeq_regression/` on the `main` checkout.
- **Tasks:**
  - [ ] In the worktree: `lake build` (full default target). Expected: green, ~3331 jobs,
        ~7 min wall (report 02 §8: 6m55s), INCLUDING the `Cslib` barrel as one of the final
        jobs. Tolerate up to 20 min; capture the final job count and wall time.
  - [ ] In the worktree: build the test driver (`lake test` or `lake build CslibTests` per the
        phase-3 confirmed invocation) — green including the new regression file.
  - [ ] Confirm `git -C <wt> status` clean and `git -C <wt> log --oneline main..task-619-phase8-wip`
        shows `1e88ad3e` + the three fix commits.
  - [ ] On the `main` checkout: write
        `specs/626_scheme_lean_kernel_defeq_regression/summaries/01_precedence-collision-fix-summary.md`
        (include: measured build time/job count, the three branch commit SHAs, explicit note
        that merge-to-main is deferred to the phase-8 task).
  - [ ] Update `.return-meta.json` (status `implemented`, `completion_data`, `modified_files`
        listing ONLY the specs/** files — the Lean files were committed on the branch in
        phases 1-3 and are NOT in the main checkout's working tree) and
        `.orchestrator-handoff.json` (phase `implement`, status `implemented`).
- **Timing:** ~10-25 min total, dominated by `lake build`. A 7-minute silent stretch is normal.
- **Done when:** full `lake build` and the test driver both exit 0 in the worktree; summary,
  metadata, and handoff written on `main`.
- **Scope Hypothesis:** job count ≈3331 (may drift slightly with the new test module —
  the default target excludes CslibTests, so 3331 is expected to be exact for `lake build`;
  confirm and record the actual number).
- **Estimated output:** ~80-120 lines (summary + metadata), 0 lines of Lean.
- **Depends on:** 3
- **Verification Tier:** full

## Testing & Validation

- [ ] Sentinel: `Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` builds in bounded
      time (~29s warm; hard regression signal at >10 min).
- [ ] `Cslib.Logics.Modal.Tableau.LoopChecking` builds at the DEFAULT heartbeat budget with the
      band-aid deleted.
- [ ] Semantics-unchanged gates (named): the two E9 rfl grouping pins
      (`a ∧ b ∨ c → a` structure equation; `a → b → c` right-nesting equation) — now durable in
      `CslibTests/OperatorPrecedenceRegression.lean`.
- [ ] Performance gates (named): 24-arrow and 24-`∨` Prop-chain examples elaborate flat
      (seconds, not 46s+).
- [ ] Full gate: `lake build` green on the branch, ~3331 jobs incl. `Cslib` barrel, ~7 min.
- [ ] Zero `sorry`, zero new `maxHeartbeats`, zero task-number citations in Lean files
      (`grep -n "task [0-9]" <touched lean files>` → empty).

## Artifacts & Outputs

- plans/01_precedence-collision-fix.md (this file, on `main`)
- Three commits on branch `task-619-phase8-wip` (phases 1-3)
- CslibTests/OperatorPrecedenceRegression.lean (on the branch)
- summaries/01_precedence-collision-fix-summary.md (on `main`)
- .return-meta.json, .orchestrator-handoff.json (on `main`)

## Rollback/Contingency

- Each phase is one small, isolated commit on a non-`main` branch; rollback of any phase is
  `git -C <wt> revert <sha>` — never `reset --hard` (git-workflow.md). `main` is untouched by
  phases 1-3, so there is nothing to roll back there.
- If the full gate (phase 4) unexpectedly fails in a module the research did not flag: do NOT
  revert the precedence fix (it is E11-verified green at commit `1e88ad3e` + fix); first
  suspect the phase-3 test file or a stale `.lake` artifact (`lake build` again; if the failure
  reproduces, report as blocked with the failing module name — the research-verified state is
  recoverable by reverting only the phase-3 commit).
- If the worktree is lost mid-task, committed phases survive in the repo object store; only
  re-run the remaining phases in a recreated worktree (Overview contingency).
