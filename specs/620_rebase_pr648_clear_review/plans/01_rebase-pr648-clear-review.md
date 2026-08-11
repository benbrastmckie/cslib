# Implementation Plan: Rebase PR #648 onto upstream/main and clear the stale blocking review

- **Task**: 620 - Rebase PR #648 onto current upstream and clear the stale blocking review
- **Status**: [IMPLEMENTING]
- **Effort**: 7.5 hours
- **Dependencies**: None
- **Research Inputs**: `specs/620_rebase_pr648_clear_review/reports/01_rebase-pr648-clear-review.md`
- **Artifacts**: plans/01_rebase-pr648-clear-review.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md,
  `.claude/rules/pr-prohibition.md`, `.claude/rules/git-workflow.md`
- **Type**: cslib
- **Lean Intent**: false

## Overview

Rebase the open PR #648 branch (`origin/feat/propositional-v2`, head `4834be23`) onto current
`upstream/main` (`3951377e`), resolving the two conflicted files the research probe found, and
green the five upstream CI gates locally. The PR's approved scope is frozen at four files
(`Defs.lean`, `NaturalDeduction/Basic.lean`, `NaturalDeduction/Theory.lean`, `references.bib`)
with ungated `efq`, `IPL` as the empty theory, and minimal logic deferred. The work terminates at
a local commit on a rebase workspace branch plus a factual PR-scaffolding artifact; **no push, no
`gh` write, no Zulip post** is performed by any agent (`.claude/rules/pr-prohibition.md`).

Definition of done: the workspace branch is linear on `upstream/main`, its diff against the new
merge base is exactly the four approved files, all five CI gates pass locally, and
`specs/620_rebase_pr648_clear_review/pr-scaffolding.md` exists as verified fact tables for a human
to write from.

### Research Integration

The research report is the primary input and corrects three task-description claims that change
this plan's shape:

1. **The `IsClassical` shape reconciliation is already done on the PR branch.** The PR head
   already `public import`s `Cslib.Foundations.Logic.InferenceSystem` and states `IsClassical`
   over an inference system. The theory-membership drift described in the task lives on **this
   fork's `main`** (verified: 116 files under `Cslib/Logics/Propositional/` versus the PR
   branch's 3 and upstream's 3). That line must never be a merge source, cherry-pick source, or
   conflict-resolution reference. This is encoded structurally in Phase 1 (dedicated worktree)
   rather than left to discipline.
2. **Toolchain/manifest need no manual bump.** The PR branch touches neither `lean-toolchain` nor
   `lake-manifest.json`, so the rebase inherits upstream's `v4.33.0` / Mathlib `db584cd6`
   verbatim with zero conflict. The only practical consequence is a cold toolchain and Mathlib
   cache — which is why the warm-up is its own phase and runs in parallel with the rebase.
3. **PR #753 (`3491c629`) needs no absorption.** Its `InferenceSystem.lean` change is purely
   additive (module docstring plus an `app_delab` delaborator); the class signature and `S⇓(...)`
   notation are unchanged.

Independently re-verified for this plan against the live repository:

- `upstream/main` = `3951377e`, `origin/feat/propositional-v2` = `4834be23`, merge base
  `056cf937`, local `feat/propositional-v2` = `4834be23` (in sync with origin).
- `Cslib/Foundations/Logic/Operators.lean` exists on `upstream/main`; the PR branch and upstream
  each carry exactly 3 files under `Cslib/Logics/Propositional/`; this fork's `main` carries 116.
- The upstream PR CI (`.github/workflows/lean_action_ci.yml` on `upstream/main`) is exactly five
  gates: `lean-action` build `--wfail --iofail`, test `--wfail --iofail`, `lake exe mk_all
  --check`, `lake exe checkInitImports`, and `leanprover-community/lint-style-action` in `check`
  mode. `lake shake` is commented out. **The `sorry-suppression ratchet` and `axiom-census
  ratchet` steps present in this fork's copy of that workflow are fork-local and do not exist
  upstream** — they are not PR gates and must not be treated as such.
- `leanprover/lean4:v4.33.0` is **not** currently installed in elan (installed toolchains stop at
  `v4.33.0-rc1`), and `/home/benjamin` has 74G free. The warm-up phase is a real cost, not a
  formality.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was supplied in the delegation context and no ROADMAP.md consultation was
requested.

## Goals & Non-Goals

**Goals**:
- Produce a workspace branch whose history is linear on `upstream/main` and whose diff against
  the new merge base is exactly the four approved files.
- Resolve `Defs.lean` to the reconciled shape in research §4.3: PR semantics (five primitive
  constructors, ungated `bot`/`neg`/`top`/`efq`, `IPL = ∅`) on upstream mechanism (typeclass
  instances from `Operators.lean`, Mathlib `Bot`/`Top`, ungated `not_eq` `@[grind =]` bridge).
- Resolve `references.bib` mechanically, keeping both append blocks.
- Pass all five upstream CI gates locally.
- Emit `pr-scaffolding.md`: verified fact tables (four-bullet dispositions, API removals, `IPL`
  repurposing, blast-radius argument) as raw material for human-authored GitHub text.

**Non-Goals**:
- Any `git push`, `gh pr` write, or Zulip post. These are user actions only.
- Any finished prose intended to be pasted into GitHub or Zulip. CSLib follows Mathlib's AI
  policy and an LLM-drafted message on this exact topic was formally challenged; scaffolding only.
- Widening scope to the fork's `[IsIntuitionistic T]`-gated `efq` design, re-adding the Semantics
  layer, or restoring minimal logic. Each is a separate follow-up PR; widening forfeits
  thomaskwaring's standing approval.
- Reconciling this fork's 116-file Propositional development line against upstream. Out of scope.
- Reordering the `Proposition` constructors to reduce diff noise. Research recommends keeping the
  approved order `atom, bot, imp, and, or`; reordering churns match arms in `subst`, `weak`,
  `subs`, `substAtom` across two files that otherwise apply untouched.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Fork's `main` leaks into the rebase (merge, cherry-pick, or as a resolution reference), silently forfeiting a standing approval | H | M | Phase 1 creates a **dedicated git worktree** from `origin/feat/propositional-v2`; the fork's `main` checkout is never switched. Phase 1 gates on the worktree containing exactly 3 files under `Cslib/Logics/Propositional/` (fork main has 116). Phase 6 re-gates on a 4-file diff. |
| Checking out the PR branch in the main working tree would delete `specs/` and `.claude/` (fork-only trees absent from upstream) and collide with existing uncommitted changes | H | H if attempted | Worktree, not in-place checkout. Task artifacts are written to the **main** repo by absolute path; git operations happen in the worktree. Never `git checkout feat/propositional-v2` in `/home/benjamin/Projects/cslib`. |
| `upstream/main` has moved past `3951377e` since research, changing the conflict surface | M | M | Phase 1 re-fetches and re-runs the `git merge-tree` probe. If new upstream commits touch `Cslib/Logics/Propositional/` or `Cslib/Foundations/Logic/`, re-derive the §4.3 reconciliation table against the new head before proceeding. |
| Cold toolchain + Mathlib cache makes the first build appear to hang | M | H | Phase 3 isolates the warm-up (elan `v4.33.0` fetch, `lake exe cache get`) as its own long-running, independently verifiable phase, run in parallel with the rebase. |
| Notation ambiguity: keeping any of the PR's 5 local `scoped` declarations alongside upstream's `Cslib.Logic` scoped notation | M | M | Phase 4 deletes all five explicitly and greps the resolved file for residual `scoped infix`/`scoped prefix`/`scoped notation` as a phase gate. |
| Chained `a → b → c` / `a ∧ b ∧ c` fail to elaborate (the PR's `infix:n` is non-associative and falls through to `Prop`-level `And`/`Or`/`→`, giving a type mismatch rather than a notation error) | M | M | Adopting upstream's `infixr` instances fixes this for free. Phase 4 adds a chained-connective smoke check to confirm. |
| Scope creep into gated `efq` / Semantics / minimal logic during conflict resolution | H | L | Phase 6 gates on `git diff --stat <new-merge-base>..HEAD` naming exactly the four approved files and no others. |
| An agent pushes or runs a `gh` write | H | L | Phase 7 carries an explicit MUST-NOT and terminates at a local commit. `.claude/rules/pr-prohibition.md` applies throughout. |
| `lint-style` failures on changed lines (line length, whitespace, header conventions) | L | M | Phase 6 runs `lint-style` as a named gate, not as an afterthought. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |
| 5 | 6 | 5 |
| 6 | 7 | 6 |

Phases within the same wave can execute in parallel. Phase 3 (toolchain and Mathlib cache
warm-up) is deliberately independent of Phase 2 (the rebase): the rebase inherits upstream's pins
verbatim with zero conflict, so the target toolchain and Mathlib revision are known from
`upstream/main` before the rebase runs. Running them concurrently removes the long pole from the
critical path.

---

### Phase 1: Pre-flight verification and isolated workspace [COMPLETED]

**Goal**: Confirm the research topology still holds against live remotes, and create a rebase
workspace that structurally cannot involve this fork's `main`.

**Tasks**:
- [ ] `git fetch upstream && git fetch origin` from `/home/benjamin/Projects/cslib`.
- [ ] Re-resolve and record the four topology rows: merge base `056cf937`, PR head
      `origin/feat/propositional-v2` (`4834be23`), `upstream/main` (`3951377e`), fork `main`.
- [ ] If `upstream/main` has advanced, list the new commits' touched paths. If any touch
      `Cslib/Logics/Propositional/` or `Cslib/Foundations/Logic/`, re-derive the reconciliation
      table (research §4.3) against the new head before continuing and record the delta in the
      phase notes.
- [ ] Re-run the read-only conflict probe:
      `git merge-tree --write-tree --name-only --merge-base=<merge-base> upstream/main origin/feat/propositional-v2`.
      Record the conflicted-file list and the `Defs.lean` conflict-hunk count.
- [ ] Create the workspace worktree **from the PR branch only**:
      `git worktree add -b rebase/pr648-upstream <worktree-path> origin/feat/propositional-v2`.
      Use a sibling path outside the main checkout (e.g. `/home/benjamin/Projects/cslib-pr648`).
- [ ] Gate: `git ls-tree -r --name-only HEAD -- Cslib/Logics/Propositional/` inside the worktree
      returns exactly 3 paths. If it returns more, the worktree was created from the wrong ref —
      remove it and stop.
- [ ] Gate: the worktree contains no `specs/` and no `.claude/` tree (these are fork-only).
      Confirm task artifacts will be written to the main repo by absolute path.

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: Research asserts exactly two conflicted files (`Defs.lean`, `references.bib`)
with five conflict hunks in `Defs.lean` and one in `references.bib`, and that the two
`NaturalDeduction/` files merge clean. Confirm at implementation time by the `git merge-tree`
probe above; if the conflicted-file set differs, record the actual set and re-scope Phases 2, 4,
and 5 against it before proceeding.

**Files to modify**:
- None in the repository. Creates a worktree directory and the branch `rebase/pr648-upstream`.

**Verification**:
- The four topology rows are recorded in the phase notes with actual SHAs.
- The merge-tree probe output is recorded verbatim.
- The worktree exists, is on `rebase/pr648-upstream`, and shows exactly 3 Propositional files.
- `/home/benjamin/Projects/cslib` is still on `main` with its working tree untouched.

**Phase 1 Notes (actual, re-verified 2026-08-11)**:
- Topology: merge base `056cf937`, PR head `origin/feat/propositional-v2` = `4834be23`,
  `upstream/main` = `4bec19fc` (advanced from the plan-time `3951377e` by one commit), fork
  `main` = `f568febe` (untouched by this task).
- Upstream delta since research: `4bec19fc` "chore: bump toolchain to v4.34.0-rc1 (#792)" — touches
  `lean-toolchain` (now `leanprover/lean4:v4.34.0-rc1`), `lake-manifest.json` (Mathlib now
  `de5ce8a9`), `lakefile.toml`, and four unrelated `.lean` files under `Machines/`,
  `Foundations/Data/`, `LocallyNameless/`, `MachineLearning/`. **Does not touch**
  `Cslib/Logics/Propositional/` or `Cslib/Foundations/Logic/`. No re-derivation of the research
  §4.3 reconciliation table is required. The rebase's expected inherited toolchain/Mathlib pins
  are therefore revised from the plan's `v4.33.0`/`db584cd6` to `v4.34.0-rc1`/`de5ce8a9` — tracked
  as a deviation in Phases 2, 3, and 6.
- Merge-tree probe (`git merge-tree --write-tree --name-only --merge-base=056cf937 upstream/main
  origin/feat/propositional-v2`) confirms exactly 2 conflicted files, matching the research
  prediction: `Cslib/Logics/Propositional/Defs.lean`, `references.bib` (both `CONFLICT (content)`).
- Worktree created: `git worktree add -b rebase/pr648-upstream
  /home/benjamin/Projects/cslib-pr648 origin/feat/propositional-v2`. Gate passed: exactly 3 files
  under `Cslib/Logics/Propositional/` (`Defs.lean`,
  `NaturalDeduction/Basic.lean`, `NaturalDeduction/Theory.lean`). Gate passed: no `specs/` or
  `.claude/` tree in the worktree. Main repo confirmed still on `main` with a clean-relative
  (pre-existing, unrelated) working-tree diff.

---

### Phase 2: Execute the rebase and resolve the mechanical conflict [COMPLETED]

**Goal**: Land the PR's six commits on top of `upstream/main` with a linear history, resolving
`references.bib` mechanically and taking a first-pass `Defs.lean` resolution sufficient to
complete the rebase.

**Tasks**:
- [ ] In the worktree: `git rebase upstream/main`.
- [ ] Resolve `references.bib` mechanically per research §5: keep **both** append blocks,
      upstream's first (`Acclavio2026`, `Copes2018`, `AroraBarak09`, `Papadimitriou94`), then the
      PR's (`Gentzen1935`, `Prawitz1965`, `TroelstraVanDalen1988`, `Avigad2022`). Fix the missing
      trailing newline at the former EOF. No judgment required.
- [ ] Gate: confirm no duplicate BibTeX keys in the resolved file.
- [ ] Resolve `Defs.lean` conflicts **first-pass only**: take the PR side wherever the hunk
      encodes PR semantics, so the rebase can complete. Full reconciliation is Phase 4 — do not
      attempt the §4.3 table here.
- [ ] Confirm `NaturalDeduction/Basic.lean` and `NaturalDeduction/Theory.lean` applied without
      conflict (research predicts clean; record if not).
- [ ] Complete the rebase and verify `git log --oneline upstream/main..HEAD` shows the PR's
      commits and nothing else.
- [ ] Confirm `lean-toolchain` reads `v4.33.0` and `lake-manifest.json` pins Mathlib `db584cd6`,
      inherited from upstream with no manual edit.
- [ ] Commit checkpoint per `.claude/rules/git-workflow.md` sub-step convention.

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: This phase asserts the rebase writes exactly four files
(`Defs.lean`, `NaturalDeduction/Basic.lean`, `NaturalDeduction/Theory.lean`, `references.bib`) and
that `lean-toolchain`/`lake-manifest.json` are inherited unmodified. Confirm with
`git diff --stat $(git merge-base upstream/main HEAD)..HEAD` — the result must name those four
paths and no others. Note that the task's declared `file_scope` in state.json is inaccurate here:
it lists `lean-toolchain` and `lake-manifest.json` (inherited, not edited) and omits
`references.bib` (a real conflict).

**Files to modify** (in the worktree):
- `references.bib` - keep both append blocks; fix the missing trailing newline at the old EOF
- `Cslib/Logics/Propositional/Defs.lean` - first-pass conflict resolution only

**Verification**:
- `git status` in the worktree is clean and no rebase is in progress.
- `git log --oneline upstream/main..HEAD` shows only the PR's commits.
- `git diff --stat $(git merge-base upstream/main HEAD)..HEAD` names exactly four files.
- `lean-toolchain` = `leanprover/lean4:v4.34.0-rc1`; Mathlib rev = `de5ce8a9` (revised target per the
  Phase 1 topology deviation — upstream advanced past the plan-time `v4.33.0`/`db584cd6`).
- No duplicate BibTeX keys.

**Phase 2 Notes (actual)**:
- All 6 PR commits rebased cleanly onto `upstream/main` (`4bec19fc`):
  `c007ac73, efcf8d78, 8d204744, 2f790a10, c06d7623, 829b24eb`.
- `references.bib` conflicts arose across three of the six commits (not just the first), because
  upstream had independently converged on a near-identical five-primitive-bot design (via #607),
  producing genuine textual overlap at each point the PR's own history touched the file. Resolved
  mechanically per research §5 in each case: kept both sides' entries, no key ever dropped.
  Caught and corrected one initial duplicate (`Avigad2022` momentarily kept at two locations after
  the first conflict); final state has exactly one `Avigad2022` entry, matching the PR's own
  pre-rebase head. Final duplicate-key check: none. Trailing newline confirmed present.
- `Cslib/Logics/Propositional/Defs.lean` conflicted on the first commit (5 hunks, matching the
  research prediction exactly) and was resolved by taking the PR's side wholesale
  (`git checkout --theirs`) per the "first-pass only" instruction — full reconciliation deferred to
  Phase 4 as planned. Subsequent commits' diffs against `Defs.lean` applied without further
  conflict.
- `NaturalDeduction/Basic.lean` and `NaturalDeduction/Theory.lean` applied without conflict, as
  research predicted.
- `lean-toolchain` and `lake-manifest.json` inherited from upstream verbatim, no manual edit —
  now `v4.34.0-rc1` / Mathlib `de5ce8a9` per the Phase 1 deviation note (not the plan's original
  `v4.33.0`/`db584cd6`, which was accurate at research time but superseded by upstream's
  `4bec19fc` toolchain-bump commit).
- Final diff against the new merge base names exactly the four approved files: `Defs.lean`,
  `NaturalDeduction/Basic.lean`, `NaturalDeduction/Theory.lean`, `references.bib`.

---

### Phase 3: Toolchain and Mathlib cache warm-up [COMPLETED]

**Goal**: Make the worktree buildable before any verification phase needs it, so that build time
is not misread as a hang mid-reconciliation.

**Tasks**:
- [ ] In the worktree, let elan install `leanprover/lean4:v4.33.0` (not currently present locally;
      installed toolchains stop at `v4.33.0-rc1`).
- [ ] Fetch dependencies and run `lake exe cache get` for Mathlib `db584cd6`. Expect a long
      first run.
- [ ] Confirm free disk before and after (74G free at plan time; a full Mathlib cache plus
      toolchain is on the order of several GB).
- [ ] Gate: `lake env lean --version` reports `4.33.0`, and `lake build Cslib.Init` (or the
      cheapest available Mathlib-dependent target) completes without recompiling Mathlib from
      source.

**Timing**: 1 hour, predominantly waiting

**Depends on**: 1

**Verification Tier**: local

**Files to modify**:
- None tracked. Populates `.lake/` inside the worktree and `~/.elan`.

**Verification**:
- `lake env lean --version` reports `4.33.0`.
- A Mathlib-dependent target builds from cache rather than from source.
- Disk headroom is recorded and non-critical.

**Phase 3 Notes (actual)**: target revised to `v4.34.0-rc1` / Mathlib `de5ce8a9` per the Phase 1
deviation. `elan toolchain install leanprover/lean4:v4.34.0-rc1` succeeded (not previously
installed; prior max was `v4.33.0-rc1`). `lake update` fetched all dependencies pinned to the
rebased `lake-manifest.json` and ran Mathlib's post-update hook, which itself performed the cache
decompression (`lake exe cache get` afterwards reported "No files to download, already
decompressed 8691 file(s)"). Gate: `lake env lean --version` reports
`4.34.0-rc1`; `lake build Cslib.Init` completed 468 jobs in 3.1s (cache-backed, not a
from-source Mathlib compile). Disk: 56G free before, 45G free after (11G consumed by toolchain +
cache), non-critical relative to the 74G recorded at plan time.

---

### Phase 4: Reconcile `Defs.lean` to the target shape [NOT STARTED]

**Goal**: Resolve `Defs.lean` to the research §4.3 target: the PR's approved semantics on
upstream's mechanism. This is the only step in the task requiring judgment.

**Tasks**:
- [ ] Imports: add `public import Cslib.Foundations.Logic.Operators`; keep the existing
      `public import Cslib.Foundations.Logic.InferenceSystem`; drop the redundant
      `import Cslib.Init` (it arrives transitively and `checkInitImports` is still satisfied —
      confirmed by the Phase 6 gate).
- [ ] Keep the PR's five-constructor `Proposition` in the approved order: `atom, bot, imp, and,
      or`. Do **not** reorder.
- [ ] `Bot (Proposition Atom)`: unconditional `⟨.bot⟩`, keeping the instance name
      `instBotProposition` (upstream's atom-encoded `[Bot Atom]` form is what this replaces).
- [ ] `neg`: unconditional (drop the `[Bot Atom]` gate).
- [ ] `top`: unconditional `imp .bot .bot`, keeping the instance name `instTopProposition`.
- [ ] Keep upstream's `example : (⊤ : Proposition Atom) = Proposition.imp ⊥ ⊥ := rfl`, **ungated** —
      under primitive `bot` it is unconditionally true and demonstrates the design.
- [ ] Delete all five of the PR's local `scoped infix`/`prefix` notation declarations. Register
      `HasAnd`, `HasOr`, `HasImp`, `HasIff`, `HasNot` instances against upstream's
      `Operators.lean` — all ungated. Use the existing `HasIff` for the derived `iff`; do not
      declare a local `↔`.
- [ ] Add the ungated `not_eq` `@[grind =]` bridge
      (`(A → ⊥) = ¬ A := rfl`, with `omit [DecidableEq Atom] in`) so #607's `grind` automation
      sees through derived `neg`.
- [ ] `Theory.IPL := ∅` (the PR's meaning: empty theory plus primitive `efq` is IPL). Delete
      `Theory.MPL`, `efq_mem_ipl`, `intuitionisticCompletion`, `IsIntuitionistic`, and
      `instInhabitedOfBot`.
- [ ] Keep the PR's already-correct `IsClassical` — ungated, over `[InferenceSystem S (Proposition
      Atom)]`.
- [ ] Gate: grep the resolved file for residual `scoped infix`, `scoped prefix`, `scoped notation`
      — expect zero matches.
- [ ] Gate: chained-connective smoke check — `a → b → c` and `a ∧ b ∧ c` elaborate at
      `Proposition Atom` (not at `Prop`), confirming upstream's `infixr` forms fixed the PR's
      non-associativity defect.
- [ ] Build the module and iterate to green.
- [ ] Commit per sub-step convention.

**Timing**: 1.5 hours

**Depends on**: 2, 3

**Verification Tier**: local

**Scope Hypothesis**: This phase asserts the reconciliation is fully described by the 18 rows of
research §4.3 and requires **zero new typeclasses** — `Operators.lean` on `upstream/main` provides
`HasAnd`, `HasOr`, `HasImp`, `HasIff`, `HasNot` (plus `HasBox`, `HasDiamond`,
`HasDynamicBox`, `HasDynamicDiamond`, `HasTensor`) in namespace `Cslib.Logic`, and Mathlib's
`Bot`/`Top` cover bottom/top. Confirm at implementation time by reading
`Cslib/Foundations/Logic/Operators.lean` on the rebased tree before writing any instance.
**There is no `HasBot` and no `HasTop` upstream** — the agent context file that lists
`HasBot`/`HasTop`/`HasDia` as "existing CSLib typeclasses" is wrong on this point; do not
introduce them. If the file needs anything not on the §4.3 table, record it as a plan deviation
rather than absorbing it silently.

**Files to modify** (in the worktree):
- `Cslib/Logics/Propositional/Defs.lean` - full §4.3 reconciliation

**Verification**:
- The module builds clean.
- Zero residual local `scoped` notation declarations.
- Chained `→` and `∧` elaborate at `Proposition Atom`.
- `MPL`, `efq_mem_ipl`, `intuitionisticCompletion`, `IsIntuitionistic`, `instInhabitedOfBot` are
  absent; `instBotProposition` and `instTopProposition` retain their names.

---

### Phase 5: Verify the NaturalDeduction files and absorb any fallout [NOT STARTED]

**Goal**: Confirm the two `NaturalDeduction/` files still elaborate against the reconciled
`Defs.lean`, and make only the adjustments Phase 4 forces.

**Tasks**:
- [ ] Build `Cslib.Logics.Propositional.NaturalDeduction.Basic` and
      `Cslib.Logics.Propositional.NaturalDeduction.Theory`.
- [ ] If Phase 4's resolution forces a change, make the minimal one. The known candidate from
      research is the `Equiv := IPL.Equiv` region of `Basic.lean` (around line 159 pre-rebase).
- [ ] Confirm no other change is needed. If a change beyond the `Equiv` region is required,
      record it explicitly as a deviation from the research prediction.
- [ ] Confirm the `Avigad2022` citation is present as the lead reference in both `Defs.lean` and
      `NaturalDeduction/Basic.lean` (this is the discharge of ctchou's references bullet and must
      survive the rebase).
- [ ] Confirm no `Semantics/` file has appeared anywhere in the diff.
- [ ] Commit per sub-step convention.

**Timing**: 1 hour

**Depends on**: 4

**Verification Tier**: interface

**Scope Hypothesis**: Research asserts both `NaturalDeduction/` files merge clean and need
adjustment only if Phase 4 forces it. Confirm by building both modules; if either needs edits
beyond the `Equiv := IPL.Equiv` region, record the actual edit set in the phase notes rather than
treating it as anticipated. If neither needs an edit, close this phase on the build evidence
alone — verification is the deliverable, not an edit.

**Files to modify** (in the worktree, only if forced):
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` - `Equiv := IPL.Equiv` region if forced
- `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean` - only if forced

**Verification**:
- Both `NaturalDeduction` modules build clean against the reconciled `Defs.lean`.
- `Avigad2022` is cited as lead reference in `Defs.lean` and `NaturalDeduction/Basic.lean`.
- No `Semantics/` path appears in the diff.

---

### Phase 6: Green the five upstream CI gates locally and re-gate scope [NOT STARTED]

**Goal**: Reproduce the entire upstream PR CI locally and prove the diff has not widened beyond
the approved four files.

**Tasks**:
- [ ] `lake build --wfail --iofail`
- [ ] `lake test --wfail --iofail`
- [ ] `lake exe mk_all --check`
- [ ] `lake exe checkInitImports` (this is what confirms dropping `import Cslib.Init` from
      `Defs.lean` in Phase 4 was safe)
- [ ] Mathlib `lint-style` check in `check` mode, matching
      `leanprover-community/lint-style-action`.
- [ ] Do **not** run `lake shake` — it is commented out in the upstream workflow and is not a gate.
- [ ] Do **not** treat this fork's `sorry-suppression ratchet` or `axiom-census ratchet` workflow
      steps as gates — they are fork-local and absent from `upstream/main`'s workflow.
- [ ] Scope gate: `git diff --stat $(git merge-base upstream/main HEAD)..HEAD` names exactly
      `Cslib/Logics/Propositional/Defs.lean`,
      `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`,
      `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean`, and `references.bib` — and
      nothing else.
- [ ] Zero-debt gate: `grep -rn "sorry" Cslib/Logics/Propositional/` returns nothing. No `sorry`
      is expected or admitted anywhere in this task; the reconciliation is definitional, not
      proof-level.
- [ ] Blast-radius confirmation for the scaffolding artifact:
      `git grep -l "Cslib.Logics.Propositional" -- '*.lean'` on the rebased tree returns only
      `Cslib.lean` and the two `NaturalDeduction/` files — i.e. every deleted symbol
      (`IsIntuitionistic`, `intuitionisticCompletion`, `MPL`, `efq_mem_ipl`,
      `instInhabitedOfBot`) is used only inside files the PR already rewrites.
- [ ] Commit per sub-step convention.

**Timing**: 1.5 hours, predominantly build time

**Depends on**: 5

**Verification Tier**: full

**Scope Hypothesis**: This phase asserts the upstream PR CI is exactly five gates and the diff is
exactly four files. The five-gate claim was verified against
`upstream/main:.github/workflows/lean_action_ci.yml` at plan time — re-read that file on the
rebased tree at implementation time and reconcile if it has changed. The four-file claim is
confirmed by the `git diff --stat` gate above; any fifth file is a scope breach and must halt the
phase, not be absorbed.

**Files to modify**:
- None. This phase is verification only; any edit it provokes belongs to Phase 4 or 5 and should
  be recorded as such.

**Verification**:
- All five gates pass, each with its command output recorded.
- The diff names exactly the four approved files.
- Zero `sorry` under `Cslib/Logics/Propositional/`.
- The blast-radius grep returns only the three expected paths.

---

### Phase 7: Emit PR scaffolding, commit locally, and stop [NOT STARTED]

**Goal**: Produce the factual raw material a human needs to update the PR description and write
the re-review request, then terminate without any remote-facing action.

**Tasks**:
- [ ] Write `/home/benjamin/Projects/cslib/specs/620_rebase_pr648_clear_review/pr-scaffolding.md`
      (in the **main** repo, not the worktree) containing, as tables and verified facts only:
  - [ ] ctchou's four bullets verbatim, each with its verified disposition: (1) "I like the idea
        of adding \bot as a primitive" — supportive, unchanged, independently backed by Matthew
        Doty on DPLL grounds; (2) `Semantics/Basic.lean` vs `Semantics/Bool.lean` — moot, the PR
        ships no `Semantics` file; (3) 1930s German references — `Avigad2022` added and cited as
        lead reference in two files, Gentzen entry rewritten to the English Szabo translation
        (commit `1956d75b`) with the German original retained only as a `note`; (4) coordinate
        with #607/#587, wait for #536 — #536 merged 2026-06-16 and the PR was rebased onto it,
        #607 merged 2026-08-03 and this rebase performs that coordination, #587 is a stale draft
        untouched since 2026-06-17 whose `Connectives.lean` was superseded by #607's
        `Operators.lean`.
  - [ ] The two reviewer-visible items that must be itemized rather than left in the diff:
        `IPL` keeps its identifier but changes meaning (upstream `{⊥ → A | A}` versus the PR's
        `∅`), and five public API removals (`MPL`, `intuitionisticCompletion`, `IsIntuitionistic`,
        `efq_mem_ipl`, `instInhabitedOfBot`).
  - [ ] The Phase 6 blast-radius evidence as the safety argument for those removals.
  - [ ] The standing-approval record: thomaskwaring APPROVED 2026-07-06 after the 2026-06-28
        Zulip compromise ("if we are going to have `bot` as a primitive, we should also have
        `efq`") implemented 2026-06-29; all five of his inline comments answered and resolved
        2026-07-13; the `imp` vs `impl` question discharged by #607 landing `imp`, with upstream
        `Modal/Basic.lean` now on `Proposition.imp` + `HasImp` — so the PR body's "open to
        reverting if reviewers prefer `impl`" hedge can be dropped.
  - [ ] The `CONTRIBUTING.md` §"The role of AI" disclosure requirement, flagged as something the
        human must decide and word.
  - [ ] A prominent header stating the file is **verified factual scaffolding, not prose to
        paste**, and that the GitHub and Zulip text must be written from scratch by a human.
- [ ] Write the implementation summary under
      `specs/620_rebase_pr648_clear_review/summaries/01_rebase-pr648-clear-review-summary.md`.
- [ ] Record the two decisions left to the user, unresolved by this task: (a) whether to keep the
      approved constructor order `atom, bot, imp, and, or` (recommended — reordering churns match
      arms in `subst`, `weak`, `subs`, `substAtom` across two otherwise-untouched files); (b) the
      exact wording of the re-review request.
- [ ] Report the worktree path and branch name (`rebase/pr648-upstream`) so the user can push it
      themselves.
- [ ] **MUST NOT**: run `git push` in any form, run any `gh pr` write (including `gh pr edit` to
      update the PR description), request a review, or post to Zulip. Per
      `.claude/rules/pr-prohibition.md` these are user-invoked actions only. The task terminates
      at a local commit.

**Timing**: 1 hour

**Depends on**: 6

**Verification Tier**: prose

**Files to modify** (in the main repo):
- `specs/620_rebase_pr648_clear_review/pr-scaffolding.md` - verified fact tables
- `specs/620_rebase_pr648_clear_review/summaries/01_rebase-pr648-clear-review-summary.md` - summary

**Verification**:
- `pr-scaffolding.md` exists, carries the "not prose to paste" header, and contains all four
  dispositions plus the `IPL` and API-removal items.
- The summary names the worktree path and branch.
- `git log` on `origin` and `upstream` is unchanged — no push occurred. No `gh` write was issued.

---

## Testing & Validation

- [ ] `lake build --wfail --iofail` passes in the worktree.
- [ ] `lake test --wfail --iofail` passes.
- [ ] `lake exe mk_all --check` passes.
- [ ] `lake exe checkInitImports` passes (confirms dropping `import Cslib.Init` was safe).
- [ ] Mathlib `lint-style` in `check` mode passes.
- [ ] `git diff --stat $(git merge-base upstream/main HEAD)..HEAD` names exactly four files.
- [ ] Zero `sorry` under `Cslib/Logics/Propositional/`.
- [ ] Zero residual local `scoped` notation declarations in `Defs.lean`.
- [ ] Chained `a → b → c` and `a ∧ b ∧ c` elaborate at `Proposition Atom`.
- [ ] `git grep -l "Cslib.Logics.Propositional" -- '*.lean'` returns only `Cslib.lean` and the two
      `NaturalDeduction/` files.
- [ ] `/home/benjamin/Projects/cslib` is still on `main` with `specs/` and `.claude/` intact.

## Artifacts & Outputs

- Branch `rebase/pr648-upstream` in a dedicated worktree, linear on `upstream/main`, four files
  changed, all five CI gates green locally. Unpushed.
- `specs/620_rebase_pr648_clear_review/pr-scaffolding.md` - verified factual scaffolding for
  human-authored GitHub text (explicitly not prose to paste).
- `specs/620_rebase_pr648_clear_review/summaries/01_rebase-pr648-clear-review-summary.md`
- `specs/620_rebase_pr648_clear_review/plans/01_rebase-pr648-clear-review.md` (this file)

## Rollback/Contingency

- All work is confined to a dedicated worktree and the branch `rebase/pr648-upstream`. Nothing
  reaches `origin` or `upstream` — rollback is `git worktree remove <path>` plus
  `git branch -D rebase/pr648-upstream`. The PR branch `origin/feat/propositional-v2` and its
  standing approval are untouched by any failure mode of this plan.
- If the rebase in Phase 2 goes wrong mid-flight, `git rebase --abort` inside the worktree
  restores it to `origin/feat/propositional-v2` cleanly.
- If Phase 1's probe shows `upstream/main` has moved in a way that touches
  `Cslib/Logics/Propositional/` or `Cslib/Foundations/Logic/`, stop and re-derive the §4.3
  reconciliation table rather than proceeding on stale assumptions.
- No `git reset --hard`, `git clean -fd`, or other destructive operation on a dirty tree without
  first running `bash .claude/scripts/git-snapshot.sh 620` per
  `.claude/rules/git-workflow.md`'s "No Destructive Git on Uncommitted Work".

## Note on task terminus

`task_type` is `cslib`, whose standard terminus is `[IMPLEMENTING] -> [COMPLETED]`. `[PR READY]`
is `type=pr` only and is not available here, so the research report's "mark the task `[PR READY]`"
instruction cannot be followed literally. This plan therefore completes at `[COMPLETED]` with a
completion summary that states plainly that the rebased branch is local and unpushed and that
push, PR-description update, and re-review request remain user actions.
