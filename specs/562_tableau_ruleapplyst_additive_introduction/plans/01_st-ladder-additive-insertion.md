# Implementation Plan: Introduce `RuleApplySt` Additively and Bridge `modalExpandBranchesGen`

- **Task**: 562 - Introduce RuleApplySt additively and bridge modalExpandBranchesGen
- **Status**: [IMPLEMENTING]
- **Effort**: 2 hours
- **Dependencies**: None
- **Research Inputs**: `specs/562_tableau_ruleapplyst_additive_introduction/reports/01_ruleapplyst-additive-ladder.md`
- **Artifacts**: plans/01_st-ladder-additive-insertion.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

The research phase already compiled and machine-verified the entire code deliverable: nine new
declarations were inserted into `Cslib/Logics/Modal/Tableau/Saturation.lean`, the full
`lake build Cslib` came back green at exactly the 3313-job baseline, `lake test` exited 0, and
the working tree was then restored to HEAD. **This plan is therefore about sequencing, docstring
quality, and gate discipline — not design discovery.** Phase 1 lands the verified block verbatim;
Phase 2 raises the placeholder docstrings to the depth `Saturation.lean`'s existing declarations
carry and adds the ladder to the module docstring's `## Main Definitions` list; Phase 3 runs the
full CI gate against the measured baseline. Definition of done: the nine declarations are in
`Saturation.lean` with production-quality docstrings, zero existing declarations edited, zero
imports added, and every gate in Phase 3 matching its recorded baseline.

### Research Integration

Key findings from `reports/01_ruleapplyst-additive-ladder.md` carried into this plan:

- The mandatory consumer audit of `Saturation.lean` is **complete** (report section 1). It found
  16 driver `rfl` bridges downstream of the generic ladder — 2.7x the six named in the task
  description — all of which are protected by construction because this task edits nothing.
  **Do not re-run the audit.**
- **The task description contains an error.** `RuleApply = RuleApplySt Unit` is NOT achievable as
  a definitional equality: `RuleApplySt Atom Unit` has an extra `Unit →` argument and an extra
  `× Unit` in its result, and `Unit → X` is not `X`. Forcing it would require editing `RuleApply`,
  which the purely-additive constraint forbids. The relationship is an explicit
  `liftRuleApply : RuleApply Atom → RuleApplySt Atom Unit` embedding plus three proved bridges
  (report section 3). Docstrings written in Phase 2 must say *bridged*, never *definitional*.
- The paste-ready verified source is at `artifacts/st-ladder-verified.lean` (in-file form) with a
  standalone-module variant at `artifacts/st_probe.lean`.
- `findSome?_map_comm` is genuinely new: no `List.findSome?`/`Option.map` commutation exists in
  Mathlib (Loogle, 0 hits) or the project (local search, 0 hits). It is a 4-line induction and
  stays in the `Cslib.Logic.Modal.Tableau` namespace (report section 5.1 rejects both `private`
  and a Support-module placement — the latter would require an import, which is not additive).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` supplied in the delegation context; no ROADMAP.md consulted.

## Goals & Non-Goals

**Goals**:
- Insert the nine verified declarations (`RuleApplySt`, `liftRuleApply`, `modalStepBranchGenSt`,
  `findSome?_map_comm`, `modalStepBranchGen_eq_St`, `modalExpandBranchesGenSt`,
  `modalExpandBranchesGen_eq_St`, `modalTableauGenSt`, `modalTableauGen_eq_St`) into
  `Saturation.lean`, immediately before `end Cslib.Logic.Modal.Tableau`.
- Expand every placeholder docstring to the explanatory depth `Saturation.lean`'s existing
  declarations carry.
- Add a `## Main Definitions` entry for the St ladder to `Saturation.lean`'s module docstring.
- Land with zero existing declarations edited, zero imports added, zero `sorry`, zero new axioms.
- Pass the full CI gate against the measured baseline.

**Non-Goals** (explicitly out of scope; do not start any of these):
- Re-expressing `modalExpandBranchesS4Keyed` in terms of `modalExpandBranchesGenSt` (migration
  step 4 — a separate, later task).
- Retiring the `keys'` double derivation at `modalStepBranchS4Keyed` (step 5).
- Retiring `modalStepBranchS4Keyed` in favour of the ordered stepper (step 6).
- Removing `S4LoopInv.outDegEq` (owned by the migration task).
- Adding `modalHintikkaSetGenSt` — it would have zero consumers today (report section 8).
- Box-plus key enrichment.
- Any edit to `Rules.lean` or `Branch.lean`.
- Re-running the consumer audit.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Implementer develops in a scratch module and hits `unsolved goals: X = X` on the `fuel = 0` case | M | M | The in-file `simp only [modalExpandBranchesGen, modalExpandBranchesGenSt]` form is correct ONLY inside `Saturation.lean` (Lean shares the auxiliary matcher within a module). Paste `artifacts/st-ladder-verified.lean` directly into `Saturation.lean`; do not develop in a scratch file. The separate-module form (explicit `cases hf : (branches.zip accs).findSome? ...`) is in `artifacts/st_probe.lean` and is NOT what lands. |
| Docstring edit accidentally crosses out of the `/-- ... -/` boundary | M | L | Phase 2 declares `local` tier: `lake build Cslib.Logics.Modal.Tableau.Saturation` after the docstring pass, not a diff read-through. Lean doc comments elaborate; a broken delimiter is a compile error. |
| Gating on `lake lint` exit 0 produces a false failure | M | M | `lake lint` exits **1** at baseline with 145 pre-existing `unusedArguments` findings repo-wide. Gate on the **delta** (145 -> 145, `diff` empty), never on exit code. |
| Gating on `lake shake` exit 0 produces a false failure | M | M | `lake shake` exits **1** at baseline with 9 findings. Gate on "no Modal/Tableau findings AND count stays 9". |
| Reformulating the state list as `List.replicate accs.length ()` | H | L | Forbidden. The `accs.map fun _ => ()` form is what makes the loop induction close with no side hypothesis; `List.replicate` would require threading `sts.length = accs.length` through both the pending and done lists. |
| Attempting `modalStepBranchGen_eq_St` by induction on the branch `b` | H | L | Forbidden. `apply sf b acc` closes over the whole branch, not the tail, so the IH is about the wrong function. Factor `Option.map` out of `findSome?` via `findSome?_map_comm` first — this is exactly why that lemma exists. |
| Introducing `StateM`/`StateT` | H | L | Forbidden. The subsystem is deliberately monad-free and computable; a monad would change the elaborated term shape of every downstream `unfold`. |
| Line-number drift from the task description | L | M | Anchor every edit on declaration names, never line numbers. The insertion point is "immediately before `end Cslib.Logic.Modal.Tableau`". |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Insert the Verified St Ladder [COMPLETED]

**Goal**: Land the nine machine-verified declarations in `Saturation.lean` verbatim, with the
build green.

**Tasks**:
- [x] Read `specs/562_tableau_ruleapplyst_additive_introduction/artifacts/st-ladder-verified.lean`
      in full.
- [x] Locate the insertion point by name: the line `end Cslib.Logic.Modal.Tableau` at the end of
      `Cslib/Logics/Modal/Tableau/Saturation.lean`. Do not use a line number.
- [x] Insert the artifact's body (everything from the `/-! ## State-Threading Ladder ... -/`
      section marker onward, excluding the four leading `--` provenance comment lines) immediately
      before that `end`, keeping the existing blank-line spacing convention of the file.
- [x] Rename the section marker from `/-! ## State-Threading Ladder (ADDITIVE PROBE) -/` to
      `/-! ## State-Threading Ladder -/` — "ADDITIVE PROBE" was scaffolding language for the
      research prototype and must not land.
- [x] Confirm the nine declarations are present and in dependency order: `RuleApplySt`,
      `liftRuleApply`, `modalStepBranchGenSt`, `findSome?_map_comm`, `modalStepBranchGen_eq_St`,
      `modalExpandBranchesGenSt`, `modalExpandBranchesGen_eq_St`, `modalTableauGenSt`,
      `modalTableauGen_eq_St`.
- [x] Confirm by `git diff` that no existing declaration body was touched and no `import` line was
      added or changed.
- [x] Run `lake build Cslib` and confirm green at 3313 jobs.

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: full

**Commit Mode**: atomic-batch

Declared batch file set: `Cslib/Logics/Modal/Tableau/Saturation.lean` (single file). The nine
declarations are mutually dependent — the bridges reference the defs — so intermediate per-
declaration states are expected red and MUST NOT be committed. One commit covers the whole batch,
taken at the phase's `full` tier verification.

**Scope Hypothesis**: The phase asserts exactly **nine** new declarations, **zero** edited
existing declarations, and **zero** added imports, in exactly **one** file. Confirm at
implementation time by (a) grepping the post-insert file for the nine declaration names and
counting 9 hits, and (b) reading `git diff Cslib/Logics/Modal/Tableau/Saturation.lean` and
confirming every hunk is a pure addition inside the new section — no deletion lines outside it,
no change to the `public import` block. If the diff shows any modification to an existing
declaration, stop: the additive constraint has been violated.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Saturation.lean` — insert the St ladder section immediately before
  `end Cslib.Logic.Modal.Tableau`.

**Verification**:
- `lake build Cslib` green at 3313 jobs (baseline 3313).
- `git diff Cslib/Logics/Modal/Tableau/Saturation.lean` shows additions only, confined to the new
  section, with the `public import` block unchanged.
- `grep -c 'sorry' Cslib/Logics/Modal/Tableau/Saturation.lean` returns 0.

---

### Phase 2: Expand Docstrings and Module Docstring [COMPLETED]

**Goal**: Raise the nine placeholder docstrings to the explanatory depth `Saturation.lean`'s
existing declarations carry, and list the ladder in the module docstring.

**Tasks**:
- [x] Read the existing docstrings on `RuleApply`, `modalStepBranchGen`, `modalExpandBranchesGen`,
      `modalTableauGen`, and `modalHintikkaSetGen` in `Saturation.lean` to calibrate depth and
      house style (they explain *why* a definition has its shape, not just what it does).
- [x] `RuleApplySt`: document what `σ` is for, that the argument order
      `RuleApplySt (Atom) [insts] (σ)` makes `RuleApplySt Atom Unit` read as "`RuleApply Atom`,
      state-threaded", and why `@[nolint unusedArguments]` is required (same reason as on
      `RuleApply`).
- [x] `liftRuleApply`: state explicitly that `RuleApply Atom` is **bridged into**
      `RuleApplySt Atom Unit`, not equal to it — `RuleApplySt Atom Unit` has an extra `Unit →`
      argument and an extra `× Unit` result component, and neither `Unit → X = X` nor
      `X × Unit = X` holds definitionally. Note that making them defeq would require editing
      `RuleApply`, which the additive constraint forbids and which would break the driver `rfl`
      bridges.
- [x] `modalStepBranchGenSt`: document that the state is threaded **per-branch** (as `sts : List σ`
      parallel to `accs`), that this shape is forced by the intended first consumer
      `modalExpandBranchesS4Keyed` (which carries a `keyss` list parallel to `accs` and propagates
      one `keys'` to every child of a split), and that the state from a `.notApplicable` probe is
      discarded exactly as that probe's `newAcc` is discarded today — no behavioural divergence.
- [x] `findSome?_map_comm`: document it as a local helper for the step-level bridge, note it is
      absent from Mathlib and from the project, and state why it is needed (the step bridge cannot
      be proved by induction on the branch, because `apply sf b acc` closes over the whole branch
      rather than the tail; factoring `Option.map` out of `findSome?` is the working route).
- [x] `modalStepBranchGen_eq_St`: document the projection-at-`σ := Unit` reading.
- [x] `modalExpandBranchesGenSt`: document the per-branch state list and that the loop replicates
      `modalExpandBranchesGen`'s worklist shape declaration-for-declaration.
- [x] `modalExpandBranchesGen_eq_St`: document why the state list is instantiated as
      `accs.map fun _ => ()` rather than `List.replicate accs.length ()` — the `.map` form commutes
      through the loop's three `++` appends and its `List.replicate`, so the invariant is preserved
      definitionally by `simpa` with **no side hypothesis**; a `List.replicate` statement would need
      `sts.length = accs.length` threaded through both the pending and done lists.
- [x] `modalTableauGenSt`: document why the entry point takes an explicit `st0 : σ` (the S4 Keyed
      entry point seeds `keys := [(0, ∅)]`, not `[]`; at `σ := Unit`, `st0 = ()`).
- [x] `modalTableauGen_eq_St`: document it as the two-line corollary of the loop bridge.
- [x] Add a `## Main Definitions` entry to `Saturation.lean`'s module docstring for the St ladder,
      in the same style as the existing `modalHintikkaSetGen` entry, naming `RuleApplySt`,
      `modalStepBranchGenSt`, `modalExpandBranchesGenSt`, `modalTableauGenSt` and pointing at the
      three bridges.
- [x] Add a forward pointer, in the `modalExpandBranchesGenSt` docstring or the section marker,
      that `modalExpandBranchesS4Keyed` is the intended first consumer and that migrating it is a
      separate, later task.
- [x] Run `lake build Cslib.Logics.Modal.Tableau.Saturation` and confirm green.

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: The phase asserts **nine** declaration docstrings plus **one** module-
docstring edit, all in **one** file. Confirm at implementation time by grepping the post-edit file
for `/--` immediately preceding each of the nine declaration names and confirming none still
matches the placeholder one-liners from `artifacts/st-ladder-verified.lean` (e.g. the exact strings
`/-- Step-level bridge. -/`, `/-- Loop-level bridge. -/`, `/-- Entry-point bridge. -/`,
`/-- State-threading entry point. -/`). A surviving placeholder means the phase is not done.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Saturation.lean` — nine docstrings plus the module docstring's
  `## Main Definitions` list.

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.Saturation` exits 0 (the `local` tier check — Lean doc
  comments elaborate, so a broken `/-- ... -/` delimiter is a compile error, not a prose defect).
- No placeholder docstring string from the artifact survives in the file.
- `git diff` still shows no change to any pre-existing declaration body and no import change.

---

### Phase 3: Full Verification Gate [COMPLETED]

**Goal**: Confirm every CI gate matches its measured baseline, with zero debt introduced.

**Tasks**:
- [x] `lake build Cslib` — confirm green at **3313 jobs** (baseline 3313). Confirmed: green at
      3313 jobs.
- [x] Sorry census over `Cslib/Logics/Modal/Tableau/` — confirm **exactly 1**, and that the single
      site is `branchSatisfiableIn_s4FC_ancestor_redirect` in
      `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (anchor on the declaration name; the line
      number recorded during research was 1227 but line numbers drift). Confirmed: exactly one
      `sorry` in `Cslib/Logics/Modal/Tableau/` (`FrameSoundness.lean:1251`, the
      `branchSatisfiableIn_s4FC_ancestor_redirect` blocked case; the build-warning line number
      1227 points at the enclosing declaration's signature, not the `sorry` token itself).
- [x] Confirm **zero** new `axiom` declarations. Run `#print axioms` (or `lean_verify`) on
      `modalStepBranchGen_eq_St`, `modalExpandBranchesGen_eq_St`, and `modalTableauGen_eq_St`;
      each must depend on `propext` and `Quot.sound` only — no `Classical.choice`, no `sorryAx`.
      Confirmed via `lean_verify` on all three: `{"axioms":["propext","Quot.sound"],"warnings":[]}`
      for each. `git diff` against pre-task HEAD shows zero new `axiom` lines anywhere.
- [x] `lake exe checkInitImports` — exit **0**. Confirmed.
- [x] `lake exe lint-style` — exit **0**. Confirmed.
- [x] `lake lint` — gate on **delta**, not exit code. It exits 1 at baseline with 145 pre-existing
      `unusedArguments` findings repo-wide. Capture the findings and confirm the count is 145 and
      that `Saturation.lean` contributes 0. Confirmed: "Found 145 errors" (delta 0), zero findings
      mentioning `Saturation.lean`.
- [x] `lake shake --add-public --keep-implied --keep-prefix` — gate on "**no Modal/Tableau findings
      AND count stays 9**", not on exit 0 (it exits 1 at baseline). Confirmed: 9 file entries,
      none in `Modal/Tableau`.
- [x] `lake test` — exit **0**, including `S4LoopGuardRegression` and `ModalFrameSeparation`.
      Confirmed: exit 0, both tests built successfully (9378 jobs).
- [x] Confirm no vacuous definitions were introduced (`:= True`, `:= Unit`, `:= trivial`).
      Confirmed: zero matches in `Saturation.lean`.

**Timing**: 0.5 hours

**Depends on**: 2

**Verification Tier**: full

**Scope Hypothesis**: Every baseline number above (3313 build jobs, 1 Modal/Tableau sorry, 145
`lake lint` findings, 9 `lake shake` findings) is a measurement taken during the research phase at
one specific HEAD, not a permanent constant. Other tasks may have landed since. Confirm at
implementation time by re-measuring each baseline on a **clean tree at the current HEAD before
Phase 1's insertion** — or, if Phase 1 is already committed, by `git stash`-free comparison against
the parent commit. If a baseline has moved for reasons unrelated to this task, record the new
baseline in the summary and gate on **delta from the current baseline**, never on the stale
recorded number.

**Files to modify**: none (verification only).

**Verification**: Every bullet above matches its stated baseline. Any deviation is a phase
failure, not a tolerance — the research phase measured all of these with the exact same change in
the tree, so a mismatch means the insertion diverged from the verified artifact.

---

## Testing & Validation

- [x] `lake build Cslib` green at 3313 jobs.
- [x] `lake test` exit 0 (9378 jobs at research time), `S4LoopGuardRegression` and
      `ModalFrameSeparation` both passing.
- [x] Modal/Tableau sorry census exactly 1, at `branchSatisfiableIn_s4FC_ancestor_redirect`.
- [x] Zero new axioms; the three bridges depend on `propext` and `Quot.sound` only.
- [x] `lake exe checkInitImports` exit 0; `lake exe lint-style` exit 0.
- [x] `lake lint` delta zero (145 -> 145); zero findings in `Saturation.lean`.
- [x] `lake shake` count stays 9 with none in Modal/Tableau.
- [x] `git diff` confirms zero existing declarations edited and zero imports added.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Tableau/Saturation.lean` — nine new declarations plus expanded docstrings
  and an updated module-docstring `## Main Definitions` list.
- `specs/562_tableau_ruleapplyst_additive_introduction/plans/01_st-ladder-additive-insertion.md`
  (this file).
- `specs/562_tableau_ruleapplyst_additive_introduction/summaries/01_st-ladder-additive-insertion-summary.md`
  (written at implementation completion).

## Rollback/Contingency

The change is confined to a single file and is purely additive, so rollback is
`git checkout Cslib/Logics/Modal/Tableau/Saturation.lean` at the last green commit — subject to
the "No Destructive Git on Uncommitted Work" rule: if the tree is dirty, run
`bash .claude/scripts/git-snapshot.sh 562` first. Because Phase 1 is `atomic-batch`, a failed
Phase 1 leaves nothing committed and rollback is a single-file discard of uncommitted work
(snapshot first). A failed Phase 2 or 3 rolls back to the Phase 1 commit, which is independently
green. There is no downstream consumer to unwind: nothing in the repository references the St
ladder yet — `modalExpandBranchesS4Keyed`'s migration onto it is a separate, later task.
