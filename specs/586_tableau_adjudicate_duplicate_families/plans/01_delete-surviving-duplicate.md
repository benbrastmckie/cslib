# Implementation Plan: Adjudicate and delete the audited duplicate re-derivation families

- **Task**: 586 - Adjudicate and delete the audited duplicate re-derivation families
- **Status**: [IMPLEMENTING]
- **Effort**: 2 hours
- **Dependencies**: 553 (satisfied; parent task 558's phases 8-11 already landed)
- **Research Inputs**: specs/586_tableau_adjudicate_duplicate_families/reports/01_adjudicate-duplicate-families.md
- **Artifacts**: plans/01_delete-surviving-duplicate.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

The task brief presumes 45 surviving duplicate re-derivation rows awaiting deletion. The research
census established that 43 of them no longer exist — task 558's own Phases 8-11 deleted them
roughly five and a half hours *before* the statement-equivalence audit that enumerates them was
committed. The audit is an input-staleness artifact, not a description of the live tree. Exactly
two audited declarations survive: `accFreshInv_append_S4` (out of scope by the task's own
reachability boundary) and `modalSubfmls_self_mem_S5` (in scope, and already trial-verified
deletable by a reversible build experiment that was fully restored).

The net actionable work is therefore **one declaration deletion, eight same-file call-site
rewrites, and three prose reconciliations** — plus a full verification gate. Definition of done:
`modalSubfmls_self_mem_S5` is gone, its eight call sites route to the public
`FmpMeasure.lean` origin `modalSubfmls_self_mem`, the stale prose that justified the copy is
corrected, and every gate in §Testing & Validation holds at its measured baseline.

### Research Integration

Findings from `reports/01_adjudicate-duplicate-families.md` carried directly into this plan:

- **Row census** (§2): 43 GONE, 2 PRESENT. Reproduced independently by a suffix-family census
  over all 910 `Modal/Tableau` declarations returning 14 residue families — matching task 558
  Phase 11's recorded figure exactly, zero drift. Phase 1 re-runs this as a drift guard.
- **The three verdict classes** (§3): the 6 WEAKER rows are all already deleted and the mandatory
  pre-deletion `.1`/Nodup check passes retrospectively — the strong `modalKnownWorlds_fold_spec`
  survives public in `Support/KnownWorlds.lean` with its `.Nodup` conjunct consumed by
  `modalKnownWorlds_nodup` (six live consumers). The 1 DIFFERENT row's trap did not fire:
  `Support/Accessibility.lean` publishes both converse directions as distinct public lemmas.
  Neither class needs any action; neither appears as a phase below.
- **The falsified exclusion rationale** (§4): task 558 Phase 10 retained `modalSubfmls_self_mem`
  on the ground that the copy dodges an ambient `[Hashable Atom]` instance. `git blame` dates the
  copy to 2026-07-15 and the origin's `omit [DecidableEq Atom] [Hashable Atom] in` prefix to
  2026-07-27. The rationale was true when written and false twelve days later.
- **Pre-verified feasibility** (§4): the deletion was performed as a reversible experiment,
  `S5Simplification` + `FiveSimplification` + `FrameSoundness` built green, and the tree was
  restored clean. This plan is not proposing an untested change.
- **Re-measured baselines** (§6): every figure in §Testing & Validation below is a fresh
  measurement against the current tree, not a carried-forward number.

### Prior Plan Reference

No prior plan for this task. Parent task 558's plans are a historical record of what was done and
must not be rewritten; the correction to its Phase 10 Reasoned Exclusions entry belongs in this
task's summary (Phase 3).

### Roadmap Alignment

No ROADMAP.md consultation was requested for this task and no `roadmap_path` was supplied.

## Goals & Non-Goals

**Goals**:
- Delete `modalSubfmls_self_mem_S5` from `S5Simplification.lean` and route its eight call sites to
  the public origin `modalSubfmls_self_mem` in `FmpMeasure.lean`.
- Correct the three prose records that the already-landed deletions falsified: the orphaned
  section header in `FiveSimplification.lean`, the drifted comment-site count in
  `LoopChecking.lean`, and the `[Hashable Atom]` rationale in `S5Simplification.lean`'s module
  docstring.
- Record in this task's summary that task 558's Phase 10 Reasoned Exclusions entry for
  `modalSubfmls_self_mem` is superseded, with the dated evidence.
- Hold every measured gate at its baseline.

**Non-Goals**:
- **Do not treat "45 deletions" as a target.** 43 of the 45 audited rows were already correctly
  deleted. Manufacturing work to reach 45 is the single highest-severity failure mode identified
  by the research; the actionable set is one declaration.
- **Do not touch `accFreshInv_append_S4`.** Its origin `accFreshInv_append` is private to
  `Soundness.lean`, and `LoopChecking.lean` does not import `Soundness.lean` — the two are
  siblings, never in an upstream relation. This is class (c) (import reachability), explicitly
  excluded by the task's own scope boundary, and de-privatization would not fix it.
- Do not absorb the sibling class-(c) families (`hasEdge_addEdge_mono` for `FrameSoundness`;
  `modalApplyOne_boxPos_acc_eq` / `modalApplyOne_diamondNeg_acc_eq` / `not_shape_of_not_or` for
  `BDriver`←`TDriver`).
- Do not re-run the statement-equivalence audit; it is a given input.
- Do not edit `.lean` artifacts under `specs/archive/` — they are frozen, out of the build, and
  are the only other places the deleted name appears.
- Do not rewrite task 558's historical plan files.
- Do not fix the stale line-number citations in
  `Propositional/Tableau/Intuitionistic/Scheme.lean` (§10.1 of the research) — different
  subsystem, flagged for a future prose pass.
- No new definitions, lemmas, notation, or typeclasses. No de-privatization, no new imports, no
  re-exports.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The brief's 45-row premise is treated as a target and invented work is produced | H | M | Phase 1 is a mandatory drift guard whose expected result is *two* survivors, and the Non-Goals above state the countermeasure explicitly. Any phase producing more than one deletion is out of contract |
| Tree moved again between research and implementation | M | L | Phase 1 gates all writes. If the census does not return 14 residue families and exactly the two named survivors, stop and mark `[BLOCKED]` for user review — do not re-derive the adjudication ad hoc |
| `accFreshInv_append_S4` silently absorbed as "the last one left" | H | L | Named in Non-Goals with the import-graph evidence; Phase 3 records it as a decided exclusion rather than leaving it looking unfinished |
| `@[simp]` on the origin changes simp behaviour at the eight sites | M | L | The origin is `@[simp]` and is already publicly imported and in scope at every site, so the simp set is unchanged by the deletion. Verified green in the research experiment |
| Lint delta from removing a private declaration | L | L | Gate on delta = 0, never on exit code. The deleted declaration already carries `omit [DecidableEq Atom] [Hashable Atom] in`, so it contributes zero `unusedArguments` findings and its removal must move the count by exactly zero. A non-zero delta signals something other than the intended deletion happened |
| Gating on `lake shake` / `lake lint` exit code instead of content | M | M | Both are non-zero at steady state (9 and 145 findings). Gate on "none in `Modal/Tableau`" and "delta 0" respectively |
| Naive `grep -rn '\bsorry\b'` misreads the sorry census as 24 | M | M | The 24 includes docstring prose (`sorry-free`) and `LoopChecking.lean`'s own census-script text. Count actual `sorry` terms; the true figure is 1 |
| Line-number anchors drift mid-task | L | M | Anchor every edit on declaration names and quoted comment text, never line numbers |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel. This plan is fully sequential: Phase 2 must
not write before the drift guard passes, and Phase 3's corrected figures are only true once
Phase 2's deletion has landed.

### Phase 1: Drift guard — re-run the declaration-level census [COMPLETED]

**Goal**: Confirm the tree still matches the state the adjudication was derived against, before
anything is written. This phase writes no code and no prose.

**Tasks**:
- [x] Confirm `modalSubfmls_self_mem_S5` is still present as a `private lemma` in
      `Cslib/Logics/Modal/Tableau/S5Simplification.lean`, and count its references
      (expected: one declaration, one module-docstring mention, eight call sites). **Observed**:
      exactly 10 matches — 1 `private lemma` declaration (line 819), 1 module-docstring mention
      (line 88), 8 call sites (lines 1145, 1195, 1212, 1251, 1301, 1318, 1365, 1415). Matches
      exactly.
- [x] Confirm the public origin `modalSubfmls_self_mem` is still present in
      `Cslib/Logics/Modal/Tableau/FmpMeasure.lean`, still `@[simp]`, and still carries the
      `omit [DecidableEq Atom] [Hashable Atom] in` prefix. If the `omit` prefix is gone, the
      deletion rationale is void — stop and mark `[BLOCKED]`. **Observed**: present at line 273,
      `@[simp]` on line 272, `omit [DecidableEq Atom] [Hashable Atom] in` on line 268. Rationale
      intact.
- [x] Confirm `S5Simplification.lean` still carries
      `public import Cslib.Logics.Modal.Tableau.FmpMeasure`. **Observed**: present at line 10.
- [x] Re-run the suffix-family census over `Cslib/Logics/Modal/Tableau/` (any suffixed
      declaration whose unsuffixed base name also exists as a declaration). Expected: 14 residue
      families. **Observed**: exactly 14 residue families over 1099 declarations, matching
      exactly (including `modalSubfmls_self_mem` and `accFreshInv_append` among the 14).
- [x] Spot-check that a representative sample of the 43 GONE names (e.g.
      `modalKnownWorlds_fold_spec_S5`, `mem_modalUniverse_of_Five`, `outDeg_addEdge_self_S4`)
      still return zero declaration matches. **Observed**: zero matches for all three.
- [x] Confirm `accFreshInv_append_S4` is present in `LoopChecking.lean` and that
      `LoopChecking.lean` still does not import `Soundness.lean`. **Observed**: present (private
      lemma at line 5449, 3 call sites). `LoopChecking.lean`'s import block (lines 9-20) has no
      `Soundness` import.
- [x] Record the observed figures. If any expectation fails, stop: mark the task `[BLOCKED]` with
      the divergence recorded, and do not proceed to Phase 2. **All six confirmations passed with
      zero divergence from the research's figures. Proceeding to Phase 2.**

**Timing**: 0.3 hours

**Depends on**: none

**Verification Tier**: prose

*(Tier rationale: this phase makes zero edits and has no compile surface. `prose` is the correct
floor, not a relaxation — the tie-break-upward rule has nothing to bite on where no file is
written.)*

**Scope Hypothesis**: This phase asserts 14 residue families, exactly two surviving audit-row
declarations (`modalSubfmls_self_mem_S5`, `accFreshInv_append_S4`), and eight call sites for the
former. Confirm all three by direct grep at implementation time. These figures are the *gate*,
not a description: a mismatch blocks the task rather than being reconciled in passing.

**Files to modify**: none (read-only phase)

**Verification**:
- All six confirmations above return their expected values, recorded in the phase notes.
- `git status --porcelain Cslib/` is empty at the end of this phase.

---

### Phase 2: Delete the one in-scope duplicate [COMPLETED]

**Goal**: Remove `modalSubfmls_self_mem_S5` and route its call sites to the public origin.

**Tasks**:
- [x] In `Cslib/Logics/Modal/Tableau/S5Simplification.lean`, rewrite each call site of
      `modalSubfmls_self_mem_S5` to `modalSubfmls_self_mem`. Every site has the identical shape
      `List.mem_cons_of_mem _ (modalSubfmls_self_mem_S5 X)` with `X ∈ {φ, ψ}`; the change is a
      pure name substitution. Locate by declaration name, never by line number. **Observed**: all
      8 sites rewritten (lines 1137, 1187, 1204, 1243, 1293, 1310, 1357, 1407 in the post-edit
      file).
- [x] Delete the `private lemma modalSubfmls_self_mem_S5` declaration, its `/-- Local
      re-derivation of ... -/` docstring, and the `omit [DecidableEq Atom] [Hashable Atom] in`
      line that immediately precedes that docstring. Take care not to remove the `omit
      [Hashable Atom] in` line belonging to the *next* declaration. **Observed**: deleted lines
      814-821 of the pre-edit file (the `omit [DecidableEq Atom] [Hashable Atom] in` line,
      3-line docstring, and 2-line declaration+proof); the following `omit [Hashable Atom] in`
      line for `modalApplyOneS5_knownWorlds_step` is untouched.
- [x] Verify no reference to `modalSubfmls_self_mem_S5` remains anywhere under `Cslib/`.
      Matches under `specs/archive/` are frozen historical artifacts and must be left untouched.
      **Observed**: one remaining match — the module-docstring mention at line 88, deliberately
      deferred to Phase 3's prose reconciliation (not a declaration reference).
- [x] Build `lake build Cslib.Logics.Modal.Tableau.S5Simplification` and confirm exit 0.
      **Observed**: exit 0, 868 jobs, matching the research's measured figure exactly.

**Timing**: 0.5 hours

**Depends on**: 1

**Verification Tier**: local

*(Tier rationale: `modalSubfmls_self_mem_S5` is `private`, so no other module can reference it and
no externally visible signature changes. All eight call sites are in the same file. Building
`S5Simplification` alone is the correct in-phase scope; the research additionally built
`FiveSimplification` and `FrameSoundness` green, and re-running those is optional reassurance,
not a requirement of this tier. The full gate in Phase 4 remains unchanged.)*

**Scope Hypothesis**: Eight call sites, all within `S5Simplification.lean`, all of the identical
`List.mem_cons_of_mem _ (modalSubfmls_self_mem_S5 X)` shape; `S5Simplification.lean` is the only
live consumer repo-wide. Confirm the count and the sole-consumer claim by grep before editing and
again after; if the true count differs, record the actual figure rather than forcing the edit to
match eight.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean` — delete one `private lemma` plus its
  docstring and `omit` prefix; substitute the origin name at each call site.

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.S5Simplification` exits 0.
- Zero matches for `modalSubfmls_self_mem_S5` under `Cslib/`.
- No `sorry` introduced (the origin's proof already exists verbatim and is reachable; this
  deletion cannot create one).

---

### Phase 3: Reconcile the stale records [COMPLETED]

**Goal**: Correct the three prose defects the deletions falsified, and record the superseded
exclusion rationale. Prose only — no declarations are added, removed, or renamed.

**Tasks**:
- [x] `S5Simplification.lean` module docstring, section `## modalSubfmls Structural
      Re-Derivations`: its body is now false on both counts — it names
      `modalSubfmls_self_mem_S5` as "the sole surviving local re-derivation" and justifies
      retaining it by the `[Hashable Atom]` argument. Rewrite the section to record that the copy
      was consolidated to the now-public `FmpMeasure.lean` origin, alongside the existing note
      about `modalSubfmls_trans_S5`. If no re-derivation content remains in the section, remove
      the header rather than leaving it empty. **Observed**: no re-derivation content remained
      (both `modalSubfmls_self_mem_S5` and the already-consolidated `modalSubfmls_trans_S5` were
      gone), so the whole section was removed per the fallback instruction. Its one
      non-redundant fact (the `modalUniverseS5`/`modalWorldBoundS5` archival note) is
      independently recorded elsewhere in the same file near the `modalWorldBoundS5` definition.
- [x] `FiveSimplification.lean`: remove the orphaned section header
      `/-! ## modalKnownWorlds/modalUniverse Local Re-Derivations` and its body. The body
      describes Five-suffixed re-derivations that no longer exist, and it is followed immediately
      by the next `/-! ##` header with no declarations in between. **Observed**: header (actual
      text: `` `modalKnownWorlds`/`modalUniverse` Local Re-Derivations``) removed; confirmed
      orphaned (immediately followed by the next `/-! ##` header, no declarations between).
- [x] `LoopChecking.lean` inventory-census prose: the "Post-de-duplication update" bullet records
      the comment-string count as **11**; the tree's true count before Phase 2 is 13. Correct it
      to the post-Phase-2 measurement. Leave the historical **55** and **77** figures in the
      "Inventory figures that drifted" block alone — that block explicitly retains them as
      superseded historical baselines, and rewriting them would destroy the record it exists to
      keep. **Observed**: post-Phase-2 `grep -rho 'Local re-derivation' Cslib/ | wc -l` returns
      12; corrected all three occurrences of the stale figure within the bullet (headline count,
      "55 minus N" comparison, "remaining N comment sites" cross-reference). The 55/77 historical
      baselines in the separate block were left untouched.
- [x] Record in this task's summary artifact that task 558's Phase 10 Reasoned Exclusions entry
      for `modalSubfmls_self_mem` is **superseded**: its evidence ("Confirmed the ambient instance
      at the copy's site and the absence of an `omit` escape") did not survive the origin's
      2026-07-27 addition of `omit [DecidableEq Atom] [Hashable Atom] in`, twelve days after the
      copy was created on 2026-07-15. Do not edit task 558's plan files. **Observed**: recorded in
      `summaries/01_delete-surviving-duplicate-summary.md`; task 558's plan files untouched.
- [x] Record in this task's summary that `accFreshInv_append_S4` is a decided, evidenced
      exclusion (class (c), import reachability — `LoopChecking.lean` does not import
      `Soundness.lean`, and the origin is private to it), not unfinished work. **Observed**:
      recorded in the summary.
- [x] Read back each edited hunk and confirm every change lies inside a comment, docstring, or
      module-docstring region. **Observed**: `git diff` confirms all three hunks are whole,
      balanced `/-! ... -/` block removals or in-place figure edits inside an existing markdown
      code-fence prose block; `lake build` on all three files (Phase 2 + this phase) passed.

**Timing**: 0.4 hours

**Depends on**: 2

**Verification Tier**: prose

*(Blind spot acknowledged: `prose` does not catch an edit that crosses out of a comment boundary,
nor a doc-comment that is load-bearing. Lean's `/-! ... -/` and `/-- ... -/` blocks are
elaborated, and an unbalanced delimiter is a compile error — so the diff read-through must
confirm delimiter balance explicitly. Phase 4's full build is the backstop.)*

**Scope Hypothesis**: Three prose defects across three files, and a comment-site count moving from
13 to 12. Re-run `grep -rho 'Local re-derivation' Cslib/ | wc -l` after Phase 2 and write the
figure it actually returns — do not write 12 on the strength of this plan. Note the count is
case-sensitive and does not match line-wrapped occurrences, so the `FiveSimplification.lean`
orphan header's own wrapped mention is not part of the count and its removal should not move it.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean` — module-docstring section rewrite
- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` — remove orphaned section header and body
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — correct the comment-site count
- `specs/586_tableau_adjudicate_duplicate_families/summaries/01_*-summary.md` — supersession and
  exclusion records

**Verification**:
- Diff read-through confirms every changed hunk lies inside a comment/docstring region with
  balanced `/-! -/` and `/-- -/` delimiters.
- The corrected comment-site figure matches a freshly-run count.
- No declaration was added, removed, or renamed in this phase.

---

### Phase 4: Full gate [NOT STARTED]

**Goal**: Confirm every measured gate holds at baseline after the deletion and prose edits.

**Tasks**:
- [ ] `lake build Cslib` — expect exit 0. Baseline 3313 jobs; the figure may be at most trivially
      lower for the one removed declaration. A materially different figure warrants investigation
      before proceeding.
- [ ] `Modal/Tableau` sorry census — expect exactly **1**
      (`branchSatisfiableIn_s4FC_ancestor_redirect`, `FrameSoundness.lean`). Count actual `sorry`
      terms; naive `grep -rn '\bsorry\b'` returns 24 by over-counting docstring prose
      (`sorry-free`) and `LoopChecking.lean`'s own census-script text.
- [ ] `Modal/Tableau` axiom census — expect **0** (`grep -rnE '^axiom '`).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — expect **9 findings, exit 1**, with
      **none in `Modal/Tableau`**. Do **not** gate on exit 0. The nine known files are
      `Algorithms/Lean/TimeM`, `Computability/.../MultiTape/Deterministic`,
      `Foundations/Data/StackTape`, `Foundations/Relation/Defs`,
      `Computability/.../SingleTape/NonDeterministic`, `Foundations/Relation/Confluence`,
      `Foundations/Control/Monad/Free`, `Languages/CCS/Basic`,
      `Languages/CombinatoryLogic/Defs`.
- [ ] `lake lint` — expect **145 findings, exit 1**, i.e. **delta 0** against baseline. Gate on
      the delta, not the exit code. A non-zero delta means something other than the intended
      deletion happened.
- [ ] `lake exe checkInitImports` — expect exit 0.
- [ ] `lake exe lint-style` — expect exit 0.
- [ ] `lake test` — expect exit 0 (baseline 3676 jobs).
- [ ] Record every observed figure against its baseline in the summary.

**Timing**: 0.8 hours (dominated by build and test wall time)

**Depends on**: 3

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts eight gate baselines (3313 build jobs, sorry census 1,
0 axioms, 9 shake findings with 0 in `Modal/Tableau`, 145 lint findings, checkInitImports 0,
lint-style 0, test exit 0 / 3676 jobs). Each is a re-measurement obligation, not a fact to assume:
run every gate and record what it returns. Where a figure differs from baseline, report the
divergence rather than adjusting the baseline to match.

**Files to modify**: none (verification phase; the summary artifact is written under Phase 3's
recording obligation and updated here with the observed gate figures)

**Verification**:
- All eight gates recorded with observed-vs-baseline values.
- Any divergence is reported explicitly, never silently normalized.

---

## Testing & Validation

- [ ] `lake build Cslib` exits 0 (baseline 3313 jobs)
- [ ] `Modal/Tableau` sorry census is exactly 1, counting real `sorry` terms not naive grep hits
- [ ] `Modal/Tableau` axiom count is 0
- [ ] `lake shake --add-public --keep-implied --keep-prefix` yields 9 findings with none in
      `Modal/Tableau` (exit 1 is the steady state; not a gate)
- [ ] `lake lint` delta against the 145-finding baseline is 0 (exit 1 is the steady state; not a
      gate)
- [ ] `lake exe checkInitImports` exits 0
- [ ] `lake exe lint-style` exits 0
- [ ] `lake test` exits 0
- [ ] Zero references to `modalSubfmls_self_mem_S5` under `Cslib/`
- [ ] `accFreshInv_append_S4` is untouched and still present in `LoopChecking.lean`
- [ ] Exactly one declaration was deleted across the whole task

### Zero-debt compliance

No phase can introduce a `sorry`. The only Lean change is deleting a lemma whose proof
(`cases φ <;> simp [modalSubfmls]`) already exists byte-identically at a reachable public origin
with a byte-identical signature, verified green by build. No new axioms. If Phase 1's drift guard
fails, the correct response is `[BLOCKED]` for user review — never deferral, and never a
`sorry`-shaped workaround.

## Artifacts & Outputs

- `specs/586_tableau_adjudicate_duplicate_families/plans/01_delete-surviving-duplicate.md` (this
  file)
- `specs/586_tableau_adjudicate_duplicate_families/summaries/01_delete-surviving-duplicate-summary.md`
  — including the task 558 Phase 10 supersession record, the `accFreshInv_append_S4` exclusion
  record, and the observed-vs-baseline gate table
- Modified: `Cslib/Logics/Modal/Tableau/S5Simplification.lean`,
  `Cslib/Logics/Modal/Tableau/FiveSimplification.lean`,
  `Cslib/Logics/Modal/Tableau/LoopChecking.lean`

## Rollback/Contingency

- The change surface is three files and one deleted private declaration. Reverting is a single
  `git revert` of the phase commits, or `git checkout` of the three files from the pre-task
  commit if nothing has been committed yet.
- If Phase 1's drift guard fails: stop, mark the task `[BLOCKED]` with the observed divergence
  recorded, and surface it for user review. Do not re-derive the adjudication ad hoc — the whole
  point of the guard is that a moved tree invalidates the research's census.
- If Phase 2's build fails despite the research's green experiment: restore
  `S5Simplification.lean` from HEAD and mark `[BLOCKED]`. Do not attempt to keep the deletion by
  patching the proof — the deletion's entire justification is that the origin is a drop-in.
- If a Phase 4 gate diverges from baseline: report the divergence with the observed figure.
  Do not adjust the recorded baseline to match, and do not proceed to completion on a divergent
  gate.
