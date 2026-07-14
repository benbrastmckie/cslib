# Implementation Plan: Task #459 - CSLib longLine style fix

- **Task**: 459 - Vet 299 longLine style: wrap lines exceeding 100 chars in Modal Tableau modules
- **Status**: [COMPLETED]
- **Effort**: 1.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/459_vet_299_longline_style/.orchestrator-handoff.json
- **Artifacts**: plans/01_longline-style-fix.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Purely mechanical whitespace reflow to bring 57 over-length lines under the CSLib
`linter.style.longLine` 100-character limit across two Modal Tableau modules. All lines wrap at
existing comma/operator/keyword boundaries with ZERO change to tactic order, term structure,
hypothesis names, or proof logic. The plan is split one file per phase; the two phases are
independent (no shared symbols, no ordering dependency) and could run in parallel, but each
gates on its own scoped `lake build` staying green plus `awk 'length>100'` returning nothing.

### Research Integration

The research handoff (`.orchestrator-handoff.json`) verified exact line counts and numbers (no
drift from the task description) and categorized every long line into five mechanical wrapping
patterns:

- **A1** (single-element `refine ⟨[⟨.sign, PROP, lbl⟩] ++ b, ...⟩`): SoundnessStep lines
  268, 334, 348, 371, 384, 398, 412, 1086, 1136, 1149, 1164, 1204, 1219, 1234 (14 lines).
- **A2** (`rcases Classical.em (...) with ha | ha`): SoundnessStep lines 522, 545, 568, 686,
  709, 732, 850, 873, 896 (9 lines).
- **A3** (two-element `refine ⟨[⟨.pos, ...⟩, ⟨.neg, ...⟩] ++ b, ...⟩`): SoundnessStep lines
  1256, 1274, 1292, 1310, 1328, 1346, 1364, 1384, 1402, 1420, 1512, 1530, 1548, 1566, 1584,
  1602, 1620 (17 lines).
- **A4** (`have hnc : ... := fun hC => hneg (fun _ => hC)`): SoundnessStep lines 1437, 1455,
  1473, 1491 (4 lines).
- **C** (Completeness varied statements): Completeness lines 118, 128, 169, 177, 195, 455,
  477, 479, 529 (9 lines).

The in-file wrapping precedent is `SoundnessStep.lean` lines 320-322 (three-line `refine`
anonymous-constructor split, +2-space continuation indent). All new wraps must mirror this exact
style.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this fix task (roadmap flag not set).

## Goals & Non-Goals

**Goals**:
- Bring all 48 long lines in `SoundnessStep.lean` under 100 characters.
- Bring all 9 long lines in `Completeness.lean` under 100 characters.
- Preserve identical proof semantics (compiled output unchanged); each module stays green.

**Non-Goals**:
- No change to tactic order, term structure, hypothesis names, or proof logic.
- No new lemmas, `set`/`let` bindings, abstractions, or helper definitions.
- No edits to any file other than the two named modules.
- No reformatting of lines already within the limit (touch only the enumerated lines and the
  continuation lines they spawn).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Line-number drift after earlier edits shifts later targets within the same file | M | M | Edit each file top-to-bottom; re-derive targets from `awk 'length>100 {print NR": "length}'` before and after; match on line content, not absolute number |
| A single break still leaves line 1 > 100 for deeply-nested imp-prop cases (A1 lines 384/398/412/1204/1219/1234; A3 worst cases) | M | M | Apply the second inner-comma break per handoff strategy; re-run `awk` to confirm every physical line <= 100 |
| Accidental mid-token break or altered term changes proof semantics | H | L | Break only at commas inside anonymous constructors, at `∧`, before `with`, or before `:=`; verify with scoped `lake build` after each file |
| Continuation indent inconsistent with CSLib convention | L | L | Use +2-space continuation from the keyword column, matching the 320-322 precedent |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |

Phases within the same wave can execute in parallel. Phases 1 and 2 touch disjoint files with no
shared symbols; they may be executed in either order or concurrently. Each phase is
self-verifying.

### Phase 1: Wrap long lines in SoundnessStep.lean [COMPLETED]

**Goal**: Reduce all 48 over-length lines in
`Cslib/Logics/Modal/Tableau/SoundnessStep.lean` to <= 100 characters using the A1/A2/A3/A4
mechanical wrapping patterns, mirroring the 320-322 precedent.

**Tasks**:
- [ ] Snapshot current offenders: `awk 'length>100 {print NR": "length}' Cslib/Logics/Modal/Tableau/SoundnessStep.lean` (expect 48 lines matching the handoff list).
- [ ] **A1** (lines 268, 334, 348, 371, 384, 398, 412, 1086, 1136, 1149, 1164, 1204, 1219, 1234): break after the list-literal comma — line 1 ends `] ++ b,`, then `List.mem_cons_self, W, m, f, hacc, ?_⟩` on a +2-indent continuation. For the deeply-nested imp-prop cases (384/398/412/1204/1219/1234, ~145-147 chars) add a second break after `.sign,` placing `Proposition.imp a1 (...), lbl⟩] ++ b,` on its own +4-indent line so line 1 stays <= 100.
- [ ] **A2** (lines 522, 545, 568, 686, 709, 732, 850, 873, 896): break before `with` — `rcases Classical.em (...)` on line 1, `with ha | ha` on a +2-indent continuation.
- [ ] **A3** (lines 1256, 1274, 1292, 1310, 1328, 1346, 1364, 1384, 1402, 1420, 1512, 1530, 1548, 1566, 1584, 1602, 1620): three-line split — line 1 ends `⟨.pos, PROP1, lbl⟩,`; line 2 `⟨.neg, PROP2, lbl⟩] ++ b,` at +2 indent; line 3 `List.mem_cons_self, W, m, f, hacc, ?_⟩` at +2 indent. Use the uniform 3-line form for all A3 sites (safe even for the 160-char worst cases).
- [ ] **A4** (lines 1437, 1455, 1473, 1491): break after `:=` — type signature `have hnc : ... :=` on line 1, body `fun hC => hneg (fun _ => hC)` on a +2-indent continuation. (Each is exactly 1 char over.)
- [ ] Edit top-to-bottom so later line numbers are re-derived from content, not stale absolute positions.

**Timing**: ~1 hour (48 edit sites).

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/SoundnessStep.lean` - reflow the 48 enumerated long lines (plus the continuation lines they introduce); no other lines touched.

**Verification**:
- `awk 'length>100' Cslib/Logics/Modal/Tableau/SoundnessStep.lean` returns nothing.
- `lake build Cslib.Logics.Modal.Tableau.SoundnessStep` stays green (sorry-free, no new warnings).

---

### Phase 2: Wrap long lines in Completeness.lean [COMPLETED]

**Goal**: Reduce all 9 over-length lines in
`Cslib/Logics/Modal/Tableau/Completeness.lean` to <= 100 characters using the category-C
case-by-case boundary breaks.

**Tasks**:
- [ ] Snapshot current offenders: `awk 'length>100 {print NR": "length}' Cslib/Logics/Modal/Tableau/Completeness.lean` (expect 9 lines: 118, 128, 169, 177, 195, 455, 477, 479, 529).
- [ ] Line 118 (`cases hfind_bot : b.find? (fun ...) with`): break before `with` at +2 indent.
- [ ] Line 128 (`have hany : b.any (fun ...) = true :=`): break before `:=` (or before `= true`) at +2 indent.
- [ ] Lines 169, 177 (`by_cases hinb : (b.any fun x => x == (⟨...⟩ : SignedFormula ...)) = true`): break before `= true` at +2 indent.
- [ ] Line 195 (`∃ w', acc.hasEdge w w' = true ∧ (...) ∈ b :=`): break at the `∧` connective, continuation at +2 indent.
- [ ] Lines 455, 477, 479, 529 (continuation tails of already-wrapped IH-application terms ending `...omega) w).N (h... ⟨...⟩ (by simp))`): break before the final `(hbr ...)` / `(hcond ...)` argument application, aligning under the existing continuation indent.
- [ ] Edit top-to-bottom, matching on line content.

**Timing**: ~30 minutes (9 edit sites).

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Completeness.lean` - reflow the 9 enumerated long lines (plus continuation lines); no other lines touched.

**Verification**:
- `awk 'length>100' Cslib/Logics/Modal/Tableau/Completeness.lean` returns nothing.
- `lake build Cslib.Logics.Modal.Tableau.Completeness` stays green (sorry-free, no new warnings).

---

## Testing & Validation

- [x] `awk 'length > 100' Cslib/Logics/Modal/Tableau/SoundnessStep.lean` returns nothing.
- [x] `awk 'length > 100' Cslib/Logics/Modal/Tableau/Completeness.lean` returns nothing.
- [x] `lake build Cslib.Logics.Modal.Tableau.SoundnessStep` succeeds, no new errors/warnings.
- [x] `lake build Cslib.Logics.Modal.Tableau.Completeness` succeeds, no new errors/warnings.
- [x] `lake exe lint-style` reports no `longLine` violations for the two modules (exit 0, no output).
- [x] `git diff` confirms only whitespace/line-break changes (verified via whitespace-normalization
  diff: content identical to HEAD after collapsing all whitespace to single spaces).

## Artifacts & Outputs

- `Cslib/Logics/Modal/Tableau/SoundnessStep.lean` (reflowed, 0 long lines)
- `Cslib/Logics/Modal/Tableau/Completeness.lean` (reflowed, 0 long lines)
- `specs/459_vet_299_longline_style/summaries/01_longline-style-fix-summary.md` (on completion)

## Rollback/Contingency

Because the change is pure reflow confined to two files, rollback is `git checkout --
Cslib/Logics/Modal/Tableau/SoundnessStep.lean Cslib/Logics/Modal/Tableau/Completeness.lean`. If
a scoped `lake build` regresses after wrapping a specific line, revert that single line's break
(restore the original one-liner) and re-attempt with the alternate boundary given in the handoff
strategy (e.g., A3 2-line vs 3-line form, or Completeness `:=` vs `= true` break point). No
proof-logic recovery is needed since no logic is altered.
