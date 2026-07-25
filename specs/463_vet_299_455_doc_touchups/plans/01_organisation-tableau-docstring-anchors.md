# Implementation Plan: Docs — ORGANISATION.md Tableau/ entries + durable-anchor docstring rewrites

- **Task**: 463 - Docs: update ORGANISATION.md Tableau/ tree sketches + strip internal task refs from public docstrings
- **Status**: [COMPLETED]
- **Effort**: 1 hour
- **Dependencies**: None
- **Research Inputs**: `specs/463_vet_299_455_doc_touchups/reports/01_organisation-tableau-and-docstring-cleanup.md`
- **Artifacts**: plans/01_organisation-tableau-docstring-anchors.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/plan-format-enforcement.md
  - .claude/rules/no-task-references-in-deliverables.md
  - .claude/rules/state-management.md
- **Type**: markdown

## Overview

Two independent, documentation-only fixes. First, `ORGANISATION.md`'s two tree sketches that omit
`Tableau/` get the missing entries: a full 8-file block under `Foundations/Logic/` plus its
`Tableau.lean` barrel, and a single terse collapsed line under `Logics/Modal/`. Second,
`Cslib/Logics/Modal/Tableau/LoopChecking.lean` has four docstring/section-comment citations of
ephemeral task numbers rewritten to durable anchors per
`.claude/rules/no-task-references-in-deliverables.md`. Definition of done: both tree sketches
document `Tableau/`, `grep -n "[Tt]ask [0-9]" LoopChecking.lean` returns nothing, and the Lean
file still builds unchanged.

### Research Integration

The research report materially narrowed the scope stated in the original task description:

- **Line anchors confirmed, no drift**: `ORGANISATION.md:26` (`Foundations/Logic/`) and
  `ORGANISATION.md:148` (`Modal/`) are exactly where the vet finding placed them.
- **`CompletenessLoop.lean` needs no changes.** The flagged `(task 442 Phase 6, FINAL)` /
  `(task 442 Phase 5a)` docstring notes on `modalTableau_complete`/`modalTableau_decides` were
  already stripped by commit `2f93962a`, an ancestor of HEAD. `grep` confirms zero
  `task`/`phase`/`FINAL` matches in the whole file. Do not touch this file.
- **The real remaining violation is `LoopChecking.lean`** — 4 citations at lines 4665
  (`Task 535`), 5481, 5696, 5949 (`task 511` x3). Exact current text and suggested replacements
  are in the report's Findings §3.
- **Modal/ `Tableau/` entry should be terse**, matching the `Propositional/Tableau/` precedent at
  `ORGANISATION.md:127-131`, which likewise collapses a large subdirectory rather than listing
  all 20 files.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No roadmap context provided for this task.

## Goals & Non-Goals

**Goals**:
- Document the existing `Tableau/` placement in both `ORGANISATION.md` tree sketches.
- Replace all four ephemeral task-number citations in `LoopChecking.lean` with durable anchors.
- Leave every Lean proof, definition, and declaration byte-identical — comments and docstrings only.

**Non-Goals**:
- Fixing the broader staleness of the `Modal/` tree sketch (also missing `LogicalEquivalence.lean`,
  `Metalogic.lean`, `ProofSystem/`, `Semantics/Birelational.lean`). Out of scope; a follow-up task
  can pick this up.
- Touching `CompletenessLoop.lean` — already clean.
- Rewriting the ~25 bare `Phase N` narrative section headers in `LoopChecking.lean`. These carry no
  task number and the rule's explicit trigger is the `task N` pattern; they read as durable internal
  section markers. Left as-is unless separately requested.
- Any restructuring of `ORGANISATION.md` beyond inserting the two `Tableau/` entries.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A docstring edit breaks a Lean comment delimiter (`/-!`, `/--`, `-/`) and fails the build | M | L | Phase 2 verification runs `lake build` on the module; edits stay inside existing comment bodies and never touch delimiters |
| Scope creep into the rest of the stale `Modal/` tree sketch | L | M | Explicit Non-Goal above; Phase 1 touches only the `Tableau/` line |
| Report's inferred one-line file descriptions for `Foundations/Logic/Tableau/` do not match actual module docstrings | L | M | Phase 1 verifies each description against the file's own module docstring rather than copying the report verbatim |
| Tree-sketch ASCII box-drawing alignment drifts from surrounding entries | L | M | Match the column alignment of the adjacent entries in the same fenced block |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |

Phases within the same wave can execute in parallel. Phases 1 and 2 touch disjoint files
(`ORGANISATION.md` vs. `Cslib/Logics/Modal/Tableau/LoopChecking.lean`) and have no ordering
constraint.

---

### Phase 1: Add Tableau/ entries to both ORGANISATION.md tree sketches [COMPLETED]

- **Goal:** Both tree sketches document the `Tableau/` subdirectory that already exists on disk.
- **Tasks:**
  - [x] In the `Foundations/` fenced block (opens line 24), add a `Tableau.lean` barrel line plus a
        `Tableau/` block enumerating all 8 files: `Sign.lean`, `SignedFormula.lean`,
        `RuleResult.lean`, `Branch.lean`, `Closure.lean`, `ClosureCondition.lean`, `Measure.lean`,
        `PropositionalRules.lean`. Place between `ProofSystem.lean` (line 30) and `Theorems.lean`
        (line 32) to mirror on-disk ordering, or as the last `Logic/` block after `Automation/`
        (lines 47-48) — either is consistent with the file's existing conventions. *(completed:
        placed as the last `Logic/` block, after `Automation/`, mirroring how `Theorems.lean`
        precedes `Theorems/`)*
  - [x] Verify each one-line description against the corresponding file's actual module docstring
        (`Cslib/Foundations/Logic/Tableau/*.lean`). Do not copy the research report's inferred
        descriptions verbatim. *(completed: descriptions rewritten from each file's own `/-!`
        module docstring, not copied verbatim from the report)*
  - [x] In the `Modal/` fenced block (lines 147-159), add a single terse collapsed entry for
        `Tableau/` summarizing the 20-file subdirectory (K/T/B/S4/S5 drivers, saturation,
        soundness/completeness), matching the `Propositional/Tableau/` precedent at lines 127-131.
        *(completed)*
  - [x] Fix the box-drawing connectors so the last entry in each block uses `└──` and preceding
        entries use `├──` (inserting after `Metalogic/` at line 153 changes which entry is last).
        *(completed: `Automation/` and `Metalogic/` connectors changed `└──`→`├──` in their
        respective blocks; new last entries `Tableau/` use `└──`)*
  - [x] Match the description-column alignment of adjacent entries in the same block. *(completed)*
- **Timing:** 30 minutes
- **Depends on:** none
- **Files to modify:**
  - `ORGANISATION.md` — insert `Tableau.lean` + `Tableau/` block in the `Foundations/Logic/` sketch;
    insert one collapsed `Tableau/` line in the `Modal/` sketch
- **Verification:**
  - `grep -n "Tableau" ORGANISATION.md` shows entries inside both the `Foundations/` block and the
    `Modal/` block
  - Every file listed under `Foundations/Logic/Tableau/` in the sketch matches
    `ls Cslib/Foundations/Logic/Tableau/` exactly (8 files, no extras, none missing)
  - Both fenced blocks still render as well-formed trees (no orphaned `├──` on a final entry)

---

### Phase 2: Rewrite LoopChecking.lean task-number citations to durable anchors [COMPLETED]

- **Goal:** Zero ephemeral task-number citations remain in `LoopChecking.lean`, with no change to
  any proof, definition, or declaration.
- **Tasks:**
  - [x] Line 4665, `/-! ## Keyed S4 Driver (Bespoke, Path (b))` section comment: drop the
        `Task 535 closes ...` lead-in and state the rationale directly (e.g. `This section closes
        \`Decidable (s4Valid φ)\` via a bespoke, S4-specific \`keys\`-threaded driver, rather than
        ...`). The remainder of the paragraph is already durable and needs no other change.
        *(completed: reflowed to stay within the 100-char line-length linter)*
  - [x] Line 5481, keyed Hintikka bundle docstring: replace `` `S4LoopInv` (task 511, frozen,
        above) `` with a durable anchor to the structure itself — `` `S4LoopInv` (frozen, defined
        above in this file) `` or similar. `S4LoopInv` is a `structure` declared at line 4362; the
        declaration name is the durable anchor, so prefer naming it over citing a line number.
        *(completed)*
  - [x] Line 5696, `S4KeyedHintikkaInv` docstring: replace `` the frozen `S4LoopInv` (task 511) ``
        with the same durable-anchor form. *(completed)*
  - [x] Line 5949, `Phase 7 — single-step preservation` docstring: replace `` the ambient
        `S4LoopInv` (task 511, consumed for `keyLowerBd`'s blocked-witness argument) `` with the
        durable-anchor form, keeping the `keyLowerBd` rationale intact. *(completed)*
  - [x] Confirm no Lean comment delimiters (`/-!`, `/--`, `-/`) were altered and no code line was
        touched. *(completed: confirmed via `git diff` — all changed lines are within existing
        comment/docstring bodies)*
- **Timing:** 30 minutes
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — 4 comment/docstring edits at lines 4665, 5481,
    5696, 5949 (line numbers shift as edits are applied; anchor on the surrounding text)
- **Verification:**
  - `grep -n -i "task [0-9]" Cslib/Logics/Modal/Tableau/LoopChecking.lean` returns no matches
  - `git diff --stat Cslib/Logics/Modal/Tableau/LoopChecking.lean` shows a small comment-only diff
  - `git diff Cslib/Logics/Modal/Tableau/LoopChecking.lean` contains no changed line outside a
    comment or docstring body
  - `lake build Cslib.Logics.Modal.Tableau.LoopChecking` succeeds

---

## Testing & Validation

- [ ] `grep -rn -i "task [0-9]" Cslib/Logics/Modal/Tableau/ Cslib/Foundations/Logic/Tableau/`
      returns zero matches
- [ ] `ORGANISATION.md`'s `Foundations/Logic/Tableau/` listing matches
      `ls Cslib/Foundations/Logic/Tableau/` exactly
- [ ] `ORGANISATION.md`'s `Modal/` block contains a `Tableau/` entry
- [ ] `lake build Cslib.Logics.Modal.Tableau.LoopChecking` succeeds
- [ ] Full diff is documentation-only: no `.lean` code line, definition, or proof term changed

## Artifacts & Outputs

- `ORGANISATION.md` (modified — two tree-sketch insertions)
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (modified — 4 comment/docstring rewrites)
- `specs/463_vet_299_455_doc_touchups/summaries/01_organisation-tableau-docstring-anchors-summary.md`

## Rollback/Contingency

Both phases are self-contained, documentation-only edits to two files with no cross-dependency.
Revert either independently with `git checkout HEAD -- <path>` (safe only on an otherwise clean
tree — see `.claude/rules/git-workflow.md`). If the `lake build` in Phase 2 fails, the cause is
almost certainly a mangled comment delimiter: restore the file and re-apply the four edits one at a
time, rebuilding after each.
