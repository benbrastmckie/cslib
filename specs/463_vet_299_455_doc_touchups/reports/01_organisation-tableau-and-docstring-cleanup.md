# Research Report: Task #463

**Task**: 463 - vet_299_455_doc_touchups
**Started**: 2026-07-24T23:03:00-07:00
**Completed**: 2026-07-24T23:20:00-07:00
**Effort**: small (documentation-only)
**Dependencies**: None
**Sources/Inputs**: Codebase (ORGANISATION.md, Cslib/Logics/Modal/Tableau/, Cslib/Foundations/Logic/Tableau/), git log/blame
**Artifacts**: - this report
**Standards**: report-format.md, subagent-return.md, `.claude/rules/no-task-references-in-deliverables.md`

## Executive Summary

- **ORGANISATION.md**: both cited line numbers are accurate (no drift). `Modal/` tree sketch
  starts at line 148 and omits `Tableau/` entirely (20 files). `Foundations/Logic/` tree sketch
  starts at line 26 and omits `Tableau/` entirely (8 files, matching the task description's
  enumeration exactly).
- **CompletenessLoop.lean**: the specific finding (ephemeral `(task 442 ...)` notes in the
  `modalTableau_complete`/`modalTableau_decides` docstrings) is **already resolved on disk**.
  Commit `2f93962a` ("task 542 phase 2.2: strip provenance from CompletenessLoop.lean") already
  stripped all task/phase provenance from this file and is an ancestor of current HEAD. Grep
  confirms zero `task`/`phase`/`FINAL` matches anywhere in the file today. **No action needed
  for CompletenessLoop.lean itself.**
- **Sibling files**: `LoopChecking.lean` (same `Modal/Tableau/` directory) has the same problem
  the vet flagged — 4 docstring citations of `task 511`/`task 535` that should be rewritten to
  durable anchors per the repo rule. No other Tableau file (Modal or Foundations) has any
  `task NNN` citation.
- Additionally noted (out of the stated scope, flagged for awareness only): the `Modal/` tree
  sketch is stale beyond just `Tableau/` — it is also missing `LogicalEquivalence.lean`,
  `Metalogic.lean` (barrel), `ProofSystem/` (16 files), and `Semantics/Birelational.lean`.

## Context & Scope

Vet found two low-severity documentation gaps in task 299/455's output (code placement itself
was judged correct):
1. `ORGANISATION.md` tree sketches for `Logics/Modal/` and `Foundations/Logic/` omit the
   `Tableau/` subdirectory.
2. `CompletenessLoop.lean` docstrings for `modalTableau_complete`/`modalTableau_decides`
   embedded ephemeral task-number notes, violating
   `.claude/rules/no-task-references-in-deliverables.md`.

This research verifies current on-disk state (line numbers may have drifted), enumerates exact
`Tableau/` contents for each tree sketch, and locates every ephemeral task-number reference in
the flagged docstrings and sibling Tableau files.

## Findings

### 1. ORGANISATION.md — line numbers confirmed, exact fix content

**No drift.** Both anchors from the vet finding are exactly where cited.

#### (a) `Foundations/Logic/` tree sketch — `ORGANISATION.md:24-74`

- Fenced block opens at line 24, `Foundations/` at line 25, `├── Logic/` at line 26 (matches
  vet finding exactly).
- Directory listing on disk (`Cslib/Foundations/Logic/`, in filesystem order) is:
  `Automation/`, `Axioms.lean`, `Connectives.lean`, `InferenceSystem.lean`,
  `LogicalEquivalence.lean`, `Metalogic/`, `ProofSystem.lean`, **`Tableau/`**, `Tableau.lean`,
  `Theorems/`, `Theorems.lean`.
- The tree sketch (lines 24-74) currently documents all of these **except** `Tableau/` and
  `Tableau.lean` (the barrel file for the subdirectory).
- `Cslib/Foundations/Logic/Tableau/` contents (confirmed via `ls`, 8 files) exactly match the
  task description's enumeration:
  `Sign.lean`, `SignedFormula.lean`, `RuleResult.lean`, `Branch.lean`, `Closure.lean`,
  `ClosureCondition.lean`, `Measure.lean`, `PropositionalRules.lean`.
- **Suggested insertion point**: after the `Automation/` block (lines 47-48, the last entry in
  the existing sketch, right before the closing ` ``` ` at line 74), matching filesystem
  ordering (`ProofSystem.lean` at line 30 already precedes where `Tableau/` sits on disk, so a
  literal filesystem-order insertion would go between `ProofSystem.lean` (line 30) and
  `Theorems.lean`/`Theorems/` (lines 32-33); either position is acceptable since the existing
  sketch groups by conceptual role rather than strict alphabetical/fs order — placing it near
  `Automation/` as the last block, or between `ProofSystem.lean` and `Theorems.lean` to mirror
  disk order, are both consistent with the file's existing conventions).
- Suggested content block (one-line-per-file, matching the sketch's existing terseness for
  small subdirectories like `Automation/`):
  ```
  ├── Tableau.lean               -- Tableau barrel (re-exports Tableau/ modules)
  ├── Tableau/                   -- Generic (signed-formula) tableau infrastructure
  │   ├── Sign.lean               -- Signed-formula sign type (T/F)
  │   ├── SignedFormula.lean      -- Signed formula structure
  │   ├── RuleResult.lean         -- Tableau rule application result type
  │   ├── Branch.lean             -- Branch (formula list) utilities
  │   ├── Closure.lean            -- Branch closure predicate
  │   ├── ClosureCondition.lean   -- Closure condition typeclass
  │   ├── Measure.lean            -- Termination measure for tableau expansion
  │   └── PropositionalRules.lean -- Propositional expansion rules
  ```
  (One-line docstring comments above are inferred from filenames/module role for template
  purposes; the implementer should verify each comment against the file's actual module
  docstring rather than trust this report's paraphrase verbatim.)

#### (b) `Logics/Modal/` tree sketch — `ORGANISATION.md:145-159`

- `### Modal Logic (\`Logics/Modal/\`)` heading at line 145, fenced block opens line 147,
  `Modal/` at line **148** (matches vet finding exactly), closes at line 159.
- Current sketch lists only: `Basic.lean`, `Denotation.lean`, `Cube.lean`,
  `FromPropositional.lean`, `Metalogic/` (5 sub-entries). It omits `Tableau/` entirely.
- `Cslib/Logics/Modal/Tableau/` contains **20 files** (confirmed via `ls`):
  `BDriver.lean`, `Branch.lean`, `Closure.lean`, `Completeness.lean`, `CompletenessLoop.lean`,
  `Defs.lean`, `FiveSimplification.lean`, `FmpMeasure.lean`, `FrameCompleteness.lean`,
  `FrameRules.lean`, `FrameSoundness.lean`, `GenericDriver.lean`, `LoopChecking.lean`,
  `LoopInduction.lean`, `Rules.lean`, `S5Simplification.lean`, `Saturation.lean`,
  `Soundness.lean`, `SoundnessStep.lean`, `TDriver.lean`.
- Because this is a much larger directory than the `Foundations/Logic/Tableau/` one (20 files
  vs. 8, spanning K/T/B/S4/S5/generic-driver machinery), a full per-file enumeration would be
  disproportionately long compared to the terse style used for `Metalogic/` in the same block
  (5 files, one line each, no descriptive comments). Two options for the implementer, both
  consistent with existing conventions elsewhere in this document:
  - **Terse** (matches this block's own style): `└── Tableau/  -- Tableau decision procedures
    (K/T/B/S4/S5 drivers, saturation, soundness/completeness)` as a single collapsed line,
    mirroring how `Propositional/Tableau/` is summarized at `ORGANISATION.md:127-131` (one line
    per sub-bucket: `Defs.lean`, `Classical/`, `Intuitionistic/`, `Minimal/` — not every file
    inside those buckets).
  - **Full enumeration**: list all 20 files individually (verbose but exhaustive; would roughly
    double this section's length).
  Given the sibling `Propositional/Tableau/` entry (lines 127-131) already sets the precedent of
  summarizing rather than fully enumerating a large `Tableau/` subdirectory, the **terse
  option is recommended** for consistency, unless the implementer judges per-file detail more
  valuable here.

**Out-of-scope observation (flag only, not part of this fix)**: the `Modal/` sketch is stale
beyond `Tableau/` too — `Cslib/Logics/Modal/` on disk also contains `LogicalEquivalence.lean`,
`Metalogic.lean` (barrel), `ProofSystem/` (`Instances.lean`, `SchemaTags.lean`,
`SchemaUnion.lean`, `Instances/` with 15 per-axiom-system files), and
`Semantics/Birelational.lean` — none of which appear in the current tree sketch. This is beyond
the vet finding's stated scope (which named only the `Tableau/` omission) and is noted here so
a follow-up task can pick it up if desired; it is not part of this task's deliverable.

### 2. CompletenessLoop.lean — already fixed, no action needed

The vet finding cited `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean:1178 and nearby` for
`modalTableau_complete`/`modalTableau_decides` docstrings embedding `'(task 442 Phase 6,
FINAL)'`, `'(task 442 Phase 5a)'`.

Verification against current on-disk state:
- `modalTableau_complete` is now at line 2237, `modalTableau_decides` at line 2281 (the file has
  grown/shifted since the vet ran — line 1178 today is unrelated proof-tactic content, not a
  docstring).
- Their docstrings (lines 2230-2236 and 2277-2280) are already clean, plain mathematical
  descriptions with no task/phase citations:
  > "**K-completeness of the modal tableau**: if the tableau on `φ0` returns an open branch,
  > `φ0` is not K-valid. Combines the top-loop Hintikka lemma (`modalExpandBranches_hintikka`,
  > above) ... and the countermodel extraction theorem (`modalOpenBranch_countermodel`,
  > `Completeness.lean:561`)."
  > "**The modal K tableau decides K-validity**: `modalTableau φ0` closes exactly when `φ0` is
  > K-valid. Combines soundness (`modalTableau_sound`, `Soundness.lean:334`) with completeness
  > (`modalTableau_complete`, above) via the two-constructor dichotomy of `ModalTableauResult`."
- `grep -in '\btask\b\|\bphase\b\|FINAL' Cslib/Logics/Modal/Tableau/CompletenessLoop.lean`
  returns **zero matches** in the entire 2300-line file.
- `git log` shows commit `2f93962a` — "task 542 phase 2.2: strip provenance from
  CompletenessLoop.lean" (166 lines changed) — already performed exactly this cleanup, and
  `git merge-base --is-ancestor 2f93962a HEAD` confirms it is an ancestor of the current branch
  tip (`0c33374f`).

**Conclusion**: item (2) of the vet finding, as originally scoped to CompletenessLoop.lean, is
stale — the fix already landed before this vet ran (or the vet ran against an older checkout).
No implementation work is needed on this file.

### 3. Sibling Tableau files — LoopChecking.lean has the same problem

Per the research scope's instruction to check sibling files, a repo-wide scan
(`grep -rn -i "task [0-9]\{2,\}"` across `Cslib/Logics/Modal/Tableau/` and
`Cslib/Foundations/Logic/Tableau/`) found exactly one file with violations:
**`Cslib/Logics/Modal/Tableau/LoopChecking.lean`** — 4 docstring citations of ephemeral task
numbers:

| Line | Context | Citation |
|------|---------|----------|
| 4665 | Section-comment header for "Keyed S4 Driver (Bespoke, Path (b))": "Task 535 closes `Decidable (s4Valid φ)` via a bespoke, S4-specific `keys`-threaded driver, rather than generalizing the shared generic driver..." | `Task 535` |
| 5481 | Docstring for the "Phase 6 (handoff 3d-i)" keyed Hintikka bundle: "...for `modalApplyOneS4Keyed φ₀ keys`. `S4LoopInv` (task 511, frozen, above) already carries the universe-closure/keys-bookkeeping conjuncts..." | `task 511` |
| 5696 | Docstring for `S4KeyedHintikkaInv` structure: "...The universe-closure/ keys-bookkeeping conjuncts already live in the frozen `S4LoopInv` (task 511) and are threaded as a separate ambient hypothesis..." | `task 511` |
| 5949 | Docstring for "Phase 7 — single-step preservation of `S4KeyedHintikkaInv`": "...given the ambient `S4LoopInv` (task 511, consumed for `keyLowerBd`'s blocked-witness argument)." | `task 511` |

Each is a case where "task NNN" is being used as a stand-in for "the `S4LoopInv` structure,
defined/frozen earlier in this file" or "the design decision documented in this section" — i.e.
exactly the anti-pattern the rule's example calls out. A durable-anchor rewrite would replace:
- `` `S4LoopInv` (task 511, frozen, above) `` → `` `S4LoopInv` (frozen, above — see `S4LoopInv`'s
  own definition/comment for why the keys-bookkeeping conjuncts are frozen there) `` or a direct
  line/section-heading anchor to wherever `S4LoopInv` is defined in this file.
- `Task 535 closes ...` → drop the task-number lead-in and just state the design rationale
  directly, e.g. `This section closes \`Decidable (s4Valid φ)\` via a bespoke, S4-specific
  ...` (the rest of the paragraph after "Task 535" is already a plain, durable rationale and
  needs no other change).

**Not flagged (judgment call, likely out of the rule's literal scope)**: `LoopChecking.lean`
also contains ~25 bare `Phase N` references (e.g. "Phase 6", "Phase 7", "Phase 8 (handoff...)")
that describe internal proof-development stages without an accompanying task number. These read
as an internal narrative-structure device (dividing the file into named sections) rather than a
citation of task-tracker metadata per se, and the repo rule's explicit trigger pattern is
`"task N"`/`"tasks N-M"`/`"(task N)"`, not bare phase numbers. This report surfaces them for
awareness but does not treat them as required fixes — an implementer or the user should decide
whether "Phase N (handoff ...)" section headers also count as ephemeral task-management
metadata under the rule's spirit, versus being read as durable internal section markers akin to
"Part 1"/"Part 2". No other Tableau file (Modal or Foundations) has any bare `Phase N` or `task
NNN` citations — `LoopChecking.lean` is the sole outlier.

## Decisions

- Treat CompletenessLoop.lean's docstring cleanup as already complete; do not re-touch it.
- Scope the docstring-cleanup half of this task's fix to `LoopChecking.lean`'s 4 explicit
  `task NNN` citations (lines 4665, 5481, 5696, 5949).
- Leave `LoopChecking.lean`'s bare `Phase N` narrative headers untouched unless the
  implementer/user explicitly wants the stricter reading of the rule applied.
- For the `Modal/` `Tableau/` tree-sketch entry, default to a terse one-line summary
  (consistent with the `Propositional/Tableau/` precedent at `ORGANISATION.md:127-131`) rather
  than enumerating all 20 files, unless the implementer prefers full enumeration.

## Risks & Mitigations

- **Risk**: rewriting `LoopChecking.lean`'s docstrings could look like a plan-compliance
  violation of `.claude/rules/plan-compliance.md` (no plan exists for this file currently) —
  mitigated because this is a documentation-only rewording, not a proof/lemma-structure change,
  and no implementation plan is in force for this file.
- **Risk**: the `Modal/` tree sketch's broader staleness (noted in Findings §1(b)) could tempt
  scope creep. Mitigation: explicitly flagged as out-of-scope in this report; implementer should
  only touch the `Tableau/` entry unless separately asked to fix the rest.

## Context Extension Recommendations

None — this is a one-off documentation-drift fix, not a recurring pattern requiring new context
documentation.

## Appendix

Search commands used:
- `grep -n "Tableau\|Modal/\|Foundations/Logic" ORGANISATION.md`
- `find Cslib/Logics/Modal/Tableau Cslib/Foundations/Logic -type f -iname "*.lean" | sort`
- `grep -n -i "task 442\|task442\|phase 5a\|phase 6\|FINAL" Cslib/Logics/Modal/Tableau/CompletenessLoop.lean`
- `grep -n -i "\btask\b\|\bphase\b\|FINAL" Cslib/Logics/Modal/Tableau/CompletenessLoop.lean`
- `git log --oneline -10 -- Cslib/Logics/Modal/Tableau/CompletenessLoop.lean`
- `git merge-base --is-ancestor 2f93962a HEAD`
- `grep -rln -i "task [0-9]\{2,\}" Cslib/Logics/Modal/Tableau/ Cslib/Foundations/Logic/Tableau/ Cslib/Foundations/Logic/Tableau.lean`
- `ls` on `Cslib/Foundations/Logic/`, `Cslib/Logics/Modal/`, `Cslib/Logics/Modal/Tableau/`,
  `Cslib/Logics/Modal/Metalogic/`, `Cslib/Logics/Modal/ProofSystem/` (recursive),
  `Cslib/Logics/Modal/Semantics/` (recursive), `Cslib/Foundations/Logic/Tableau/`
