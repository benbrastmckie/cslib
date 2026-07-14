# Implementation Plan: Task #499

- **Task**: 499 - pr_662_contributing_compliance
- **Status**: [COMPLETED]
- **Effort**: 2 hours
- **Dependencies**: Parent task 498 (source of the slice); coordination 476; related 497 (imp/impl naming)
- **Research Inputs**: specs/499_pr_662_contributing_compliance/reports/01_contributing-compliance-audit.md
- **Artifacts**: plans/01_contributing-compliance.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; CONTRIBUTING.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Bring the PR #662 native-primitive foundational-semantic-layer slice into CONTRIBUTING.md
compliance through documentation-only edits (docstrings/comments/header only). Two files are
touched: the staged slice
`specs/498_modal_foundational_semantic_layer_662/artifacts/pr-662-slice/Basic.lean` (all five
findings) and the live `Cslib/Logics/Modal/Basic.lean` on branch `task-441-native-refactor`
(the internal task-number scrub only, so re-extraction does not reintroduce it). No definition or
proof changes are permitted; the final `git diff` must touch only comment/docstring/header lines.
Edits are sequenced by severity — MUST FIX first, then SHOULD/MINOR/OPTIONAL — with the
copyright-holder question held as a no-auto-change maintainer-confirmation item, and a closing CI
verification phase to keep the live build green. `Denotation.lean` needs no changes.

### Research Integration

The pre-seeded audit report (`reports/01_contributing-compliance-audit.md`) drives every phase.
Findings and confirmed line numbers (verified against the current slice and live source):

- §3.1 [MUST FIX] internal task-tracker numbers — slice `Basic.lean:34` ("task 441"), `:113`
  ("task 340"), `:119` ("task 340"), `:272` ("task 441"); the identical strings exist in the live
  `Cslib/Logics/Modal/Basic.lean` at lines 34, 113, 119, 272 (confirmed via grep).
- §3.2 [SHOULD FIX] dangling docstring cross-references — slice `Basic.lean:41–44` (Axioms.lean /
  ProofSystem/Instances proof-system layer) and `:46–50` (`PL.Proposition.toModal` / `.embed` /
  "in `FromPropositional`" Bimodal-embedding paragraph; note no module literally named
  `FromPropositional`). Slice-only — these refs remain valid in the live task-441 file.
- §3.3 [MINOR] `## References` (slice `Basic.lean:52–56`) lists only `[Blackburn2001]`;
  `[ChagrovZakharyaschev1997]` is cited inline at `:37` but missing from the list.
- §3.4 [CONFIRM WITH MAINTAINER] copyright-holder line adds "Benjamin Brast-McKie" to Fabrizio's
  file (slice `Basic.lean:2`). Authors-line addition (`:4`) is fine; holder-line addition needs
  Fabrizio's OK. NO auto-change.
- §3.5 [OPTIONAL] "Lukasiewicz" → "Łukasiewicz" diacritic — slice `Basic.lean:30,36`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (documentation-compliance fix; roadmap flag not set).

## Goals & Non-Goals

**Goals**:
- Remove all internal task-tracker numbers from published docstrings in both the slice and the live task-441 `Basic.lean` (§3.1).
- Trim the slice module docstring of dangling proof-system and Bimodal-embedding cross-references (§3.2, slice only).
- Complete the slice `## References` section with `[ChagrovZakharyaschev1997]` (§3.3).
- Apply the optional "Łukasiewicz" diacritic in the slice (§3.5).
- Record the copyright-holder decision as a maintainer-confirmation item with no code change (§3.4).
- Keep the live build green; ensure the final diff is documentation-only.

**Non-Goals**:
- No changes to any definition, `abbrev`, `lemma`, `theorem`, `structure`, `instance`, or proof.
- No changes to `Denotation.lean` (its docstrings are clean).
- No auto-change to the copyright-holder line (§3.4) — pending Fabrizio.
- No trimming of the §3.2 cross-references in the live task-441 file (those files exist there; refs are valid).
- No mandatory diacritic change in the live file (optional; scope kept to slice unless trivially consistent).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| An edit accidentally changes a definition/proof line, not just a comment | H | L | Restrict edits to docstring/comment text; audit with `git diff` in Phase 6 to confirm only comment/header lines changed |
| Rewording §3.1 breaks the surrounding docstring's meaning or a valid cross-ref in the live file | M | L | Reword to state design rationale without task numbers; live edit is §3.1 scrub only, leaving §3.2 cross-refs intact and valid |
| §3.2 trim removes rationale the reviewer expects (diamond primitivity / IK-CK reuse) | M | L | Keep the literature-backed rationale; drop only the forward references to proof-system and Bimodal layers, or gate them as "(in later PRs)" |
| Slice files are outside the lake package, so `lake build` does not compile them | M | M | Slice edits are doc-only and cannot break compilation; verify the slice via a git-diff comment-only audit. Run full CI only against the live file edit |
| Copyright-holder line changed without Fabrizio's confirmation | M | L | Phase 5 is explicitly no-auto-change: record the decision only, leave the holder line as-is pending maintainer input |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 5 | -- |
| 2 | 3 | 1 |
| 3 | 4 | 3 |
| 4 | 6 | 1, 2, 3, 4 |

Phases within the same wave can execute in parallel. Phases 3 and 4 are serialized after Phase 1
because they edit the same file (slice `Basic.lean`); Phase 2 edits a different file and runs in
parallel with Phase 1.

### Phase 1: [MUST FIX] Scrub internal task numbers from slice Basic.lean [COMPLETED]

**Goal**: Remove "task 441" and "task 340" references from the slice's published docstrings, rewording to state the design rationale without internal tracker numbers.

**Tasks**:
- [x] Reword slice `Basic.lean:34` — replace "However, task 441 makes `diamond` a native constructor…" with a task-number-free statement (e.g. "`diamond` is a native constructor (alongside `and`/`or`) so that:").
- [x] Reword slice `Basic.lean:113` — "Delegates to the canonical `PropositionalConnectives.neg` default (task 340)." → drop "(task 340)".
- [x] Reword slice `Basic.lean:119` — "Delegates to the canonical `PropositionalConnectives.top` default (task 340)." → drop "(task 340)".
- [x] Reword slice `Basic.lean:272` — "Since `diamond` is a native constructor (task 441), this is no longer…" → drop "(task 441)".
- [x] Confirm no other "task NNN" strings remain in the slice (`grep -n "task [0-9]" Basic.lean`).

**Timing**: 20 minutes

**Depends on**: none

**Files to modify**:
- `specs/498_modal_foundational_semantic_layer_662/artifacts/pr-662-slice/Basic.lean` — docstring text at lines 34, 113, 119, 272 only.

**Verification**:
- `grep -n "task [0-9]"` on the slice `Basic.lean` returns no matches.
- Reworded docstrings still read as coherent design rationale.

---

### Phase 2: [MUST FIX] Scrub internal task numbers from live task-441 Basic.lean [COMPLETED]

**Goal**: Apply the identical §3.1 scrub to the live `Cslib/Logics/Modal/Basic.lean` on branch `task-441-native-refactor`, so re-extraction of the slice does not reintroduce the task numbers.

**Tasks**:
- [x] Reword live `Cslib/Logics/Modal/Basic.lean:34` — drop "task 441" (same wording as Phase 1).
- [x] Reword live `Basic.lean:113` and `:119` — drop "(task 340)".
- [x] Reword live `Basic.lean:272` — drop "(task 441)".
- [x] Leave the §3.2 cross-references (Axioms.lean / ProofSystem/Instances, `FromPropositional` paragraph) intact — they are valid in the live file. Do NOT trim them here.
- [x] Confirm `grep -n "task [0-9]"` on the live file returns no matches.

**Timing**: 15 minutes

**Depends on**: none (different file from Phase 1; runs in parallel)

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` (branch `task-441-native-refactor`) — docstring text at lines 34, 113, 119, 272 only.

**Verification**:
- `grep -n "task [0-9]"` on the live `Basic.lean` returns no matches.
- §3.2 cross-references remain present and unchanged in the live file.

---

### Phase 3: [SHOULD FIX] Trim dangling docstring cross-references in slice (slice only) [COMPLETED]

**Goal**: Trim the slice module docstring of forward references to machinery excluded from PR #662, so the standalone PR has no dangling cross-refs.

**Tasks**:
- [x] Trim slice `Basic.lean:41–44` — remove/gate the proof-system-layer references (`AxiomDiaDualityFwd`/`AxiomDiaDualityBack` in `Foundations/Logic/Axioms.lean`; `ProofSystem/Instances/*.lean`). Keep the semantic statement that the duality `◇φ ↔ ¬□¬φ` is recovered as a theorem (`Satisfies.dual`); drop or gate the Hilbert/axiom-schema forward reference behind "(in later PRs)".
- [x] Trim slice `Basic.lean:46–50` — remove the `PL.Proposition.toModal` / `PL.Proposition.embed` / "in `FromPropositional`" Bimodal-embedding paragraph (those symbols live in `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean`, absent from the slice; and there is no module named `FromPropositional`).
- [x] Preserve the literature-backed rationale (diamond primitivity, IK/CK reuse, `[Blackburn2001]` / `[ChagrovZakharyaschev1997]` citations) — trim only the forward references.

**Timing**: 25 minutes

**Depends on**: 1 (same file — sequence after the §3.1 scrub to avoid conflicting edits)

**Files to modify**:
- `specs/498_modal_foundational_semantic_layer_662/artifacts/pr-662-slice/Basic.lean` — module docstring lines 41–50 only.

**Verification**:
- Slice module docstring no longer references `Axioms.lean`, `ProofSystem/Instances`, `PL.Proposition.toModal/embed`, or `FromPropositional`.
- Diamond-primitivity rationale and literature citations remain intact.
- This trim is NOT applied to the live task-441 file.

---

### Phase 4: [MINOR + OPTIONAL] Complete References and apply diacritic in slice [COMPLETED]

**Goal**: Add the missing `[ChagrovZakharyaschev1997]` reference entry (§3.3) and apply the optional "Łukasiewicz" diacritic (§3.5), both slice-only.

**Tasks**:
- [x] Add a `[ChagrovZakharyaschev1997]` entry to the slice `## References` section (slice `Basic.lean:52–56`), matching the `[Blackburn2001]` entry style. (BibKey confirmed present in `references.bib` per audit §2.)
- [x] [OPTIONAL] Replace "Lukasiewicz" → "Łukasiewicz" at slice `Basic.lean:30` and `:36`.
- [x] Confirm the References section now lists every BibKey cited inline in the slice.

**Timing**: 15 minutes

**Depends on**: 3 (same file — sequence after the §3.2 trim)

**Files to modify**:
- `specs/498_modal_foundational_semantic_layer_662/artifacts/pr-662-slice/Basic.lean` — References section and (optional) lines 30, 36.

**Verification**:
- `## References` contains both `[Blackburn2001]` and `[ChagrovZakharyaschev1997]`.
- Every inline `[BibKey]` citation in the slice has a matching References entry.

---

### Phase 5: [CONFIRM WITH MAINTAINER — no auto-change] Record copyright-holder decision [COMPLETED]

**Goal**: Flag the copyright-holder-line question for Fabrizio without changing any code.

**Tasks**:
- [x] Record in the implementation summary that slice `Basic.lean:2` adds "Benjamin Brast-McKie" to the `Copyright (c) 2026 …` holder line, while #607's base is `Copyright (c) 2026 Fabrizio Montesi`.
- [x] Note that the `Authors:` addition (slice `Basic.lean:4`) is standard and fine; the holder-line addition is a maintainer preference requiring Fabrizio's confirmation.
- [x] Make NO change to the copyright-holder line — leave it exactly as-is pending maintainer input.

**Timing**: 10 minutes

**Depends on**: none (documentation/flag only; no file edit)

**Files to modify**:
- None (records a decision item only).

**Verification**:
- Copyright-holder line is unchanged from the current slice.
- The maintainer-confirmation item is recorded in the summary for follow-up.

---

### Phase 6: CI verification and documentation-only diff audit [COMPLETED]

**Goal**: Confirm the live build stays green and that all edits are documentation-only.

**Tasks**:
- [x] Audit the slice diff: `git diff` (or file-level review) confirms slice `Basic.lean` changes touch only comment/docstring/header lines — zero definition/proof changes. (The slice is outside the lake package, so it is not compiled; a comment-only audit is the applicable check.)
- [x] For the live file edit, run the CSLib CI pipeline in order: `lake build` (targeted `lake build Cslib.Logics.Modal.Basic` first, then full `lake build` if needed), `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`, `lake shake --add-public --keep-implied --keep-prefix`.
- [x] Confirm the live `git diff` for `Cslib/Logics/Modal/Basic.lean` touches only docstring/comment lines.
- [x] Verify no `Denotation.lean` changes were made.

**Timing**: 35 minutes (includes build time; run `lake exe cache get` first if the branch cache is cold)

**Depends on**: 1, 2, 3, 4

**Files to modify**:
- None (verification only).

**Verification**:
- `lake build`, `checkInitImports`, `lake lint`, `lint-style`, `lake test`, `lake shake` all pass on the live file.
- `git diff --stat` shows only `Cslib/Logics/Modal/Basic.lean` (live) and the slice `Basic.lean` (artifact) changed; both diffs are comment/docstring/header lines only.

## Testing & Validation

- [x] `grep -n "task [0-9]"` returns no matches in both the slice and live `Basic.lean`.
- [x] Slice module docstring free of `Axioms.lean` / `ProofSystem/Instances` / `PL.Proposition.toModal`/`embed` / `FromPropositional` references (§3.2).
- [x] Slice `## References` includes `[ChagrovZakharyaschev1997]`.
- [x] Live CI pipeline green: `lake build`, `checkInitImports`, `lake lint`, `lint-style`, `lake test`, `lake shake`.
- [x] `git diff` for both files touches only comment/docstring/header lines (zero proof/definition changes).
- [x] Copyright-holder line unchanged; maintainer-confirmation item recorded.

## Artifacts & Outputs

- `specs/499_pr_662_contributing_compliance/plans/01_contributing-compliance.md` (this plan)
- Edited `specs/498_modal_foundational_semantic_layer_662/artifacts/pr-662-slice/Basic.lean` (§3.1, §3.2, §3.3, §3.5)
- Edited `Cslib/Logics/Modal/Basic.lean` on `task-441-native-refactor` (§3.1 only)
- `specs/499_pr_662_contributing_compliance/summaries/01_contributing-compliance-summary.md` (on implementation; includes §3.4 maintainer-confirmation note)

## Rollback/Contingency

All changes are documentation-only and confined to comment/docstring/header text in two files.
To revert: `git checkout -- Cslib/Logics/Modal/Basic.lean` for the live file, and restore the
slice `Basic.lean` from git (or re-extract from the live file after the §3.1 scrub). Because no
definitions or proofs change, reverting cannot affect the build. If CI reveals any unexpected
failure on the live file, it indicates a non-comment edit slipped in — revert and re-apply the
docstring text change in isolation.
