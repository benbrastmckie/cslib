# Implementation Plan: Task #446 - Temporal Burgess Citation Hygiene

- **Task**: 446 - Burgess citation hygiene in the task-180 Temporal metalogic
- **Status**: [COMPLETED]
- **Effort**: 1 hour
- **Dependencies**: None
- **Research Inputs**: specs/446_fix_temporal_burgess_citation_hygiene/reports/01_burgess-citation-hygiene.md
- **Artifacts**: plans/01_burgess-citation-hygiene.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Convert 12 plain-prose "Burgess 1982" citation sites in `Cslib/Logics/Temporal/Metalogic/`
to the established bracket house style `* [First. Last, *Title in Title Case*][BibKey]`,
disambiguating `Burgess1982I` (BX axiom system — "Since and Until") from `Burgess1982II`
(chronicle construction — "Time Periods"). This is a pure docstring/comment edit: no proofs,
no `sorry`, no axioms, zero behavioural change. Every edit lives inside a `/-! ... -/` or
`/-- ... -/` doc block. All target BibKeys already resolve in `./references.bib`, so no
`references.bib` edits are required. Definition of done: all 12 sites converted per the
research report's exact target strings, `lake build` remains green, and a grep guard finds
zero residual prose citations in the in-scope files.

### Research Integration

The research report (`reports/01_burgess-citation-hygiene.md`) supplies a complete,
verified site-by-site conversion table (Section 4) with corrected file paths, the house
style spec (Section 2), the Burgess I/II disambiguation rationale (Section 3), a clean
`references.bib` validation (Section 3 — all keys present, no bib edits), the EXCLUSIONS
list (Section 6), and the out-of-scope Reynolds1994/Tableau finding (Section 7). This plan
executes that table verbatim; the implementer must copy target strings exactly from the
report rather than re-deriving them.

**Corrected paths** (task description had stale paths):
- `Metalogic/TruthLemma.lean` -> `Metalogic/Chronicle/TruthLemma.lean`
- `Semantics/RRelation.lean` -> `Metalogic/Chronicle/RRelation.lean`

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted (roadmap flag not set). This task is a hygiene follow-up to the
task-180 Temporal metalogic work.

## Goals & Non-Goals

**Goals**:
- Convert all 12 prose citation sites to the bracket `[Description][BibKey]` house style.
- Apply the exact target strings from the research report's conversion table (Section 4).
- Normalize the bullet marker `-` -> `*` at the 5 flagged sites (sites 1, 4, 6, 8, 10).
- Split `Completeness.lean:40` (which conflates Burgess I and II) into two bullets.
- Keep `lake build` green and verify no residual prose "Burgess 1982" citations remain.

**Non-Goals**:
- No `references.bib` edits (all keys already resolve; no new entries).
- No proof, definition, tactic, or signature changes; no behavioural change of any kind.
- Do NOT touch Lean identifiers, module names, or informal proof-comment shorthand
  (see EXCLUSIONS below).
- Do NOT fix the Reynolds1994/Tableau description mismatch (Section 7 of the report) —
  it is out of scope for task 446 and belongs to a separate bib-hygiene task.
- No advisory Section-5 docstring tidy-ups (module-title headers) — leave as-is.

### EXCLUSIONS (carried forward from report Section 6 — do NOT modify)

- Lean identifiers / definitions: `BurgessR3Maximal`, `burgessR`, `burgessRSince`,
  `burgessRSet`, `burgessR3`, `BurgessR3Maximal_extension_fails`,
  `BurgessR3Maximal_g_content_sub`, `BurgessR3Maximal_sdc`, `BurgessR3Maximal_bot_not_mem`.
- Module / import: `Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion.Burgess`
  and the `**Burgess** (`PointInsertion.Burgess`)` module-description bullet.
- Section-header shorthand: `## Burgess Lemma 2.3`, `## Burgess Absorption (Lemma 2.5)`,
  `Burgess C4a`, `Burgess C5a`, `Burgess 2.10 induction`, and inline "Burgess 2.x" proof
  comments.
- `Burgess-Xu (BX)` system naming in `ProofSystem/Axioms.lean:13,67,71` — this is the name
  of the system, not a citation.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Unterminated `/-! -/` or `/-- -/` block after an edit | H | L | Edit only the citation line; run `lake build` on edited modules in Phase 3 — the only real parse risk |
| Line/path drift (report line numbers stale after earlier edits) | M | L | Grep for the current-text string rather than trusting the line number; report gives exact `current text` per site |
| Accidentally converting an excluded identifier/header | M | L | Match on the exact prose citation strings only; EXCLUSIONS list enumerated above |
| Completeness.lean:40 split done incorrectly (loses I or II intent) | M | L | Follow report site 11 verbatim: two bullets, I for axioms, II for chronicle completeness (Claim 2.11) |
| lint-style line-length regression from longer bullets | L | L | Report confirms new bullets are well under limits; run `lake exe lint-style` in Phase 3 |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |

Phases within the same wave can execute in parallel. Phases 1 and 2 touch disjoint file
sets (Chronicle/ subtree vs. Metalogic top-level), so they may run in parallel; Phase 3
verifies both.

### Phase 1: Chronicle/ subtree conversions (Burgess1982II) [COMPLETED]

**Goal**: Convert the 8 Chronicle-construction citation sites (all `Burgess1982II` — "Time
Periods") to bracket house style, normalizing `-` -> `*` where flagged.

**Tasks** (each target string copied exactly from report Section 4):
- [ ] `Metalogic/Chronicle/TruthLemma.lean:34` (site 1, `-` -> `*`): `- Burgess 1982: Section 2, Claim 2.11` -> `* [J. Burgess, *Axioms for Tense Logic II: Time Periods*][Burgess1982II] — Section 2, Claim 2.11`
- [ ] `Metalogic/Chronicle/TruthLemma.lean:274` (site 2, inline prose): `This is Claim 2.11 of Burgess 1982, adapted to the temporal logic setting. -/` -> `This is Claim 2.11 of Burgess (see [Burgess1982II]), adapted to the temporal logic setting. -/`
- [ ] `Metalogic/Chronicle/RRelation.lean:21` (site 5): `* Burgess 1982: "Axioms for tense logic II: Time periods"` -> `* [J. Burgess, *Axioms for Tense Logic II: Time Periods*][Burgess1982II]`
- [ ] `Metalogic/Chronicle/ChronicleToCountermodel.lean:33` (site 6, `-` -> `*`): `- Burgess 1982: Section 2, Claim 2.11` -> `* [J. Burgess, *Axioms for Tense Logic II: Time Periods*][Burgess1982II] — Section 2, Claim 2.11`
- [ ] `Metalogic/Chronicle/PointInsertion.lean:41` (site 7): `* Burgess 1982: "Axioms for tense logic II: Time periods"` -> `* [J. Burgess, *Axioms for Tense Logic II: Time Periods*][Burgess1982II]`
- [ ] `Metalogic/Chronicle/ChronicleConstruction.lean:52` (site 8, `-` -> `*`): `- Burgess 1982: "Axioms for tense logic II: Time periods", Section 2` -> `* [J. Burgess, *Axioms for Tense Logic II: Time Periods*][Burgess1982II] — Section 2`
- [ ] `Metalogic/Chronicle/ChronicleTypes.lean:21` (site 9): `* Burgess 1982: "Axioms for tense logic II: Time periods"` -> `* [J. Burgess, *Axioms for Tense Logic II: Time Periods*][Burgess1982II]`
- [ ] `Metalogic/Chronicle/CounterexampleElimination.lean:40` (site 10, `-` -> `*`): `- Burgess 1982: "Axioms for tense logic II: Time periods", Section 2` -> `* [J. Burgess, *Axioms for Tense Logic II: Time Periods*][Burgess1982II] — Section 2`
- [ ] Do NOT touch the excluded identifiers/headers in these files (e.g. `PointInsertion.Burgess` module, `# r-Relation Lemmas (Burgess 1982, ...)` title headers, `Burgess 2.x` proof comments).

**Timing**: 30 minutes

**Depends on**: none

**Files to modify** (all under `Cslib/Logics/Temporal/`):
- `Metalogic/Chronicle/TruthLemma.lean` - sites 1, 2
- `Metalogic/Chronicle/RRelation.lean` - site 5
- `Metalogic/Chronicle/ChronicleToCountermodel.lean` - site 6
- `Metalogic/Chronicle/PointInsertion.lean` - site 7
- `Metalogic/Chronicle/ChronicleConstruction.lean` - site 8
- `Metalogic/Chronicle/ChronicleTypes.lean` - site 9
- `Metalogic/Chronicle/CounterexampleElimination.lean` - site 10

**Verification**:
- All 8 Chronicle sites read exactly as the report's target strings (spot-check each edited line).
- No excluded identifier/header/module reference altered.

---

### Phase 2: Metalogic top-level conversions (Burgess1982I, split, Xu1988) [COMPLETED]

**Goal**: Convert the 4 top-level `Metalogic/` sites: the two BX-axiom-system references
(`Burgess1982I` — "Since and Until"), the Completeness.lean:40 I/II split, and the Xu1988
reference.

**Tasks** (each target string copied exactly from report Section 4):
- [ ] `Metalogic/Soundness.lean:28` (site 3): `* Burgess (1982) — BX axiom system` -> `* [J. Burgess, *Axioms for Tense Logic I: Since and Until*][Burgess1982I] — BX axiom system`
- [x] `Metalogic/DenseSoundness.lean:28` (site 4, `-` -> `*`): `- Burgess (1982): BX axiom system for temporal logic` -> `* [J. Burgess, *Axioms for Tense Logic I: Since and Until*][Burgess1982I] — BX axiom system for temporal logic` *(deviation: altered -- the report's target string was 110 chars, exceeding the 100-char `lake exe lint-style` limit (confirmed by a real `lake build` warning in Phase 3, contrary to the plan's risk-table prediction of "well under limits"); shortened trailing description to "— BX axioms (dense case)" (98 chars), preserving the `[Burgess1982I]` citation and dense-case disambiguation)*
- [x] `Metalogic/Completeness.lean:40` (site 11, SPLIT into two bullets): `* Burgess (1982) — BX axiom system and completeness` -> two bullets: `* [J. Burgess, *Axioms for Tense Logic I: Since and Until*][Burgess1982I] — BX axiom system` and `* [J. Burgess, *Axioms for Tense Logic II: Time Periods*][Burgess1982II] — chronicle completeness (Claim 2.11)` *(deviation: altered -- the second bullet's report target string was 110 chars, exceeding the 100-char lint-style limit; shortened to "— completeness, Claim 2.11" (99 chars), preserving `[Burgess1982II]` citation and the Claim 2.11 reference)*
- [ ] `Metalogic/Completeness.lean:41` (site 12): `* Xu (1988) — Temporal completeness proofs` -> `* [M. Xu, *On Some U,S-Tense Logics*][Xu1988] — temporal completeness proofs`
- [ ] Do NOT touch the `Burgess-Xu (BX)` system naming (it is not a citation) or any section-header shorthand.

**Timing**: 20 minutes

**Depends on**: none

**Files to modify** (all under `Cslib/Logics/Temporal/`):
- `Metalogic/Soundness.lean` - site 3
- `Metalogic/DenseSoundness.lean` - site 4
- `Metalogic/Completeness.lean` - sites 11 (split), 12

**Verification**:
- Sites 3, 4 use `Burgess1982I`; site 11 produces both `Burgess1982I` and `Burgess1982II`
  bullets; site 12 uses `Xu1988`.
- The Completeness.lean reference block gains exactly one net bullet from the split.

---

### Phase 3: Build + grep-guard verification [COMPLETED]

**Goal**: Confirm the docstring-only edits parse cleanly (build stays green) and that no
prose "Burgess 1982" citations remain in the in-scope files.

**Tasks**:
- [ ] Run `lake build Cslib.Logics.Temporal.Metalogic.Completeness` and the other edited
      modules (or a full `lake build`) — must be green; docstring-only edits must not break parsing.
- [ ] Run `lake exe lint-style` — confirm no line-length or style regressions from the
      longer bracket bullets.
- [ ] Grep guard: `grep -rn "Burgess (19\|Burgess 1982:" Cslib/Logics/Temporal/Metalogic/`
      must return zero prose-citation hits (identifier/header hits are excluded by the
      pattern; if any remain, they are excluded shorthand and should be confirmed as such).
- [ ] Confirm no unintended diffs: `git diff --stat` shows only the 8 in-scope files, all
      changes inside doc comments.

**Timing**: 10 minutes

**Depends on**: 1, 2

**Verification**:
- `lake build` exits 0 (green).
- `lake exe lint-style` passes.
- Grep guard returns no prose citations.
- `git diff` shows zero changes outside doc comments (no proof/signature lines touched).

## Testing & Validation

- [ ] `lake build` green after edits (docstring-only; parse integrity is the only real risk).
- [ ] `lake exe lint-style` passes (line-length under limits).
- [ ] Grep guard `grep -rn "Burgess (19\|Burgess 1982:" Cslib/Logics/Temporal/Metalogic/`
      returns no prose citations.
- [ ] All 12 sites match the report's exact target strings.
- [ ] No EXCLUSIONS-list item altered; no Reynolds1994/Tableau change made.
- [ ] `git diff` confirms zero behavioural change (edits confined to doc comments).

## Artifacts & Outputs

- plans/01_burgess-citation-hygiene.md (this plan)
- Edited files (8, all under `Cslib/Logics/Temporal/Metalogic/`):
  - `Chronicle/TruthLemma.lean`, `Chronicle/RRelation.lean`,
    `Chronicle/ChronicleToCountermodel.lean`, `Chronicle/PointInsertion.lean`,
    `Chronicle/ChronicleConstruction.lean`, `Chronicle/ChronicleTypes.lean`,
    `Chronicle/CounterexampleElimination.lean`
  - `Soundness.lean`, `DenseSoundness.lean`, `Completeness.lean`
- summaries/01_burgess-citation-hygiene-summary.md (produced at /implement)

## Rollback/Contingency

All changes are confined to documentation comments and are trivially reversible with
`git checkout -- <file>` or `git revert` of the task commit. If `lake build` fails after an
edit (only plausible cause: an accidentally malformed `/-! -/` / `/-- -/` block), revert the
single offending file, re-apply the citation-line edit in isolation, and rebuild. No proof
state or dependency graph is affected, so there is no partial-completion hazard.
