# Implementation Summary: Tableau Vetting-Pipeline Acceptance Gate

**Task**: 567 — final acceptance gate for the modal-tableau refactor programme
**Plan**: `specs/567_tableau_vetting_pipeline_acceptance_gate/plans/01_acceptance-gate-fixes-verdict.md`
**Verdict**: `PASS WITH FIX TASKS` (see `artifacts/acceptance-gate-verdict.md`)

## Phases Completed

All six phases completed, in the order the plan's dependency-wave table specifies (Phase 1 ->
Phases 2 and 4 in parallel -> Phase 3 -> Phase 5 -> Phase 6).

### Phase 1 — Live re-measurement and evidence ledger
Re-derived every disputed figure and edit anchor against tree state `3a11702e`. Wrote
`artifacts/measurement-ledger.md` with a CORRECT/DRIFTED partition. **Critical scope finding**:
the naive `grep -rn 'eleven'` census returns 12 hits, not the plan's hypothesized 6 — six are the
genuine S4-module-count off-by-one (in scope), and six are an unrelated, correct
`RuleApplicationSpec` structural-hypothesis-bundle field-count reference that must never be
touched. This was documented in the ledger before any edit, preventing an over-correction that
would have corrupted accurate documentation. Also captured the live `s4witness.lean` trace and
the box-plus attribution chain, confirming the attribution fully explains the divergence (Phase
4's contingency did not trigger).

### Phase 2 — Correct the S4 module count (eleven -> ten)
Edited exactly the six module-count sites: `LoopChecking.lean`'s docstring, `ORGANISATION.md`,
and four `README.md` prose sites. Left the seven unrelated `RuleApplicationSpec` "eleven fields"
references untouched (in `TDriver.lean`, `CompletenessLoop.lean` x2, `GenericDriver.lean` x2,
`BDriver.lean` x2). Built `Cslib.Logics.Modal.Tableau.LoopChecking` — exit 0, `git diff` confined
to the docstring region.

### Phase 3 — Correct the drifted README numeric figures
Corrected all ten pre-identified DRIFTED figures (LoopChecking.lean size, pre-split declaration
count and its derived residue, repo-wide sorry count, regression-corpus size, `hintikkaS4_*`
bridge set, `ModalTableauResult` span with the repo-wide command rescoped away from `specs/`
volatility, and the two self-flagged-stale FrameSoundness/FrameCompleteness sizes). The
mandatory closing re-run of every command in the README's `## Measured Baseline` region surfaced
two additional drifted figures the research report and Phase 1 partition had missed — the raw
`axiom` word-occurrence counts (3->11 subsystem, 1,701->1,704 repo-wide) — corrected per the
phase's own escape clause. Also dropped one unverifiable secondary claim ("distinct identifiers
returns 11") rather than assert an unconfirmed replacement number.

### Phase 4 — Re-record the s4witness verdict with attribution
Additively annotated `specs/553_.../reports/02_redirect-inertness-divergence-audit.md`: a
`[SUPERSEDED]` pointer above the original §2.2 trace, and a new §2.2a subsection with the live
trace, the three concrete divergences, the box-plus attribution (three commits, all dated
2026-08-05, `git merge-base --is-ancestor` confirming they predate the programme's own
2026-08-06 commits), and an explicit "stale recorded verdict, not a behaviour-preservation
failure" statement. Verified: 75 insertions, 0 deletions; `CslibTests/` untouched; KNOWN-UNSOUND
row 1 still `"CLOSED"`.

### Phase 5 — Post-fix full CI gate re-run
Re-ran the full seven-step CI order plus all `pre-pr-check` ratchets plus `--wfail --iofail`
against the post-fix tree. All eleven blocking criteria green; both known non-blocking failures
(`lake lint` 145/145, `--wfail --iofail` same six modules) unchanged in character with zero new
programme-territory findings. All twelve figures written in Phase 3 (including the two Phase-3
discoveries) re-measured and matching. Full evidence table appended to the measurement ledger.

### Phase 6 — Acceptance-gate verdict document and fix-task handoff
Wrote `artifacts/acceptance-gate-verdict.md`: verdict `PASS WITH FIX TASKS`, the four-level
verdict grammar, the eleven-row blocking-criteria table, the four-row non-blocking-criteria
table, the decision rule (applied explicitly to D8), the remediation ledger, Reasoned Exclusions,
and standing do-nots. Wrote the three fix-task bundles into `completion_data.roadmap_items` in
`.return-meta.json` — no tasks were created directly, per the plan's explicit prohibition.

## Plan Deviations

1. **Phase 1**: "eleven" occurrence census returned 12 raw hits, not 6 — 6 are the genuine
   module-count defect, 6 are an unrelated correct figure. Documented, not forced into 6.
2. **Phase 2**: the verification step "grep returns zero hits" could not be satisfied literally
   without corrupting the unrelated `RuleApplicationSpec` figure. Reinterpreted as: zero
   module-count hits, exactly 7 unrelated hits remaining untouched.
3. **Phase 3**: dropped the unverifiable "hintikkaS4_* distinct identifiers returns 11" secondary
   claim rather than assert a number without a reproducible command.
4. **Phase 3**: discovered two additional drifted figures (axiom word-occurrence counts) not in
   the research report or Phase 1 partition, during the phase's own mandatory closing re-run.
   Corrected per the phase's explicit escape clause and recorded in the ledger.

No phase was blocked. No `.lean` proof term was modified — every edit is confined to docstrings,
README prose, and one `specs/`-tree report. The KNOWN-UNSOUND regression row was never touched.
No direct `Cslib.Init` import was added to any `S4/` module. No fix tasks were created directly.

## Verification

- `sorry_count`: 0 introduced (subsystem census unchanged at exactly 1, the pre-existing
  `[BLOCKED]` obstruction)
- `vacuous_count`: 0
- `axiom_count`: 0 introduced (subsystem 0, repo-wide 26, both unchanged)
- `build_passed`: true (3323 jobs, matching baseline)
- `ci_pipeline_passed`: true (all eleven blocking criteria green)

## Artifacts

- `specs/567_tableau_vetting_pipeline_acceptance_gate/artifacts/measurement-ledger.md`
- `specs/567_tableau_vetting_pipeline_acceptance_gate/artifacts/acceptance-gate-verdict.md`
- `specs/567_tableau_vetting_pipeline_acceptance_gate/summaries/01_acceptance-gate-summary.md` (this file)

## Modified Files

- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (docstring only)
- `Cslib/Logics/Modal/Tableau/README.md`
- `ORGANISATION.md`
- `specs/553_s4_loop_guard_soundness_reachability_restriction/reports/02_redirect-inertness-divergence-audit.md`
