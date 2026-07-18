# Implementation Plan: S5 Decidability DELIVERED — KB5 Residual Delegated to 525 (v7, corrective revision)

- **Task**: 515 - s5_universal_rule_termination_unblock_504
- **Status**: [BLOCKED]
- **Started**: 2026-07-15
- **S5 mandate delivered**: 2026-07-17 (commit `af593180`, plan v6 Phases 0-22)
- **Blocked (residual only)**: 2026-07-18 — the sole open deliverable (KB5 completeness + `Decidable kb5Valid`) is delegated to child task **525**, which needs a **new KB5 rule + extraction design** (task 524's rule was mechanically proven insufficient). The S5/5 mandate is DONE; this is not a block on the S5 work.
- **Effort**: 60 hours delivered across plan v6 Phases 0-22 (S5 chain + Euclidean 5 chain, all COMPLETED and CI-green). Remaining KB5 residual is scoped and owned by task 525's own plan (`specs/525_kb5_completeness_and_decidability/plans/01_kb5-completeness-decidability.md`), not re-estimated here.
- **Dependencies**: 525 (KB5 completeness redesign — the real and only remaining gate). **Dropped by this revision**: 514 (archived; research-only, genuinely delivered — stale dep) and 524 (completed but mechanically proven insufficient — see Revision Integration below). Task 504 remains the informational parent (`modalApplyOneS5`, `extractModelS5*`, `modalTruthLemmaS5` landed and consumed). Task 511 (S4 sibling) is decoupled.
- **Research Inputs**:
  - `specs/ROADMAP-alignment-audit.md` sections **A** (blocked-cluster four-branch verdict) and **C** (dependency-graph corrections) — **the authority for this corrective revision**. Ground-truthed against the repo.
  - plans/07_s5-termination-machinery.md (v6; **the full per-phase ledger of the delivered S5/5 work — retained as the authoritative record of the completed phases, superseded only at the header/status/deps level by this file**)
  - reports/03_s5-infrastructure-deep-research.md (S5 architecture authority; integrated in v3)
  - probes/five-s5-separation.lean (machine-verified, zero-axiom; settled the 5/KB5-route question in v4)
  - reports/07_phase19-soundness-blocker-remediation.md, reports/08_mint-arm-reuse-route-decision.md (the two Phase-19 soundness-gap resolutions, both landed)
- **Artifacts**: plans/08_s5-termination-machinery.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/rules/state-management.md
  - .claude/rules/git-workflow.md
  - .claude/rules/plan-format-enforcement.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This is a **corrective bookkeeping revision**, not a new implementation plan. It carries no new
Lean work of its own. Its purpose is to make the task metadata match audit-verified repository
reality:

1. **The S5 headline mandate is DELIVERED and live in-tree, sorry-free.** Task 515's own plan v6
   Phases 0-22 landed the terminating S5 tableau machinery, S5 soundness/completeness, S5
   decidability, and the full Euclidean-`5` route — all committed and CI-green (headline commit
   `af593180`). The rank obstruction that stalled prior attempts was **engineered around** via a
   witness-reuse mint rule, not defeated head-on. The task was mislabeled `[blocked]` on
   prerequisites that were already satisfied; this revision records the deliverables as DONE.

2. **The only genuinely open deliverable is the KB5 spin-off, and it is delegated to child task
   525.** Task 524 delivered a KB5 rule; a machine-checked lemma then **proved that rule's truth
   lemma false**. KB5 completeness is achievable (Blackburn-de Rijke-Venema §4.8-4.9) but needs a
   **new rule + extraction design**, not a re-run. That redesign is the scope of task 525
   (`parent_task = 515`), which already carries its own plan. Task 515 is re-scoped as the
   **parent tracker** for that work.

3. **Stale dependency edges are dropped.** 514 (archived, research-only) and 524 (completed but
   insufficient) are removed as blocking deps; the real and only gate is 525.

### Definition of done (S5 mandate) — ACHIEVED

Every one of the following is live in-tree, sorry-free, and axiom-clean (verified 2026-07-18):

| Deliverable | Symbol | Location |
|---|---|---|
| S5 soundness | `modalTableauS5_sound` | `Cslib/Logics/Modal/Tableau/FrameSoundness.lean:2991` |
| S5 completeness | `modalTableauS5_complete` | `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:2340` |
| S5 decision bridge | `s5Valid_decides` | `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:2411` |
| S5 decidability instance | `instDecidableS5Valid` | `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:2422` |
| `5` decision bridge | `fiveValid_decides` | `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:3203` |
| `5` decidability instance | `instDecidableFiveValid` | `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:3213` |

The witness-reuse rule, the linear tag-injection world budget, the spec split, the R7
refutation-as-theorem, the archival of ~2,000 superseded lines, and both Phase-19 soundness-gap
fixes all landed as recorded in plan v6.

## Revision Integration

This revision integrates **`specs/ROADMAP-alignment-audit.md` sections A and C** (the only new
inputs since plan v6). Verified against the repo by reading the actual files; no Lean code was
changed by this revision.

- **Section A (S5/T/B branch = DELIVERED, mislabeled blocked):** confirmed. `instDecidableS5Valid`
  and the full S5 chain are live and sorry-free (table above). Recorded here as DONE.
- **Section A (KB5 branch = NEEDS NEW DESIGN):** confirmed. `extractModelKb5_nonRoot_boxPos_gap`
  (`Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:3544`, sorry-free) mechanically witnesses
  that task 524's frozen `modalApplyOneKb5'` rule has a **false** truth lemma (root box-positive
  case fails for the counter `φ₀ := ¬(◇◇□p)`). This is not an impossibility — it is a
  design gap closable per BdRV §4.8-4.9 with a new rule + extraction. Delegated to task 525.
- **Section C (dependency corrections):**
  - `515→514`: 514 archived (research-only, genuinely delivered) — **dropped as stale**.
  - `515→524`: 524 completed but proven insufficient by 525 (`extractModelKb5_nonRoot_boxPos_gap`)
    — **demoted / dropped**; re-pointed at 525.
  - Real gate: **525** (`parent_task = 515`, already carries its own plan). Retained as the single
    dependency.

## Phase Ledger (delivered — preserved from plan v6)

All phases below are COMPLETE except the KB5 residual (Phase 23), which is delegated to task 525.
Full per-phase detail, lemma signatures, blocker diagnoses, and commit records are preserved in
`plans/07_s5-termination-machinery.md` (retained, not superseded at the phase level). This table
is the durable index; it does not restate the completed proofs.

| Phase | Description | Status |
|---|---|---|
| 0 | `modalSubfmls` tag closure under `neg` encoding (kill test) | [COMPLETED] |
| 1 | Witness-reuse rule + free bridges | [COMPLETED] |
| 2 | Hintikka congruence bridge | [COMPLETED] |
| 3 | R7 refutation-as-theorem + docstring/route corrections | [COMPLETED] |
| 4 | Linear budget arithmetic | [COMPLETED] |
| 5 | `accTargetsKnown` top-loop generalization | [COMPLETED] |
| 6 | Tag invariant (breaks the circularity) | [COMPLETED] |
| 7 | Counting crux | [COMPLETED] |
| 8 | Soundness re-proof feasibility probe | [COMPLETED] |
| 9 | Spec split + one-token weakening | [COMPLETED] |
| 10 | Rank-free loop invariant with `Aux` parametrization | [COMPLETED] |
| 11 | Step preservation | [COMPLETED] |
| 11.5 | `Aux` re-arity — thread `e` | [COMPLETED] |
| 12 | Parametric Hintikka lift + K/T/B regression gate | [COMPLETED] |
| 13 | Soundness re-proof — `modalTableauS5_sound` | [COMPLETED] |
| 14 | S5 assembly, archival, CI, regression test | [COMPLETED] |
| 15 | Euclidean route feasibility gate | [COMPLETED] |
| 16 | `Relation.EuclGen` least-Euclidean closure | [COMPLETED] |
| 17 | Rooted normal form (root + universal cluster) | [COMPLETED] |
| 18 | `modalApplyOneFive` root-aware rule + termination reuse | [COMPLETED] |
| 19a | Guarded mint arm + termination bound re-derivation | [COMPLETED] (`56a84d07`, `2c7abe73`) |
| 19b | `modalTableauFive_sound` bespoke assembly | [COMPLETED] |
| 20 | `extractModelFive` + Euclidean truth lemma | [COMPLETED] |
| 21 | `modalTableauFive_complete` + `Decidable (fiveValid φ)` | [COMPLETED] |
| 22 | KB5 rule `modalApplyOneKb5` + `modalTableauKb5_sound` | [COMPLETED] |
| 23 | **KB5 completeness + `Decidable (kb5Valid φ)`** | **[DELEGATED → task 525]** |

## Phase 23 (residual) — KB5 completeness, delegated to task 525

- **Status**: [DELEGATED → 525]
- **Why not done under 515**: `modalTableauKb5_sound` (Phase 22) landed by reusing
  `modalApplyOneFive` as a root-restricted alias ("factor, not clone"). That reuse is **provably
  incomplete** for `kb5Valid`: `extractModelKb5`'s forced closure relates the root to indirect
  chain targets (`0→a→c`) to which the root-restricted rule never propagates content, so the truth
  lemma's root box-positive case is **false**. Machine-checked witness:
  `extractModelKb5_nonRoot_boxPos_gap` (`FrameCompleteness.lean:3544`, sorry-free) and the design
  scout `extractModelKb5_root_reach_scout` (zero axioms).
- **What it needs (owned by task 525)**: a genuinely new KB5-specific propagation rule (or model
  extraction with cluster-membership bookkeeping rather than trigger-identity gating), its
  soundness against `kb5FC`, then `modalTableauKb5_complete` and `instDecidableKb5Valid` via the
  Phase-12 lift pattern, plus docstring reconciliation and CI. Task 525
  (`parent_task = 515`) already carries this in
  `specs/525_kb5_completeness_and_decidability/plans/01_kb5-completeness-decidability.md`.
  Task 525 is itself gated on a new-rule-design step (its `[BLOCKED]` record); that chain is 525's
  to manage, not 515's.
- **Do-not-re-attempt record (standing)**: do NOT re-run against task 524's frozen
  `modalApplyOneKb5'` rule — its truth lemma is a machine-checked falsehood, not an open goal.

## Verification

No Lean verification is performed by this revision (no code change). The delivered-symbol table
under "Definition of done" was ground-truthed by reading the actual files at the cited line
numbers on 2026-07-18. All claims trace to `specs/ROADMAP-alignment-audit.md` sections A and C.

## Recommended terminal status

This agent does **not** set status. Recommendation for the skill postflight:

- **Primary — `[BLOCKED]` on 525** (parent-tracker framing, consistent with the already-corrected
  `dependencies: [525]`): the S5/5 mandate is delivered and recorded; 515 remains open only as the
  parent tracker for the KB5 residual, which is delegated to and gated on child task 525. The block
  is narrow and legitimate (KB5 spin-off only), no longer the mislabeled "fully blocked" state the
  audit flagged.
- **Alternative — `[COMPLETED]`** (fold-out framing): if the orchestrator prefers to close 515 on
  its delivered S5 mandate and let 525 carry KB5 wholly independently, mark 515 `[COMPLETED]` with a
  completion summary pointing at the delivered instances, and drop the `515→525` edge (525 already
  has `parent_task = 515`). Choose this only if KB5 is considered fully out of 515's scope.
