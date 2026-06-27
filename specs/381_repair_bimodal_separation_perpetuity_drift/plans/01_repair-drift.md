# Implementation Plan: Task #381 - Repair Bimodal Separation/Perpetuity Drift

- **Task**: 381 - Repair the 4 Bimodal Separation/Perpetuity drift modules
- **Status**: [NOT STARTED]
- **Effort**: 2 hours
- **Dependencies**: None
- **Research Inputs**: specs/381_repair_bimodal_separation_perpetuity_drift/reports/01_drift-diagnosis.md
- **Artifacts**: plans/01_repair-drift.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: lean
- **Lean Intent**: false

## Overview

Four sorry-free Bimodal modules fail to build after the `leanprover/lean4:v4.31.0` toolchain bump. The repair is a mechanical, statement-preserving drift fix authoritatively diagnosed and verified in the research report (every replacement was confirmed by `lean_multi_attempt` returning `goals:[]`, zero diagnostics). Definition of done: all four modules build clean, `lake build` (full) is green, lint-style passes, and the touched declarations carry zero `sorry` and zero new axioms.

### Research Integration

The report establishes ONE shared root for 3 of the 4 modules and a distinct (but same-flavor) fix for the 4th:

- **Shared root (Modules 1-3 = Duality, QLemma, Eliminations)**: `Formula.neg/and/or` are a two-layer `abbrev` chain ending in `PropositionalConnectives.neg` (`fun φ => imp φ bot`). Under v4.31.0, naming only `Formula.neg` (or nothing) in a `simp` set unfolds one layer then stalls at `PropositionalConnectives.neg`, so the purity predicates (`isUFree`/`isSFree`/`isFutureOnly`/`isPastOnly`/`isSyntacticallySeparated`) never see the `.imp` head. **Fix idiom**: add `PropositionalConnectives.neg` (plus `Formula.and/or/neg` where a bare `simp` omits them) to the simp set — exactly the idiom already accepted in the repaired `Separation/Defs.lean`. Preserve each site's existing `simp` vs `simp only` form.
- **Module 4 (Bridge) is distinct** (same flavor as task-364 Family-2): a `Type mismatch` at line 102 because the proof unfolds the raw recursive `swapTemporal`, which over-normalizes. **Fix**: replace the raw def `Bimodal.Formula.swapTemporal` with the structural `@[simp]` lemma `Bimodal.Formula.swapTemporal_allFuture` (fully qualified) in the `simp only` set. This is lemma substitution, not simp-set augmentation, so it is its own phase.

Every per-line current→replacement is taken verbatim from the report's tables.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (no roadmap_path provided / flag not set).

## Goals & Non-Goals

**Goals**:
- Restore clean builds for all four modules: `Separation/Duality.lean`, `Separation/DedekindZ/QLemma.lean`, `Separation/Eliminations.lean`, `Theorems/Perpetuity/Bridge.lean`.
- Apply only the verified, mechanical simp-set / lemma-substitution edits from the report.
- Verify zero-debt: zero `sorry`, zero new axioms, all theorem statements preserved verbatim; CI-green (`lake build` + `lake exe lint-style` + `lake lint`).

**Non-Goals**:
- No statement changes, no new lemmas, no new axioms, no `admit`, no redesign.
- No global change to `PropositionalConnectives.neg`/`.top` attributes (the report explicitly rejects the `@[simp]`/`@[reducible]` global alternative as out of scope and risky).
- No edits to the already-repaired `Separation/Defs.lean`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Line numbers drift from report after edits (Eliminations is multi-site) | M | M | Match on the `simp` tactic text and enclosing lemma name, not just the line number; fix one site, scoped-build-confirm, then transcribe to siblings |
| A site needs `PropositionalConnectives.top` not covered by report | L | L | Report says none of the listed sites need `top` except via already-named simp lemmas; if a residual `PropositionalConnectives.top` appears in a build error, add `PropositionalConnectives.top` (and `Formula.top`) defensively per report §1 |
| `unusedSimpArgs` lint flags added simp args | L | L | Added `PropositionalConnectives.neg` is load-bearing (it fires); affected files also set `linter.unusedSimpArgs false` locally (e.g. QLemma:21). Keep that option where present |
| Over-normalization recurs in Bridge if raw def left in | M | L | Use the structural `@[simp]` lemma `swapTemporal_allFuture` (fully qualified), leave `exact past_raw` unchanged |
| Accidental statement edit | H | L | Edits touch only `simp` argument lists inside existing theorem bodies; diff-review each phase before commit |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3, 4 | -- |
| 2 | 5 | 1, 2, 3, 4 |

Phases within the same wave can execute in parallel. Phases 1-4 each touch a distinct file (no shared territory) and may be parallelized under a `--team` run with per-file territory contracts; Phase 3 is the long pole. Phase 5 is sequential after all repairs land.

**Global constraints for every phase (carry into each agent run)**:
- NEVER call `lean_diagnostic_messages`. Use `lean_goal` (sparingly) + a scoped `lake build` of the module to confirm.
- Preserve each site's existing tactic form (`simp` vs `simp only`).
- Zero `sorry`, zero new axioms, no statement changes.
- After the module builds clean, make an incremental commit before moving on.

---

### Phase 1: Duality (2 edits) [COMPLETED]

**Goal**: Fix the two `simp made no progress` failures in `neg_future_only` / `neg_past_only` by naming the full neg unfold chain.

**File**: `Cslib/Logics/Bimodal/Metalogic/Separation/Duality.lean`
**Module**: `Cslib.Logics.Bimodal.Metalogic.Separation.Duality`

**Tasks**:
- [ ] Line 357 (`neg_future_only`): replace `simp [isFutureOnly, h]` with `simp [Formula.neg, PropositionalConnectives.neg, isFutureOnly, h]`.
- [ ] Line 362 (`neg_past_only`): replace `simp [isPastOnly, h]` with `simp [Formula.neg, PropositionalConnectives.neg, isPastOnly, h]`.
- [ ] Leave neighbouring `and_/or_/imp_future_only` (367-402) untouched — they build (their formula heads are `.imp` directly).
- [ ] Scoped build: `lake build Cslib.Logics.Bimodal.Metalogic.Separation.Duality`.
- [ ] Commit: `task 381 phase 1: repair Separation/Duality drift`.

**Timing**: 15 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation/Duality.lean` — 2 simp-set augmentations (lines 357, 362).

**Verification**:
- `lake build` of the module succeeds with no errors/warnings.
- (Optional) `lean_goal` at the post-`simp` position shows `no goals`.

---

### Phase 2: QLemma (1 edit) [COMPLETED]

**Goal**: Fix the `unsolved goals` in `Q_Z_U_free` where the `neg` over `snce` is left unreduced.

**File**: `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/QLemma.lean`
**Module**: `Cslib.Logics.Bimodal.Metalogic.Separation.DedekindZ.QLemma`

**Tasks**:
- [ ] Line 192 (`Q_Z_U_free`): replace `simp [qZ, isUFree, hA, hB, hC]` with `simp [qZ, Formula.or, Formula.neg, PropositionalConnectives.neg, isUFree, hA, hB, hC]`.
- [ ] Leave sibling `Q_Z_no_S_nested` (195-199) untouched (different `repeat (first | …)` tactic; not in failing set).
- [ ] Preserve the local `linter.unusedSimpArgs false` option (QLemma:21).
- [ ] Scoped build: `lake build Cslib.Logics.Bimodal.Metalogic.Separation.DedekindZ.QLemma`.
- [ ] Commit: `task 381 phase 2: repair Separation/DedekindZ/QLemma drift`.

**Timing**: 10 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/QLemma.lean` — 1 simp-set augmentation (line 192).

**Verification**:
- `lake build` of the module succeeds; the leftover goal `⊢ isUFree (¬(¬A) S C) = true` is gone.

---

### Phase 3: Eliminations (~15 edits) [COMPLETED]

**Goal**: Fix the repeated second-layer `neg` unfold stall across the parallel Case-2/Case-3 elimination clones. All same family; NO `obtain`-shape drift.

**File**: `Cslib/Logics/Bimodal/Metalogic/Separation/Eliminations.lean`
**Module**: `Cslib.Logics.Bimodal.Metalogic.Separation.Eliminations`

**Approach**: Fix one representative site, scoped-build-confirm the idiom, then transcribe to the structurally identical siblings. Match on the `simp` text + enclosing `have`/lemma name (line numbers may shift ±1 after edits). Per-site fix = add `PropositionalConnectives.neg` (and `Formula.and`/`Formula.or`/`Formula.neg` where a bare `simp` omits them). Preserve `simp` vs `simp only` form at each site.

**Tasks** (verified/representative current → replacement from report §2; lines are the `simp` line):
- [ ] 63 `neg_separated`: `simp [Formula.neg, isSyntacticallySeparated, h]` → add `PropositionalConnectives.neg`.
- [ ] ~501-503 `case2_psi_properties` sep-check: `simp only [d1, d2, d3, Formula.or, Formula.and, Formula.neg, isSyntacticallySeparated, isUFree, isSFree, ha, hq, hA, hB, hA', hB', Bool.true_and, Bool.and_true, hsep_A, hsep_B]` → add `PropositionalConnectives.neg`.
- [ ] 544 `elim_case_3.haq_Uf`: `simp [Formula.and, Formula.neg, isUFree, ha, hq]` → add `PropositionalConnectives.neg` (**VERIFIED closes** — fix this site first as the representative).
- [ ] 546 `…haq_Sf`: `simp [Formula.and, Formula.neg, isSFree, ha', hq']` → add `PropositionalConnectives.neg`.
- [ ] 547 `…ha_neg_Uf`: `simp [Formula.neg, isUFree, ha]` → add `PropositionalConnectives.neg`.
- [ ] 548 `…ha_neg_Sf`: `simp [Formula.neg, isSFree, ha']` → add `PropositionalConnectives.neg`.
- [ ] 553 `…hsep_H`: `simp only [is_syntactically_separated_allPast, Formula.neg, isUFree, ha, Bool.and_true]` → add `PropositionalConnectives.neg`.
- [ ] 603/605/606/607/612 `elim_case_3_gen`-sibling haves (same shapes as 544-553): add `PropositionalConnectives.neg`.
- [ ] 661 `…haq_Uf` (bare): `simp [isUFree, ha, hq]` → `simp [Formula.and, Formula.neg, PropositionalConnectives.neg, isUFree, ha, hq]` (**VERIFIED closes**).
- [ ] 662 `…ha_neg_Uf` (bare): `simp [isUFree, ha]` → `simp [Formula.neg, PropositionalConnectives.neg, isUFree, ha]`.
- [ ] 667 `…hsep_H`: `simp only [is_syntactically_separated_allPast, Formula.neg, isUFree, ha, Bool.and_true]` → add `PropositionalConnectives.neg`.
- [ ] Sweep the full reported line set (63, 498, 543, 545, 547, 548, 552, 602, 604, 606, 607, 611, 660, 662, 666) to confirm every Case-2/Case-3 clone in the failing set is covered; the error line and `simp` line differ by ±1 at some sites (Lean reports `unsolved goals` at the enclosing `have`/proof head — the fix always lands on the `simp` call).
- [ ] Scoped build: `lake build Cslib.Logics.Bimodal.Metalogic.Separation.Eliminations`.
- [ ] If a build error still shows a residual `PropositionalConnectives.top`, add `PropositionalConnectives.top` (and `Formula.top`) at that site defensively (report §1).
- [ ] Commit: `task 381 phase 3: repair Separation/Eliminations drift`.

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Separation/Eliminations.lean` — ~15 simp-set augmentations across parallel Case-2/Case-3 clones.

**Verification**:
- `lake build` of the module succeeds; no `unsolved goals` remain at any of the listed sites.
- (Optional) `lean_goal` at the representative site 544 shows `no goals` after the edit.

---

### Phase 4: Bridge (1 edit, distinct idiom) [COMPLETED]

**Goal**: Fix the `Type mismatch` at line 102 in `pastMono` by routing the `swapTemporal` normalization through the structural `@[simp]` lemma instead of the raw recursive def.

**File**: `Cslib/Logics/Bimodal/Theorems/Perpetuity/Bridge.lean`
**Module**: `Cslib.Logics.Bimodal.Theorems.Perpetuity.Bridge`

**Tasks**:
- [ ] Line 101: replace `simp only [Bimodal.Formula.swapTemporal, Bimodal.Formula.swapTemporal_involution] at past_raw` with `simp only [Bimodal.Formula.swapTemporal_allFuture, Bimodal.Formula.swapTemporal_involution] at past_raw`.
- [ ] Use the fully-qualified `Bimodal.Formula.swapTemporal_allFuture` (bare name is not in scope in this file).
- [ ] Leave `exact past_raw` (line 102) unchanged — it type-checks once `past_raw` is rewritten to `⊢ H(φ₁ → φ₂)`.
- [ ] Scoped build: `lake build Cslib.Logics.Bimodal.Theorems.Perpetuity.Bridge`.
- [ ] Commit: `task 381 phase 4: repair Perpetuity/Bridge swapTemporal drift`.

**Timing**: 15 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Bridge.lean` — 1 lemma substitution (line 101).

**Verification**:
- `lake build` of the module succeeds; the `Type mismatch` at line 102 is gone.
- (Optional) `lean_goal`/`lean_multi_attempt` confirms `past_raw` rewrites to exactly the goal `⊢ H(φ₁ → φ₂)`.

---

### Phase 5: Zero-debt verification [NOT STARTED]

**Goal**: Confirm the whole repair is CI-green and debt-free across all four modules.

**Depends on**: 1, 2, 3, 4

**Tasks**:
- [ ] Full build: `lake build` (entire project) — green.
- [ ] Lint-style: `lake exe lint-style` — passes.
- [ ] `lake lint` — passes; specifically confirm `unusedSimpArgs` does not flag the added `PropositionalConnectives.neg` (it is load-bearing, and affected files set `linter.unusedSimpArgs false` locally — keep that option where present).
- [ ] Import sanity: run the project's `checkInitImports` (init-imports) check.
- [ ] Axiom audit: `lean_verify` / `#print axioms` on the touched declarations (`neg_future_only`, `neg_past_only`, `Q_Z_U_free`, the Eliminations Case-2/3 lemmas, `pastMono`) shows zero `sorry` and zero new axioms.
- [ ] Statement-preservation check: `git diff` confirms edits touch only `simp` argument lists / one lemma substitution inside existing theorem bodies — no theorem signatures changed, no new declarations.
- [ ] Commit: `task 381: complete implementation` (final, includes summary).

**Timing**: 30 minutes

**Files to modify**:
- None (verification only).

**Verification**:
- `lake build` + `lake exe lint-style` + `lake lint` all green.
- Axiom audit shows no `sorryAx` and no new axioms on any touched declaration.

---

## Testing & Validation

- [ ] Each module builds clean under scoped `lake build` (Phases 1-4).
- [ ] Full `lake build` green (Phase 5).
- [ ] `lake exe lint-style` and `lake lint` pass (Phase 5).
- [ ] `checkInitImports` / init-imports check passes (Phase 5).
- [ ] Axiom audit: zero `sorry`, zero new axioms on all touched declarations (Phase 5).
- [ ] `git diff` confirms all theorem statements preserved verbatim (Phase 5).
- [ ] `lean_diagnostic_messages` was NEVER invoked at any point.

## Artifacts & Outputs

- `Cslib/Logics/Bimodal/Metalogic/Separation/Duality.lean` (2 edits)
- `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/QLemma.lean` (1 edit)
- `Cslib/Logics/Bimodal/Metalogic/Separation/Eliminations.lean` (~15 edits)
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Bridge.lean` (1 edit)
- `specs/381_repair_bimodal_separation_perpetuity_drift/plans/01_repair-drift.md` (this plan)
- `specs/381_repair_bimodal_separation_perpetuity_drift/summaries/01_repair-drift-summary.md` (implementation summary, created at completion)

## Rollback/Contingency

- Each phase is an independent file with its own incremental commit; revert a phase's commit to roll it back without affecting the others.
- All edits are simp-set augmentations / a single lemma substitution inside existing theorem bodies. If any verified replacement unexpectedly fails to close, re-run `lean_multi_attempt` at that exact site (per the report's verified tables), add `PropositionalConnectives.top`/`Formula.top` defensively if a residual `top` appears, and preserve the original tactic form. Do NOT introduce `sorry`, new axioms, or statement changes to force a build.
