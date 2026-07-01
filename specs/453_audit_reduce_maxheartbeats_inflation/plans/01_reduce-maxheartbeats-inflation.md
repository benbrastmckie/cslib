# Implementation Plan: Audit and Reduce maxHeartbeats Inflation (Task 453)

- **Task**: 453 - Audit and reduce `maxHeartbeats` inflation across Bimodal/Temporal metalogic; normalize scoping to `in`-scoped
- **Status**: [IMPLEMENTING]
- **Effort**: 12 hours (build-time dominated; reasoning time small)
- **Dependencies**: None (must NOT run concurrently with task 414 on shared Modal/Temporal/Bimodal files — sequence, do not parallelize)
- **Research Inputs**: specs/453_audit_reduce_maxheartbeats_inflation/reports/01_maxheartbeats-audit.md
- **Artifacts**: plans/01_reduce-maxheartbeats-inflation.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

This task reduces `set_option maxHeartbeats` inflation across `Cslib/Logics/Bimodal/Metalogic/**`
and `Cslib/Logics/Temporal/Metalogic/**` (64 sites total: 15 unscoped file-wide, 49 scoped `... in`).
The work is a **zero-debt code-hygiene** effort: NO proof weakening; `lake build` and `lake test`
must stay green after every phase (green-gated). Because this metalogic area has heavy, slow builds,
all reductions are **build-driven** — there are no pre-computed minimal values. Each phase (and each
batch within a phase) is independently verifiable and committable so the work can be interrupted and
resumed without losing green state. Definition of done: 0 unscoped sites remain, the 3.2M/6.4M
offenders are lowered or restructured to their measured minimum with modest headroom, every
surviving high budget carries a one-line justification, and the full CI pipeline passes.

### Research Integration

Built directly on `reports/01_maxheartbeats-audit.md`. Key findings driving the plan:
- **Inventory**: 64 sites (not the stale review headline of 72). Value distribution:
  6.4M×1, 3.2M×33, 1.6M×12, 1.2M×3, 800k×11, 400k×4.
- **15 unscoped sites** each sit atop an `@[expose] public section` governing 2–40 declarations
  (RRelation 40, Burgess 38, Seeds 29). Unscoped→scoped is a **build-probe** operation (delete
  the file-wide option, `lake build`, then scope `... in` onto exactly the declaration(s) that
  report "maxHeartbeats exceeded"), NOT a text move.
- **Worst offender**: `Temporal/Metalogic/Chronicle/CounterexampleElimination/MainElimination.lean:38`
  (6.4M) governs the monolithic `eliminatePotentialCounterexample` (4-way `match pc.kind` dispatch,
  ~1600 lines) — fix by lemma-extracting each dispatch arm.
- **33× 3.2M cluster** is largely copy-paste defensive inflation (incl. CompletenessHelpers 8
  identical sites) — bisectable by binary search to the smallest passing round value.
- **Independence**: tasks 412/413/414 concern `simp only [...]` list normalization, a disjoint
  concern from heartbeat budgets; only light file-level coordination with 414 is needed.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (no roadmap_path provided). Task is self-contained code hygiene.

## Goals & Non-Goals

**Goals**:
- Convert all 15 unscoped (file-wide) `set_option maxHeartbeats` sites to `... in`-scoped options
  attached to exactly the declaration(s) that require them, at their smallest passing value.
- Lower the copy-paste 3.2M scoped cluster (33 sites) to measured minimums with modest headroom
  via binary search.
- Restructure the 6.4M `eliminatePotentialCounterexample` and residual monolithic 3.2M proofs by
  lemma/`have` extraction so their ceilings drop.
- Document every surviving high budget (>= 1.6M) with a one-line irreducibility justification.
- Keep `lake build` + `lake test` green after every phase and every intra-phase batch (zero-debt).

**Non-Goals**:
- No proof weakening, no `sorry`, no axiom additions, no statement changes.
- The 5 further `maxHeartbeats` sites elsewhere under `Cslib/Logics/` (outside the two Metalogic
  trees) are OUT OF SCOPE — flag as possible follow-up, do not touch.
- No `simp only [...]` list normalization (that is task 414's concern).
- No pre-computing "theoretical" minimal values — every value must be build-verified.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Lowering a ceiling below its true passing value → CI red on slower machines | H | M | Binary-search to smallest passing value, then round UP to next sensible multiple for headroom; never set to exactly the passing edge |
| Lemma-extraction (Phase 3) changes a proof and breaks a downstream proof | H | M | Isolate Phase 3; extract one arm/`have` at a time; `lake build` after each; keep statements identical; do last |
| Heavy/slow builds exhaust the agent run before a phase completes | M | H | Batch each phase per-file/per-site; commit after every green batch; phase is resumable from the next un-done site |
| Merge churn if task 414 edits the same files concurrently | M | L | Do NOT run 453 and 414 in parallel; sequence them; 453 touches only `set_option` lines (+ Phase 3 extractions), 414 touches `simp only` argument lists |
| A file-wide option was masking several individually-expensive declarations | M | M | The build-probe surfaces each failing declaration by name; scope each one separately (still strictly better than file-wide) |
| Profiling all 64 sites is infeasible in budget | M | H | Reserve `lean_profile_proof` for residual offenders only (after bisection), not the whole inventory |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases are fully sequential: each is a green-gated commit and later phases assume the earlier
numeric reductions are already in place. No two phases may run in parallel (they share files).

### Phase 1: Unscoped → scoped conversions (build-probe) [COMPLETED]

**Goal**: Eliminate all 15 unscoped file-wide `set_option maxHeartbeats` sites, converting each to
`... in`-scoped options attached to exactly the declaration(s) that exceed the 200000 default.

**Probe procedure (per file)**: (1) delete the file-wide `set_option maxHeartbeats N` line;
(2) `lake build <Module>`; (3) each declaration that fails prints `maxHeartbeats … exceeded` with
its name; (4) add `set_option maxHeartbeats N in` immediately above *each* failing declaration
(using the smallest passing round value — bisect if the old value looks inflated); (5) rebuild green.
If exactly one declaration needs it, the file ends with one scoped option (ideal). If several do,
each gets its own scoped option.

**Tasks**:
- [x] Process EASY small-count files first to validate the procedure: `Completeness.lean:47` (2 decls),
      `DenseSoundness.lean:32` (6), `ChronicleToCountermodel.lean:38` (5). *(all 3 pass clean at
      default 200000 with option deleted entirely -- no scoped option needed)*
- [x] Process MEDIUM files: `Soundness.lean:32` (8), `TruthLemma.lean:40` (10), `Since.lean:33` (10),
      `Splitting.lean:32` (11), `WitnessSeed.lean:29` (12), `Frame.lean:28` (14),
      `BooleanStructure.lean:33` (20). *(all 7 pass clean at default -- no scoped option needed)*
- [x] Process HARD high-count files: `MCS.lean:38` (23), `UltrafilterMCS.lean:34` (24),
      `Seeds.lean:36` (29), `Burgess.lean:35` (38), `RRelation.lean:29` (40). *(all 5 pass clean at
      default -- no scoped option needed)*
- [x] Commit after each file (or small batch of files) is green, so the phase is resumable. *(3
      commits: EASY batch, MEDIUM batch, HARD batch)*
- [x] Confirm 0 unscoped `set_option maxHeartbeats` sites remain in the two Metalogic trees
      (`grep -rn 'set_option maxHeartbeats' | grep -v ' in$'` style check, adjusted for exact syntax).
      *(confirmed: 0 remain)*

**Outcome note**: every one of the 15 unscoped file-wide options was pure defensive inflation --
in all 15 cases the governed declaration(s) built clean at the 200000 default with the option
simply deleted (never needed a scoped replacement). This differs from the plan's anticipated
outcome (some declarations needing individually-scoped high budgets); the build-probe confirmed
no declaration in these 15 files actually required extra heartbeat budget.

**Timing**: ~4 hours (dominated by ~15 clean-build probes plus per-declaration rebuilds).

**Depends on**: none

**Files to modify** (all under `Cslib/Logics/`):
- `Bimodal/Metalogic/Algebraic/BooleanStructure.lean` (line 33, 400k)
- `Bimodal/Metalogic/Algebraic/UltrafilterMCS.lean` (line 34, 800k)
- `Temporal/Metalogic/Chronicle/ChronicleToCountermodel.lean` (line 38, 1.6M)
- `Temporal/Metalogic/Chronicle/Frame.lean` (line 28, 800k)
- `Temporal/Metalogic/Chronicle/PointInsertion/Burgess.lean` (line 35, 3.2M)
- `Temporal/Metalogic/Chronicle/PointInsertion/Seeds.lean` (line 36, 3.2M)
- `Temporal/Metalogic/Chronicle/PointInsertion/Since.lean` (line 33, 3.2M)
- `Temporal/Metalogic/Chronicle/PointInsertion/Splitting.lean` (line 32, 3.2M)
- `Temporal/Metalogic/Chronicle/RRelation.lean` (line 29, 1.6M)
- `Temporal/Metalogic/Chronicle/TruthLemma.lean` (line 40, 3.2M)
- `Temporal/Metalogic/Completeness.lean` (line 47, 3.2M)
- `Temporal/Metalogic/DenseSoundness.lean` (line 32, 1.6M)
- `Temporal/Metalogic/MCS.lean` (line 38, 1.6M)
- `Temporal/Metalogic/Soundness.lean` (line 32, 1.6M)
- `Temporal/Metalogic/WitnessSeed.lean` (line 29, 800k)

**Verification (CI gate for this phase)**:
- `lake build` — green
- `lake test` — green
- `lake exe checkInitImports` — passes
- `lake exe lint-style` — passes
- 0 unscoped `maxHeartbeats` sites remain in Bimodal/Temporal Metalogic trees.

---

### Phase 2: Bisect scoped ceilings (3.2M cluster) [COMPLETED]

**Goal**: Binary-search downward on the scoped 3.2M cluster (and other inflated scoped sites),
setting each to the smallest passing round value with modest headroom.

**Bisection methodology (per site)**: bisect between 200000 and the current value; `lake build <Module>`
at each step; set the option to the smallest passing round value (next power-of-two multiple, e.g.
800k or 1.6M). Round UP for CI-machine headroom. Do NOT lower below the measured passing value.

**Tasks**:
- [x] Bisect `CompletenessHelpers.lean` 8 identical 3.2M sites (lines 81, 104, 122, 142, 162, 186,
      210, 255) on `deriveDne`, `deriveHNec`, `deriveAndTopIntro`, `mcs_dne`, `mcs_ff_imp_f`,
      `mcs_pp_imp_p`, `mcs_g_trans`, `mcs_h_trans`. *(all 8 pass clean at default 200000 with
      option deleted -- no scoped replacement needed)*
- [x] Bisect `DedekindZ/Cases.lean` 3.2M sites (436, 701, 898, 1217, 1496). *(and the 2x1.6M sites
      at 549, 1341, done together -- all 7 pass clean at default)*
- [x] Bisect `Decidability/CountermodelExtraction.lean` 3.2M sites (666, 721, 776, 828) and lower
      values (547, 598, 633). *(all 7 pass clean at default)*
- [x] Bisect remaining 3.2M sites: `Saturation.lean:638`, `DedekindZ/QLemma.lean:306`,
      `Separation/Eliminations.lean` (377, 505), `Separation/Hierarchy/HierarchyCaseSep.lean`
      (70, 104, 255), `RecursiveWalks.lean` (37, 580), `DenseCompleteness.lean:98`. *(all pass
      clean at default, along with their co-located lower-value siblings in the same files)*
- [x] Also bisect obvious over-provisioned lower sites opportunistically (1.6M/1.2M/800k) where a
      quick probe shows headroom, but do NOT touch sites already at their minimum. *(opportunistic:
      GeneralizedNecessitation.lean's 3x400k sites also probed -- all pass clean at default)*
- [x] Leave sites that survive at high values for Phase 3 (restructure) or Phase 4 (document).
      *(none survived at high values -- only MainElimination.lean:38 (6.4M) remains, reserved for
      Phase 3 by design)*
- [x] Commit after each file's sites are green, so the phase is resumable. *(9 commits, one per
      file)*

**Outcome note**: every scoped site probed in Phase 2 (45 of 49, all except MainElimination's 6.4M
and the 3 GeneralizedNecessitation 400k sites which were also probed and removed) was pure
defensive inflation -- ALL passed clean at the 200000 default with the option deleted entirely.
Zero sites needed a lowered-but-nonzero scoped replacement value; bisection-to-a-value was never
required because every ceiling probe went straight to "no option needed at all". After Phase 2,
only 1 `maxHeartbeats` site remains in the two Metalogic trees: `MainElimination.lean:38` (6.4M),
Phase 3's target.

**Timing**: ~4 hours (each bisection is ~4–6 builds per site; ~20 sites).

**Depends on**: 1

**Files to modify** (scoped sites, under `Cslib/Logics/`):
- `Temporal/Metalogic/CompletenessHelpers.lean`
- `Bimodal/Metalogic/Separation/DedekindZ/Cases.lean`, `.../QLemma.lean`
- `Bimodal/Metalogic/Decidability/CountermodelExtraction.lean`, `.../Saturation.lean`
- `Bimodal/Metalogic/Separation/Eliminations.lean`, `.../Hierarchy/HierarchyCaseSep.lean`
- `Temporal/Metalogic/Chronicle/CounterexampleElimination/RecursiveWalks.lean`
- `Temporal/Metalogic/DenseCompleteness.lean`

**Verification (CI gate for this phase)**:
- `lake build` — green
- `lake test` — green
- `lake exe checkInitImports` — passes
- `lake exe lint-style` — passes
- 3.2M site count sharply reduced from 33; remaining 3.2M sites are known/queued for Phase 3 or 4.

---

### Phase 3: Restructure the 6.4M and residual monolithic 3.2M offenders [COMPLETED]

**Goal**: Lower the ceilings of the offenders that survive bisection by restructuring proof
structure — the ONLY phase that changes proofs. Highest regression risk; isolated; done one
declaration at a time with a rebuild after each.

**Tasks**:
- [x] Lemma-extract `eliminatePotentialCounterexample` (`MainElimination.lean:38`, 6.4M) --
      *(deviation: skipped -- the build-probe (delete option, rebuild) showed the declaration
      builds clean at the 200000 default in ~7s. It was pure defensive inflation like every other
      site in this task; there is no ceiling left to lower via lemma-extraction, so the 4-arm
      extraction is unnecessary. The option and its stale comment were simply removed.)*
- [ ] Rebuild after each arm extraction... *(deviation: skipped -- no extraction was performed,
      see above; dispatcher already needs only the default budget as-is)*
- [ ] For residual monolithic 3.2M proofs that survived Phase 2... *(deviation: skipped -- Phase 2
      left ZERO surviving scoped sites in `DedekindZ/Cases.lean`, `Eliminations.lean`,
      `HierarchyCaseSep.lean`, or `RecursiveWalks.lean`; every site in every one of these files was
      removed as pure defensive inflation during Phase 2. There are no residual offenders to
      profile or restructure.)*
- [x] Keep all statements identical — extraction must be behavior-preserving (zero-debt).
      *(trivially satisfied: no proof structure was changed anywhere in this task, only
      `set_option maxHeartbeats` lines and their accompanying comments were removed)*
- [x] Commit after each extracted declaration is green, so the phase is resumable. *(1 commit:
      MainElimination.lean option removal)*

**Outcome note**: Phase 3 as originally scoped (lemma-extraction + profiling-driven restructuring)
turned out to be entirely unnecessary. The build-probe methodology used throughout phases 1-2
already surfaced the true minimum for every single site in the inventory, and in every case
(64/64 across the whole task) the true minimum was the 200000 default itself. The one declaration
Phase 3 targeted (the worst offender, `eliminatePotentialCounterexample` at 6.4M / 32x default)
was no exception. This means the entire 64-site `maxHeartbeats` inventory across
`Cslib/Logics/{Bimodal,Temporal}/Metalogic/**` was defensive inflation with zero declarations
actually requiring extra heartbeat budget -- confirmed by an actual `lake build` on every single
site, not assumed.

**Timing**: ~3 hours (extraction + per-arm rebuilds + targeted profiling; profiling is SLOW — reserve
for residuals only).

**Depends on**: 2

**Files to modify** (under `Cslib/Logics/`):
- `Temporal/Metalogic/Chronicle/CounterexampleElimination/MainElimination.lean` (extract 4 arms)
- `Temporal/Metalogic/Chronicle/CounterexampleElimination/RecursiveWalks.lean` (residual `have` extraction)
- `Bimodal/Metalogic/Separation/DedekindZ/Cases.lean` (residual `have` extraction where a single term dominates)
- `Bimodal/Metalogic/Separation/Eliminations.lean`, `.../Hierarchy/HierarchyCaseSep.lean` (residual `have` extraction)

**Verification (CI gate for this phase)**:
- `lake build` — green
- `lake test` — green
- `lake exe checkInitImports` — passes
- `lake exe lint-style` — passes
- `eliminatePotentialCounterexample` no longer needs 6.4M; each extracted arm at its own reduced ceiling.

---

### Phase 4: Document irreducibles + final CI gate [COMPLETED]

**Goal**: Add one-line justification comments above every remaining high (>= 1.6M) scoped option and
run the full CI pipeline as the final acceptance gate.

**Tasks**:
- [x] For every surviving scoped option at >= 1.6M (Category B — genuinely high after bisection +
      extraction), add a one-line comment above the option explaining why it is irreducible.
      *(deviation: N/A -- zero options survived to Phase 4; nothing to document. Category B is
      empty.)*
- [x] Produce a short reduction summary (before/after value distribution and unscoped count) for the
      implementation summary artifact. *(summaries/01_reduce-maxheartbeats-inflation-summary.md)*
- [x] Add a follow-up note (in the summary, not code) flagging the 5 out-of-scope `maxHeartbeats`
      sites elsewhere under `Cslib/Logics/` for a possible future task. *(done in summary)*
- [x] Note in the summary that this task must not have run concurrently with task 414 on shared files.
      *(done in summary; confirmed task 414 status remained not_started throughout)*
- [x] Run the full CI pipeline as the final gate. *(lake build/test/checkInitImports/lint-style all
      green; lake lint clean on modified files; lake shake clean on modified files; mk_all
      no-op)*

**Timing**: ~1 hour.

**Depends on**: 3

**Files to modify** (comment-only, across the Metalogic trees where high scoped options survive):
- Various `Bimodal/Metalogic/**` and `Temporal/Metalogic/**` files with surviving >= 1.6M scoped options.

**Verification (CI gate for this phase — final acceptance)**:
- `lake build` — green
- `lake test` — green
- `lake exe checkInitImports` — passes
- `lake exe lint-style` — passes
- Every surviving >= 1.6M scoped option carries a one-line justification comment.

## Testing & Validation

- [ ] `lake build` green after every phase AND after every intra-phase per-file/per-site commit.
- [ ] `lake test` green after every phase.
- [ ] `lake exe checkInitImports` passes at each phase gate.
- [ ] `lake exe lint-style` passes at each phase gate.
- [ ] Zero-debt confirmed: `git diff` shows no `sorry`, no axioms, no changed theorem/def statements
      (Phase 3 extractions preserve statements; only structure changes).
- [ ] 0 unscoped `maxHeartbeats` sites remain in the two Metalogic trees after Phase 1.
- [ ] Value distribution measurably reduced vs. baseline (6.4M eliminated; 3.2M count sharply down).

## Artifacts & Outputs

- plans/01_reduce-maxheartbeats-inflation.md (this file)
- summaries/01_reduce-maxheartbeats-inflation-summary.md (on completion; includes before/after
  value distribution, per-phase reductions, and the out-of-scope 5-site follow-up note)
- Modified `.lean` files across `Cslib/Logics/Bimodal/Metalogic/**` and `Cslib/Logics/Temporal/Metalogic/**`
- Incremental green-gated commits (one per file/site batch) plus one commit per phase

## Rollback/Contingency

- Every change is a green-gated commit; to revert, `git revert` the offending commit(s) — the
  repository returns to a green state at any commit boundary.
- If a bisected value proves too tight on CI (red on a slower machine), raise that single option to
  the next multiple and commit; no other change is coupled.
- If a Phase 3 extraction breaks a downstream proof and cannot be quickly repaired, revert just that
  extraction commit and either leave the original high budget in place (documented in Phase 4) or
  defer that specific offender to a follow-up task. Phases 1–2 gains are unaffected.
- The 5 out-of-scope sites are never touched, so they carry no rollback risk.
