# Implementation Plan: Modal Tableau Refactor — Abstractions, Module Division, Boneyard, Documentation

- **Task**: 557 - modal_tableau_refactor_abstractions_boneyard
- **Status**: [IMPLEMENTING]
- **Effort**: 27 phases; ~60-80 hours across multiple dispatch cycles (expansion expected — see Risks, "Cut line")
- **Dependencies**: None. Task 553 (S4 keyed loop-guard soundness) is downstream by explicit user decision and is NOT touched by this plan.
- **Research Inputs**:
  - `specs/557_modal_tableau_refactor_abstractions_boneyard/reports/01_tableau-abstraction-boneyard-analysis.md` (1,107 lines, hard-mode, H4 Claim Verification Table at :987 with 49 verified rows)
  - Adversarial re-verification pass of that report (findings folded into "Corrected Figures" below)
- **Artifacts**: `plans/01_tableau-refactor-abstractions-boneyard.md`
- **Standards**:
  - `.claude/context/formats/plan-format.md`
  - `.claude/rules/artifact-formats.md`
  - `.claude/rules/plan-format-enforcement.md`
  - `.claude/rules/state-management.md`
  - `.claude/rules/cslib.md`, `.claude/rules/lean4.md`, `.claude/rules/plan-compliance.md`
  - `.claude/context/contracts/anti-analysis.md`, `wrap-up.md`, `territory.md`
  - `CONTRIBUTING.md`, `ORGANISATION.md`, `NOTATION.md`, `CODE_OF_CONDUCT.md`
- **Type**: cslib

---

## Overview

The modal Tableau subsystem (20,164 lines in three files, plus 17 sibling modules) carries a
factoring defect that four successive S4 loop-guard soundness routes died against. This plan does
**not** attempt that soundness obligation. It restructures the subsystem to library-publication
quality along the four scopes the task description sets: (A) adopt the two abstractions the
completed analysis licenses — Lemmon box-plus birth keys and a state-threading `RuleApplySt σ`
generalisation of `RuleApply`; (B) discharge the cross-file re-derivation debt and then split the
oversized files along real seams; (C) create and populate a `Boneyard/` quarantine; (D) correct
four verified-false or stale documentation claims and land a reproducible measured baseline.

Every change must be **behaviour-preserving on all landed theorems**. Definition of done: the
CSLib vetting pipeline passes against `CONTRIBUTING.md` / `NOTATION.md` / `ORGANISATION.md` /
`CODE_OF_CONDUCT.md` (never run on this subsystem before), with `modalTableauS4Keyed_complete` and
the six landed `Decidable` instances green, the Tableau sorry census still exactly 1, and no new
axioms.

### Research Integration

Report `01_tableau-abstraction-boneyard-analysis.md` is integrated in full. Its Recommendations
section (Tasks A-I) maps onto this plan's phases as follows: Task A → Phases 3-7; Task B → Phase
26; Task B2 → Phase 2; Task C (the review gate) → Phase 1; Task D → Phases 8-10; Task E → Phases
11-12; Task F → Phases 13-15; Task G → Phases 16-23; Task H → Phases 24-25; Task I → Phase 27.

### Corrected Figures (adversarial re-verification; these supersede report 01 where they differ)

The report was re-verified before this plan was written. Scope A is fully intact — every anchor
under the edge-vs-identification diagnosis (§3), the box-plus recommendation (§4), and the
`RuleApplySt` unification (§5) re-resolves exactly. Four figures were corrected, and **Phase 1
must record these corrections in the decision record**:

| Figure | Report 01 says | Corrected value | Consequence for this plan |
|---|---|---|---|
| Local re-derivation sites | 77 | **55** exact-phrase occurrences (`grep -rho 'Local re-derivation' Cslib/ \| wc -l`) | The headline count is smaller, but **every per-lemma spot-check was an UNDERCOUNT**: `modalSubfmls_trans` 4x not 3x, `modalKnownWorlds_fold_spec` 6x not 4x, `hasEdge_addEdge_cases` 7x not 4x. Report 01's per-file distribution **omits `LoopChecking.lean`'s 14 sites** entirely. The Scope B extraction work is therefore **larger**, not smaller, than stated. |
| `hasEdge_addEdge_cases` origin | `FmpMeasure.lean` (implied by §7 Seam 1) | **`Soundness.lean:75`** (with a separate `hasEdge_addEdge_cases_local` at `FmpMeasure.lean:1063`) | Phase 6 must extract from **two** source files, not one. |
| `ModalTableauResult` module span | 11 Tableau modules | **8** Tableau modules (9 repo-wide) | The task description's original figure of 8 was correct; report §2's "measured 11" row is drift. **Correct it back in the recorded baseline (Phase 2).** |
| `keysOriginS4` consumers | 22 | **not reproducible as 22**; measured 61 textual references, 55 on non-comment-leading lines | **Conclusion unchanged, with a large margin**: not zero-consumer, therefore not Boneyard-eligible, therefore `LoopChecking.lean:2001-2002`'s removal claim is FALSE and must be corrected (Phase 26). |
| `S4LoopInv` structure header | `:7072` | **`:7070`** | `outDegEq` field line `:7084` and all three provision sites (`LoopChecking.lean:7569`, `:7633`, `FrameCompleteness.lean:4217-4218` positional anonymous constructor) are **exact**. |

**Prerequisite confirmed still failing**: `lake exe checkInitImports` fails on a stale build
(missing `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.olean`), unrelated to the
Tableau subsystem. This is Phase 2, a real phase, not a footnote.

### Preserved Assets

No implementation phase of this task has run. The following are **landed, green, and must not
regress** — every one is a task-declared preserved asset or a measured baseline:

| Component | File / Location | Status | Verified |
|---|---|---|---|
| `modalTableauS4Keyed_complete` | `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:4267` | [COMPLETED] | 2026-07-26 |
| Six `Decidable` instances (K/T/B/S5/Five/KB5) | across Tableau modules | [COMPLETED] | 2026-07-26 |
| `modalS4Saturated` (7 consumers) | `LoopChecking.lean:6581` | [COMPLETED] | 2026-07-26 |
| The 8 `hintikkaS4_*` bridges | `LoopChecking.lean:6626,6712,6804,6887,6972,6984,7008,7024` | [COMPLETED] | 2026-07-26 |
| `hasEdge_accWithReds_iff`, `reflTransGen_accWithReds_first_red` | `LoopChecking.lean:8862`, `:8882` | [COMPLETED] | 2026-07-26 |
| `blockedRedirect_unwrapped_{boxPos,diaNeg}_mem` + `Reds`/`accWithReds` packaging | `LoopChecking.lean:8850-8990` | [COMPLETED] | 2026-07-26 |
| `keysOriginS4` (NOT Boneyard-eligible) | `LoopChecking.lean:1279` | [COMPLETED] | 2026-07-26 |
| `branchSatisfiableIn_s4FC_ancestor_redirect` (retained sorry, IMMOVABLE) | `FrameSoundness.lean:1220-1244` | [COMPLETED — carve-out] | 2026-07-26 |
| Regression corpus (197 lines) | `CslibTests/S4LoopGuardRegression.lean` | [COMPLETED] | 2026-07-26 |
| Six true-`rfl` driver bridges | `modalExpandBranchesB_eq`, `modalTableauB_eq`, `modalTableauS5_eq`, `modalTableauFive_eq`, `modalTableauKb5_eq`, `modalTableauKb5''_eq` | [COMPLETED] | 2026-07-26 |

### Source-to-Implementation Mapping (H3, Tier 1 — literature-backed)

| Source claim | Citation (BibKey + locator) | Implementation site | Phase |
|---|---|---|---|
| Lemmon filtration; `□⁺ψ = ψ ∧ □ψ` is the syntactic analogue of reflexivization | `ChagrovZakharyaschev1997`, `chunk_0173.md:11-14` (print p. 98) for `□⁺`; `chunk_0248.md:24-31` (print p. 142) for the Lemmon filtration (both unnumbered) | `boxPlusPair`, `BoxPlusClosed` | 11 |
| S4 admits filtration via the transitive closure of the finest filtration or the Lemmon filtration | `ChagrovZakharyaschev1997`, Corollary 5.32 | licence for the S4 scoping of box-plus | 1, 11 |
| Lemmon filtration is defined for **transitive** models only; Prop. 3.6 likewise (`chunk_0124.md:41`) | `ChagrovZakharyaschev1997`, `chunk_0248.md:24-25` | box-plus stays in `Cslib.Logic.Modal.Tableau`; **MUST NOT** be lifted into `Foundations/` | 1, 11 |
| `□⁺` is never iterated beyond depth 1; where more power is needed the **filter** is enlarged (Thms 5.34/5.35), which is expensive | `ChagrovZakharyaschev1997`, `p02:582-589`, `p02:602-604` | justification that box-plus is free in `modalWorldBoundS4` | 1, 11, 12 |
| Blocking records a **non-injective identification** `ı()`, not an edge | `Massacci2000`, Definition 10.2 | diagnosis only — **not implemented here** (soundness is out of scope) | 1 (recorded), 26 (documented) |
| Pruning deletes the descendant-closed subtree `Ftree(σ.n)` | `Massacci2000`, Lemma 8.2 | diagnosis only — not implemented | 1, 26 |
| Theorem 8.1 (blocking preserves satisfiability) is **stated and never proved**; deferred to Goré's model graphs | `Massacci2000`, `chunk_0054.md:3-7`, Appendix B.2 proves only Thm 8.4 | must be recorded in `FrameSoundness.lean`'s documentation | 26 |
| A constructed relation contained in the ambient one discharges (HSm1) immediately | `ChagrovZakharyaschev1997`, Thm 5.51, `chunk_0267.md:49-54` (**Grz via SELECTIVE filtration, not S4 via filtration**) | diagnosis only | 1, 26 |

---

## Postmortem Constraints

Binding rules for **every** implementation dispatch under this plan. Derived from four failed
soundness routes, the completed hard-mode analysis, and its adversarial re-verification.

**Do NOT**:

- **Do NOT attempt the S4 keyed loop-guard soundness obligation.** Not a lemma of it, not a
  weakening of it, not a "small preparatory step" toward it. The task description is emphatic.
  Four routes have died there. If a phase appears to require it, the phase is mis-scoped —
  report that, do not attempt it.
- **Do NOT add a `sorry` anywhere.** This is a behaviour-preserving refactor; there is no
  legitimate strategic-sorry division point in it (`anti-analysis.md`'s five-condition test
  cannot be met by a refactor phase). If a phase cannot be completed sorry-free, mark it
  `[BLOCKED]` and hand off. Explicitly: if box-plus enrichment (Phase 12) breaks
  `modalTableauS4Keyed_complete` and it cannot be repaired sorry-free, mark **BLOCKED**.
- **Do NOT split any file by line count.** The `S4/Hintikka.lean` and `S4/Redirect.lean` source
  ranges are **discontiguous** in the current `LoopChecking.lean` — that discontiguity is itself
  the evidence that a line-count split would be wrong.
- **Do NOT edit `Rules.lean`, `Saturation.lean`, or `Branch.lean` without a completed consumer
  audit.** A `Saturation.lean` change *is* proposed (`RuleApplySt`); Phase 8 is its audit and is a
  **mandatory gate**, not an inline step.
- **Do NOT edit `modalExpandBranchesGen`.** The six driver bridges are true `rfl` and will break
  if its definitional shape changes. All `RuleApplySt` work is additive first (Phases 9-10), then
  bridged, then migrated.
- **Do NOT move anything to `Boneyard/` on the strength of report §6's audit alone.** That audit
  is dated. Phase 25 re-runs it at execution time and moves only what the re-run confirms.
- **Do NOT move `FrameSoundness.lean:1220-1244`** (`branchSatisfiableIn_s4FC_ancestor_redirect`).
  It is zero-consumer, which would otherwise make it eligible; the retained sorry is an explicit
  user decision and the "proven and consumed" rule does not by itself protect it. **IMMOVABLE.**
- **Do NOT move `keysOriginS4`.** It is not zero-consumer (measured 55 non-comment references).
  `LoopChecking.lean:2001-2002`'s claim that it was removed is FALSE and gets corrected, not acted on.
- **Do NOT lift box-plus into `Foundations/`.** The Lemmon filtration and `ChagrovZakharyaschev1997`
  Prop. 3.6 are stated for **transitive** models only. It is S4-scoped.
- **Do NOT "fix" a drifted number by adjusting it.** Record the measured baseline with its exact
  reproduction command. The 26-vs-47 axiom discrepancy was a scope confusion, not a drift.
- **Do NOT reinstate the retired premises.** (a) There is no theorem numbered "interval theorem";
  cite `chunk_0246.md:43-65` by chunk and page as unnumbered prose and build no inference on it.
  (b) `Massacci2000` Theorem 8.1 is unproved in its source. (c) Theorem 5.51 is Grz via *selective*
  filtration, not S4 via filtration. (d) Box-plus is defined in Chapter 3 (`chunk_0173.md:11-14`),
  not in `chunk_0248`.
- **Do NOT produce analysis-only output.** Phases 1, 8, 16 and 25 have written artifacts as their
  deliverable; every other phase must produce file writes. A dispatch that ends with a description
  of what should be done, and no diff, has failed.

**MUST preserve** (see Preserved Assets table above for exact locations):

- `modalTableauS4Keyed_complete` and the six `Decidable` instances green at **every commit**.
- The Tableau sorry census at exactly **1** (`FrameSoundness.lean:1244`).
- The Tableau axiom-declaration census at exactly **0**.
- All task-declared route-independent assets (`modalS4Saturated`, the 8 bridges,
  `hasEdge_accWithReds_iff`, `reflTransGen_accWithReds_first_red`, the two
  `blockedRedirect_unwrapped_*_mem` transfers, the `Reds`/`accWithReds` packaging). These are
  **inputs to be placed correctly**, never Boneyard candidates.
- `CslibTests/S4LoopGuardRegression.lean` reproducing its recorded verdicts exactly.

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):

1. **The mis-factoring is edge-addition where the literature identifies worlds** (report §3), not
   the bridge set. The 8 bridges are a faithful transcription of `Massacci2000` Prop. 8.1 and duals
   plus two orthogonal witness conjuncts. Do not "collapse the adapters".
2. **Box-plus is adopted at the birth-key level and is free in the world bound.** `modalSubfmls
   (.box a) = .box a :: modalSubfmls a` (`FmpMeasure.lean:79`) keeps the enriched key inside
   `signedSubfmls φ₀`. `signedSubfmls_card_le`, `signedSubfmls_powerset_card_le`,
   `modalWorldBoundS4` and the pigeonhole argument are untouched. Do not re-derive this.
3. **Box-plus collapses AT MOST 2 of 8 bridges** (`hintikkaS4_box_pos_self`, `_dia_neg_self`) and
   **does not touch the reachability defect.** Scope the expectation down; do not plan around a
   larger payoff.
4. **The weakened bridge hypotheses were a minimisation** from `modalHintikkaSetS4` to
   `modalS4Saturated` — a factoring improvement that already happened, not a wrong abstraction.
5. **`RuleApplySt σ` with `RuleApply = RuleApplySt Unit` is added ADDITIVELY first**, then bridged,
   then migrated. Exactly one driver family of nine forks (S4 Keyed / KeyedOrdered).
6. **The de-duplication (Scope B extraction) goes FIRST**, before any abstraction change and before
   any split. It is behaviour-preserving by construction and shrinks the files before seams are cut.
7. **The abstraction analysis must be REVIEWED AND ACCEPTED (Phase 1) before any file is moved or
   split and before any abstraction is implemented.** This is a hard gate.

### Standing Verification Contract (V1-V7)

Every phase that touches `Cslib/**` or `CslibTests/**` is done only when **all** of V1-V7 hold.
Per-phase "Done when" clauses list phase-specific criteria **in addition to** V1-V7. V6 becomes
meaningful only after Phase 2.

| ID | Criterion | Command |
|---|---|---|
| V1 | Build green | `lake build` (full; scoped `lake build Cslib.Logics.Modal.Tableau.<Module>` permitted mid-phase, full build required before the phase's final commit) |
| V2 | `modalTableauS4Keyed_complete` sorry-free | `#print axioms Cslib.Logic.Modal.Tableau.modalTableauS4Keyed_complete` shows no `sorryAx` |
| V3 | Six `Decidable` instances (K/T/B/S5/Five/KB5) green | covered by V1; confirm none was deleted or stubbed |
| V4 | Tableau sorry census == 1, at `FrameSoundness.lean:1244` | block-comment-aware scan of `Cslib/Logics/Modal/Tableau/`; the 11 other textual `sorry` hits are prose |
| V5 | Tableau axiom declarations == 0 | `grep -rnE '^(private \|protected )*axiom ' Cslib/Logics/Modal/Tableau/*.lean` → no output |
| V6 | Import hygiene | `lake exe checkInitImports` |
| V7 | Regression corpus reproduces recorded verdicts | `lake test`; `CslibTests/S4LoopGuardRegression.lean` unchanged at 197 lines unless the phase explicitly owns it |

---

## Goals & Non-Goals

**Goals**

- Produce an explicit, durable decision record accepting or rejecting each of report 01's
  recommendations, before any code moves (Scope A gate).
- Clear the stale build so `checkInitImports` is a meaningful acceptance gate.
- Eliminate the cross-file re-derivation debt by extracting the re-derived facts as **public**
  declarations into `Cslib/Logics/Modal/Tableau/Support/{Subfmls,KnownWorlds,Accessibility}.lean`.
- Adopt Lemmon box-plus birth keys and the `RuleApplySt σ` generalisation, additively then
  bridged then migrated, with `modalTableauS4Keyed_complete` green at every commit.
- Split `LoopChecking.lean` along the six real seams identified in report §7, and update
  `ORGANISATION.md` (which currently describes `Modal/Tableau/` in one undifferentiated line).
- Create `Boneyard/` with a documented quarantine convention and move only re-verified
  zero-consumer declarations into it.
- Correct the four adjudicated documentation defects, leave the seven TRUE verdicts alone, and land
  the measured baseline table with its reproduction commands.
- Pass the CSLib vetting pipeline as an acceptance gate.

**Non-Goals**

- The S4 keyed loop-guard soundness obligation. Out of scope, forbidden, not attempted.
- Disposition of the retained `sorry` at `FrameSoundness.lean:1244`. Not this task's decision.
- Any change to the K/T/B/S5/Five/Kb5/Kb5'' drivers' semantics.
- Generalising box-plus beyond S4 or into `Foundations/`.
- Enlarging the filter `Σ` beyond `signedSubfmls φ₀` (would change `modalWorldBoundS4`; expensive).
- Re-measuring the amplification figures (4 decls / 1,036 lines; 43 / 1,983). They need an
  elaborated-environment dependency query, not a text scan. Report 01 correctly declined to
  fabricate a substitute; this plan does likewise.

---

## Risks & Mitigations

- **Phase count exceeds one orchestration run — and the expansion has ALREADY happened.** This plan
  has **27 phases**, which exceeds both the hard-mode complexity ceiling and what ~13 orchestrator
  cycles can deliver. This is stated openly rather than compressed away, because compressing it
  would produce exactly the unbounded phases H8 forbids. **Critically: tasks 558-567 already exist
  and already implement this programme's decomposition** — see "Relationship to the Spawned
  Programme Tasks" below, which must be read before any dispatch against this plan. **The natural
  cut line is after Phase 15** (Scope A complete: de-duplication landed, `RuleApplySt` migrated,
  box-plus adopted, `outDegEq` removed) — at that point the subsystem is smaller, the abstractions
  are settled, and the split seams are stable. Do not cut mid-Scope-A (Phases 8-15 are a single
  migration sequence and leaving it half-migrated is worse than not starting it). **If Phase 26 is
  deferred, pull it forward** to run immediately after Phase 15, so the documentation corrections
  travel with the content when the split phases later relocate it.

### Relationship to the Spawned Programme Tasks 558-567

Ten follow-up tasks already exist in `specs/state.json`, spawned from report 01's Recommendations
section with its dependency DAG intact. **This plan and those tasks describe the same work.**
Dispatching both would duplicate every phase. The mapping is exact:

| This plan's phases | Spawned task | Report 01 | Task dependencies |
|---|---|---|---|
| 3-7 (Support de-duplication) | 558 `tableau_support_private_dedup` | Task A | none |
| 26 (documentation + baseline) | 559 `tableau_measured_baseline_doc_corrections` | Task B | none |
| 2 (literature index half) | 560 `repair_literature_subindex_massacci_chunks` | Task B2 | none |
| **1 (decision record — the review gate)** | 561 `tableau_abstraction_decision_record` | Task C | none |
| 8-10 (`RuleApplySt` audit + additive + bridge) | 562 `tableau_ruleapplyst_additive_introduction` | Task D | 561 |
| 11-12 (box-plus birth keys) | 563 `tableau_boxplus_birth_keys` | Task E | 561 |
| 13-15 (St migration, duplication retirement, `outDegEq`) | 564 `tableau_s4keyed_migration_st_ladder` | Task F | 562, 563 |
| 16-23 (seam re-cut + splits + `ORGANISATION.md`) | 565 `loopchecking_split_s4_modules` | Task G | 561, 563, 564 |
| 24-25 (`Boneyard/` + audited moves) | 566 `boneyard_creation_eligible_moves` | Task H | 564 |
| 27 (vetting acceptance gate) | 567 `tableau_vetting_pipeline_acceptance_gate` | Task I | 558, 559, 561-566 |

**Only Phase 2's stale-build clearance is unowned by any spawned task** — tasks 558-567 all
presuppose a green build and none of them owns clearing it. `lake exe checkInitImports` currently
fails on a missing `Constructive/Nested/Soundness.olean`, so **every** task in the programme that
verifies against that gate is verifying against nothing until it is cleared.

**Recommended disposition** (a user/orchestrator decision, not one this plan makes unilaterally):
execute **Phase 2 only** under task 557, then run the programme through tasks 558-567 in their
declared dependency order, using this plan's phase bodies as the per-task implementation detail
those task descriptions compress. In that reading, this document's value is the H8 phase sizing,
the per-phase territory contracts, the Standing Verification Contract V1-V7, the Postmortem
Constraints, and the Corrected Figures table — none of which the spawned task descriptions carry,
and all of which bind whichever task executes the work.

**If instead 557 executes the full plan itself**, tasks 558-567 must be marked `[ABANDONED]` with
a pointer to this plan first, or the same work will be done twice. **Do not dispatch both.**
- **Box-plus changes which steps block, breaking `modalTableauS4Keyed_complete`.** Likelihood:
  medium. This is the one real risk in Scope A. Mitigation: Phase 12 gates on
  `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness`. Completeness is proved from
  `modalExpandBranchesS4Keyed_hintikka`, which is quantified over the driver's actual behaviour, so
  it *should* transport — but this must be demonstrated, not assumed. **If it cannot be repaired
  sorry-free, mark Phase 12 `[BLOCKED]`. Do not add a sorry.**
- **Editing `Saturation.lean` breaks the six true-`rfl` driver bridges.** Likelihood: high if done
  wrong, near-zero if the ordering is respected. Mitigation: Phases 9-10 are purely additive —
  `modalExpandBranchesGen` is never edited, so no `rfl` can break. Phase 8's consumer audit is a
  mandatory gate before any `Saturation.lean` edit.
- **Deleting `S4LoopInv.outDegEq` cascades into the other invariant proofs that destructure the
  structure, including a POSITIONAL anonymous-constructor site inside the landed completeness
  capstone** (`FrameCompleteness.lean:4217-4218`). Likelihood: medium. Mitigation: Phase 15 owns
  the field removal and nothing else; `lake build` before and after. If the cascade is large, **keep
  the field and Boneyard nothing** — 386 lines are not worth a regression.
- **The consumer audit goes stale between Phase 1 and Phase 25.** Likelihood: high (multi-cycle
  programme). Mitigation: Phase 25 must re-run the audit script at execution time; the method is
  recorded in report §6 and is reproducible.
- **Extraction phases collide territorially.** Every Scope B extraction phase edits
  `LoopChecking.lean` plus two or more driver files. Likelihood of conflict if parallelised: high.
  Mitigation: Phases 3-7 are strictly sequential; the wave table declares only the two genuine
  parallel opportunities (1 ‖ 2, and 3 ‖ 8).
- **The re-derivation site count is larger than report 01 states.** Every per-lemma spot-check was
  an undercount and `LoopChecking.lean`'s 14 sites were omitted from the distribution. Mitigation:
  each extraction phase re-measures its own family with the exact command before starting, and
  reports the measured count in its commit message.
- **A split seam moves because of an abstraction decision.** Report §7 Seam 3: if box-plus is
  adopted, `S4/BirthKey.lean` becomes the module the whole keyed track depends on and
  `S4/Redirect.lean` may collapse. Mitigation: Phase 16 re-cuts the seams after Scope A lands and
  produces a module manifest; Phases 17-23 execute that manifest, not report §7's provisional table.
- **A future reader treats the retained sorry as Boneyard-eligible because it is zero-consumer.**
  Mitigation: the carve-out is stated in Postmortem Constraints, in Phase 24's README requirements,
  and in Phase 25's checklist.

---

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3, 8 | 1, 2 |
| 3 | 4 | 3 |
| 4 | 5 | 4 |
| 5 | 6 | 5 |
| 6 | 7 | 6 |
| 7 | 9 | 7, 8 |
| 8 | 10 | 9 |
| 9 | 11 | 10 |
| 10 | 12 | 11 |
| 11 | 13 | 12 |
| 12 | 14 | 13 |
| 13 | 15 | 14 |
| 14 | 16 | 15 |
| 15 | 17 | 16 |
| 16 | 18 | 17 |
| 17 | 19 | 18 |
| 18 | 20 | 19 |
| 19 | 21 | 20 |
| 20 | 22 | 21 |
| 21 | 23 | 22 |
| 22 | 24 | 23 |
| 23 | 25 | 24 |
| 24 | 26 | 25 |
| 25 | 27 | 26 |

Phases within the same wave can execute in parallel. **Only two genuine parallel opportunities
exist**, and both are declared above: Phase 1 ‖ Phase 2 (Phase 1 writes only under `specs/`;
Phase 2 touches only the build cache and `specs/literature-index.json`), and Phase 3 ‖ Phase 8
(Phase 8 is a read-only audit whose deliverable is a `specs/` artifact). **Everything else is
sequential by territory**: Phases 3-7 all edit `LoopChecking.lean` plus overlapping driver files;
Phases 9-15 form one migration sequence over `Saturation.lean` and `LoopChecking.lean`; Phases
17-23 all carve from `LoopChecking.lean`. Do not parallelise them.

**Territory contract (H7)**: each phase below names the files it owns. A dispatch may write only
files it owns. Phase 26 owns comment blocks in `LoopChecking.lean` and `FrameSoundness.lean` and
must therefore **never** run concurrently with any phase owning those files.

---

### Phase 1: Abstraction Decision Record [IN PROGRESS]

**Goal**: Produce the explicit decision record the task description requires before any file is
moved or split and before any abstraction is implemented. This is the review gate.

**Owner / territory**: `specs/557_modal_tableau_refactor_abstractions_boneyard/decisions/` only.
**No `.lean` file may be created, moved, or edited in this phase.**

**Tasks**:
- [ ] Create `specs/557_modal_tableau_refactor_abstractions_boneyard/decisions/01_abstraction-decision-record.md`.
- [ ] Record an explicit ACCEPT / REJECT / DEFER verdict, with a one-paragraph rationale each, for:
  - Report §3's diagnosis (edge-addition vs world-identification) as the *recorded* primary finding
    — note that it is diagnostic only and that nothing in this task implements a repair for it.
  - Report §4: box-plus birth keys (`boxPlusPair`, `BoxPlusClosed`, enriched
    `successorBirthContent`), **with the scoped-down expectation stated in the record**: at most 2
    of 8 bridges collapse, and the reachability defect is untouched.
  - Report §5: the `RuleApplySt σ` generalisation with `RuleApply = RuleApplySt Unit`, additive
    first, and its six-step migration order.
  - Report §6: the Boneyard eligibility list, **with both mandatory carve-outs restated verbatim**
    (`FrameSoundness.lean:1220-1244` IMMOVABLE; `keysOriginS4` NOT eligible).
  - Report §7: the Seam-2 module table as *provisional*, explicitly subject to re-cutting in
    Phase 16 per Seam 3.
  - Report §8: the four documentation defects to correct and the seven TRUE verdicts to leave alone.
- [ ] Record the **Corrected Figures** table from this plan's Overview verbatim, including that
  `ModalTableauResult` spans **8** Tableau modules (report §2's "measured 11" row is drift; the
  task description's original 8 was right).
- [ ] Record the **retired premises** (a)-(d) as binding, so no future dispatch reinstates them.
- [ ] Record the S4-scoping constraint on box-plus (transitivity precondition,
  `ChagrovZakharyaschev1997` `chunk_0248.md:24-25` and `chunk_0124.md:41`) and the prohibition on
  lifting it into `Foundations/`.
- [ ] State the sequencing decision: de-duplication (Phases 3-7) precedes every abstraction change.

**Estimated output**: ~250-300 lines (one markdown artifact).

**Done when**: the decision record exists, every bullet above has an explicit verdict with a
rationale, and no `.lean` file in the repository has been modified (`git status` shows changes only
under `specs/`).

**Timing**: 1 dispatch, ~2 hours.
**Depends on**: none.

---

### Phase 2: Stale-Build Clearance, Baseline Capture, and Literature Index Repair [BLOCKED]

**Blocker (recorded 2026-07-26)**: `lake build` fails on a **genuine compile error outside the
Tableau subsystem** — `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean:1329:2`,
`Missing cases: _, (NestedProof.cut (InputCtx.mk _ _ _) _ _ _)`. The missing
`Nested/Soundness.olean` is a *consequence* of this error, not a stale artifact, so
`lake exe checkInitImports` cannot be cleared by rebuilding and **V6 is not established**. The
failing file is committed work belonging to an in-flight constructive nested-sequent task
(commit `88b198bf`), outside this task's territory; per this phase's own carve-out it was recorded
rather than repaired. Baseline capture (V4) and the sorry census (V5) **did** complete — see
`artifacts/baseline.md`. The literature-index task could not be completed as written: the defect
is not in `specs/literature-index.json` (which is reference-only and validates clean, 34/34
entries resolving) but in the global `~/Projects/Literature/index.json`, which lacks `parent_doc`
child entries for 19 of 34 documents; root cause and exact repair are recorded in
`artifacts/baseline.md` §12.

**Goal**: Make `lake exe checkInitImports` a meaningful acceptance gate, and capture the measured
baseline every later phase verifies against.

**Owner / territory**: `.lake/` build products; `specs/literature-index.json`;
`specs/557_modal_tableau_refactor_abstractions_boneyard/artifacts/baseline.md`. **No `Cslib/` file
is edited in this phase.**

**Tasks**:
- [ ] `lake exe cache get` (once; prevents a 30-45 minute Mathlib rebuild).
- [ ] `lake build` to green. The known failure is a missing
  `.lake/build/lib/lean/Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.olean` —
  unrelated to the Tableau subsystem. If the build surfaces genuine errors outside Tableau, record
  them and mark `[BLOCKED]`; do not repair unrelated subsystems under this task.
- [ ] `lake exe checkInitImports` → must be clean. This establishes V6.
- [ ] Capture the baseline into `artifacts/baseline.md`, each row with its exact reproduction
  command: three-file line counts (`LoopChecking.lean` 10,540 / `FrameSoundness.lean` 5,317 /
  `FrameCompleteness.lean` 4,307, total 20,164); `LoopChecking.lean` 230 declarations; Tableau
  sorry census **1** at `FrameSoundness.lean:1244`; repo-wide `Cslib/` sorry census 10; Tableau
  axiom declarations **0** (3 raw word matches) vs repo-wide 26 declarations / 1,701 raw matches —
  **recorded as a scope distinction, not a corrected number**; tag census 0/0/0/0 in the three files
  and 11 TODO / 8 NOTE repo-wide; `hintikkaS4_*` bridge count **8**; re-derivation site count **55**
  with the per-file distribution **including `LoopChecking.lean`'s 14**; `ModalTableauResult` span
  **8 Tableau modules (9 repo-wide)**; `S4LoopInv` header `:7070`, `outDegEq` field `:7084`,
  provision sites `LoopChecking.lean:7569`, `:7633`, `FrameCompleteness.lean:4217-4218`;
  `CslibTests/S4LoopGuardRegression.lean` 197 lines; `Boneyard/` absent.
- [ ] Note explicitly in the baseline artifact that the amplification figures were **not**
  re-measured and that no substitute number was fabricated.
- [ ] Run `/literature --validate` to repair `specs/literature-index.json`, which reports the
  `massacci_2000_single_step_tableaux_for_modal_logics` corpus as **1 chunk** where it holds **77**
  plus a full-text file. Record the before/after chunk count.

**Estimated output**: ~150 lines (one markdown artifact) plus the index repair diff.

**Done when**: `lake build` green, `lake exe checkInitImports` clean, `artifacts/baseline.md`
exists with a command per row, and `specs/literature-index.json` reports the Massacci corpus at its
true chunk count. V4, V5, V6 recorded as passing.

**Timing**: 1 dispatch, ~2 hours (mostly build wall-clock).
**Depends on**: none.

---

### Phase 3: `Tableau/Support/Subfmls.lean` — Extract and De-Duplicate [NOT STARTED]

**Goal**: Create the first public support module and delete the subformula-family re-derivations.

**Owner / territory**: new `Cslib/Logics/Modal/Tableau/Support/Subfmls.lean`; `FmpMeasure.lean`
(visibility changes only); `S5Simplification.lean`, `FiveSimplification.lean`, `BDriver.lean`,
`LoopChecking.lean` (deletion of the named re-derivations + import lines); `Cslib.lean` (barrel).

**Tasks**:
- [ ] Re-measure the family first: `grep -rn 'Local re-derivation' Cslib/ | grep -iE 'Subfmls|Universe|boxPositives'` and record the count in the commit message.
- [ ] Create `Cslib/Logics/Modal/Tableau/Support/Subfmls.lean` importing `Cslib.Init`, exporting as
  **public** declarations, in namespace `Cslib.Logic.Modal.Tableau`: `modalSubfmls_trans`,
  `modalSubfmls_self_mem`, `modalUniverse_mem_formula`, `mem_modalUniverse_of`, `mem_boxPositivesOf`.
  Statements are taken verbatim from `FmpMeasure.lean` (`modalSubfmls_trans` at `:393`); the
  re-derivations are stated identically, so this is behaviour-preserving by construction.
- [ ] De-privatise the corresponding declarations in `FmpMeasure.lean`, or re-export from the new
  module and delete the private originals — whichever keeps `lake shake` clean.
- [ ] Delete the re-derivations and re-point their consumers: `BDriver.lean:211`
  (`modalSubfmls_trans_B`), `S5Simplification.lean:95-97` (`_S5`) and `:862`
  (`modalSubfmls_self_mem`) and the `:87` header comment, `FiveSimplification.lean:736-738` (`_Five`),
  `LoopChecking.lean:1576` (`_S4`).
- [ ] `lake exe mk_all --module` (new file added) and
  `lake shake --add-public --keep-implied --keep-prefix`.

**Estimated output**: ~150 lines added (new module), ~200 lines deleted.

**Done when**: V1-V7 hold; `grep -rn 'Local re-derivation' Cslib/` no longer reports any
subformula-family site; the new module is in the barrel; `lake shake` reports no unused import.

**Timing**: 1 dispatch, ~3 hours.
**Depends on**: 1, 2.

---

### Phase 4: `Tableau/Support/KnownWorlds.lean` — Module plus `fold_spec` / `mem_modalKnownWorlds` Sites [NOT STARTED]

**Goal**: Create the known-worlds support module and clear its two largest re-derivation families
(12 sites measured).

**Owner / territory**: new `Cslib/Logics/Modal/Tableau/Support/KnownWorlds.lean`; `FmpMeasure.lean`
(visibility only, `modalKnownWorlds_fold_spec` at `:1710`); `BDriver.lean`, `S5Simplification.lean`,
`FiveSimplification.lean`, `FrameSoundness.lean`, `FrameCompleteness.lean`, `LoopChecking.lean`
(deletions + imports); `Cslib.lean`.

**Tasks**:
- [ ] Re-measure: `grep -rn 'modalKnownWorlds_fold_spec\|mem_modalKnownWorlds' Cslib/`. Report the count.
- [ ] Create the module with **public** `modalKnownWorlds_fold_spec` and `mem_modalKnownWorlds`.
- [ ] Delete the six `modalKnownWorlds_fold_spec` re-derivations: `FiveSimplification.lean:775-777`,
  `BDriver.lean:914-918`, `S5Simplification.lean:990-993` and `:1051`, `FrameSoundness.lean:2029-2032`,
  `FrameCompleteness.lean:3745`, `LoopChecking.lean:2754-2757`. Re-point consumers.
- [ ] Delete the six `mem_modalKnownWorlds` re-derivations and re-point consumers.
- [ ] `lake exe mk_all --module`; `lake shake --add-public --keep-implied --keep-prefix`.

**Estimated output**: ~120 lines added, ~250 lines deleted.

**Done when**: V1-V7 hold; no `fold_spec` or `mem_modalKnownWorlds` re-derivation site remains;
barrel and shake clean.

**Timing**: 1 dispatch, ~3 hours.
**Depends on**: 3.

---

### Phase 5: `Tableau/Support/KnownWorlds.lean` — `mono_append` / `nodup` / `le_modalMaxWorld` Sites [NOT STARTED]

**Goal**: Complete the known-worlds module by clearing its remaining three families (7 sites).

**Owner / territory**: `Cslib/Logics/Modal/Tableau/Support/KnownWorlds.lean` (extend);
`FmpMeasure.lean` (visibility only); the same six consumer files as Phase 4.

**Tasks**:
- [ ] Re-measure: `grep -rn 'modalKnownWorlds_mono_append\|modalKnownWorlds_nodup\|modalKnownWorlds_le_modalMaxWorld' Cslib/`.
- [ ] Add **public** `modalKnownWorlds_mono_append`, `modalKnownWorlds_nodup`,
  `modalKnownWorlds_le_modalMaxWorld` to the module.
- [ ] Delete the five `mono_append` re-derivations, the `nodup` re-derivation (including
  `LoopChecking.lean:6437`), and the `le_modalMaxWorld` re-derivation. Re-point consumers.
- [ ] `lake shake --add-public --keep-implied --keep-prefix`.

**Estimated output**: ~80 lines added, ~180 lines deleted.

**Done when**: V1-V7 hold; `grep -rn 'Local re-derivation' Cslib/` reports zero known-worlds-family
sites.

**Timing**: 1 dispatch, ~2 hours.
**Depends on**: 4.

---

### Phase 6: `Tableau/Support/Accessibility.lean` — Extract from TWO Source Files [NOT STARTED]

**Goal**: Create the accessibility support module and clear its re-derivation family (~11 sites).

**Owner / territory**: new `Cslib/Logics/Modal/Tableau/Support/Accessibility.lean`;
**`Soundness.lean`** (visibility only — `hasEdge_addEdge_cases` originates at `:75`, **not** in
`FmpMeasure.lean`) and `FmpMeasure.lean` (the separate `hasEdge_addEdge_cases_local` at `:1063`);
`BDriver.lean`, `FrameCompleteness.lean`, `FrameSoundness.lean`, `LoopChecking.lean`; `Cslib.lean`.

**Tasks**:
- [ ] Re-measure: `grep -rn 'hasEdge_addEdge_cases\|mem_successorsOf_hasEdge\|accFreshInv_append\|mintGroup_label_eq_freshWorld' Cslib/`. **Expect 7 `hasEdge_addEdge_cases` sites, not 4.**
- [ ] Confirm by reading `Soundness.lean:75` and `FmpMeasure.lean:1063` whether the two originals
  are the same statement. If they differ, extract **both** under distinct names and record the
  difference in the module docstring — do not silently unify them.
- [ ] Create the module with **public** `hasEdge_addEdge_cases`, `mem_successorsOf_hasEdge`,
  `accFreshInv_append`, `mintGroup_label_eq_freshWorld`.
- [ ] Delete the re-derivations: `BDriver.lean:904-906`, `FrameCompleteness.lean:2917-2919` and
  `:3839-3842`, `FrameSoundness.lean:1196-1199` and `:2106-2109`, `LoopChecking.lean:5321-5323` and
  `:1230`. Re-point consumers.
- [ ] **Do not touch `FrameSoundness.lean:1176`** — that "Local re-derivation" mention sits inside
  the retained-sorry attempt-and-verdict prose block, not a re-derivation. Leave it for Phase 26.
- [ ] `lake exe mk_all --module`; `lake shake --add-public --keep-implied --keep-prefix`.

**Estimated output**: ~130 lines added, ~230 lines deleted.

**Done when**: V1-V7 hold; no accessibility-family re-derivation remains; the two-origin question is
resolved in writing in the module docstring.

**Timing**: 1 dispatch, ~3 hours.
**Depends on**: 5.

---

### Phase 7: Residue Re-Derivation Adjudication (Measure and Driver-Shape Sites) [NOT STARTED]

**Goal**: Dispose of every re-derivation site that does not belong to the three named Support
modules, so `grep -rn 'Local re-derivation' Cslib/` reaches a justified fixed point.

**Owner / territory**: optional new `Cslib/Logics/Modal/Tableau/Support/Measure.lean`;
`FmpMeasure.lean`, `CompletenessLoop.lean`, `TDriver.lean`, `S5Simplification.lean` (visibility
only); `BDriver.lean`, `FiveSimplification.lean`, `LoopChecking.lean`; `Cslib.lean`.

**Tasks**:
- [ ] Enumerate the residue: `grep -rn 'Local re-derivation' Cslib/`. Measured residue sites:
  `LoopChecking.lean:9622` / `:9641` / `:9654` (`modalExpMeasure_split` / `_append` / `_const_exp`
  from `FmpMeasure.lean`), `LoopChecking.lean:9944` (`modalStepBranchGen_newExps_const` from
  `CompletenessLoop.lean`), `LoopChecking.lean:9974` (saturated-leaf characterisation),
  `BDriver.lean:101` (`modalApplyOneT_boxPos_fst` from `TDriver.lean`), `BDriver.lean:1036` (from
  `CompletenessLoop.lean`), `S5Simplification.lean:1172` (`modalApplyOneS5_fresh_local` from
  `FrameSoundness.lean`), `FiveSimplification.lean:611` / `:3303` / `:3318` (from
  `S5Simplification.lean`), `FiveSimplification.lean:2087` (retired frozen rule).
- [ ] For the `modalExpMeasure_*` family, create `Support/Measure.lean` with public declarations and
  delete the three `LoopChecking.lean` re-derivations.
- [ ] For each remaining site, either extract-and-delete, or **leave in place with a written
  justification appended to its docstring** (e.g. the statement genuinely differs, or extraction
  would create an import cycle). A site left in place must say *why* in one sentence.
  `FiveSimplification.lean:2087` refers to a retired rule and is a deletion candidate — verify
  zero consumers before deleting.
- [ ] Record the final justified count in `artifacts/baseline.md`.

**Estimated output**: ~90 lines added, ~150 lines deleted, plus docstring justifications.

**Done when**: V1-V7 hold; every remaining `Local re-derivation` occurrence carries a one-sentence
justification; the final count is recorded in the baseline artifact.

**Timing**: 1 dispatch, ~3 hours.
**Depends on**: 6.

---

### Phase 8: `Saturation.lean` Consumer Audit (Mandatory Gate) [NOT STARTED]

**Goal**: Discharge the task's mandatory constraint that `Saturation.lean` may not be edited without
a prior explicit consumer audit. This is a **gate deliverable in its own right**, not an inline step.

**Owner / territory**: `specs/557_modal_tableau_refactor_abstractions_boneyard/artifacts/saturation-consumer-audit.md`
only. **Read-only over `Cslib/`. No `.lean` file is edited.**

**Tasks**:
- [ ] Enumerate every consumer of each of: `RuleApply` (`Saturation.lean:107-111`),
  `modalStepBranchGen`, `modalExpandBranchesGen`, `modalTableauGen`, `ModalTableauResult`
  (`Saturation.lean:82-87`), `modalHintikkaSetGen`. Report file, line, and whether the use is a
  definitional instantiation, a `rfl` bridge, a proved bridge, or a mention.
- [ ] Record which bridges are **true `rfl`** and will therefore break if `modalExpandBranchesGen`'s
  definitional shape changes. Report 01 names six: `modalExpandBranchesB_eq`, `modalTableauB_eq`,
  `modalTableauS5_eq`, `modalTableauFive_eq`, `modalTableauKb5_eq`, `modalTableauKb5''_eq`.
  **Verify each independently** — do not carry the figure forward unchecked.
- [ ] Confirm the `ModalTableauResult` module span. The task description says 8 Tableau modules;
  report §2 says 11; the adversarial pass measured **8 (9 repo-wide)**. Settle it with
  `grep -rl ModalTableauResult Cslib/` and record the result — this correction feeds the baseline.
- [ ] Confirm which drivers already route through the generic ladder (report §5 lists eight of nine)
  and that exactly the S4 Keyed / KeyedOrdered pair forks.
- [ ] State an explicit GO / NO-GO verdict on the additive `RuleApplySt` introduction.

**Estimated output**: ~200 lines (one markdown artifact).

**Done when**: the audit artifact exists with a per-consumer table, the six `rfl` bridges are
individually verified, the `ModalTableauResult` span is settled with its command, and a GO/NO-GO
verdict is recorded. `git status` shows changes only under `specs/`.

**Timing**: 1 dispatch, ~2.5 hours.
**Depends on**: 1, 2. **May run in parallel with Phase 3.**

---

### Phase 9: `RuleApplySt σ` and the `St` Ladder — Additive Introduction Only [NOT STARTED]

**Goal**: Add the state-threading shape as **new declarations**, editing nothing existing, so the
six true-`rfl` bridges are green by construction.

**Owner / territory**: `Cslib/Logics/Modal/Tableau/Saturation.lean` (**additions only**).

**Tasks**:
- [ ] Restate the Phase 8 GO verdict at the top of the dispatch. If it was NO-GO, stop and report.
- [ ] Add `RuleApplySt (Atom) [DecidableEq Atom] [Hashable Atom] (σ : Type*)` per report §5:
  `SignedFormula (Proposition Atom) WorldIndex → List (SignedFormula (Proposition Atom) WorldIndex)
  → Accessibility → σ → RuleResult (Proposition Atom) WorldIndex × Accessibility × σ`.
- [ ] Add `liftRuleApply : RuleApply Atom → RuleApplySt Atom Unit`.
- [ ] Add `modalStepBranchGenSt`, `modalExpandBranchesGenSt`, `modalTableauGenSt`, each threading `σ`.
- [ ] **Edit nothing existing.** `modalExpandBranchesGen` must be byte-identical after this phase.
  Verify with `git diff` that no existing declaration body changed.

**Estimated output**: ~180 lines added, 0 deleted.

**Done when**: V1-V7 hold; `git diff Cslib/Logics/Modal/Tableau/Saturation.lean` shows additions
only (no deletions, no modifications to existing declaration bodies); all six `rfl` bridges still
elaborate.

**Timing**: 1 dispatch, ~3 hours.
**Depends on**: 7, 8.

---

### Phase 10: `modalExpandBranchesGen_eq_St` Bridge [NOT STARTED]

**Goal**: Prove the projection equation connecting the existing ladder to the `St` ladder at
`σ := Unit`.

**Owner / territory**: `Cslib/Logics/Modal/Tableau/Saturation.lean` (additions only).

**Tasks**:
- [ ] Prove `modalExpandBranchesGen apply … = modalExpandBranchesGenSt (liftRuleApply apply) … ()`
  by induction on fuel, mirroring the existing `modalExpandBranches_eq` (`Saturation.lean:312-356`),
  which is already exactly this proof at a different pair.
- [ ] Prove the corresponding `modalStepBranchGen_eq_St` and `modalTableauGen_eq_St` if the
  induction requires them.
- [ ] Sorry-free. If the induction stalls, use `lean_goal` + `lean_multi_attempt` and report the
  exact residual goal; **do not** stub it.

**Estimated output**: ~120 lines added.

**Done when**: V1-V7 hold; `#print axioms` on the new bridge shows no `sorryAx`; the six existing
`rfl` bridges still elaborate.

**Timing**: 1 dispatch, ~3 hours.
**Depends on**: 9.

---

### Phase 11: `boxPlusPair` and `BoxPlusClosed` — Additive Introduction and Codomain Closure [NOT STARTED]

**Goal**: Add the Lemmon box-plus abstraction as new declarations plus the one lemma that makes the
world bound provably free, **without yet changing `successorBirthContent`**.

**Owner / territory**: `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (additions only, in the
`:295-443` birth-key cluster).

**Tasks**:
- [ ] In namespace `Cslib.Logic.Modal.Tableau`, add:
  `boxPlusPair (φ₀ : Proposition Atom) (s : Sign) (ψ : Proposition Atom) : Finset (Sign × Proposition Atom)`
  — Lemmon's `□⁺ψ = ψ ∧ □ψ` at the signed-pair level, i.e. `{(pos, ψ), (pos, .box ψ)}`, dually
  `{(neg, ψ), (neg, .diamond ψ)}`. Docstring cites `ChagrovZakharyaschev1997` `chunk_0173.md:11-14`
  (print p. 98) for `□⁺` and `chunk_0248.md:24-31` (print p. 142) for the Lemmon filtration, both
  **unnumbered**, plus Corollary 5.32 for the S4 licence.
- [ ] Add `BoxPlusClosed (φ₀) (k : Finset (Sign × Proposition Atom)) : Prop`.
- [ ] Prove the codomain closure lemma: if `T(□ψ)@w ∈ b` and `b ⊆ modalUniverseS4 φ₀` (guaranteed by
  `S4LoopInv.bClosure`), then `(pos, .box ψ) ∈ signedSubfmls φ₀`. This follows from
  `modalSubfmls (.box a) = .box a :: modalSubfmls a` (`FmpMeasure.lean:79`). **This lemma is what
  makes box-plus free in the world bound; prove it before enriching anything.**
- [ ] Add a docstring note recording that box-plus is **S4-scoped** (transitivity is a precondition
  of the Lemmon filtration and of Prop. 3.6) and **must not** be lifted into `Foundations/`.
- [ ] **Change nothing existing.** `successorBirthContent` is untouched in this phase.

**Estimated output**: ~140 lines added, 0 deleted.

**Done when**: V1-V7 hold; `git diff` shows additions only; the closure lemma is sorry-free;
`modalWorldBoundS4` and the cardinality lemmas are byte-identical.

**Timing**: 1 dispatch, ~3 hours.
**Depends on**: 10.

---

### Phase 12: `successorBirthContent` Box-Plus Enrichment and `keyLowerBd` Repair [NOT STARTED]

**Goal**: Emit both members of each box-plus pair from `successorBirthContent`, and repair the two
`_preserves_keyLowerBd` proofs. **This is the one phase that can break a landed theorem.**

**Owner / territory**: `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (`:384-393` and the two
preservation proofs at `:2341`, `:2449`); `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` only
if the completeness proof needs re-routing.

**Tasks**:
- [ ] Change `successorBirthContent`'s filter (`LoopChecking.lean:384-393`) so that when
  `T(□ψ)@w ∈ b` it records **both** `(pos, ψ)` and `(pos, .box ψ)`, dually for `F(◇ψ)@w`.
- [ ] Repair `S4LoopInv.keyLowerBd`'s minting case: it must now also show
  `(pos, .box ψ) ∈ relevantSetFinset φ₀ (newForms ++ b) w'`. This is exactly `modalFourBoxProp`'s
  output landing on the branch — the fact `hintikkaS4_box_pos_step` already proves at
  `LoopChecking.lean:6626-6652` (`htarget_mem_fourNew`). **The supporting lemma already exists; do
  not re-derive it.**
- [ ] Discharge `S4LoopInv.keysInUniverse` from Phase 11's closure lemma.
- [ ] Extend `modalStepBranchS4_preserves_keyLowerBd` (`:2341`) and
  `modalStepBranchS4KeyedOrdered_preserves_keyLowerBd` (`:2449`). Both are already structured
  around the minting case.
- [ ] Confirm `S4LoopInv.keysDistinct` is unaffected: `blockingWorldS4Keyed_none_fresh` is stated
  over whatever `successorBirthContent` returns, so enriching it does not change the contract shape.
- [ ] **GATE**: `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` must be green, and V2 must
  hold. Enriching the key changes *which* worlds match, hence which steps block, hence the computed
  tableau. Completeness is proved from `modalExpandBranchesS4Keyed_hintikka`, which is quantified
  over the driver's actual behaviour, so it should transport — **demonstrate it, do not assume it**.
- [ ] **If `modalTableauS4Keyed_complete` breaks and cannot be repaired sorry-free: mark this phase
  `[BLOCKED]`, write the continuation handoff, and STOP. Do not add a sorry. Do not proceed to
  Phase 13.**
- [ ] Confirm the cardinality lemmas are untouched: `signedSubfmls_card_le` (`:313`),
  `signedSubfmls_powerset_card_le` (`:325`), `modalWorldBoundS4`,
  `modalKnownWorlds_length_le_worldBoundS4` must all be byte-identical.

**Estimated output**: ~200-300 lines modified.

**Done when**: V1-V7 hold; `modalTableauS4Keyed_complete` green and sorry-free; the pigeonhole
cardinality lemmas byte-identical; `CslibTests/S4LoopGuardRegression.lean` reproduces its recorded
verdicts exactly (V7 is load-bearing here — the guard's decisions have changed).

**Timing**: 1 dispatch, ~4 hours.
**Depends on**: 11.

---

### Phase 13: `modalExpandBranchesS4Keyed` on the `St` Ladder [NOT STARTED]

**Goal**: Re-express the forked S4 Keyed driver as `modalExpandBranchesGenSt` at
`σ := List (WorldIndex × Finset (Sign × Proposition Atom))`, and re-route the completeness capstone
through the resulting equation.

**Owner / territory**: `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (`:7670`, `:7734`, `:7762`,
`:7823`); `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (the re-route only).

**Tasks**:
- [ ] Add `modalApplyOneS4KeyedSt : RuleApplySt Atom σ` returning `keys'` **directly**, instead of
  freezing `keys` and forcing the stepper to re-derive the `blockingWorldS4Keyed` decision.
- [ ] Re-express `modalExpandBranchesS4Keyed` (`:7670`) and the `KeyedOrdered` variant (`:7762`) as
  `modalExpandBranchesGenSt` instances.
- [ ] Prove `modalExpandBranchesS4Keyed_eq_St` and the ordered analogue.
- [ ] Re-route `modalTableauS4Keyed_complete` through those equations.
- [ ] **This is the second gate.** If the re-route cannot be completed sorry-free, mark `[BLOCKED]`
  and hand off with the exact residual goal. Do not stub.

**Estimated output**: ~250-350 lines modified.

**Done when**: V1-V7 hold; `modalExpandBranchesS4Keyed` no longer forks off the generic ladder;
`modalTableauS4Keyed_complete` green and sorry-free; the six `rfl` bridges still elaborate.

**Timing**: 1 dispatch, ~4 hours.
**Depends on**: 12.

---

### Phase 14: Retire the Duplicated `keys'` Re-Derivation [NOT STARTED]

**Goal**: Collect the payoff. With `keys'` coming out of the apply call, the correspondence
bookkeeping collapses.

**Owner / territory**: `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (`:951-996`, `:2288`, `:2315`,
and the affected preservation lemmas).

**Tasks**:
- [ ] Delete the duplicated `blockingWorldS4Keyed` re-derivation in the stepper. The code's own
  comment at `LoopChecking.lean:951-953` documents that it "re-derives the SAME
  `blockingWorldS4Keyed` decision `modalApplyOneS4Keyed` already made internally"; delete that
  comment along with the duplication.
- [ ] Reduce `modalStepBranchS4Keyed_result_keys_eq` (`:2288`) and `_result_acc_eq` (`:2315`) to
  `rfl` (or delete them if they become trivial and have no consumers — verify first).
- [ ] Simplify each `S4LoopInv` preservation pair that carried re-derivation bookkeeping.
- [ ] Record the measured line-count reduction in `artifacts/baseline.md` (this is where the
  previously-unquantified reduction lives — **measure it, do not assert it**).

**Estimated output**: ~100 lines added, ~400-800 lines deleted.

**Done when**: V1-V7 hold; no `blockingWorldS4Keyed` double derivation remains; the measured
`LoopChecking.lean` line count is recorded against the 10,540 baseline.

**Timing**: 1 dispatch, ~4 hours.
**Depends on**: 13.

---

### Phase 15: Remove `S4LoopInv.outDegEq` and Repair Its Three Provision Sites [NOT STARTED]

**Goal**: Remove the zero-consumer invariant field, freeing its 386 lines of preservation proof for
Phase 25's Boneyard move. **This is not a pure deletion.**

**Owner / territory**: `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (`:7070` structure, `:7084`
field, `:7569` and `:7633` provisions, `:4917-5105` and `:5111-5307` preservation proofs);
`Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:4217-4218` (**positional anonymous-constructor
provision inside the landed completeness capstone `modalTableauS4Keyed_initial`**).

**Tasks**:
- [ ] Re-verify zero-consumer status at execution time. **Critical distinction**: the only two
  `.outDegEq` projections in the repository (`CompletenessLoop.lean:1403`, `:1782`) are on
  `hpot : ModalPotentialInv` (`FmpMeasure.lean:2336`) — the **K/generic** line, not S4. Confirm
  this still holds.
- [ ] Confirm `modalStepBranch_preserves_outDegEq_gen` (`FmpMeasure.lean:1520`),
  `modalStepBranch_preserves_outDegEq` (`:1574`), and `modalStepBranchGen_preserves_outDegEq`
  (`GenericDriver.lean:385`) are **consumed by the K/generic line and are NOT candidates**. Do not
  touch them.
- [ ] `lake build` and record the pre-change state.
- [ ] Delete the `outDegEq` field from `S4LoopInv` (`:7084`).
- [ ] Repair the two named provision sites (`:7569`, `:7633`) and **the positional
  anonymous-constructor site at `FrameCompleteness.lean:4217-4218`** — a positional constructor
  silently shifts when a field is removed, so this must be re-read and re-checked, not
  search-and-replaced.
- [ ] Leave `modalStepBranchS4_preserves_outDegEq` (`:4917-5105`, 189 lines) and
  `modalStepBranchS4KeyedOrdered_preserves_outDegEq` (`:5111-5307`, 197 lines) **in place** — they
  become Boneyard candidates in Phase 25, not deletions here.
- [ ] **Contingency**: if the cascade into the four other invariant proofs that destructure the
  structure is large, **keep the field, revert, and record the decision**. 386 lines are not worth
  a regression. Mark the phase `[PARTIAL]` with that verdict.

**Estimated output**: ~150 lines modified.

**Done when**: V1-V7 hold; `S4LoopInv` has nine fields; both `_preserves_S4LoopInv` theorems and the
`FrameCompleteness.lean` positional site elaborate; **or** the contingency verdict is recorded and
the field is retained.

**Timing**: 1 dispatch, ~4 hours.
**Depends on**: 14.

---

### Phase 16: Split Seam Re-Cut and Module Manifest [NOT STARTED]

**Goal**: Re-cut the module seams **after** the abstractions have landed, and produce a manifest in
which each destination module is sized to one bounded dispatch.

**Owner / territory**:
`specs/557_modal_tableau_refactor_abstractions_boneyard/artifacts/module-manifest.md` only.
**No `.lean` file is edited.**

**Rationale**: report §7 Seam 3 states that if box-plus is adopted, `S4/BirthKey.lean` becomes the
module the entire keyed track depends on and `S4/Redirect.lean` may collapse entirely. Report §7's
Seam-2 table is therefore **provisional**. Phases 3-15 have also removed several hundred to a few
thousand lines. The seams must be re-measured, not carried forward.

**Tasks**:
- [ ] Re-measure `LoopChecking.lean`'s current line count and declaration count against the 10,540 /
  230 baseline.
- [ ] For each proposed destination module, list its **exact declaration names** (not line ranges —
  the ranges have moved) and a measured line total: `S4/Universe.lean`, `S4/BirthKey.lean`,
  `S4/Guard.lean`, `S4/Invariant.lean`, `S4/Hintikka.lean`, `S4/Redirect.lean`.
- [ ] Verify import acyclicity of the proposed dependency chain
  (Universe → BirthKey → Guard → Invariant → Hintikka → Redirect).
- [ ] **H8 subdivision requirement**: any destination module measuring over ~500 lines MUST be
  subdivided in the manifest into named sub-modules, each with its own declaration list.
  `S4/Invariant.lean` as scoped in report §7 spans roughly 6,800 lines and is **explicitly not one
  bounded run** — the manifest must subdivide it (a natural cut is stepper/shape lemmas vs the
  `S4LoopInv` structure vs the preservation lemmas grouped by field family).
- [ ] Record whether `S4/Redirect.lean` still has content after Scope A, or has collapsed.
- [ ] State which manifest entries become Phases 17-22 of this plan and which must be spawned as
  additional phases.

**Estimated output**: ~200 lines (one markdown artifact).

**Done when**: the manifest exists; every entry has a declaration list and a measured line total;
no entry exceeds ~500 lines without being subdivided; import acyclicity is verified on paper;
`git status` shows changes only under `specs/`.

**Timing**: 1 dispatch, ~3 hours.
**Depends on**: 15.

---

### Phase 17: `Tableau/S4/Universe.lean` [NOT STARTED]

**Goal**: Extract the world-universe and cardinality cluster into its own module.

**Owner / territory**: new `Cslib/Logics/Modal/Tableau/S4/Universe.lean`; `LoopChecking.lean`
(removal of the extracted declarations + import); `Cslib.lean`.

**Tasks**:
- [ ] Extract the declarations the Phase 16 manifest assigns to `S4/Universe.lean` — provisionally
  `modalUniverseS4`, `modalWorldBoundS4`, `signedSubfmls`, `signedSubfmls_card_le`,
  `signedSubfmls_powerset_card_le`, `modalKnownWorlds_length_le_worldBoundS4`.
- [ ] Preserve declaration order and docstrings verbatim; a split must be a move, not a rewrite.
- [ ] Add the module docstring per `ORGANISATION.md` and `NOTATION.md` conventions.
- [ ] `lake exe mk_all --module`; `lake shake --add-public --keep-implied --keep-prefix`.

**Estimated output**: ~120 lines moved.

**Done when**: V1-V7 hold; `S4/Universe.lean` depends only on `FmpMeasure` and `Support/*`; barrel
and shake clean; no declaration body changed (verify with `git diff --stat` — the diff should be a
near-pure move).

**Timing**: 1 dispatch, ~2 hours.
**Depends on**: 16.

---

### Phase 18: `Tableau/S4/BirthKey.lean` [NOT STARTED]

**Goal**: Extract the birth-key cluster, now including the box-plus abstraction, into its own module.

**Owner / territory**: new `Cslib/Logics/Modal/Tableau/S4/BirthKey.lean`; `LoopChecking.lean`;
`Cslib.lean`.

**Tasks**:
- [ ] Extract per the manifest — provisionally `relevantSetFinset`, `successorBirthContent`,
  `blockingWorldS4` and its three contract lemmas, plus `boxPlusPair`, `BoxPlusClosed` and the
  codomain closure lemma from Phase 11.
- [ ] Carry the box-plus docstrings (with their `ChagrovZakharyaschev1997` citations and the
  S4-scoping / no-`Foundations` note) across verbatim.
- [ ] `lake exe mk_all --module`; `lake shake`.

**Estimated output**: ~250 lines moved.

**Done when**: V1-V7 hold; `S4/BirthKey.lean` imports `S4/Universe.lean` and nothing above it;
barrel and shake clean.

**Timing**: 1 dispatch, ~2.5 hours.
**Depends on**: 17.

---

### Phase 19: `Tableau/S4/Guard.lean` [NOT STARTED]

**Goal**: Extract the loop-check guard and the rule-application layer.

**Owner / territory**: new `Cslib/Logics/Modal/Tableau/S4/Guard.lean`; `LoopChecking.lean`;
`Cslib.lean`.

**Tasks**:
- [ ] Extract per the manifest — provisionally `blockingWorldS4Keyed` and its contract lemmas,
  `modalApplyOneS4`, `modalApplyOneS4Keyed` (and `modalApplyOneS4KeyedSt` from Phase 13) with the
  four shape lemmas, `modalStepBranchS4`, `modalTableauS4`.
- [ ] **Preserve the guard docstring at (current) `:478-501` verbatim**, including the "No
  reachability restriction" defect statement — it is the load-bearing documentation of the
  known limitation and Phase 26 depends on it being intact.
- [ ] `lake exe mk_all --module`; `lake shake`.

**Estimated output**: ~400 lines moved.

**Done when**: V1-V7 hold; the guard docstring is byte-identical; barrel and shake clean.

**Timing**: 1 dispatch, ~3 hours.
**Depends on**: 18.

---

### Phase 20: `Tableau/S4/Invariant.lean` and Its Manifest Sub-Modules [NOT STARTED]

**Goal**: Extract the `S4LoopInv` structure, the steppers, and the preservation lemmas.

**Owner / territory**: the `Cslib/Logics/Modal/Tableau/S4/` modules the Phase 16 manifest names for
this cluster; `LoopChecking.lean`; `Cslib.lean`.

**H8 note**: as scoped in report §7 this cluster spans roughly 6,800 lines and is **explicitly not
one bounded dispatch**. Phase 16's manifest MUST have subdivided it. This phase executes the
**first** manifest sub-module only; each remaining sub-module is its own dispatch, appended to this
plan as Phase 20a, 20b, … by the implementer, or spawned as a follow-up task per the cut line in
Risks. **Do not attempt the whole cluster in one run.**

**Tasks**:
- [ ] Read the Phase 16 manifest and restate which sub-module this dispatch owns.
- [ ] Extract exactly that sub-module's declaration list. Move, do not rewrite.
- [ ] `lake exe mk_all --module`; `lake shake`.
- [ ] Report the remaining sub-modules and their sizes in the handoff.

**Estimated output**: ~300-500 lines moved per dispatch.

**Done when**: V1-V7 hold for the owned sub-module; the handoff names every remaining sub-module.

**Timing**: 1 dispatch per sub-module, ~3 hours each.
**Depends on**: 19.

---

### Phase 21: `Tableau/S4/Hintikka.lean` [NOT STARTED]

**Goal**: Extract the Hintikka / saturation cluster, whose source range is **discontiguous** in the
current file.

**Owner / territory**: new `Cslib/Logics/Modal/Tableau/S4/Hintikka.lean`; `LoopChecking.lean`;
`Cslib.lean`.

**Tasks**:
- [ ] Extract per the manifest — provisionally `modalHintikkaSetS4`, `modalS4Saturated`, the **8**
  `hintikkaS4_*` bridges, `S4KeyedHintikkaInv`, `hintikka_congr_S4`, and the top-loop Hintikka
  theorem. The source ranges are discontiguous (two blocks); the manifest supplies the exact
  declaration list.
- [ ] All 8 bridges and `modalS4Saturated` are **task-declared preserved assets**. Move them; do not
  restate, weaken, or merge them.
- [ ] `lake exe mk_all --module`; `lake shake`.

**Estimated output**: ~500 lines moved.

**Done when**: V1-V7 hold; all 8 bridges present and unchanged; `modalS4Saturated`'s 7 consumers all
elaborate.

**Timing**: 1 dispatch, ~3 hours.
**Depends on**: 20.

---

### Phase 22: `Tableau/S4/Redirect.lean` [NOT STARTED]

**Goal**: Extract the redirect / `Reds` cluster, or record that it has collapsed.

**Owner / territory**: new `Cslib/Logics/Modal/Tableau/S4/Redirect.lean`; `LoopChecking.lean`;
`Cslib.lean`.

**Tasks**:
- [ ] If the Phase 16 manifest records that this cluster still has content, extract it —
  provisionally `keysOriginS4` (**NOT Boneyard-eligible**), the `Reds` / `accWithReds` packaging,
  `hasEdge_accWithReds_iff`, `reflTransGen_accWithReds_first_red`, and the two
  `blockedRedirect_unwrapped_{boxPos,diaNeg}_mem` transfers. All are **task-declared preserved
  assets** to be *placed*, never moved to `Boneyard/`.
- [ ] If the manifest records that the cluster collapsed after Scope A, record that outcome in the
  manifest and skip the module creation — do not create an empty module.
- [ ] `lake exe mk_all --module`; `lake shake`.

**Estimated output**: ~350 lines moved (or a recorded collapse verdict).

**Done when**: V1-V7 hold; every named preserved asset is present exactly once and unchanged.

**Timing**: 1 dispatch, ~3 hours.
**Depends on**: 21.

---

### Phase 23: `LoopChecking.lean` Reduction, `ORGANISATION.md` Update, Barrel and Shake [NOT STARTED]

**Goal**: Reduce `LoopChecking.lean` to whatever legitimately remains, and update the repository
documentation that currently describes `Modal/Tableau/` in one undifferentiated line.

**Owner / territory**: `Cslib/Logics/Modal/Tableau/LoopChecking.lean`; `ORGANISATION.md`;
`Cslib.lean`.

**Tasks**:
- [ ] Reduce `LoopChecking.lean` to its residue (or convert it to a re-export barrel for the `S4/`
  cluster if nothing substantive remains). Record the final line count against the 10,540 baseline.
- [ ] Update `ORGANISATION.md`'s `Modal/Tableau/` entry to describe the actual module structure:
  `Support/` (shared facts), `S4/` (the keyed cluster), and the driver/soundness/completeness
  modules. **`ORGANISATION.md` gives no line-count guidance and this update must not introduce
  any** — the splits are justified by seams, and the document should say so.
- [ ] `lake exe mk_all --module`; `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] Verify import acyclicity across the whole `Modal/Tableau/` tree.

**Estimated output**: ~150 lines modified across `LoopChecking.lean` and `ORGANISATION.md`.

**Done when**: V1-V7 hold; `ORGANISATION.md` describes the real structure; shake reports no unused
or missing import; the final line counts are recorded in `artifacts/baseline.md`.

**Timing**: 1 dispatch, ~3 hours.
**Depends on**: 22.

---

### Phase 24: Create `Boneyard/` and Document the Quarantine Convention [NOT STARTED]

**Goal**: Establish the `Boneyard/` quarantine at the repository root with an explicit, documented
convention. `Boneyard/` does **not** currently exist in this repository.

**Owner / territory**: new `Boneyard/` directory and `Boneyard/README.md`; `lakefile` /
`lake-manifest` exclusion configuration; `.gitignore` only if required. **No `Cslib/` file is edited
and nothing is moved in this phase.**

**Tasks**:
- [ ] Create `Boneyard/` and `Boneyard/README.md` documenting the convention borrowed from the
  source repository: **quarantined; never imported by `Cslib/`; excluded from `lake build`,
  `mk_all`, `lint-style`, `shake`, and all sorry/axiom censuses; retained for provenance rather
  than use.**
- [ ] Configure the build so `Boneyard/` is genuinely excluded — verify that `lake build` does not
  compile it and `lake exe mk_all --module` does not add it to the barrel.
- [ ] Verify the census commands (V4, V5) do not scan `Boneyard/`. If they would, record the
  corrected command in `artifacts/baseline.md`.
- [ ] Record **both mandatory carve-outs** in `Boneyard/README.md`:
  (a) `FrameSoundness.lean:1220-1244` (`branchSatisfiableIn_s4FC_ancestor_redirect`) is
  **IMMOVABLE** despite being zero-consumer, because it carries the retained sorry that is an
  explicit user decision and the "proven and consumed" rule does not by itself protect it;
  (b) `keysOriginS4` is **NOT eligible** — it is not zero-consumer.
- [ ] Record the movement rule: nothing may be moved without a **re-run zero-consumer check at
  execution time**, and nothing proven and consumed may be moved at all.

**Estimated output**: ~120 lines (README) plus build configuration.

**Done when**: `Boneyard/README.md` exists with the convention and both carve-outs; `lake build`
green with `Boneyard/` present and excluded; V4/V5 census commands verified not to scan it; V1-V7
hold.

**Timing**: 1 dispatch, ~2 hours.
**Depends on**: 23.

---

### Phase 25: Re-Run the Consumer Audit and Move Only Confirmed-Eligible Declarations [NOT STARTED]

**Goal**: Move to `Boneyard/` exactly the declarations a **freshly re-run** audit confirms are
zero-consumer. The recorded audit is dated and must not be trusted on its own.

**Owner / territory**: `Boneyard/`; `Cslib/Logics/Modal/Tableau/` (the source declarations being
moved out); `specs/557_modal_tableau_refactor_abstractions_boneyard/artifacts/boneyard-audit-rerun.md`.

**Tasks**:
- [ ] **Re-run the consumer audit at execution time** using report §6's recorded method
  (declaration site vs code reference vs structure-field provision vs comment-only mention, over
  all of `Cslib/**/*.lean` and `CslibTests/**/*.lean`, with block-comment and line-comment content
  classified as comment, not consumption). Write the result to `artifacts/boneyard-audit-rerun.md`.
- [ ] Move only the rows the **re-run** confirms zero-consumer. Candidates from the dated audit,
  each to be re-checked: `blockedRedirect_diaNeg_mem_of_diaOrigin` (`LoopChecking.lean:1506`),
  `blockedRedirect_boxctx_mem_of_boxOrigin` (`:1466`), the `keysRootEmpty` / `keysRootEmpty_entry`
  pair (`:2007`, `:2013`), and — **only if Phase 15 actually removed the field** —
  `modalStepBranchS4_preserves_outDegEq` (189 lines) and
  `modalStepBranchS4KeyedOrdered_preserves_outDegEq` (197 lines).
- [ ] **Do NOT move** `branchSatisfiableIn_s4FC_ancestor_redirect` (`FrameSoundness.lean:1220-1244`)
  — carve-out (a). **Do NOT move** `keysOriginS4` — carve-out (b). **Do NOT move** any
  task-declared preserved asset: `modalS4Saturated`, the 8 bridges, `hasEdge_accWithReds_iff`,
  `reflTransGen_accWithReds_first_red`, the two `blockedRedirect_unwrapped_*_mem` transfers, or the
  `Reds` / `accWithReds` packaging.
- [ ] **Do NOT move** `modalStepBranch_preserves_outDegEq_gen` (`FmpMeasure.lean:1520`),
  `modalStepBranch_preserves_outDegEq` (`:1574`), or `modalStepBranchGen_preserves_outDegEq`
  (`GenericDriver.lean:385`) — they are consumed by the K/generic line.
- [ ] Move rather than delete. Each moved declaration keeps its docstring and gains a one-line
  provenance note in `Boneyard/README.md`.

**Estimated output**: ~150 lines (audit artifact) plus the moves.

**Done when**: V1-V7 hold **with the Tableau sorry census still exactly 1** (the retained sorry must
still be in `FrameSoundness.lean`, not in `Boneyard/`); the re-run audit artifact exists; every move
is justified by a row in it; both carve-outs verifiably untouched.

**Timing**: 1 dispatch, ~3 hours.
**Depends on**: 24.

---

### Phase 26: Scope D — Documentation Corrections and Measured-Baseline Landing [NOT STARTED]

**Goal**: Correct the four adjudicated documentation defects, leave the seven TRUE verdicts alone,
and land the measured baseline into the subsystem documentation so the drift cannot recur.

**Owner / territory**: comment and docstring blocks in `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
(or its `S4/` successors, if Phases 17-23 have run) and
`Cslib/Logics/Modal/Tableau/FrameSoundness.lean`. **This phase must never run concurrently with any
phase owning those files.**

**Tasks**:
- [ ] **Defect 1** — `LoopChecking.lean:2001-2002`: the claim that "`keysOriginS4` and its supporting
  lemmas" were removed is **FALSE**. `keysOriginS4` is declared (current `:1279`) with 55
  non-comment references. Correct the comment; cite the audit as evidence.
- [ ] **Defect 2** — `LoopChecking.lean:8911-8912`: **STALE** references to
  `hintikkaS4_box_pos_reflTransGen_boxed` / `_dia_neg_reflTransGen_boxed`, removed in commit
  `c4b33f63`. Correct the comment and record that the bridge count is now **8**, and that the
  asserted 10 **was correct when written**.
- [ ] **Defect 3** — `LoopChecking.lean:2000-2004`: resolve the "Now possibly orphaned" hedge on
  `keysRootEmpty` into a definite zero-consumer finding, with the Phase 25 audit as evidence (or
  note that the pair was moved to `Boneyard/`).
- [ ] **Defect 4** — `FrameSoundness.lean:1215-1219`: add two facts the comment currently omits —
  (i) that `branchSatisfiableIn_s4FC_ancestor_redirect` has **zero code consumers**, and (ii) that
  `Massacci2000` Theorem 8.1 (blocking preserves satisfiability) is **stated and never proved in
  that source** — Appendix B.2 proves only Theorem 8.4, and §10.2 defers 8.1 to Goré's model graphs
  (`chunk_0054.md:3-7`). Both change how a future reader assesses the obstruction. Cite by chunk
  and page.
- [ ] **Leave alone** the seven verdicts adjudicated TRUE: `FrameSoundness.lean:1246-1255`,
  `:1314-1321`, `:1193-1194`; `LoopChecking.lean:2019-2036`(a), `:7536-7539`, `:951-953` (unless
  Phase 14 deleted the duplication it describes, in which case delete the comment with it);
  `FrameCompleteness.lean:4176-4178`, `:4163-4169`, `:4184-4186` (unless Phase 13 fixed the fork it
  describes, in which case update it to record that it was fixed).
- [ ] Land the measured baseline table from `artifacts/baseline.md` into the subsystem's module
  documentation, **each row with its exact reproduction command**, including the axiom figure as a
  **scope distinction** (Tableau: 0 declarations / 3 raw matches; repo-wide `Cslib/`: 26 / 1,701) —
  never as an adjusted number.
- [ ] Record the retired premises (a)-(d) in the subsystem documentation so no future route
  reinstates them, in particular that `Massacci2000` Theorem 8.1 supplies no transcribable proof.
- [ ] **Do not introduce any FIX:/TODO:/NOTE:/QUESTION: tag.** The three files currently have zero,
  and the debt here is prose-shaped, not tag-shaped.
- [ ] Comply with `.claude/rules/no-task-references-in-deliverables.md`: **no task numbers** in any
  `Cslib/` or `ORGANISATION.md` prose. Cite durable anchors (declaration names, file sections,
  BibKeys) instead.

**Estimated output**: ~250 lines of documentation modified.

**Done when**: V1-V7 hold; all four defects corrected; the seven TRUE verdicts unmodified except
where a prior phase changed the code they describe; the baseline table is in the subsystem docs with
commands; tag census in the affected files still 0/0/0/0; no task-number citations introduced.

**Timing**: 1 dispatch, ~3 hours.
**Depends on**: 25.

---

### Phase 27: CSLib Vetting Pipeline Acceptance Gate [NOT STARTED]

**Goal**: Run the full CSLib vetting pipeline against the subsystem — it has never been run on it —
and record the verdict.

**Owner / territory**: `specs/557_modal_tableau_refactor_abstractions_boneyard/artifacts/vetting-report.md`;
whatever files the pipeline's auto-fixers touch.

**Tasks**:
- [ ] Run the seven-step CI order from `.claude/rules/cslib.md`, in order:
  `lake exe cache get`; `lake build`; `lake exe checkInitImports`; `lake lint`;
  `lake exe lint-style`; `lake test`; `lake exe mk_all --module`;
  `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] Vet against `CONTRIBUTING.md`, `NOTATION.md`, `ORGANISATION.md`, `CODE_OF_CONDUCT.md`. Record
  each violation with its file and line.
- [ ] Re-run and record the full V1-V7 contract one final time, including the closing measurements
  against `artifacts/baseline.md`: final line counts, sorry census (**must be exactly 1**), axiom
  declarations (**must be 0**), tag census, and `CslibTests/S4LoopGuardRegression.lean` verdicts.
- [ ] Write `artifacts/vetting-report.md` with a PASS/FAIL per pipeline step and per standard.
- [ ] For violations that cannot be fixed within this dispatch, list them explicitly for follow-up
  task creation. **Do not** silently narrow the acceptance gate.

**Estimated output**: ~200 lines (vetting report) plus any lint auto-fixes.

**Done when**: every pipeline step has a recorded PASS or an explicitly listed FAIL with its
follow-up; V1-V7 all pass; the closing baseline comparison is recorded.

**Timing**: 1 dispatch, ~3 hours.
**Depends on**: 26.

---

## Testing & Validation

- **Per-phase**: the Standing Verification Contract V1-V7 (see Postmortem Constraints) plus each
  phase's own "Done when" clause. No phase is complete without both.
- **Behaviour preservation** is demonstrated by, and only by: `modalTableauS4Keyed_complete` and the
  six landed `Decidable` instances (K/T/B/S5/Five/KB5) remaining green at **every commit**; the
  Tableau sorry census not rising above **1**; no new axioms above the subsystem baseline of **0**.
- **Extraction phases (3-7)** are behaviour-preserving *by construction* — the re-derivations are
  stated identically to the originals. Any phase where they are **not** identical must extract both
  under distinct names and say so in the module docstring, never silently unify them.
- **The two gates**: Phase 12 (box-plus enrichment) and Phase 13 (St-ladder migration) are the only
  phases that can break a landed theorem. Both gate on
  `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` plus V2. Either failing sorry-free
  repair means `[BLOCKED]`, never a sorry.
- **Split phases (17-23)** must be near-pure moves. Verify with `git diff --stat`: a split that
  rewrites declaration bodies is a defect.
- **Regression corpus**: `CslibTests/S4LoopGuardRegression.lean` (197 lines) must reproduce its
  recorded verdicts exactly, plus the probe harnesses under the S4 loop-guard task's artifacts
  directory. V7 is especially load-bearing at Phase 12, where the guard's blocking decisions change.
- **Final acceptance**: Phase 27's full pipeline run against the four standards documents.

---

## Artifacts & Outputs

| Path | Type | Produced by |
|---|---|---|
| `specs/557_modal_tableau_refactor_abstractions_boneyard/decisions/01_abstraction-decision-record.md` | decision record (review gate) | Phase 1 |
| `specs/557_modal_tableau_refactor_abstractions_boneyard/artifacts/baseline.md` | measured baseline + commands | Phases 2, 7, 14, 23, 24 |
| `specs/557_modal_tableau_refactor_abstractions_boneyard/artifacts/saturation-consumer-audit.md` | mandatory gate audit | Phase 8 |
| `specs/557_modal_tableau_refactor_abstractions_boneyard/artifacts/module-manifest.md` | re-cut split seams | Phase 16 |
| `specs/557_modal_tableau_refactor_abstractions_boneyard/artifacts/boneyard-audit-rerun.md` | execution-time consumer audit | Phase 25 |
| `specs/557_modal_tableau_refactor_abstractions_boneyard/artifacts/vetting-report.md` | acceptance gate verdict | Phase 27 |
| `Cslib/Logics/Modal/Tableau/Support/{Subfmls,KnownWorlds,Accessibility}.lean` (+ `Measure.lean`) | new public support modules | Phases 3-7 |
| `Cslib/Logics/Modal/Tableau/S4/{Universe,BirthKey,Guard,Invariant,Hintikka,Redirect}.lean` | split modules (per manifest) | Phases 17-22 |
| `Boneyard/` + `Boneyard/README.md` | quarantine + convention | Phase 24 |
| `ORGANISATION.md` (updated `Modal/Tableau/` entry) | repository documentation | Phase 23 |
| `specs/literature-index.json` (repaired Massacci chunk count) | index repair | Phase 2 |

---

## Rollback/Contingency

- **Per-phase**: every phase commits only at green-build milestones (`wrap-up.md` incremental commit
  discipline). Rollback is `git revert` of that phase's commits; because each phase owns a disjoint
  file set, a revert does not strand a sibling phase.
- **Phase 12 (box-plus)**: if `modalTableauS4Keyed_complete` cannot be repaired sorry-free, revert
  the `successorBirthContent` enrichment, mark the phase `[BLOCKED]`, and stop. Phases 11's additive
  declarations may stay (they change no behaviour). **Never add a sorry.**
- **Phase 13 (St migration)**: if the re-route cannot be completed sorry-free, revert to the forked
  driver. Phases 9-10 stay — they are purely additive and the six `rfl` bridges are unaffected.
- **Phase 15 (`outDegEq`)**: if the cascade into the other invariant proofs is large, **keep the
  field**, revert, record the verdict, and Boneyard nothing. 386 lines are not worth a regression.
  Phase 25's candidate list then simply omits the two preservation lemmas.
- **Phases 17-23 (splits)**: each is a near-pure move; revert restores the monolith. If the Phase 16
  manifest proves wrong mid-split, stop, revert the in-flight phase, and re-cut the manifest rather
  than improvising a seam.
- **Phase 25 (Boneyard moves)**: moves are `git mv`-shaped; revert restores the declaration to its
  original module. If the Tableau sorry census changes as a side effect of any move, that move is
  wrong — revert it immediately (the retained sorry must never leave `FrameSoundness.lean`).
- **Whole-task rollback**: the task is a restructuring; reverting every commit restores the
  20,164-line three-file baseline recorded in `artifacts/baseline.md`. No external system, schema,
  or published interface is touched, so no rollback beyond `git` is required.
