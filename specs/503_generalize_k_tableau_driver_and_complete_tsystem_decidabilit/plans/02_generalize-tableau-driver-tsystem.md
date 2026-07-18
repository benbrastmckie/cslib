# Implementation Plan (v2 — corrective revision): Task #503 — Generalize K Tableau Driver + Complete T-System Decidability

- **Task**: 503 - Generalize the K tableau driver and complete T-system decidability
- **Status**: [COMPLETED]
- **Effort**: 13 hours (delivered across 503 + spawned tasks 507/510/513)
- **Dependencies**: None. (Builds on the already-committed, green rule-level work in
  `FrameRules.lean`/`FrameSoundness.lean`/`FrameCompleteness.lean`. The former blocking edge
  503→513 has been dropped: task 513 is archived-COMPLETED and delivered exactly the generic
  soundness chain Phase 6 needed — see Research Integration below.)
- **Research Inputs**: specs/300_modal_extensions_t_s4_s5/reports/02_spawn-analysis.md;
  specs/300_modal_extensions_t_s4_s5/handoffs/phase2-blocked-handoff.md;
  specs/ROADMAP-alignment-audit.md (sections A, C — consolidated alignment audit, ground-truthed)
- **Artifacts**: plans/02_generalize-tableau-driver-tsystem.md (this file);
  plans/01_generalize-tableau-driver-tsystem.md (superseded prior version, retained for history)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md;
  CONTRIBUTING.md; NOTATION.md; ORGANISATION.md
- **Type**: cslib
- **Lean Intent**: false

## Revision Note (v2)

This is a **corrective revision** driven by the consolidated alignment audit
(`specs/ROADMAP-alignment-audit.md`). It changes **no Lean code**. It reconciles the plan and task
metadata with audit-verified, ground-truthed reality:

1. **The stale blocker is removed.** Phase 6 (`Decidable (tValid φ)`) was recorded `[BLOCKED]` on
   task 513 (generic soundness). Task 513 is now **archived-COMPLETED**
   (`specs/archive/513_generalize_tableau_soundness_chain_over_spec`) and delivered the
   `modalTableauT_sound` soundness chain that was Phase 6's exact prerequisite. The 503→513
   dependency edge has already been dropped from `state.json` (`dependencies: []`).
2. **The Phase-6 target artifacts are LIVE and sorry-free in the tree right now**:
   `tValid_decides` (`Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:1298`) and
   `instDecidableTValid` (`:1311`), both proved via `modalTableauT_sound` (`:1212`) with only the
   standard `propext`/`Classical.choice`/`Quot.sound` axiom trio. Phases 1–5 landed at
   `14d9931c`; Phase 6 was closed by task 513.
3. **The T-decidability target is the real terminus, and it is SATISFIED.** Phases 6 and 7 are
   updated from `[BLOCKED]`/`[PARTIAL]` to `[COMPLETED]`. See the Closure Recommendation.

**Recommended status change (NOT applied by this revision):** move task 503 from `[BLOCKED]` to
`[COMPLETED]` in `state.json` with a completion summary. This revision does not itself perform any
terminal status transition.

### Caveats verified (do not conflate)

- **`S5Simplification.lean:1814` carries a genuine live `[BLOCKED]`** — but it is about discharging
  `RuleApplicationSpec modalApplyOneS5` (an S5 driver-generalization attempt owned by **task 504**),
  **not** 503's T-decidability target. Do not conflate the two.
- **`GenericDriver.lean:131` / `:149` carry now-STALE narrative prose** asserting "Task 503
  Phase 6 (`Decidable (tValid φ)`) is **[BLOCKED]**". This is a stale in-file docstring only; the
  instances it describes as missing are live. Correcting that comment is a Lean-code documentation
  cleanup, deliberately **out of scope** for this no-Lean-edit revision — flag it for a future
  docstring sweep (or fold into task 504/505 when they next touch `GenericDriver.lean`).

## Research Integration

Newly integrated in v2 from `specs/ROADMAP-alignment-audit.md` (sections A and C), each claim
ground-truthed against the repository before adoption:

- **§A (four-branch verdict)**: "S5 / T / B — ✅ DELIVERED — mislabeled blocked. Decidable
  instances live & sorry-free." Verified: `instDecidableTValid` (`FrameCompleteness.lean:1311`),
  `instDecidableBValid` (`:1926`), `instDecidableS5Valid` (`:2422`), `instDecidableFiveValid`
  (`:3213`) are all present and sorry-free. The `RuleApplicationSpec` interface 503 established
  demonstrably served the entire downstream T/B/S5/5 family.
- **§C (dependency-graph correction)**: "503→513 — 513 archived-complete; 503 blocker stale
  (target `instDecidableTValid` live) → Drop block; re-check 503 for closure." Verified: 513 is in
  `specs/archive/`; the edge is already `[]` in `state.json`; the target is live. This revision
  performs the recommended closure re-check and finds the terminus satisfied.
- **Generic-driver scope, re-checked against the tree (beyond the audit)**: the v1 Phase-4
  deviation recorded that `CompletenessLoop.lean`'s `ModalLoopInv` was *not* generalized over an
  abstract `apply`. That residual was **subsequently delivered by task 510**:
  `ModalLoopInvGen (apply : RuleApply Atom)` now exists at `CompletenessLoop.lean:134`, with a
  `ModalLoopInv ↔ ModalLoopInvGen modalApplyOne` bridge at `:162`. Combined with task 507
  (FmpMeasure termination) and task 513 (soundness), the 91-call-site generic-driver
  parametrization was carried through **all three** target files
  (`Saturation.lean`/`FmpMeasure.lean`/`CompletenessLoop.lean`). No generic-driver scope remains as
  503 open work (see Closure Recommendation).

**reports_integrated**: `ROADMAP-alignment-audit.md`

## Overview

Parametrize the K signed-tableau decision procedure over an abstract rule-application function
`apply` (matching `modalApplyOne`'s signature) plus an explicit structural-hypothesis bundle
(`RuleApplicationSpec`); re-derive K as the trivial instantiation with zero regression; instantiate
the generic driver with `modalApplyOneT` to obtain `modalStepBranchT`/`modalExpandBranchesT`/
`modalTableauT`; close the T truth lemma and `tValid` completeness; and deliver `tValid_decides` +
`Decidable (tValid φ)`. **Definition of done — the stated deliverable terminus — is
`Decidable (tValid φ)`, and it is met**: `instDecidableTValid` is live and sorry-free at
`FrameCompleteness.lean:1311`.

The generalization was delivered by 503's own phases plus three spawned follow-up tasks that the
plan's own `[BLOCKED]`-fallback discipline created — a pattern that worked exactly as designed:

| Concern | File | Delivered by | Evidence |
|---------|------|--------------|----------|
| Driver definitions (`*Gen`) | `Saturation.lean` | 503 Phase 1 | `modalStepBranchGen`/`modalExpandBranchesGen`/`modalTableauGen` |
| `RuleApplicationSpec` interface | `GenericDriver.lean` | 503 Phase 2 | `RuleApplicationSpec`, `modalApplyOne_spec` |
| Termination / FMP measure | `FmpMeasure.lean` | **task 507** (`009cc348`) | `_gen` step lemmas; spec grew 3→7 fields |
| T driver instantiation | `TDriver.lean` | 503 Phase 4 | `modalApplyOneT_spec` (all 7 fields) |
| Completeness / loop invariant | `CompletenessLoop.lean` | **task 510** | `ModalLoopInvGen` (`:134`), `modalExpandBranchesT_hintikka` |
| T truth lemma + `tValid` completeness | `FrameCompleteness.lean` | 503 Phase 5 (`14d9931c`) | `modalTruthLemmaT`, `modalTableauT_complete` |
| Soundness chain + decidability | `FrameSoundness.lean`/`FrameCompleteness.lean` | **task 513** (archived) | `modalTableauT_sound` (`:1212`), `tValid_decides` (`:1298`), `instDecidableTValid` (`:1311`) |

### Prior Plan Reference

Prior plan `specs/300_modal_extensions_t_s4_s5/plans/01_frame-extensions-implementation.md`
(task 300, [PARTIAL]) is reference-only; its Phase-1 frame scaffolding and Phase-2 rule-level T
work are committed and green (do not re-derive). Plan v1
(`plans/01_generalize-tableau-driver-tsystem.md`) is superseded by this file but retained for its
detailed phase-by-phase deviation and blocker-history records (valuable postmortem on why the
crux phases were spawned rather than inlined).

### Roadmap Alignment

**Task 503 is OFF the project ROADMAP.** `specs/ROADMAP.md`'s "Remaining" section tracks only
Bimodal/Temporal completeness; this modal-tableau-decidability work grew up beside the roadmap and
was never folded in (audit §executive-summary point 3: "0 of 13 tasks are on the ROADMAP"). This
revision adds **no** roadmap claims. Whether to extend ROADMAP.md with a "Modal Tableau
Decidability" section is a user strategic decision (audit §D, Tier 4), explicitly not undertaken
here.

## Goals & Non-Goals

**Goals** (all met):
- Generic driver `modalStepBranchGen`/`modalExpandBranchesGen`/`modalTableauGen` over an abstract
  `apply`. ✓ (Phase 1)
- Explicit `RuleApplicationSpec` structural-hypothesis bundle; `modalApplyOne_spec` trivial
  witness. ✓ (Phase 2; extended 3→7 fields by task 507)
- K re-derived as the trivial instantiation with zero regression / zero sorry / zero axiom;
  `modalTableau_decides`/`instDecidableKValid` unchanged. ✓
- `modalStepBranchT`/`modalExpandBranchesT`/`modalTableauT` from `modalApplyOneT`, T structural
  hypotheses discharged (`modalApplyOneT_spec`). ✓ (Phase 4)
- T truth lemma, `tValid` completeness, and **`Decidable (tValid φ)`** — all genuinely sorry-free.
  ✓ (Phases 5–6; soundness via task 513)
- Full CSLib CI clean; interface documented for downstream reuse. ✓ (Phase 7)

**Non-Goals** (unchanged):
- S4 support / loop-checking / `2^|Sf|` termination (task 506; structurally different).
- S5, B, or 5/Euclidean instantiation as *503's* deliverable (tasks 504/505; though those
  decidability instances have since independently landed in-tree using this interface).
- Re-proving the committed rule-level T work.
- Any `sorry`/`axiom`/vacuous placeholder.
- Changing K's observable behavior or public theorem statements.
- **New in v2**: any Lean-code edit (including correcting the stale `GenericDriver.lean` docstring)
  and any terminal status transition — this revision touches only plan/metadata artifacts.

## Risks & Mitigations

All original crux risks (generic termination measure, T truth-lemma box-positive case, driver-level
T soundness) **materialized and were resolved** via the spawned tasks 507/510/513 rather than
inline — the plan's `[BLOCKED]`-with-documented-goal-state discipline is what enabled that. The
only residual risks are now documentation/bookkeeping:

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Stale `GenericDriver.lean:131/149` docstring still asserts Phase 6 `[BLOCKED]` | L | Certain (present now) | Documented as an explicit out-of-scope cleanup above; flag for a docstring sweep or fold into task 504/505's next `GenericDriver.lean` touch. Not a correctness issue — the instances are live. |
| Task metadata (`state.json`) still shows `[BLOCKED]` after terminus met | L | Certain (present now) | Closure Recommendation below; user/orchestrator applies the `[BLOCKED]`→`[COMPLETED]` transition. |
| Confusing 503's satisfied T-target with the live S5 `[BLOCKED]` in `S5Simplification.lean:1814` | M | L | Caveat section above explicitly separates them (S5 gap is task 504's). |

## Implementation Phases

**Dependency Analysis** (all waves delivered):
| Wave | Phases | Blocked by | Status |
|------|--------|------------|--------|
| 1 | 1 | -- | ✓ delivered (503) |
| 2 | 2 | 1 | ✓ delivered (503) |
| 3 | 3 | 2 | ✓ delivered (task 507) |
| 4 | 4 | 3 | ✓ delivered (503 + task 510 for the loop-invariant residual) |
| 5 | 5 | 4 | ✓ delivered (503, task 510) |
| 6 | 6 | 5 | ✓ delivered (task 513) |
| 7 | 7 | 6 | ✓ delivered (503) |

---

### Phase 1: Generic driver definitions in Saturation.lean [COMPLETED]

- **Goal:** Parametrize the driver definitions over an abstract `apply` and re-derive K's
  `modalStepBranch`/`modalExpandBranches`/`modalTableau` as the trivial instantiation, keeping the
  K build green with no downstream changes.
- **Delivered:** `modalStepBranchGen`/`modalExpandBranchesGen`/`modalTableauGen` added to
  `Saturation.lean` as separate parallel definitions; K's originals kept byte-identical (zero
  touch); three `_eq` bridge lemmas (`modalStepBranch_eq` by `rfl`, `modalExpandBranches_eq` by
  fuel+worklist induction, `modalTableau_eq`) prove the K↔Gen agreement without altering
  auto-generated equation-lemma shapes. `lake build` green; zero sorry/axiom; no K regression.
  *(v1 deviation retained: the `abbrev`/wrapper-defeq approach was tried first and broke 14+
  downstream `simp only`/`unfold` sites, so the safer parallel-definition + bridge-lemma mechanism
  was used.)*
- **Files:** `Cslib/Logics/Modal/Tableau/Saturation.lean`.

---

### Phase 2: Structural-hypothesis interface bundle [COMPLETED]

- **Goal:** Define the explicit `RuleApplicationSpec` bundle a rule extension must satisfy to reuse
  the K-style termination measure, and prove `modalApplyOne` satisfies it.
- **Delivered:** `Cslib/Logics/Modal/Tableau/GenericDriver.lean` with
  `structure RuleApplicationSpec (apply)` and `modalApplyOne_spec`. Initial three fields
  (`freshLocal`, `outputsSubsetUniverse`, `persistentFresh`) derived from what
  `modalStepBranch_potential_step`/`_worldBound` actually consume; downstream-reuse notes for
  T/S5/B; S4 explicitly documented as **not** an instance. `lake build` + full CI green.
  *(v1 deviation retained: the three fields sufficed to restate the step lemmas' types generically
  but not to replay their proofs — that gap was escalated to Phase 3, and the spec grew to seven
  fields in task 507.)*
- **Files:** `Cslib/Logics/Modal/Tableau/GenericDriver.lean` (new); `Cslib.lean` registration.

---

### Phase 3: Generalize the FMP / termination measure over the interface [COMPLETED]

**RESOLVED by task 507** (`specs/507_generalize_k_fmp_termination_measure_over_ruleapplicationspec/`,
commit `009cc348`) — escalated via `/spawn 503` exactly as this phase's `[BLOCKED]` fallback
recommended.

- **Delivered:** all three rule-dependent step lemmas (`modalStepBranch_potential_step`,
  `modalStepBranch_worldBound`, `modalExpMeasure_step_lt`) now hold for an abstract
  `apply : RuleApply Atom` given a `RuleApplicationSpec apply` witness, as `_gen` lemmas in
  `FmpMeasure.lean` with `(apply, spec)`-bundled wrappers in `GenericDriver.lean`.
  `RuleApplicationSpec` grew 3→7 fields (added `rankStep`, `outDegStep`, `knownWorldsStep`,
  `branchingLength`), each discharged for `modalApplyOne` via `modalApplyOne_spec`. The ~900-line
  dependency chain was re-derived generically; K statements are byte-identical to pre-507
  (diffed against `d5b24e67`), now one-line corollaries. 29 declarations `#print axioms`-clean.
- **Known constraint:** an import cycle (`GenericDriver.lean`→`FmpMeasure.lean`) forces the `_gen`
  lemmas to take raw hypotheses; bundled wrappers live in `GenericDriver.lean`.
- **Files:** `Cslib/Logics/Modal/Tableau/FmpMeasure.lean`, `GenericDriver.lean`.

*(The full original blocker record and postmortem — why the ~900-line potential-function argument
could not be a mechanical substitution — is preserved in plan v1 §Phase 3 for reference.)*

---

### Phase 4: Generalize CompletenessLoop + instantiate the T driver [COMPLETED]

- **Goal:** Thread `apply`/`spec` through `CompletenessLoop.lean`, re-derive K, and instantiate the
  generic stack with `modalApplyOneT` to obtain the T driver and `modalApplyOneT_spec`.
- **Delivered:**
  - `Cslib/Logics/Modal/Tableau/TDriver.lean` (new) — `modalStepBranchT`/`modalExpandBranchesT`/
    `modalTableauT` as `…Gen modalApplyOneT`; `modalApplyOneT_spec : RuleApplicationSpec
    modalApplyOneT` with all seven fields discharged (via
    `modalApplyOneT_eq_of_not_boxPos_diaNeg` agreement + T-shape facts). Two additive public
    helpers added to `FmpMeasure.lean` (`modalUniverse_mem_of_sameWorld_subfml`,
    `label_mem_modalKnownWorlds`); no `modalUniverse` enlargement needed. Full CI green.
  - **CompletenessLoop.lean loop-invariant generalization**: v1 recorded this as a deliberate
    scope cut (skipped, `ModalLoopInv` left K-concrete). **That residual was subsequently delivered
    by task 510**: `ModalLoopInvGen (apply : RuleApply Atom)` now exists at
    `CompletenessLoop.lean:134` with a `ModalLoopInv ↔ ModalLoopInvGen modalApplyOne` bridge at
    `:162`. The v1 "recommend a dedicated `generic-completeness-loop` task" contingency is thereby
    also discharged.
- **Files:** `TDriver.lean` (new), `FmpMeasure.lean` (two additive helpers), `CompletenessLoop.lean`
  (generic loop invariant, via task 510), `Cslib.lean`.

---

### Phase 5: T truth lemma and `tValid` completeness [COMPLETED]

**UNBLOCKED by task 510** (which delivered `modalExpandBranchesT_hintikka`, the
Hintikka-set-production prerequisite) and delivered at commit `14d9931c`.

- **Delivered:** a "T Modal Truth Lemma" section (~340 lines) in `FrameCompleteness.lean`:
  `hintikkaT_box_pos`/`hintikkaT_diamond_neg` (the two genuinely-new `Relation.ReflGen` bridges),
  `modalTruthLemmaT` (strong induction on `modalComplexity`), `modalOpenBranchT_countermodel`, and
  the headline `modalTableauT_complete` (`modalTableauT φ0 = .openBranch b a → ¬ tValid φ0`),
  assembled from `modalExpandBranchesT_hintikka` (task 510) plus two `apply`-agnostic
  CompletenessLoop lemmas un-privatized (visibility-only) for reuse. Zero sorry, standard axiom
  trio only. Full CI green.
- **Files:** `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`.

*(The original Phase-5 blocker analysis — the Hintikka-set prerequisite that surfaced one layer
below the anticipated box-positive case, and why it was spawned as task 510 — is preserved in plan
v1 §Phase 5.)*

---

### Phase 6: `Decidable (tValid φ)` [COMPLETED]

**RESOLVED by task 513** (`specs/archive/513_generalize_tableau_soundness_chain_over_spec`,
archived-COMPLETED). This phase was recorded `[BLOCKED]` in v1 on a missing driver-level T
soundness lemma; task 513 delivered exactly that generic soundness chain, and the Phase-6 target
artifacts are now live and sorry-free.

- **Delivered (verified in-tree, `FrameCompleteness.lean`):**
  - `modalTableauT_sound (φ) (h : modalTableauT φ = .closed) : tValid φ` — `:1212` (task 513
    Phase 5: T soundness discharges, lifting the committed rule-level
    `modalTBoxSelf_sound`/`modalTDiaNegSelf_sound` through the generalized fuel loop over
    `branchSatisfiableIn reflFC`).
  - `tValid_decides (φ0) : modalTableauT φ0 = .closed ↔ tValid φ0` — `:1298` (combines
    `modalTableauT_sound` with `modalTableauT_complete` via the `ModalTableauResult` dichotomy;
    mirrors `modalTableau_decides`).
  - `instDecidableTValid (φ0) : Decidable (tValid φ0)` — `:1311` (runs `modalTableauT φ0` and
    consults `tValid_decides`; no `Fintype Atom` assumption — the tableau computation is the
    decision procedure; mirrors `instDecidableKValid`).
  - **Verification:** genuinely sorry-free; `#print axioms` reports only
    `propext`/`Classical.choice`/`Quot.sound`.
- **Files:** `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (soundness lift, task 513),
  `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (`tValid_decides`, `instDecidableTValid`).

*(The original Phase-6 blocker record — the ~500-line `modalStepBranch_preserves_sat` soundness
generalization and the structural finding that the ambient Kripke model is never replaced — is
preserved in plan v1 §Phase 6. It correctly predicted the fix and correctly recommended spawning
it as a dedicated task, which became task 513.)*

---

### Phase 7: Interface documentation, downstream contract, and final CI [COMPLETED]

- **Goal:** Document the reusable `RuleApplicationSpec` interface for downstream tasks, run full CI,
  write the completion summary.
- **Delivered:** `GenericDriver.lean` module docstring (seven-field interface, T/S5/B
  downstream-reuse table, S4 exclusion, plus the "Completeness Is Generic; Soundness Is Not Yet"
  narrative — see caveat below); full CSLib CI green (`lake build`, `checkInitImports`, `lint`,
  `lint-style`, `test`, `mk_all --module`, `shake`); final `lean_verify` sweep on the delivered
  top decls; summary written.
- **v2 correction:** v1 marked this `[PARTIAL]` **solely** because Phase 6 was then `[BLOCKED]` and
  `tValid_decides`/`instDecidableTValid` did not yet exist. Both now exist and are verified, so this
  phase is **[COMPLETED]**. **Residual documentation debt (out of scope here):** the
  `GenericDriver.lean:131/149` docstring still narrates Phase 6 as `[BLOCKED]` on soundness — now
  stale (task 513 closed it). Flag for a docstring sweep; do not treat as a correctness gap.
- **Files:** `Cslib/Logics/Modal/Tableau/GenericDriver.lean`;
  `specs/503_.../summaries/01_generalize-tableau-driver-tsystem-summary.md`.

---

## Closure Recommendation

**The stated deliverable terminus — `Decidable (tValid φ)` — is satisfied.** `instDecidableTValid`
is live and sorry-free at `FrameCompleteness.lean:1311`, backed by `tValid_decides` (`:1298`) and
`modalTableauT_sound` (`:1212`).

**No generic-driver scope remains as 503 open work.** The 91-call-site parametrization across
`Saturation.lean`/`FmpMeasure.lean`/`CompletenessLoop.lean` was carried through in full by 503's
own phases plus the three spawned tasks (507 termination, 510 completeness/loop invariant, 513
soundness). The interface demonstrably served the entire downstream family: `instDecidableTValid`,
`instDecidableBValid`, `instDecidableS5Valid`, and `instDecidableFiveValid` are all live and
sorry-free. The T-decidability target was the real terminus; the generalization was the means, and
it is complete.

**Recommended action → move task 503 to `[COMPLETED]`** in `state.json` (this revision does not
apply the transition). Suggested `completion_summary`:

> Generic K tableau driver parametrized over `RuleApplicationSpec` across
> Saturation/FmpMeasure/CompletenessLoop (with spawned tasks 507/510/513 delivering the
> termination, completeness-loop, and soundness generalizations); K re-derived with zero
> regression; T instantiated and `Decidable (tValid φ)` delivered sorry-free
> (`instDecidableTValid`, FrameCompleteness.lean:1311). Off-ROADMAP.

**Two non-blocking follow-ups** (do not hold 503 open):
1. **Docstring cleanup** (Lean-code, deferred): correct the stale `[BLOCKED]` Phase-6 narrative in
   `GenericDriver.lean:131/149`.
2. **Dependency hygiene** (audit §C, unrelated to 503's closure): the audit's other edge
   corrections (504/505/515 mislabels, 512↔517 cycle) are separate `/revise` targets.

## Testing & Validation

Verified in-tree at revision time (no new build run by this metadata-only revision; facts
ground-truthed by inspection):
- `tValid_decides` / `instDecidableTValid` present at `FrameCompleteness.lean:1298`/`:1311`,
  sorry-free, standard axiom trio only.
- `modalTableauT_sound` present at `:1212` (task 513).
- `ModalLoopInvGen` present at `CompletenessLoop.lean:134` (task 510).
- Downstream `instDecidableBValid`/`instDecidableS5Valid`/`instDecidableFiveValid` all live.
- Zero-regression gate: `modalTableau_decides`/`instDecidableKValid` unchanged (K is the trivial
  instantiation).

Any subsequent Lean edit (e.g. the docstring cleanup) must re-run the full CSLib CI:
`lake build`, `checkInitImports`, `lint`, `lint-style`, `test`, `mk_all --module`, `shake`.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Tableau/Saturation.lean` — generic `*Gen` driver defs; K re-derived.
- `Cslib/Logics/Modal/Tableau/GenericDriver.lean` — `RuleApplicationSpec` (7 fields),
  `modalApplyOne_spec`, downstream-contract docstring (with one stale `[BLOCKED]` narrative to be
  swept).
- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` — generic termination step lemmas (task 507);
  two additive T helpers.
- `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` — `ModalLoopInvGen` + bridge (task 510).
- `Cslib/Logics/Modal/Tableau/TDriver.lean` — T driver instances, `modalApplyOneT_spec`.
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — T truth lemma, `tValid` completeness,
  `modalTableauT_sound`, `tValid_decides`, `instDecidableTValid`.
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` — driver-level T soundness lift (task 513).
- `specs/503_.../summaries/01_generalize-tableau-driver-tsystem-summary.md`.

## Rollback/Contingency

This revision is metadata/plan-only; nothing to roll back in code. The recommended `state.json`
`[BLOCKED]`→`[COMPLETED]` transition is reversible via git and via a subsequent `/revise` if a
downstream consumer later surfaces a genuine 503-scoped gap (none identified). Each underlying Lean
phase remains a self-contained, revertible commit at a green milestone.
