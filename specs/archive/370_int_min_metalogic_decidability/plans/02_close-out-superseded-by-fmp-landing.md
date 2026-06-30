# Implementation Plan: Task #370 — Close-Out (Superseded by FMP Landing on main)

- **Task**: 370 - int_min_metalogic_decidability
- **Status**: [COMPLETED] — superseded; all deliverables landed on main via tasks 411/421 (+ reconciliation 422)
- **Effort**: 0 hours (no residual implementable work)
- **Dependencies**: None (411 and 421 already merged to main)
- **Research Inputs**: specs/370_int_min_metalogic_decidability/reports/01_int-min-decidability-fmp-vs-lj.md
- **Artifacts**: plans/01_int-min-fmp-decidability.md (superseded original); plans/02_close-out-superseded-by-fmp-landing.md (this close-out)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

This is a **close-out revision**. Task 370's original 7-phase FMP plan
(`plans/01_int-min-fmp-decidability.md`) targeted CREATING sorry-free
`Decidable (Derivable IntPropAxiom φ)` and `Decidable (Derivable MinPropAxiom φ)` via the finite
model property — building `IntFinWorld`/`MinFinWorld`, the `Fintype` instance, the finite truth
lemma, the finite (Zorn-free) Lindenbaum witness, and `int_fmp`/`min_fmp`.

**That work has already landed on `main`.** Two now-completed tasks delivered the exact artifacts
the 370 plan enumerated:

- **Task 411** (commit `af9daf5e`, "adopt complete sorry-free IntDecidability") created
  `Cslib/Logics/Propositional/Metalogic/IntDecidability.lean`.
- **Task 421** (commit `6fb9f38b`, "complete implementation — Min-side FMP decidability") created
  `Cslib/Logics/Propositional/Metalogic/MinDecidability.lean`.
- **Task 422** (in flight, commits `22b4ee84`, `e01440f3`, `0a24c9af`) is reconciling the two
  decidability routes — it demoted the FMP instances to named `noncomputable def`s and added
  "two routes, distinct roles" docstrings. 422 owns the header/docstring/instance regions of both
  files until it completes. **370 does not touch 422's territory.**

The original plan's central premise — *"Both existing Int/Min decidability instances are
sorry-tainted via the tableau"* and *"the FMP layer does not yet exist"* — is now **false**. The
FMP layer exists and is **sorry-free** (axiom profile `{propext, Classical.choice, Quot.sound}`;
no `sorryAx`; independent of `intuitionisticTableau_complete` / `minimalTableau_complete`).

**Recommendation: mark task 370 [COMPLETED] as superseded.** There is no concrete, non-redundant
residual deliverable left to implement. See "Residual Gap Analysis" below for the explicit
goal-by-goal accounting and why the one remaining nuance (instance registration) is owned by 422
and must not be re-opened here.

### Research Integration

No new research reports were generated for this revision; the revision is driven entirely by the
state of `main`. The investigation that produced this close-out:

- Read `IntDecidability.lean` (24,869 bytes) and `MinDecidability.lean` (22,609 bytes) on `main`.
- Confirmed the FMP definitions are sorry-free: every `sorry` token in both files appears only in
  docstrings describing the *separate tableau route's* 317-owned `truthLemma` sorry
  (`Tableau/Intuitionistic/Scheme.lean:234`), never as a tactic in an FMP definition. The
  module-summary docstrings explicitly state the FMP `decidableDerivable…FMP` defs carry
  `{propext, Classical.choice, Quot.sound}` and "no `sorryAx`".
- Confirmed task 422's plan and in-flight state (`phase_4`, CI verification) and its standing
  decision: **tableau instances stay canonical; the FMP results are exposed as named
  `noncomputable def`s, not registered instances**. Re-registering a competing FMP `instance`
  would conflict with 422 and is therefore explicitly excluded from any 370 residual scope.

### Prior Plan Reference

Supersedes `plans/01_int-min-fmp-decidability.md`. That plan's phase structure is preserved below
(in the goal mapping) as the checklist against which "fully superseded" is verified. No phase
from plan 01 is discarded or reopened — each is reconciled to a landed artifact.

### Roadmap Alignment

No `roadmap_path` provided in delegation context; ROADMAP.md not consulted.

## Goals & Non-Goals

**Goals** (of this close-out revision):
- Establish, goal-by-goal, that every deliverable of plan 01 is already satisfied on `main`.
- Record the landing commits and exact symbol names for traceability.
- Recommend the disposition (completed-as-superseded) and update task state accordingly.
- Confirm the orphan scratch file `IntFMPSpike.lean` is gone (no cleanup needed).

**Non-Goals**:
- Any new Lean proof work (the FMP layer is complete and sorry-free on `main`).
- Registering a competing FMP `Decidable` instance — **owned by / deliberately excluded by 422**.
- Discharging the four tableau completeness `sorry`s (task 317 — out of scope, as in plan 01).
- Factoring Int/Min into a shared parametric FMP layer — **explicitly deferred by task 422**
  (commit `0a24c9af`, "factoring deferred"); not a 370 goal.
- Touching `IntDecidability.lean` / `MinDecidability.lean` header/docstring/instance regions
  while 422 is in flight (territory conflict).

## Residual Gap Analysis

Mapping each goal from plan 01 ("Goals & Non-Goals" + "Implementation Phases") to its landed
artifact on `main`:

| Plan 01 Goal / Phase | Landed Artifact (symbol) | File | Landed by |
|----------------------|--------------------------|------|-----------|
| Sorry-free `Decidable (Derivable IntPropAxiom φ)`, tableau-independent | `decidableDerivableIntPropAxiomFMP` (noncomputable def, `decidable_of_iff … (int_fmp φ).symm`) | IntDecidability.lean:486 | 411 (`af9daf5e`) |
| Sorry-free `Decidable (Derivable MinPropAxiom φ)`, tableau-independent | `decidableDerivableMinPropAxiomFMP` | MinDecidability.lean:443 | 421 (`6fb9f38b`) |
| Phase 2: subformula closure infrastructure | `Proposition.subformulas`, `IsSubformula`, closure lemmas, `self_mem_subformulas` | Subformula.lean | 334 (pre-existing) |
| Phase 3: `IntFinWorld` + `Fintype` + `Preorder` | `IntFinWorld`, `instFintypeIntFinWorld` (`Fintype.ofInjective` into `Σ.powerset`), `instPreorderIntFinWorld`, `intFinWorld_propConsistent` | IntDecidability.lean:106–166 | 411 |
| Phase 1/3: finite (Zorn-free) Lindenbaum witness | `int_fin_imp_witness` (infinite-canonical-restricted-to-Σ route) | IntDecidability.lean:221 | 411 |
| Phase 4: valuation + upward closure + finite truth lemma | `intFinVal`, `intFinVal_upward_closed`, `int_fin_truth_lemma` | IntDecidability.lean:288–324 | 411 |
| Phase 5: `int_fmp` + decidable | `int_fmp`, `decidableDerivableIntPropAxiomFMP` | IntDecidability.lean:440–488 | 411 |
| Phase 6: full Min mirror | `MinFinWorld`, `instFintypeMinFinWorld`, `minFinVal`, `minFinBotForces`, `min_fin_imp_witness`, `min_fin_truth_lemma`, `min_fmp`, `decidableDerivableMinPropAxiomFMP` | MinDecidability.lean | 421 |
| Phase 7: CI green on the new files | Files are on `main` and build; CI re-verification is in flight under 422 phase 4 | both | 421/422 |
| Phase 1: orphan `IntFMPSpike.lean` disposition | File removed (curated swap); not referenced anywhere, not in `Cslib.lean` | n/a | 411 (`af9daf5e`) |

**Candidate residual deliverables explicitly checked and rejected:**

1. *A reusable FMP layer beyond what 411/421 exposed.* — None. 411/421 expose the complete layer
   plan 01 Goal 3 enumerated (world type, `Fintype`, `Preorder`, valuation + upward closure,
   imp-witness, finite truth lemma, `…_fmp`, plus the `IntPrimeDCCS`/`MinPrimeTheory`→world
   restriction helpers at IntDecidability.lean:412 / MinDecidability.lean:379). Nothing in plan 01
   is unexposed.
2. *A subformula-closure or finite-Lindenbaum lemma not yet landed.* — None. Subformula closure
   is in `Subformula.lean` (334); the finite Lindenbaum obligation is realized as
   `int_fin_imp_witness` / `min_fin_imp_witness` plus the prime-DCCS-restriction helpers. Landed.
3. *Registered `Decidable` instances.* — Deliberately **not** a residual gap. Task 422's standing
   decision keeps the tableau instance canonical and the FMP path as a named `noncomputable def`.
   Re-registering a competing FMP instance would conflict with 422 and is excluded.
4. *Shared parametric factoring of Int/Min.* — Not a 370 goal; explicitly **deferred by 422**.

**Conclusion: no meaningful, non-redundant residual gap exists. Task 370 is fully superseded.**

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Re-opening 370 as implementation would conflict with 422's in-flight edits to the two files | M | L | Close out 370 as superseded; do not touch `IntDecidability.lean` / `MinDecidability.lean` while 422 is in flight |
| Misreading docstring `sorry` mentions as live sorries in the FMP path | L | L | Verified: all `sorry` tokens are in docstrings referencing the tableau route's 317 sorry; FMP defs carry only `{propext, Classical.choice, Quot.sound}` |
| 422 not yet CI-green could be read as 370 incomplete | L | L | 370's deliverables (the sorry-free FMP defs + layer) are on `main` and build independently; 422's remaining work is docstring/reconciliation polish, not a 370 deliverable |

## Implementation Phases

### Phase 1: Disposition — Mark 370 Completed-as-Superseded [COMPLETED]

**Goal**: Record that all plan-01 deliverables are landed and close the task; no Lean work.

**Tasks**:
- [x] Confirm `IntDecidability.lean` (411) and `MinDecidability.lean` (421) on `main` provide the
      full FMP layer and sorry-free `decidableDerivable{Int,Min}PropAxiomFMP` defs.
- [x] Confirm the orphan `IntFMPSpike.lean` is gone (removed by 411's curated swap; not in barrel).
- [x] Confirm 422 owns the file header/docstring/instance regions and that no competing FMP
      instance should be registered by 370.
- [x] Produce this close-out plan and recommend `[COMPLETED]` (superseded).

**Timing**: 0 hours

**Depends on**: none

**Files to modify**: none (Lean tree untouched; state.json/handoff updated by orchestrator postflight).

**Verification**:
- Symbols listed in "Residual Gap Analysis" resolve in the named files at the cited lines.
- No `sorry`/`admit` tactic in either FMP definition (docstring mentions excepted).

## Testing & Validation

No code changes, so no new build/test obligations are introduced by this revision. The relevant
verification was performed during investigation:

- [x] `IntDecidability.lean` and `MinDecidability.lean` exist on `main` and are in the `Cslib.lean`
      barrel.
- [x] FMP definitions are sorry-free (axiom profile `{propext, Classical.choice, Quot.sound}` per
      module docstrings; no `sorryAx`; tableau-independent).
- [x] Orphan `IntFMPSpike.lean` removed; not referenced anywhere.
- [ ] (Owned by 422) full CI pipeline green after the reconciliation pass — not a 370 obligation.

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Metalogic/IntDecidability.lean` (task 411) — full Int FMP layer +
  `decidableDerivableIntPropAxiomFMP`.
- `Cslib/Logics/Propositional/Metalogic/MinDecidability.lean` (task 421) — full Min FMP mirror +
  `decidableDerivableMinPropAxiomFMP`.
- `specs/370_int_min_metalogic_decidability/plans/02_close-out-superseded-by-fmp-landing.md`
  (this close-out plan).

## Rollback/Contingency

- **If 370 is later found to need a registered FMP instance**: do NOT add it here while 422 is in
  flight — coordinate with task 422, which holds the canonical-instance decision.
- **If a genuine reusable-layer extraction is wanted** (shared parametric Int/Min FMP): open a new
  task; it is 422's deferred concern, not a reopening of 370.
- **Zero-debt invariant** preserved: no `sorry`, `admit`, or new axiom is introduced by this
  close-out (no code is touched).
