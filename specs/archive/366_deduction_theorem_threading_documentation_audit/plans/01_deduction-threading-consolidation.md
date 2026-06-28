# Implementation Plan: Task #366 — Deduction-Theorem Threading & Documentation Audit

- **Task**: 366 - deduction_theorem_threading_documentation_audit
- **Status**: [COMPLETED]
- **Effort**: 7 hours
- **Dependencies**: None (task-364 Tableau/Bimodal-Separation subtree is OUT OF SCOPE)
- **Research Inputs**: specs/366_deduction_theorem_threading_documentation_audit/reports/01_deduction-threading-audit.md
- **Artifacts**: plans/01_deduction-threading-consolidation.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

The generic algebraic deduction-theorem seam (`algebraic_has_deduction_theorem` in
`GenericMCS.lean` over `list_deduction_theorem`) is already complete for the
single-frame-class deduction theorems (Propositional, Modal, Temporal `FrameClass.Base`).
Two material residues remain — fc-polymorphic hand WF-recursion bodies in Bimodal
`Core/DeductionTheorem.lean` (R1) and Temporal `DenseMCS.lean` (R2) — plus a stale
documentation surface and a factual correction (`deductionWithMem` is load-bearing, not
callerless). This plan opens with a GO/NO-GO feasibility spike that decides between
**Option A (full consolidation of R1/R2 through a per-`fc` bridge)** and **Option B
(documented design boundary, retain structural recursion)**, then executes the chosen
path, and finishes with the three documentation deliverables (D1/D2/D3) and the
`deductionWithMem` keep-annotate. The definition of done: all three scoped build batches
from report §3 stay green and sorry-free, no new `sorry`/axiom is introduced under either
option, public signatures are unchanged, and the full-library RED from task-364 is left
untouched.

### Research Integration

- **Residue inventory (§1.2)**: R1 = Bimodal `deductionTheorem`/`deductionWithMem`
  (`Core/DeductionTheorem.lean` L80-130, L151-200, `termination_by h.height`); R2 =
  Temporal `deductionTheoremFc`/`deductionWithMemFc` (`DenseMCS.lean` L178-217, L220-264,
  `termination_by d.height`). Only the `FrameClass.Base` instances are seam-routed today.
- **Root cause (§1.3)**: the bridge (`bimodal_deriv_iff_algebraic`,
  `temporal_deriv_iff_algebraic`) is built at a single fixed proof system
  (`HilbertTM`/`temporalDerivationSystem` at `FrameClass.Base`). R1/R2 are polymorphic over
  arbitrary `fc : FrameClass`, for which no `MinimalHilbert` instance exists. The spike
  (Phase 1) tests whether such a per-`fc` instance is constructible cleanly.
- **Factual correction (§1.4)**: PL `deductionWithMem` has 4 external callers
  (`IntLindenbaum:148`, `MinLindenbaum:131`, `StrongCompleteness:447`,
  `SemanticConsequence:159`); Modal has 1 (`Completeness:542`). KEEP + annotate, do NOT delete.
- **Doc deliverables (§4)**: D1 authoritative docstring in `GenericMCS.lean`; D2 revise four
  module docstrings (Bimodal `Core/DeductionTheorem.lean` docstring is STALE); D3 resolve
  `## References` cross-refs to D1.
- **Verification (§3)**: three scoped `lake build` batches (655/998/962 jobs) all green;
  full-library build RED only from task-364 (out of scope).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (not provided in delegation context).

## Goals & Non-Goals

**Goals**:
- Resolve R1/R2 via the GO/NO-GO spike: pursue Option A (full consolidation) when a per-`fc`
  `InferenceSystem` + `MinimalHilbert` instance typechecks without new axioms/sorry; otherwise
  fall back cleanly to Option B (documented design boundary).
- Under Option A: reroute `Bimodal.deductionTheorem {fc}` / `deductionWithMem` and
  `Temporal.deductionTheoremFc` / `deductionWithMemFc` through the generalized bridge and
  delete the `termination_by`/`decreasing_by` hand-recursion bodies, keeping public
  signatures byte-for-byte identical.
- Deliver D1 (one authoritative architecture docstring in `GenericMCS.lean`), D2 (revise four
  module docstrings, correcting the stale Bimodal narrative), and D3 (cross-refs to D1).
- KEEP + annotate PL (4 callers) and Modal (1 caller) `deductionWithMem` as thin
  `removeAll`-aware wrappers over the seam-routed `deductionTheorem`.
- Keep all three scoped build batches green and sorry-free; `lake exe checkInitImports` clean
  on touched files.

**Non-Goals**:
- No new `sorry` and no new `axiom` under any circumstances — prefer Option B over either.
- Do NOT touch the task-364 Tableau / Bimodal-Separation subtree
  (`Cslib/Logics/Modal/Tableau/Soundness.lean`, 68 pre-existing errors) or attempt a
  full-library `lake build`.
- Do NOT delete PL or Modal `deductionWithMem` (load-bearing).
- No change to any public signature of `deductionTheorem` / `deductionWithMem(Fc)` (≈25+ raw
  call sites must remain valid).
- No behavioral change to any proof term consumed downstream.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Per-`fc` `MinimalHilbert` instance is not constructible without new axioms | M | M | This is exactly what Phase 1 spike tests; on failure, fall back to Option B (no code change, document the boundary). Decision is explicit and reversible. |
| Pressure to force Option A with a `sorry`/axiom | H | L | ABSOLUTE CONSTRAINT: prefer Option B over any `sorry`/axiom. Phase 1 exit criterion is "instance typechecks WITHOUT new axioms/sorry"; any axiom/sorry => NO-GO. |
| Rerouting R1/R2 drifts a public signature, breaking ~25+ raw call sites | H | L | Keep `def deductionTheorem`/`deductionWithMem(Fc)` signatures identical; only the body changes. Verify via scoped build batch 2+3 (consumers + equivalence). |
| Accidentally building/editing the task-364 RED subtree | M | L | Scope every `lake build` to the explicit module lists in report §3; never run bare `lake build`. Document the exclusion in the summary. |
| Stale Bimodal docstring rewritten to wrong narrative (says "seam" when B retained) | M | M | D2 wording is branch-dependent: Phase 4 reads the Phase 1 decision outcome and writes the matching narrative (A => seam; B => why fc-polymorphic body keeps structural recursion). |
| Regression of sorry-free status in any in-scope module | H | L | `grep` for `sorry`/`admit` across touched files after each code phase; scoped builds gate every change. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel. This plan is sequential by design: the
Phase 1 decision gate determines whether Phase 2 is a reroute (A) or a documented no-op (B),
and the documentation phases (3-5) must reflect the final code state.

---

### Phase 1: GO/NO-GO fc-bridge feasibility spike (decision gate) [COMPLETED]

- **Goal:** Decide Option A vs Option B by attempting to construct a per-`fc`
  `InferenceSystem` + `MinimalHilbert` instance for the `HilbertOf`-style tag type at an
  *arbitrary* `fc : FrameClass`. GO (Option A) iff that instance typechecks with NO new
  axioms and NO `sorry`; otherwise NO-GO (Option B).
- **Tasks:**
  - [ ] Read the fixed-`fc` bridge construction to understand the seam shape:
    `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` (L79-215, the
    `bimodalAlgDS = algebraicDerivationSystem (S := Bimodal.HilbertTM)` and
    `bimodal_deriv_iff_algebraic` / `list_deriv_to_tree` hardcoded to
    `DerivationTree FrameClass.Base`), plus `Foundations/Logic/Metalogic/GenericMCS.lean`
    (`algebraic_has_deduction_theorem`, `HasMinimalAxioms`, `MinimalHilbert`).
  - [ ] In a scratch location, attempt to generalize the bridge: build an
    `InferenceSystem`/`MinimalHilbert` instance for the `HilbertOf`-style tag type
    parameterized by an arbitrary `fc : FrameClass` (mirror the Temporal
    `temporal_deriv_iff_algebraic` at `FrameClass.Base`). Use `lean_multi_attempt` /
    scoped build to check typechecking.
  - [ ] Verify the candidate instance introduces NO `axiom` and NO `sorry`
    (`lean_verify` / `grep`). Any axiom/sorry => NO-GO.
  - [ ] Record the decision (GO=Option A, or NO-GO=Option B) with the concrete reason
    (e.g., which `MinimalHilbert` field cannot be discharged at arbitrary `fc`) at the top
    of Phase 2's working notes and in the eventual summary.
- **Timing:** 1.5 hours
- **Depends on:** none
- **Files to inspect (read-only this phase):**
  - `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean`
  - `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean`
  - `Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean` (Base bridge reference)
  - `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` (R2 signatures)
  - `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean` (R1 signatures)
- **Verification:**
  - A written, justified decision: GO (Option A) or NO-GO (Option B).
  - If GO: the spike instance typechecks in isolation with no new axioms/sorry (evidence
    captured).
  - If NO-GO: the specific obstruction is named (the un-dischargeable instance field at
    arbitrary `fc`).

---

### Phase 2: Execute the A/B decision — reroute R1/R2 (Option A) or record boundary (Option B) [COMPLETED]

- **Goal:** Under Option A, reroute the two residues through the generalized bridge and
  delete the hand recursion, preserving public signatures and sorry-free status. Under
  Option B, make no code change and capture the design boundary for the docstrings.
- **Tasks (Option A — only if Phase 1 = GO):**
  - [ ] Generalize `Core/GenericMCSBridge.lean` (and the Temporal bridge layer) to arbitrary
    `fc : FrameClass` per the validated Phase 1 instance.
  - [ ] Reroute `Bimodal.deductionTheorem {fc}` (`Core/DeductionTheorem.lean` L151-200) and
    internal `deductionWithMem` (L80-130) through the generalized bridge; delete the
    `match`/`termination_by h.height`/`decreasing_by` bodies. Keep the public signatures
    byte-for-byte identical.
  - [ ] Reroute `Temporal.deductionTheoremFc` (`DenseMCS.lean` L220-264) and
    `deductionWithMemFc` (L178-217) likewise; delete `termination_by d.height`/`decreasing_by`.
    Repoint `temporal_has_deduction_theorem_fc` (L269-274) at the seam.
  - [ ] `grep` the touched files for `sorry`/`admit`/`axiom` — must be none.
  - [ ] Run scoped build batch 1 (deduction core + seam, 655 jobs) and batch 2
    (consumers, 998 jobs) green.
- **Tasks (Option B — only if Phase 1 = NO-GO):**
  - [ ] Make NO code change to R1/R2. Confirm both residues still build green and sorry-free
    (scoped batch 1).
  - [ ] Capture the precise design-boundary statement (the seam services the
    `FrameClass.Base` instances the generic MCS framework consumes; fc-polymorphic public
    defs retain structural recursion by necessity, with the Phase 1 obstruction named) for
    use in D1 (Phase 3) and D2 (Phase 4).
- **Timing:** 2 hours
- **Depends on:** 1
- **Files to modify (Option A only):**
  - `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` - generalize bridge to arbitrary `fc`
  - `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean` - reroute R1, delete hand recursion
  - `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` - reroute R2, delete hand recursion
  - (Temporal bridge layer file, if separate) - generalize to arbitrary `fc`
- **Verification:**
  - Option A: no `termination_by`/`decreasing_by` remain in the two residue files; public
    signatures unchanged; scoped batches 1+2 green and sorry-free.
  - Option B: no code change; scoped batch 1 green; boundary statement recorded.

---

### Phase 3: D1 — authoritative architecture docstring in GenericMCS.lean [COMPLETED]

- **Goal:** Add ONE authoritative architecture docstring explaining the predicate→type
  `HilbertOf` bridge and one-deduction-theorem inheritance, with an explicit frame-class
  caveat that reflects the Phase 1/2 outcome.
- **Tasks:**
  - [ ] In `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` (preferred home — it owns
    `algebraic_has_deduction_theorem` and `HasMinimalAxioms`), add the D1 docstring covering:
    - The `listImp` → `ListDeriv` → `algebraic_has_deduction_theorem` chain (one generic
      proof; no per-logic tree induction).
    - The predicate→type pattern: `HasMinimalAxioms Axioms` (predicate) →
      `HilbertOf Axioms` empty tag type → `MinimalHilbert (HilbertOf Axioms)` instance →
      algebraic path, with the per-logic `*_deriv_iff_algebraic` bridge closing back to
      `DerivationTree`.
    - The frame-class caveat: the seam services single-frame-class systems
      (`FrameClass.Base` / `HilbertTM`); state the R1/R2 outcome — under Option A, the
      fc-polymorphic Bimodal/Temporal theorems now also route through the generalized bridge;
      under Option B, they retain structural recursion and why (name the Phase 1 obstruction).
  - [ ] Confirm no behavioral/code change — docstring only.
- **Timing:** 1 hour
- **Depends on:** 2
- **Files to modify:**
  - `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` - add D1 architecture docstring
- **Verification:**
  - D1 docstring present, references the seam chain and the predicate→type pattern, and its
    frame-class caveat matches the Phase 1/2 decision.
  - Scoped batch 1 still green (docstring change does not break the build).

---

### Phase 4: D2 module docstrings + deductionWithMem keep-annotate [COMPLETED]

- **Goal:** Revise the four module docstrings to the consolidated reality and annotate the
  load-bearing PL/Modal `deductionWithMem` helpers. Correct the false "zero callers" framing.
- **Tasks:**
  - [ ] `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean`: docstring already
    describes the re-route; add a one-line note that `deductionWithMem` has **4 real
    callers** (`IntLindenbaum:148`, `MinLindenbaum:131`, `StrongCompleteness:447`,
    `SemanticConsequence:159`) and a cross-ref to D1. Remove any "zero callers / candidate
    for deletion" framing.
  - [ ] PL `deductionWithMem` (L85-96) + Modal `deductionWithMem` (Modal
    `DeductionTheorem.lean` L82-93, caller `Completeness:542`): add the docstring note that
    each is a thin `removeAll`-aware wrapper over the seam-routed `deductionTheorem`, KEPT
    because remove-all-occurrences is the shape Lindenbaum/consistency elimination requires.
    Do NOT delete either.
  - [ ] `Cslib/Logics/Propositional/Metalogic/GenericMCSBridge.lean`: add cross-ref to D1
    (docstring already strong).
  - [ ] `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean`: replace the STALE
    hand-recursion narrative (L26-41). Branch on Phase 1/2 outcome: under Option A, rewrite
    to describe the seam routing; under Option B, state explicitly *why* the fc-polymorphic
    body cannot use the seam (Phase 1 obstruction), cross-referencing D1 and the
    Base-only `bimodalHasDeductionTheorem` instance.
  - [ ] `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean`: add a docstring note on
    `deductionTheoremFc`/`deductionWithMemFc` mirroring the Bimodal decision (R2 parallels R1).
- **Timing:** 1.5 hours
- **Depends on:** 3
- **Files to modify:**
  - `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` - correct caller framing + annotate
  - `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` - annotate Modal `deductionWithMem`
  - `Cslib/Logics/Propositional/Metalogic/GenericMCSBridge.lean` - cross-ref D1
  - `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean` - replace stale narrative
  - `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` - fc deduction-theorem docstring note
- **Verification:**
  - No "zero callers"/"candidate for deletion" language remains anywhere.
  - Bimodal docstring no longer presents hand-recursion as the intended design (matches A/B).
  - PL/Modal `deductionWithMem` retained with wrapper annotation; scoped batches 1+2 green.

---

### Phase 5: D3 cross-refs + scoped CI verification [COMPLETED]

- **Goal:** Resolve `## References` cross-refs across all four DeductionTheorem/bridge files
  to point at D1, then run the full scoped CI gate.
- **Tasks:**
  - [ ] Ensure each `## References` block points to D1 (in `GenericMCS.lean`) and to the
    sibling logics' files, across:
    - `Propositional/Metalogic/DeductionTheorem.lean`
    - `Propositional/Metalogic/GenericMCSBridge.lean`
    - `Bimodal/Metalogic/Core/DeductionTheorem.lean`
    - `Temporal/Metalogic/DenseMCS.lean`
    (and `Modal/Metalogic/DeductionTheorem.lean` if it carries a References block).
  - [ ] Run scoped build batch 1 (deduction core + seam, 655 jobs).
  - [ ] Run scoped build batch 2 (consumers: PL StrongCompleteness/MinLindenbaum/
    IntLindenbaum/MCS/SemanticConsequence, Modal Completeness/MCS, Temporal MCS/Completeness,
    Bimodal Completeness, 998 jobs).
  - [ ] Run scoped build batch 3 (PL NaturalDeduction Equivalence/FromHilbert, Bimodal
    Core MaximalConsistent, Temporal DenseCompleteness, 962 jobs).
  - [ ] Run `lake exe checkInitImports` on the touched files.
  - [ ] `grep` all touched files for `sorry`/`admit`/`axiom` — confirm none.
  - [ ] Do NOT run a bare full-library `lake build` (RED from task-364); note the exclusion.
- **Timing:** 1 hour
- **Depends on:** 4
- **Files to modify:**
  - `## References` blocks in the four DeductionTheorem/bridge files listed above
- **Verification:**
  - All three scoped batches return `Build completed successfully` (655/998/962 jobs).
  - `lake exe checkInitImports` clean on touched files.
  - No `sorry`/`admit`/new `axiom` in any touched file.

---

## Testing & Validation

- [ ] Scoped build batch 1 (deduction core + seam, 655 jobs) green.
- [ ] Scoped build batch 2 (consumers, 998 jobs) green.
- [ ] Scoped build batch 3 (equivalence + extras, 962 jobs) green.
- [ ] `lake exe checkInitImports` clean on all touched files.
- [ ] `grep -nE 'sorry|admit' ` across touched files returns nothing new; no new `axiom`.
- [ ] Public signatures of `deductionTheorem` / `deductionWithMem(Fc)` unchanged (≈25+ raw
      call sites still compile within scoped batches).
- [ ] (Option A) No `termination_by`/`decreasing_by` remain in `Core/DeductionTheorem.lean`
      or `DenseMCS.lean`.
- [ ] No edit to `Cslib/Logics/Modal/Tableau/Soundness.lean` or any task-364 subtree; no bare
      full-library `lake build` attempted.

## Artifacts & Outputs

- plans/01_deduction-threading-consolidation.md (this file)
- summaries/01_deduction-threading-consolidation-summary.md (on implementation)
- D1: architecture docstring in `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean`
- D2: revised docstrings in PL/Modal `DeductionTheorem.lean`, PL `GenericMCSBridge.lean`,
  Bimodal `Core/DeductionTheorem.lean`, Temporal `DenseMCS.lean`
- D3: resolved `## References` cross-refs across the four DeductionTheorem/bridge files
- (Option A only) generalized per-`fc` bridge + rerouted R1/R2 with hand recursion removed
- A recorded GO/NO-GO decision (Option A vs B) with justification

## Rollback/Contingency

- All changes are confined to the in-scope deduction-theorem modules and their docstrings;
  revert via `git checkout` on the touched files. No state migration.
- **Primary contingency (Phase 1 NO-GO)**: fall back to Option B — retain R1/R2 structural
  recursion, document the boundary. This requires no code change and is the safe default.
- **Absolute constraint**: if Option A cannot be completed without a `sorry` or new `axiom`,
  abandon Option A and take Option B. Never commit a `sorry`/axiom to force consolidation.
- If any scoped batch goes RED after a doc-only change, the change is reverted (docstrings
  must not affect the build); investigate before re-applying.
