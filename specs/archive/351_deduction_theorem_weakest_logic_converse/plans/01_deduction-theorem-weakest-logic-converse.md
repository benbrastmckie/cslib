# Implementation Plan: Task #351 - Deduction Theorem Weakest-Logic Converse

- **Task**: 351 - deduction_theorem_weakest_logic_converse
- **Status**: [COMPLETED]
- **Effort**: 6 hours
- **Dependencies**: 350 (generic deduction-theorem consolidation; coordinate naming with 345)
- **Research Inputs**: reports/01_deduction-theorem-weakest-logic-converse.md
- **Artifacts**: plans/01_deduction-theorem-weakest-logic-converse.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Formalize the converse of the deduction-theorem characterization in CSLib: from an
axiom class bundling Modus Ponens with the Deduction Theorem property (plus reflection),
derive the K and S axioms, hence instance `MinimalHilbert` (IPL⟨→,⊤⟩) — the weakest logic
admitting the deduction theorem (Doty, Zulip CSLib Temporal Logic thread, 2026-06-25).
The mathematical heart is **already verified** in-repo: the proof terms for `dt_implies_implyK`
(2 `hdt` applications) and `dt_implies_implyS` (3 `hdt` + 3 `D.mp`) compile clean against the
live `DerivationSystem`/`HasDeductionTheorem` definitions (research report §3). This plan
therefore **transcribes verified work** rather than inventing it, and additionally performs a
spurious-`[HasBot F]` decoupling so the implicational core is `⊥`-free.

Definition of done: a new `Cslib/Foundations/Logic/Metalogic/DeductionCharacterization.lean`
file containing `dt_implies_implyK`, `dt_implies_implyS`, the `dtInferenceSystem` bridge, the
`MinimalHilbert` instance, and the characterization theorem; `DerivationSystem` and
`HasDeductionTheorem` decoupled from `[HasBot F]`; all CI gates green for this task's modules
with no NEW build failures introduced.

### Research Integration

Integrated from `reports/01_deduction-theorem-weakest-logic-converse.md`:
- **§3 (verified proof terms)**: `dt_implies_implyK`/`dt_implies_implyS` already `lake build`-clean
  against live definitions; transcribe verbatim (Phase 2).
- **§5 (decoupling)**: only `DerivationSystem` (Consistency.lean:55) and `HasDeductionTheorem`
  (:182) are trapped under a spurious `[HasBot F]`; consistency/Lindenbaum/closure props
  (lines 68-264) genuinely need `⊥` and stay (Phase 1).
- **§6 (home + bridge)**: new `DeductionCharacterization.lean`; `dtInferenceSystem` is the
  ~10-line dual of `algebraicDerivationSystem`; forward arrow reuses
  `algebraic_has_deduction_theorem` (GenericMCS.lean:65) (Phase 3).
- **§7 (zero-debt)**: no `sorry`, no new `axiom`, no choice, no `⊥` in the converse heart.
- **§8 (CI + lint)**: docstrings on every decl (docBlame); `theorem` for Prop-valued decls
  (defLemma); snake_case theorem names match `list_deduction_theorem` neighbors; update
  `Cslib.lean` barrel via `mk_all` for the new file.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Decouple `DerivationSystem` and `HasDeductionTheorem` from `[HasBot F]` (constraint removal /
  widening), leaving the consistency machinery untouched under `[HasBot F]`.
- Transcribe the verified converse theorems `dt_implies_implyK` and `dt_implies_implyS` (report §3).
- Provide the `dtInferenceSystem` bridge and a `MinimalHilbert` instance so the converse reads
  literally as "DT + MP instances the implicational Hilbert core".
- State the characterization/equivalence theorem closing the loop with the existing forward
  arrow `algebraic_has_deduction_theorem`.
- Keep every phase CI-green (scoped to this task's modules, no NEW failures), zero `sorry`,
  zero new `axiom`.

**Non-Goals**:
- Fixing the PRE-EXISTING unrelated build failures (`Bimodal.Theorems.Perpetuity.Principles`,
  the SequentCalculus namespace collision, `Modal.Tableau.Soundness`). These are not caused by
  this task; CI gates only confirm no NEW failures.
- Reworking the consistency/Lindenbaum/closure machinery (lines 68-264 of Consistency.lean),
  which legitimately depends on `⊥`.
- Reconciling `MinimalAxioms`/`IsMinimal` (task 345) beyond naming coordination.
- Introducing the type-valued `HasDeductionTree`/`HasDeductionSystem` classes as the primary
  deliverable; the Prop-valued `DerivationSystem`+`hdt` pairing is sufficient (optional corollary
  only, see Phase 3 fallback).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Structure-signature edit (`[HasBot F]` removal from `DerivationSystem`) ripples across 33 referencing files | H | L | Edit is widening (constraint removal); existing call sites keep `[HasBot F]` in scope and still elaborate. Run full `lake build` in Phase 1; revert to fallback (leave Consistency.lean untouched, put `⊥`-free class in new file) if unexpected coupling surfaces (report §5.4). |
| Pre-existing unrelated build failures mistaken for task-introduced regressions | M | H | Capture a baseline of failing modules BEFORE Phase 1 edits; CI gate = "no NEW failing modules beyond the known three" rather than "full green". |
| `dtInferenceSystem` / `MinimalHilbert` instance awkward in Lean instance resolution | M | M | Fallback (report §7): ship converse as explicit `dt_implies_implyK`/`dt_implies_implyS` + optional `HasDeductionTree → HasHilbertTree`, state characterization without the typeclass instance. Still a complete sorry-free converse. |
| Lint failures (docBlame, defLemma, naming) on new declarations | L | M | Docstring every decl; `theorem` for Prop decls; snake_case theorem names (matches `list_deduction_theorem`); namespace-wrap instances. Run `lake exe lint-style` each phase. |
| New file omitted from `Cslib.lean` barrel / missing `import Cslib.Init` | L | M | Run `lake exe mk_all --module` and `lake exe checkInitImports` in Phase 2 and Phase 3. |
| Naming collision with task 345 if it lands first | L | L | Coordinate characterization-theorem naming; prefer descriptive `deduction_theorem_iff_minimal_hilbert`-style names. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel. This plan is fully sequential
(decouple → transcribe converse → bridge + characterization), matching report §10.

---

### Phase 1: Decouple DerivationSystem / HasDeductionTheorem from [HasBot F] [COMPLETED]

- **Goal:** Remove the spurious `[HasBot F]` constraint from `DerivationSystem` (structure) and
  `HasDeductionTheorem` so the implicational core is `⊥`-free, while keeping the consistency
  machinery under `[HasBot F]`. Confirm no library-wide ripple via a full build.
- **Tasks:**
  - [ ] Record a baseline of currently-failing modules: run `lake build` and note the known
        PRE-EXISTING failures (`Bimodal.Theorems.Perpetuity.Principles`, SequentCalculus
        namespace collision, `Modal.Tableau.Soundness`). This is the "no NEW failures" reference.
  - [ ] In `Cslib/Foundations/Logic/Metalogic/Consistency.lean`, split the file-level
        `variable {F : Type*} [HasBot F] [HasImp F]` block (line 44): emit `DerivationSystem`
        and `HasDeductionTheorem` under `[HasImp F]` only.
  - [ ] Drop `[HasBot F]` from the `DerivationSystem` structure signature (line 55).
  - [ ] Re-introduce `[HasBot F]` via a fresh `variable` line immediately before `Consistent`
        (line 68 onward) so `Consistent`/`SetConsistent`/`set_lindenbaum`/closure props keep `⊥`.
  - [ ] Confirm `HasDeductionTheorem` (line 182) now elaborates under `[HasImp F]` only.
  - [ ] Run a FULL `lake build` to confirm the widening edit produces no NEW failures across the
        33 `DerivationSystem`-referencing files / 30 `HasDeductionTheorem` occurrences.
- **Timing:** ~2 hours (dominated by the full `lake build`).
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Foundations/Logic/Metalogic/Consistency.lean` - split `variable` block; drop
    `[HasBot F]` from `DerivationSystem` signature; re-add `[HasBot F]` before `Consistent`.
- **Verification:**
  - Full `lake build` shows no NEW failing modules beyond the baseline three.
  - `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
    `lake shake --add-public --keep-implied --keep-prefix` green for Consistency.lean and
    dependents (no NEW failures).
  - Spot-check (build probe): `DerivationSystem F` / `HasDeductionTheorem D` elaborate with
    only `[HasImp F]` in scope.

---

### Phase 2: Transcribe converse heart (dt_implies_implyK / dt_implies_implyS) [COMPLETED]

- **Goal:** Create `DeductionCharacterization.lean` and transcribe the verified §3 proof terms
  deriving K and S from `D.assumption`, `D.mp`, and `hdt : HasDeductionTheorem D` — no weakening,
  no `⊥`, no choice, no `sorry`, no new `axiom`.
- **Tasks:**
  - [ ] Create `Cslib/Foundations/Logic/Metalogic/DeductionCharacterization.lean` with
        `import Cslib.Init` and imports of `Consistency`, `Axioms` (and `ProofSystem`/`ListDeduction`/
        `GenericMCS` as needed for later phases).
  - [ ] Transcribe `dt_implies_implyK (D : DerivationSystem F) (hdt : HasDeductionTheorem D)
        (A B : F) : D.Deriv [] (Axioms.ImplyK A B)` verbatim from report §3 (2 `hdt` applications).
  - [ ] Transcribe `dt_implies_implyS (D : DerivationSystem F) (hdt : HasDeductionTheorem D)
        (A B C : F) : D.Deriv [] (Axioms.ImplyS A B C)` verbatim from report §3 (3 `hdt` + 3 `D.mp`).
  - [ ] Add docstrings to both theorems (docBlame); keep snake_case names (matches
        `list_deduction_theorem` neighbors); use `theorem` (Prop-valued, defLemma-safe).
  - [ ] Register the new file in the `Cslib.lean` barrel via `lake exe mk_all --module`.
- **Timing:** ~1.5 hours.
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Foundations/Logic/Metalogic/DeductionCharacterization.lean` - new file with the two
    converse theorems.
  - `Cslib.lean` - add the new module to the barrel (via `mk_all`).
- **Verification:**
  - `lake build Cslib.Foundations.Logic.Metalogic.DeductionCharacterization` compiles clean.
  - `lake exe checkInitImports` passes (new file imports `Cslib.Init`).
  - `lake exe lint-style` clean (docstrings present; theorem naming OK).
  - `lake exe mk_all --module` leaves `Cslib.lean` consistent;
    `lake shake --add-public --keep-implied --keep-prefix` clean for the new file.
  - `lake test` green; zero `sorry`, zero new `axiom` (e.g. `lean_verify` / grep).

---

### Phase 3: dtInferenceSystem bridge, MinimalHilbert instance, characterization theorem [COMPLETED]

- **Goal:** Add the `dtInferenceSystem` wrapper (dual of `algebraicDerivationSystem`) so a
  DT-system's empty-context derivations form an `InferenceSystem`, produce the `MinimalHilbert`
  instance from the §3 converse, and state the characterization/equivalence theorem closing the
  loop with the existing forward arrow `algebraic_has_deduction_theorem`.
- **Tasks:**
  - [ ] Define `dtInferenceSystem (D : DerivationSystem F) : InferenceSystem _ F` with
        `derivation φ := PLift (D.Deriv [] φ)` so `DerivableIn ↔ D.Deriv []` (report §6.3, ~10 lines).
  - [ ] Given `hdt`, supply the `MinimalHilbert` components: `ModusPonens` ← `D.mp` at `[]`;
        `HasAxiomImplyK.implyK` ← `dt_implies_implyK`; `HasAxiomImplyS.implyS` ← `dt_implies_implyS`;
        register the `MinimalHilbert` instance (namespace-wrapped per topNamespace).
  - [ ] State the characterization theorem (e.g. `deduction_theorem_iff_minimal_hilbert`):
        forward arrow reuses `algebraic_has_deduction_theorem` (GenericMCS.lean:65); converse is the
        new bridge + `dt_implies_*`. Phrase the "weakest logic" claim: any `DerivationSystem`-with-`hdt`
        yields a `MinimalHilbert` instance, and `MinimalHilbert` yields `HasDeductionTheorem` via the
        algebraic system — closing the loop.
  - [ ] (Optional corollary, only if instance resolution is clean) the type-valued
        `HasDeductionTree → HasHilbertTree` reuse instance (report §4.2).
  - [ ] Fallback if `MinimalHilbert` instancing is awkward (report §7): ship converse as explicit
        theorems + optional tree instance and state the characterization without the typeclass
        instance — still complete and sorry-free.
  - [ ] Docstring every new decl; namespace-wrap instances.
- **Timing:** ~2 hours.
- **Depends on:** 2
- **Files to modify:**
  - `Cslib/Foundations/Logic/Metalogic/DeductionCharacterization.lean` - add `dtInferenceSystem`,
    `MinimalHilbert` instance, characterization theorem, optional tree corollary.
- **Verification:**
  - `lake build` of the new module + dependents compiles clean (no NEW failures vs. baseline).
  - Characterization theorem type-checks; `MinimalHilbert` instance resolves (or fallback applied).
  - Full CI gate: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
    `lake shake --add-public --keep-implied --keep-prefix` — no NEW failures beyond baseline.
  - Zero `sorry`, zero new `axiom` across the new file.

---

## Testing & Validation

CI pipeline (cslib order; gates scoped to this task's modules, confirming no NEW failures beyond
the known PRE-EXISTING three: `Bimodal.Theorems.Perpetuity.Principles`, SequentCalculus namespace
collision, `Modal.Tableau.Soundness`):

- [ ] `lake build` (full in Phase 1 for the signature ripple; module-scoped + no-new-failures
      check in Phases 2-3)
- [ ] `lake exe checkInitImports` (new file imports `Cslib.Init`)
- [ ] `lake exe lint-style` (docstrings; theorem naming; namespaced instances)
- [ ] `lake test` (CslibTests suite)
- [ ] `lake exe mk_all --module` (new file registered in `Cslib.lean` barrel)
- [ ] `lake shake --add-public --keep-implied --keep-prefix` (dependency hygiene)
- [ ] Zero `sorry`, zero new `axiom` (the converse uses only `assumption`/`mp`/`hdt`)
- [ ] Build probe: `DerivationSystem`/`HasDeductionTheorem` elaborate under `[HasImp F]` only

## Artifacts & Outputs

- `Cslib/Foundations/Logic/Metalogic/Consistency.lean` (modified: `[HasBot F]` decoupling)
- `Cslib/Foundations/Logic/Metalogic/DeductionCharacterization.lean` (new: converse + bridge +
  characterization)
- `Cslib.lean` (modified: barrel entry for the new module)
- `specs/351_deduction_theorem_weakest_logic_converse/plans/01_deduction-theorem-weakest-logic-converse.md`
  (this file)
- `specs/351_deduction_theorem_weakest_logic_converse/summaries/01_deduction-theorem-weakest-logic-converse-summary.md`
  (on completion)

## Rollback/Contingency

- **Phase 1 ripple:** if the structure-signature edit surfaces unexpected coupling, revert
  Consistency.lean and adopt the report §5.4 fallback — leave Consistency.lean untouched and phrase
  the new file against a fresh `⊥`-free class (`HasDeductionSystem`/`HasDeductionTree`) instead of
  generalizing `DerivationSystem`. Lower reuse but isolates the change.
- **Phase 3 instance trouble:** if `MinimalHilbert` instancing is awkward in Lean's resolution,
  apply the report §7 fallback — ship the explicit converse theorems (`dt_implies_implyK/S`) plus
  the optional `HasDeductionTree → HasHilbertTree` instance, and state the characterization without
  the typeclass instance. Still a complete, sorry-free converse.
- **General revert:** each phase is a self-contained git commit; revert the phase commit to restore
  the prior CI-green state. The converse heart (Phase 2) and decoupling (Phase 1) are independently
  revertable since Phase 2's terms compile against both the pre- and post-decoupling definitions.
