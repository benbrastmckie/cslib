# Implementation Plan: Task #355

- **Task**: 355 - Modal & Propositional deductionTheorem consolidation
- **Status**: [NOT STARTED]
- **Effort**: 6.5 hours
- **Dependencies**: Task 350 (complete — provides verified Temporal/Bimodal templates)
- **Research Inputs**: specs/355_modal_propositional_deduction_theorem_consolidation/reports/01_modal-propositional-dt-consolidation.md
- **Artifacts**: plans/01_modal-propositional-dt-reroute.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Complete the deduction-theorem consolidation begun in task 350 by routing the **Modal** and
**Propositional** `deductionTheorem` defs through the generic algebraic deduction-theorem layer.
The single new abstraction is a parameterized tag type `HilbertOf Axioms` (per-logic, in each
bridge file) plus a generic predicate-level class `HasMinimalAxioms` (in Foundations
`GenericMCS.lean`) from which the `MinimalHilbert (HilbertOf Axioms)` instance is synthesised.
Everything else is a line-for-line transcription of the verified Temporal/Bimodal bridge assets.
Signatures are preserved verbatim, so all ~25 raw `DerivationTree` / `deductionTheorem` /
`hasDeductionTheorem` consumers keep compiling; `deductionWithMem` and the hand WF-recursion
bodies are deleted. Zero new sorry, zero new axioms.

### Research Integration

The plan follows the report's §8 six-phase backbone, with the verified code sketches inlined as
per-phase references:
- §4.1 generic `HasMinimalAxioms` class (Foundations) — Phase 1.
- §4.2 `HilbertOf` wrapper + `InferenceSystem`/`ModusPonens`/`HasAxiomImplyK`/`HasAxiomImplyS`/
  `MinimalHilbert` instances — Phases 2 (Modal) and 4 (PL).
- §4.3 bridge transcription (`deriv_tree_to_list`, `unfold_listImp_in_tree`,
  `list_deriv_to_tree`, `*_deriv_iff_algebraic`, MCS equivalences) — Phases 2 and 4.
- §4.4 re-routed 3-line `deductionTheorem` body + `hasDeductionTheorem` — Phases 3 (Modal) and
  5 (PL).
- §5 import/cycle discipline (bridge must NOT import `DeductionTheorem.lean`).
- §6 call-site audit (no external `deductionWithMem` callers; signature-preserving reroute).
- §9 risk table (R1–R6) carried into Risks section below.

### Prior Plan Reference

No prior plan for this task. The functional precedent is **task 350** (Temporal/Bimodal
consolidation), whose four bridge assets are verified present and are the literal templates
(report §1). The Bimodal fresh bridge (`Bimodal/Metalogic/Core/GenericMCSBridge.lean`) is the
closest template because it was authored fresh in task 350. Effort calibration follows task 350's
measured Phase B/3 work: the Modal forward bridge adds one `necessitation` case over Bimodal; PL
is strictly simpler (4 constructors, no necessitation).

### Roadmap Alignment

No ROADMAP.md found / not provided in delegation context. This task advances the broader
deduction-theorem unification effort: after this task, all four logics (Temporal, Bimodal, Modal,
Propositional) route `deductionTheorem` through `algebraic_has_deduction_theorem`, eliminating
the last hand WF-recursion bodies.

## Goals & Non-Goals

**Goals**:
- Add a single generic `HasMinimalAxioms` predicate class to Foundations `GenericMCS.lean`.
- Build per-logic `GenericMCSBridge` for Modal (replace doc-only file) and Propositional (new file).
- Re-route Modal and PL `deductionTheorem` / `hasDeductionTheorem` through the bridge +
  `algebraic_has_deduction_theorem`, preserving signatures verbatim.
- Delete `deductionWithMem` and the hand WF-recursion bodies in both logics; delete the PL
  file-local `HasHilbertTree` instance.
- Keep CI green and all downstream consumers sorry-free; zero new sorry, zero new axioms.

**Non-Goals**:
- Refactoring Temporal/Bimodal (already consolidated in task 350).
- Changing any `deductionTheorem` / `hasDeductionTheorem` signature or call site.
- Inhabiting `HilbertOf` (it is a tag type; content lives entirely in its instances).
- Introducing any new Mathlib dependency beyond what the temporal/bimodal bridges already use.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| R1: `inductive HilbertOf … : Type` instance-key behaviour; a `def`+unfold would lose the `Axioms` parameter during TC search | H | M | Use empty `inductive`/`structure`; if search still unfolds, add `irreducible`. Verify with `#check (inferInstance : MinimalHilbert (HilbertOf MyPred))` under a local `haveI : HasMinimalAxioms`. |
| R2: `algebraic_has_deduction_theorem` fails to infer `S := HilbertOf Axioms` through the `@[reducible] modalAlgDS` alias | M | M | Annotate `(S := HilbertOf Axioms)` explicitly on `algebraic_has_deduction_theorem`. |
| R3: `.some` doesn't see through `modalDerivationSystem.Deriv` to `Nonempty` | M | L | Defeq held for temporal; if not, `unfold modalDerivationSystem Modal.Deriv` then `Nonempty.some` / `Classical.choice`. |
| R4: PL missing `HasBot`/`HasImp (PL.Proposition Atom)` instance needed for `MinimalHilbert` | M | L | `lean_hover_info` on `propDerivationSystem`; both must already exist for `imp`/`bot` to typecheck. |
| R5: `Cslib.lean` barrel drift when adding the new PL bridge file | L | H | Run `lake exe mk_all --module` (task 350 precedent). |
| R6: Lint failures (docstrings, Prop-class field casing, namespace wrapping) | M | M | Apply CSLib lint-prevention rules: `docBlame` docstrings on new class/defs; lowerCamelCase fields `hasImplyK`/`hasImplyS`; `class … : Prop`; bridge defs `noncomputable def`. |
| Instance-resolution wall with no annotation fix at R1/R2 | H | L | Mark the affected phase [BLOCKED] for user review — never a `sorry` or axiom (report §10). |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 4 | 1 |
| 3 | 3, 5 | 2 (Phase 3), 4 (Phase 5) |
| 4 | 6 | 3, 5 |

Phases within the same wave can execute in parallel. Phases 2-3 (Modal) and 4-5 (PL) are
independent file-ownership territories (Modal vs Propositional dirs are disjoint), so the two
chains can run as parallel waves once Phase 1 lands.

---

### Phase 1: Foundations — generic `HasMinimalAxioms` class [NOT STARTED]

**Goal**: Add the shared predicate-level minimal-axioms class to Foundations `GenericMCS.lean`,
the only Foundations change and the synthesis source for every `MinimalHilbert (HilbertOf Axioms)`
instance.

**Tasks**:
- [ ] Add `class HasMinimalAxioms (Axioms : F → Prop) : Prop` (over `{F : Type*} [HasImp F]`) in
  `namespace Cslib.Logic.Metalogic.GenericMCS`, with fields `hasImplyK : ∀ φ ψ, Axioms (Axioms.ImplyK φ ψ)`
  and `hasImplyS : ∀ φ ψ χ, Axioms (Axioms.ImplyS φ ψ χ)` (report §4.1).
- [ ] Add required docstrings (class + both fields) to satisfy `docBlame`; use lowerCamelCase
  field names (no underscores) to satisfy `defsWithUnderscore`.
- [ ] Confirm `Axioms.ImplyK φ ψ` is defeq to `φ.imp (ψ.imp φ)` so `⟨h_implyK, h_implyS⟩` will
  typecheck downstream.

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` - add the `HasMinimalAxioms` class only.

**Verification**:
- `lake build Cslib.Foundations.Logic.Metalogic.GenericMCS` succeeds.
- No lint errors on the new class (`lake exe lint-style` clean for the file).

---

### Phase 2: Modal bridge — `HilbertOf` + instances + full bridge [NOT STARTED]

**Goal**: Replace the doc-only `Modal/Metalogic/GenericMCSBridge.lean` with the real wrapper type,
its instances, and the full forward/backward bridge (mirror Bimodal, add the `necessitation` case).

**Tasks**:
- [ ] Add `inductive HilbertOf (Axioms : Proposition Atom → Prop) : Type` (no constructors) in
  `namespace Cslib.Logic.Modal` (report §4.2; do NOT use a plain `def`).
- [ ] Add `InferenceSystem (HilbertOf Axioms)` (`derivation φ := DerivationTree Axioms [] φ`),
  `ModusPonens`, and the `[HasMinimalAxioms Axioms]`-conditional `HasAxiomImplyK`,
  `HasAxiomImplyS`, `MinimalHilbert` instances (report §4.2 sketch).
- [ ] Add `@[reducible] def modalAlgDS` alias for `@algebraicDerivationSystem … (HilbertOf Axioms)`.
- [ ] Transcribe `deriv_tree_to_list` (forward) with 5 arms `ax`/`assumption`/`modus_ponens`/
  `necessitation`/`weakening` — `necessitation` reconstructed at empty context exactly as Temporal
  `temporal_necessitation` (report §4.3). Note the `ax` arm name (Modal uses `ax`, not `«axiom»`).
- [ ] Transcribe `unfold_listImp_in_tree`, `list_deriv_to_tree`, `modal_deriv_iff_algebraic`,
  `modal_setConsistent_iff_algebraic`, `modal_setMaxConsistent_iff_algebraic` verbatim from Bimodal
  with renames.
- [ ] Set imports: `Foundations…GenericMCS`, `Modal.Metalogic.DerivationTree`,
  `Foundations…MCSProperties`; do **NOT** import `DeductionTheorem.lean` (report §5). Remove the
  `module -- shake: keep-all` marker and gap-analysis comment; add a real module docstring.

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` - replace doc-only content with real bridge.

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.GenericMCSBridge` succeeds, sorry-free.
- `#check (inferInstance : MinimalHilbert (HilbertOf SomePred))` resolves under a local
  `haveI : HasMinimalAxioms SomePred` (R1 check).
- `modal_deriv_iff_algebraic` typechecks both directions.

---

### Phase 3: Modal DT reroute [NOT STARTED]

**Goal**: Re-implement Modal `deductionTheorem` / `hasDeductionTheorem` through the bridge, delete
`deductionWithMem` and the WF body, and confirm the 4 Modal consumers still compile.

**Tasks**:
- [ ] Delete `deductionWithMem` (def, ~line 50) and the WF-recursion body of `deductionTheorem`.
- [ ] Re-implement `deductionTheorem` with the verbatim signature
  (`{Axioms} (h_implyK) (h_implyS) (Γ) (A B) (d)`) and the 3-line body wrapped in
  `haveI : HasMinimalAxioms Axioms := ⟨h_implyK, h_implyS⟩` then
  `(modal_deriv_iff_algebraic.mpr (algebraic_has_deduction_theorem (modal_deriv_iff_algebraic.mp ⟨d⟩))).some`
  (report §4.4). If unification fails, annotate `(S := HilbertOf Axioms)` (R2).
- [ ] Re-prove `hasDeductionTheorem` via the bridge (report §4.4 sketch).
- [ ] Add `public import …Modal.Metalogic.GenericMCSBridge` and `…Foundations…GenericMCS`; drop
  `ListHelpers` + `DeductionHelpers` imports and the file-local
  `attribute [local instance] Classical.propDecidable` if now unused (confirm with `lake shake`).

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` - delete `deductionWithMem`, reroute both defs.

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic` succeeds, sorry-free.
- The 4 Modal consumers build: `Metalogic/Completeness.lean`, `Metalogic/MCS.lean`,
  `Metalogic/Systems/K/Completeness.lean`, `Metalogic/Systems/D/Completeness.lean`.
- `grep -rn deductionWithMem Cslib/Logics/Modal` returns nothing.

---

### Phase 4: Propositional bridge — `HilbertOf` + instances + bridge [NOT STARTED]

**Goal**: Create the new `Propositional/Metalogic/GenericMCSBridge.lean` (4-constructor, no
necessitation) — strictly simpler than Modal.

**Tasks**:
- [ ] Create new file with `inductive HilbertOf (Axioms : PL.Proposition Atom → Prop) : Type` in
  `namespace Cslib.Logic.PL`, plus `InferenceSystem`/`ModusPonens`/conditional `HasAxiomImplyK`/
  `HasAxiomImplyS`/`MinimalHilbert` instances (report §4.2 PL variant).
- [ ] Verify `HasBot`/`HasImp (PL.Proposition Atom)` instances exist (R4) via `lean_hover_info` on
  `propDerivationSystem`.
- [ ] Add `@[reducible] def propAlgDS` alias; transcribe `deriv_tree_to_list` with **4 arms**
  (`ax`/`assumption`/`modus_ponens`/`weakening`, no `necessitation`), `unfold_listImp_in_tree`,
  `list_deriv_to_tree`, `pl_deriv_iff_algebraic`, and the two MCS equivalences (report §4.3).
- [ ] Set imports: `Propositional.ProofSystem.Derivation`, `Foundations…GenericMCS`,
  `Foundations…MCSProperties`; do NOT import `DeductionTheorem.lean`.
- [ ] Register the new file in `Cslib.lean` via `lake exe mk_all --module` (R5).

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/GenericMCSBridge.lean` - new file.
- `Cslib.lean` - barrel registration via `mk_all --module`.

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.GenericMCSBridge` succeeds, sorry-free.
- `pl_deriv_iff_algebraic` typechecks both directions.
- `lake exe mk_all --module` leaves `Cslib.lean` consistent (no further drift).

---

### Phase 5: Propositional DT reroute [NOT STARTED]

**Goal**: Re-implement PL `deductionTheorem` / `hasDeductionTheorem` through the bridge, delete
`deductionWithMem` + the fixed `HasHilbertTree` instance, and confirm the 6 PL consumers compile.

**Tasks**:
- [ ] Delete the file-local `HasHilbertTree` instance (~line 56), `deductionWithMem` (~line 71),
  and the WF-recursion body of `deductionTheorem`.
- [ ] Re-implement `deductionTheorem` and re-prove `hasDeductionTheorem` via the PL bridge with
  signatures preserved verbatim (report §4.4, `PL.Proposition` / `propDerivationSystem`).
- [ ] Add bridge + `GenericMCS` imports; drop `ListHelpers` + `DeductionHelpers` (and
  `ProofSystem.Axioms` if the deleted `HasHilbertTree` was its only consumer — confirm with `lake shake`).

**Timing**: 1 hour

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` - delete instance + `deductionWithMem`, reroute both defs.

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic` succeeds, sorry-free.
- The 6 PL consumers build: `Metalogic/StrongCompleteness.lean`, `Metalogic/MinLindenbaum.lean`,
  `Metalogic/IntLindenbaum.lean`, `NaturalDeduction/FromHilbert.lean`,
  `NaturalDeduction/Equivalence.lean`, `Semantics/SemanticConsequence.lean`.
- `grep -rn deductionWithMem Cslib/Logics/Propositional` returns nothing.

---

### Phase 6: CI gate + downstream sorry-free verification [NOT STARTED]

**Goal**: Run the full CSLib CI pipeline and confirm zero technical debt across all downstream
consumers.

**Tasks**:
- [ ] `lake build` (full) — green.
- [ ] `lake test` — CslibTests suite passes.
- [ ] `lake exe checkInitImports` — clean.
- [ ] `lake exe lint-style` — clean (verify R6 lint items resolved).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — no unused imports; confirm dropped
  `ListHelpers`/`DeductionHelpers`/`Classical.propDecidable` are actually unused.
- [ ] Confirm sorry-free downstream: MCS, Completeness, TruthLemma, StrongCompleteness,
  NaturalDeduction (`grep -rn "sorry" ` on touched modules and their consumers returns nothing new).
- [ ] Confirm no new axioms via `lean_verify` / `#print axioms` on `deductionTheorem` (only the
  pre-existing `Classical.choice` chain present in Temporal/Bimodal).

**Timing**: 0.5 hours

**Depends on**: 3, 5

**Files to modify**:
- None (verification only; may apply small lint/shake fixes surfaced here).

**Verification**:
- All five CI commands exit 0.
- Zero new sorry, zero new axioms.

## Testing & Validation

- [ ] `lake build` green across the full library.
- [ ] `lake test` passes (CslibTests).
- [ ] `lake exe checkInitImports` clean.
- [ ] `lake exe lint-style` clean.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no unused imports.
- [ ] All 4 Modal + 6 PL `deductionTheorem`/`hasDeductionTheorem` consumers compile unchanged.
- [ ] `grep -rn deductionWithMem Cslib/Logics/{Modal,Propositional}` returns nothing.
- [ ] `#print axioms` on the re-routed defs shows no new axioms beyond `Classical.choice`.

## Artifacts & Outputs

- Modified `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` (new `HasMinimalAxioms` class).
- Rewritten `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` (real bridge).
- Modified `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` (rerouted, `deductionWithMem` removed).
- New `Cslib/Logics/Propositional/Metalogic/GenericMCSBridge.lean`.
- Modified `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` (rerouted, instance + `deductionWithMem` removed).
- Updated `Cslib.lean` barrel.
- Green CI run (build/test/checkInitImports/lint-style/shake).

## Rollback/Contingency

- Each phase is an isolated build target; `git checkout -- <file>` reverts a single phase's file
  without affecting earlier phases.
- The reroute is signature-preserving, so reverting any `DeductionTheorem.lean` to its hand-WF body
  restores the prior working state with no call-site changes required.
- If an instance-resolution wall is hit at R1/R2 with no annotation fix, mark the affected phase
  **[BLOCKED]** for user review — never introduce a `sorry` or axiom (report §10). The verified
  template parity makes a blocker unlikely.
