# Implementation Plan: Task #179 -- Add Diamond (dia) as Primitive Constructor

- **Task**: 179 - Add diamond (dia) as primitive constructor to Modal.Proposition
- **Status**: [NOT STARTED]
- **Effort**: 10 hours
- **Dependencies**: None
- **Research Inputs**: specs/179_modal_primitive_diamond/reports/03_upstream-study.md
- **Artifacts**: plans/04_primitive-dia-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Extend the Modal.Proposition inductive type from `{atom, bot, imp, box}` to `{atom, bot, imp, box, dia}` by adding `.dia` as a 5th primitive constructor. This decouples diamond from its classical definition `neg(box(neg phi))`, enabling future work on non-classical modal logics. The `HasDia` typeclass is added to `Connectives.lean`, axiom definitions (B, 5, D) in `Axioms.lean` are simplified using `HasDia.dia`, and all pattern-match sites across ~40 files gain a `.dia` case. Three families of truth lemmas (`truth_lemma`, `k_truth_lemma`, `truth_lemma_d`) each gain a `.dia` case, and all 15 system-specific completeness/soundness files are updated.

### Research Integration

The upstream study (report 03) confirmed that the upstream CSLib uses a fundamentally incompatible primitive set `{atom, not, and, diamond}`. No alignment target exists. The recommended strategy is a clean-break extension to 5 primitives, preserving our `{bot, imp}` propositional core. Key findings integrated:
- Constructor name `.dia` (not `.diamond`) parallels `HasBox`/`HasDia` symmetry
- `Proposition.diamond` kept as backward-compatible `abbrev := .dia`
- Classical duality `dia phi <-> neg(box(neg phi))` becomes a provable theorem
- `mcs_dia_witness` is the critical new proof obligation for completeness

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the Modal metalogic infrastructure. It is foundational for any future work on non-classical modal logics (intuitionistic modal logic, minimal modal logic) where `dia phi` is not definitionally `neg(box(neg phi))`.

## Goals & Non-Goals

**Goals**:
- Add `.dia` as a 5th primitive constructor to `Proposition`
- Add `HasDia` typeclass and update `ModalConnectives` to include it
- Simplify axiom B/5/D definitions in `Axioms.lean` using `HasDia.dia`
- Add `.dia` case to all pattern-match sites (Satisfies, denotation, Context, truth lemmas)
- Maintain all existing proofs (backward compatibility via `Proposition.diamond` abbrev)
- Pass full CI pipeline (`lake build`, `lake test`, `checkInitImports`, `lint-style`)

**Non-Goals**:
- Bimodal logic diamond update (separate task, different `Formula` type)
- Temporal logic changes (no diamond operator)
- Adding duality as a proof system axiom (research identified this as optional -- the completeness proofs can work via classical reasoning on the semantic level without a syntactic duality axiom)
- Upstream alignment (infeasible due to incompatible primitive sets)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Truth lemma `.dia` case proof difficulty | H | M | Proof sketch in research report; follows `mcs_box_witness` pattern with classical duality |
| Axiom formula change breaks HasAxiom instances | M | H | Instance files reference `Axioms.AxiomB` etc. which are abbrevs -- changes propagate automatically |
| `DecidableEq` derivation breaks with 5th constructor | H | L | `.dia` takes same argument shape as `.box`; Lean's `deriving` handles this |
| Cascade of proof breakage across 30+ soundness/completeness files | M | H | Lean exhaustiveness checker guides changes; most files need only a trivial `.dia` case |
| Axiom constructor formulas in instance files use expanded `neg(box(neg ...))` form | M | M | Rewrite to use `Proposition.diamond` or `.dia` directly; the `modalD`/`modalFive` constructors in 9 instance files need updating |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |

Phases are sequential due to import dependencies.

---

### Phase 1: Foundation -- Connectives and Axioms [NOT STARTED]

**Goal**: Add `HasDia` typeclass and update abstract axiom definitions to use it.

**Tasks**:
- [ ] Add `HasDia` typeclass to `Cslib/Foundations/Logic/Connectives.lean`
  - Define `class HasDia (F : Type*) where dia : F -> F`
  - Place after `HasBox` definition (line 73)
  - Update `ModalConnectives` to extend `HasBox F, HasDia F` (line 104)
  - Update `BimodalConnectives` which extends `ModalConnectives` (line 112)
- [ ] Add `dia'` abbreviation to `Cslib/Foundations/Logic/Axioms.lean`
  - Add `abbrev dia' [HasDia F] (x : F) : F := HasDia.dia x` in Abbreviations section
- [ ] Simplify `AxiomB` to use `HasDia.dia` (line 152-154)
  - Before: `HasImp.imp phi (HasBox.box (HasImp.imp (HasBox.box (HasImp.imp phi HasBot.bot)) HasBot.bot))`
  - After: `HasImp.imp phi (HasBox.box (HasDia.dia phi))`
- [ ] Simplify `Axiom5` to use `HasDia.dia` (line 158-161)
  - Before: `HasImp.imp (HasImp.imp (HasBox.box (HasImp.imp phi HasBot.bot)) HasBot.bot) (HasBox.box (HasImp.imp (HasBox.box (HasImp.imp phi HasBot.bot)) HasBot.bot))`
  - After: `HasImp.imp (HasDia.dia phi) (HasBox.box (HasDia.dia phi))`
- [ ] Simplify `AxiomD` to use `HasDia.dia` (line 165-167)
  - Before: `HasImp.imp (HasBox.box phi) (HasImp.imp (HasBox.box (HasImp.imp phi HasBot.bot)) HasBot.bot)`
  - After: `HasImp.imp (HasBox.box phi) (HasDia.dia phi)`
- [ ] Update modal axiom section header to include `HasDia F` in variable block (line 135)
- [ ] Verify `Foundations/Logic/Theorems/Modal/Basic.lean` compiles (may need `HasDia` in variable block)
- [ ] Run `lake build Cslib.Foundations.Logic.Connectives` and `lake build Cslib.Foundations.Logic.Axioms`

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Connectives.lean` -- Add `HasDia` class, extend `ModalConnectives`
- `Cslib/Foundations/Logic/Axioms.lean` -- Simplify B/5/D using `HasDia.dia`
- `Cslib/Foundations/Logic/ProofSystem.lean` -- Add `HasDia F` to modal axiom class section variable block (line 161)
- `Cslib/Foundations/Logic/Theorems/Modal/Basic.lean` -- May need `HasDia` in variable block

**Verification**:
- `lake build Cslib.Foundations.Logic.Connectives` succeeds
- `lake build Cslib.Foundations.Logic.Axioms` succeeds
- `HasDia` class is defined, `ModalConnectives` extends it

---

### Phase 2: Core Modal Type -- Basic.lean [NOT STARTED]

**Goal**: Add `.dia` constructor to `Proposition`, update `Satisfies`, and update the `ModalConnectives` instance and all theorems in Basic.lean.

**Tasks**:
- [ ] Add `.dia` constructor to `Proposition` inductive type (after line 60)
  - `| dia (phi : Proposition Atom)` with docstring "Possibility / diamond."
- [ ] Update `Proposition.diamond` abbrev body from `.neg (.box (.neg phi))` to `.dia phi` (line 78-79)
- [ ] Add `.dia` case to `Satisfies` definition (after line 108)
  - `| .dia phi => exists w', m.r w w' /\ Satisfies m w' phi`
- [ ] Update `ModalConnectives` instance to include `dia := .dia` (line 96-99)
- [ ] Update `Satisfies.diamond_iff` -- should become trivially `Iff.rfl` since `.dia` satisfaction is definitionally `exists w', ...` (line 115-124)
- [ ] Update `Satisfies.dual` proof -- no longer definitionally equal, needs classical reasoning (line 245-248)
- [ ] Update `Satisfies.t` proof (line 251-256) -- adjust for new diamond unfolding
- [ ] Update `Satisfies.t_refl` proof (line 259-271)
- [ ] Update `Satisfies.t_box_diamond` proof (line 274-285)
- [ ] Update `Satisfies.b` proof (line 288-294) -- adjust for new diamond unfolding
- [ ] Update `Satisfies.b_symm` proof (line 297-310)
- [ ] Update `Satisfies.four` proof (line 313-320) -- adjust for nested diamond
- [ ] Update `Satisfies.four_trans` proof (line 323-338)
- [ ] Update `Satisfies.five` proof (line 341-349)
- [ ] Update `Satisfies.five_rightEuclidean` proof (line 352-367)
- [ ] Update `Satisfies.d` proof (line 370-377)
- [ ] Update `Satisfies.d_serial` proof (line 380-393)
- [ ] Run `lake build Cslib.Logics.Modal.Basic`

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` -- Core type change, satisfaction, all validity proofs

**Verification**:
- `lake build Cslib.Logics.Modal.Basic` succeeds
- `Proposition` has 5 constructors: `.atom`, `.bot`, `.imp`, `.box`, `.dia`
- `Satisfies.diamond_iff` compiles (should be `Iff.rfl` or trivial)
- All 8 axiom validity theorems compile

---

### Phase 3: Context, Denotation, and Structural Files [NOT STARTED]

**Goal**: Add `.dia` case to LogicalEquivalence.lean, Denotation.lean, and FromPropositional.lean.

**Tasks**:
- [ ] Add `.dia` constructor to `Proposition.Context` inductive in `LogicalEquivalence.lean` (after line 48)
  - `| dia (c : Context Atom)` -- "Context under `dia`."
- [ ] Add `.dia` case to `Proposition.Context.fill` (after line 55)
  - `| .dia c, phi => .dia (c.fill phi)`
- [ ] Add `.dia` case to `LogicallyEquivalent.congruence` proof (after line 82)
  - Pattern: `| dia c ih =>` with existential iff reasoning
- [ ] Add `.dia` case to `Proposition.denotation` in `Denotation.lean` (after line 30)
  - `| .dia phi => {w | exists w', m.r w w' /\ w' in phi.denotation m}`
- [ ] Add `.dia` case to `satisfies_mem_denotation` induction in `Denotation.lean` (after line 51)
- [ ] Verify `FromPropositional.lean` -- no change needed (PL has no dia)
- [ ] Verify `Cube.lean` -- no change needed (only uses notation)
- [ ] Run `lake build Cslib.Logics.Modal.LogicalEquivalence` and `lake build Cslib.Logics.Modal.Denotation`

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/LogicalEquivalence.lean` -- Add `.dia` to Context, fill, congruence
- `Cslib/Logics/Modal/Denotation.lean` -- Add `.dia` to denotation, satisfies_mem_denotation

**Verification**:
- Both files build successfully
- `LogicallyEquivalent.congruence` proof compiles with `.dia` case
- `satisfies_mem_denotation` proof compiles with `.dia` case

---

### Phase 4: Proof System and MCS Infrastructure [NOT STARTED]

**Goal**: Update DerivationTree axiom constructors, MCS lemmas, and the three parameterized truth lemma families to handle `.dia`.

**Tasks**:
- [ ] Update `ModalAxiom.modalB` constructor in `DerivationTree.lean` (line 86-87)
  - Currently: `ModalAxiom (phi.imp (Proposition.box (Proposition.diamond phi)))`
  - This uses `Proposition.diamond` abbrev -- will automatically resolve to `.dia phi` after Phase 2
  - Verify it still compiles; no explicit change needed if abbrev works
- [ ] Update `mcs_box_diamond` in `MCS.lean` (line 170-173) -- verify it compiles with new diamond body
- [ ] Add `.dia` case to `truth_lemma` in `Completeness.lean` (after the `.box` case, line 410-422)
  - Forward direction: `Satisfies m S (.dia phi) -> (.dia phi) in S.val`
    - From `exists T, R S T /\ phi in T`, derive `.dia phi in S`
    - Use classical duality: `.dia phi <-> neg(box(neg phi))` is semantically valid
    - In MCS: `neg(box(neg phi))` membership follows from `phi in T` and `R S T`
  - Backward direction: `(.dia phi) in S.val -> Satisfies m S (.dia phi)`
    - This is the `mcs_dia_witness` argument: construct witness MCS containing phi
    - Uses: `{psi | box psi in S} union {phi}` is consistent, extend to MCS T
- [ ] Add `.dia` case to `k_truth_lemma` in `Systems/K/Completeness.lean`
  - Same proof structure as `truth_lemma` `.dia` case but uses K-specific box witness
- [ ] Add `.dia` case to `truth_lemma_d` in `Systems/D/Completeness.lean`
  - Same proof structure but uses D-specific box witness
- [ ] Verify `Metalogic/Soundness.lean` compiles (may not pattern-match on Proposition directly)
- [ ] Run `lake build Cslib.Logics.Modal.Metalogic`

**Timing**: 2.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` -- Verify `ModalAxiom.modalB` compiles
- `Cslib/Logics/Modal/Metalogic/MCS.lean` -- Verify `mcs_box_diamond` compiles
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` -- Add `.dia` case to `truth_lemma`
- `Cslib/Logics/Modal/Metalogic/Systems/K/Completeness.lean` -- Add `.dia` case to `k_truth_lemma`
- `Cslib/Logics/Modal/Metalogic/Systems/D/Completeness.lean` -- Add `.dia` case to `truth_lemma_d` (if D-specific truth lemma is defined here; otherwise in a shared D-completeness file)

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Completeness` succeeds
- `lake build Cslib.Logics.Modal.Metalogic.Systems.K.Completeness` succeeds
- Truth lemma handles all 5 constructor cases

---

### Phase 5: System-Specific Axiom Instances and Completeness/Soundness [NOT STARTED]

**Goal**: Update all 15 system-specific ProofSystem instance files and their corresponding Soundness/Completeness proofs.

**Tasks**:
- [ ] **ProofSystem instances -- axiom constructor formulas**: Update `modalB` constructors in 4 files (B, TB, DB, KB5) to verify they compile with new `Proposition.diamond` body
- [ ] **ProofSystem instances -- `modalD` constructors**: Rewrite `modalD` constructors in 5 files (D, DB, D4, D5, D45) from expanded `neg(box(neg phi))` form to use `Proposition.diamond phi` or `Proposition.dia phi`
  - D.lean: `DAxiom.modalD` (line 51-53)
  - DB.lean: `DBAxiom.modalD` (line 52-54)
  - D4.lean: `D4Axiom.modalD` (line 52-54)
  - D5.lean: `D5Axiom.modalD` (line ~52)
  - D45.lean: `D45Axiom.modalD` (line 52-54)
- [ ] **ProofSystem instances -- `modalFive` constructors**: Rewrite `modalFive` constructors in 4 files (K5, K45, KB5, D5, D45) from expanded form to use `Proposition.diamond`
  - K5.lean: `K5Axiom.modalFive` (line 51-53)
  - K45.lean: `K45Axiom.modalFive` (line ~55)
  - KB5.lean: `KB5Axiom.modalFive` (line 55-56)
  - D5.lean: `D5Axiom.modalFive` (line ~55)
  - D45.lean: `D45Axiom.modalFive` (line 59-60)
- [ ] **Soundness files**: Update axiom soundness proofs in all 15 systems
  - Systems with B axiom (B, TB, KB5, S5): `modalB` case needs diamond/dia reasoning
  - Systems with D axiom (D, DB, D4, D5, D45): `modalD` case needs diamond/dia reasoning
  - Systems with 5 axiom (K5, K45, KB5, D5, D45, S5): `modalFive` case needs diamond/dia reasoning
  - Systems without B/D/5 (K, T, K4, S4): soundness proof has no diamond cases -- may only need trivial updates or none
- [ ] **Completeness files**: Verify all 15 system-specific completeness proofs compile
  - Each instantiates one of the 3 truth lemma families (truth_lemma, k_truth_lemma, truth_lemma_d)
  - The truth lemma `.dia` case was added in Phase 4; the system completeness proofs just call the truth lemma
  - Systems with canonical_symm/canonical_eucl may need minor adjustments for diamond reasoning
- [ ] Run `lake build Cslib.Logics.Modal.ProofSystem.Instances` and `lake build Cslib.Logics.Modal.Metalogic.Systems`

**Timing**: 2 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Modal/ProofSystem/Instances/B.lean` -- Verify `modalB` compiles
- `Cslib/Logics/Modal/ProofSystem/Instances/TB.lean` -- Verify `modalB` compiles
- `Cslib/Logics/Modal/ProofSystem/Instances/DB.lean` -- Rewrite `modalD`, verify `modalB`
- `Cslib/Logics/Modal/ProofSystem/Instances/KB5.lean` -- Rewrite `modalFive`, verify `modalB`
- `Cslib/Logics/Modal/ProofSystem/Instances/D.lean` -- Rewrite `modalD`
- `Cslib/Logics/Modal/ProofSystem/Instances/D4.lean` -- Rewrite `modalD`
- `Cslib/Logics/Modal/ProofSystem/Instances/D5.lean` -- Rewrite `modalD`, `modalFive`
- `Cslib/Logics/Modal/ProofSystem/Instances/D45.lean` -- Rewrite `modalD`, `modalFive`
- `Cslib/Logics/Modal/ProofSystem/Instances/K5.lean` -- Rewrite `modalFive`
- `Cslib/Logics/Modal/ProofSystem/Instances/K45.lean` -- Rewrite `modalFive`
- `Cslib/Logics/Modal/ProofSystem/Instances/K.lean` -- Verify compiles (no B/D/5)
- `Cslib/Logics/Modal/ProofSystem/Instances/T.lean` -- Verify compiles (no B/D/5)
- `Cslib/Logics/Modal/ProofSystem/Instances/K4.lean` -- Verify compiles (no B/D/5)
- `Cslib/Logics/Modal/ProofSystem/Instances/S4.lean` -- Verify compiles (no B/D/5)
- `Cslib/Logics/Modal/ProofSystem/Instances/S5.lean` -- Verify `modalB` compiles
- All 15 `Metalogic/Systems/*/Soundness.lean` files -- Fix axiom soundness cases
- All 15 `Metalogic/Systems/*/Completeness.lean` files -- Verify compile
- `Cslib/Logics/Modal/Metalogic/Systems/K/ConservativeExtension.lean` -- Verify compiles

**Verification**:
- `lake build Cslib.Logics.Modal.ProofSystem.Instances` succeeds
- All 15 system-specific soundness/completeness proofs compile
- `lake build Cslib.Logics.Modal` succeeds (full modal module)

---

### Phase 6: Full CI Verification and Cleanup [NOT STARTED]

**Goal**: Run the complete CI pipeline and fix any remaining issues.

**Tasks**:
- [ ] Run `lake build` (full project build)
- [ ] Run `lake test` (CslibTests suite)
- [ ] Run `lake exe checkInitImports` (verify Cslib.Init imports)
- [ ] Run `lake exe lint-style` (style linting)
- [ ] Run `lake exe mk_all --module` (update barrel import if new files were added -- unlikely)
- [ ] Update module docstring in `Basic.lean` to reflect 5 primitives (line 24-27)
  - Change "The formula type uses `{atom, bot, imp, box}` as primitive constructors" to `{atom, bot, imp, box, dia}`
  - Update mention of diamond being derived
- [ ] Verify Bimodal logic still compiles (no changes expected, different Formula type)
- [ ] Verify Temporal logic still compiles (no changes expected, no diamond)

**Timing**: 1 hour

**Depends on**: 5

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` -- Update module docstring only

**Verification**:
- Full `lake build` passes with no errors
- `lake test` passes
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- All 5 CI steps green

## Testing & Validation

- [ ] `lake build` completes without errors
- [ ] `lake test` passes (CslibTests suite)
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `Proposition` inductive has exactly 5 constructors: `atom`, `bot`, `imp`, `box`, `dia`
- [ ] `Proposition.diamond phi` definitionally equals `.dia phi`
- [ ] `Satisfies m w (.dia phi) <-> exists w', m.r w w' /\ Satisfies m w' phi` is `Iff.rfl`
- [ ] `HasDia` typeclass exists and `ModalConnectives` extends it
- [ ] `Axioms.AxiomB`, `Axioms.Axiom5`, `Axioms.AxiomD` use `HasDia.dia` (simplified)
- [ ] All 15 system completeness/soundness theorems compile
- [ ] `Satisfies.dual` proves `dia phi <-> neg(box(neg phi))` as a theorem (not definitional)

## Artifacts & Outputs

- `specs/179_modal_primitive_diamond/plans/04_primitive-dia-plan.md` (this plan)
- Modified files: ~40 files across `Cslib/Foundations/Logic/` and `Cslib/Logics/Modal/`
- No new files created (`.dia` is added to existing types)

## Rollback/Contingency

All changes are to Lean source files tracked in git. Rollback via `git checkout main -- Cslib/` to restore the 4-constructor version. The changes are backward-compatible at the notation level (`diamond` abbrev is preserved), so downstream code using `diamond` notation should not break. If the truth lemma `.dia` case proves intractable, a fallback is to define it via `sorry` and mark Phase 4 as `[PARTIAL]` for later resolution.
