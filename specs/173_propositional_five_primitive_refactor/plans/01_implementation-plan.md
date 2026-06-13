# Implementation Plan: Propositional Five-Primitive Refactor

- **Task**: 173 - propositional_five_primitive_refactor
- **Status**: [IMPLEMENTING]
- **Effort**: 12 hours
- **Dependencies**: 172 (Connectives refactor -- completed)
- **Research Inputs**: specs/173_propositional_five_primitive_refactor/reports/01_five-primitive-research.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Refactor `Cslib/Logics/Propositional` from the three-primitive formula type `{atom, bot, imp}` to the five-primitive formula type `{atom, bot, imp, and, or}`. This requires: (1) adding `and`/`or` constructors to `Proposition` and extending all pattern-matching functions; (2) replacing the ND system's `botE` primitive with 6 new rules (andI, andE1, andE2, orI1, orI2, orE), making explosion a derived rule under `[IsIntuitionistic T]`; (3) extending the Hilbert axiom hierarchy with 6 and/or axiom schemata at the minimal level; (4) updating the ND-Hilbert bridge for level-by-level correspondence; (5) extending semantics (Evaluate, IForces) and metalogic (soundness, completeness); (6) handling downstream embedding files. The defining constraint is that each phase must leave `lake build` green.

### Research Integration

The research report provides a complete file-by-file inventory of 22 affected files, a 7-phase ordering recommendation, risk assessment, and detailed constructor signatures. Key findings integrated into this plan:

- `Proposition.and` and `Proposition.or` become constructors; `neg`, `top`, `iff` remain `abbrev`s.
- Research recommends keeping `HasAxiom*` typeclasses standalone (not bundled into `MinimalHilbert`) to avoid breaking Modal/Temporal/Bimodal Hilbert classes. This plan follows that recommendation.
- Research recommends registering `HasAnd`/`HasOr` directly on `Proposition` rather than extending `PropositionalConnectives` (task 174-176 scope). This plan follows that recommendation.
- External embeddings (`Modal/FromPropositional.lean`, `Temporal/FromPropositional.lean`) must add `and`/`or` cases using Lukasiewicz encoding to the 3-constructor target types, since Modal/Temporal formula types do not yet have `and`/`or` constructors.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the Foundations Refactor topic within the ongoing CSLib development. It does not directly correspond to a specific ROADMAP.md item (the roadmap tracks porting from BimodalLogic, not internal refactoring), but it unblocks tasks 174-176 which propagate the five-primitive type to Modal, Temporal, and Bimodal layers.

## Goals & Non-Goals

**Goals**:
- Add `and` and `or` as constructors to `PL.Proposition`, replacing the Lukasiewicz `abbrev`s
- Align ND system with upstream Waring's 10-rule system (no `botE` primitive)
- Extend all three Hilbert axiom inductives (Min/Int/Cl) with 6 and/or axiom schemata
- Add `HasAxiom{AndI,AndE1,AndE2,OrI1,OrI2,OrE}` typeclasses and instances at all three Hilbert levels
- Remove `[IsClassical T]` constraints from andE1/andE2/orE/iffE1/iffE2 in DerivedRules.lean
- Update ND-Hilbert bridge (FromHilbert, HilbertDerivedRules, Equivalence) for level-by-level correspondence
- Extend Evaluate, IForces, and iforces_persistence with and/or cases
- Extend soundness and completeness proofs with and/or cases
- Handle Modal/Temporal FromPropositional embeddings via Lukasiewicz encoding
- Pass all CI gates: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`

**Non-Goals**:
- Extending `PropositionalConnectives` to include `HasAnd`/`HasOr` (task 174-176 scope)
- Bundling `HasAxiomAndI` etc. into `MinimalHilbert`/`IntuitionisticHilbert`/`ClassicalHilbert` (deferred to avoid breaking Modal/Temporal/Bimodal)
- Adding `and`/`or` constructors to Modal, Temporal, or Bimodal formula types (tasks 174-176)
- Modifying the `DerivationTree` type or `DeductionTheorem` (formula-agnostic, no changes needed)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Completeness proofs break with and/or cases | High | Medium | Phase 6 allocated separately; existing 3-case proofs provide structural template |
| Removing botE from ND cascades through many files | High | Medium | Phase 3 provides botE as derived rule under [IsIntuitionistic T] immediately after removal |
| Lukasiewicz encoding in Modal/Temporal embeddings causes type mismatches | Medium | Low | Encoding is well-understood: and maps to neg(imp A (neg B)), or maps to imp (neg A) B |
| orE Kripke soundness proof requires careful persistence reasoning | Medium | Medium | Standard Kripke proof; persistence lemma already proved for the 3 existing cases |
| HasAxiom* instances fail without bundled MinimalHilbert extension | Low | Low | Standalone instances avoid bundled class cascade entirely |
| Notation conflicts between new constructors and existing abbrevs | Low | Low | Scoped notation already uses the same symbols; constructors replace abbrevs seamlessly |

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
| 7 | 7 | 6 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Foundations -- Polymorphic Axiom Abbrevs and HasAxiom* Typeclasses [COMPLETED]

**Goal**: Add and/or axiom definitions to `Foundations/Logic/Axioms.lean` and corresponding `HasAxiom*` typeclasses to `Foundations/Logic/ProofSystem.lean`. This phase touches only Foundations-level files and causes no downstream breakage.

**Tasks**:
- [ ] Add and/or axiom abbrevs to `Cslib/Foundations/Logic/Axioms.lean` in a new `section AndOrAxioms` (requires `[HasAnd F]` and `[HasOr F]`): `AndI`, `AndE1`, `AndE2`, `OrI1`, `OrI2`, `OrE`
- [ ] Add `HasAxiomAndI`, `HasAxiomAndE1`, `HasAxiomAndE2`, `HasAxiomOrI1`, `HasAxiomOrI2`, `HasAxiomOrE` typeclasses to `Cslib/Foundations/Logic/ProofSystem.lean` in a new section after the existing `HasAxiomPeirce` definition. These require `[HasAnd F]` and/or `[HasOr F]` in addition to `[HasBot F] [HasImp F]`.
- [ ] Do NOT add these to bundled classes (`MinimalHilbert` etc.) -- keep standalone
- [ ] Run `lake build Cslib.Foundations.Logic.ProofSystem` and `lake build Cslib.Foundations.Logic.Axioms` to verify no breakage

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Axioms.lean` -- add `AndI`, `AndE1`, `AndE2`, `OrI1`, `OrI2`, `OrE` abbrevs
- `Cslib/Foundations/Logic/ProofSystem.lean` -- add 6 `HasAxiom*` typeclasses

**Verification**:
- `lake build Cslib.Foundations.Logic.Axioms` succeeds
- `lake build Cslib.Foundations.Logic.ProofSystem` succeeds
- Existing downstream modules still build (no changes to bundled classes)

---

### Phase 2: Formula Type and Semantics -- Add and/or Constructors [COMPLETED]

**Goal**: Add `and` and `or` as constructors to `Proposition`, update all pattern-matching functions in Defs.lean and Semantics, and register `HasAnd`/`HasOr` instances. This is the core structural change that causes cascading breakage in downstream modules.

**Tasks**:
- [ ] In `Defs.lean`: Add `| and (a b : Proposition Atom)` and `| or (a b : Proposition Atom)` constructors to `Proposition` inductive
- [ ] In `Defs.lean`: Change `Proposition.and` and `Proposition.or` from `abbrev` (Lukasiewicz encoding) to the new constructors. Remove the two `abbrev` definitions (since the constructors now provide `.and` and `.or` directly). Verify that `Proposition.iff` abbrev now correctly uses the constructor `and` (i.e., `(A.imp B).and (B.imp A)` uses the new constructor)
- [ ] In `Defs.lean`: Register `HasAnd` and `HasOr` instances on `Proposition Atom`: `instance : HasAnd (Proposition Atom) where and := .and` and `instance : HasOr (Proposition Atom) where or := .or`
- [ ] In `Defs.lean`: Extend `subst` with `| and A B => .and (A.subst f) (B.subst f)` and `| or A B => .or (A.subst f) (B.subst f)`
- [ ] In `Semantics/Basic.lean`: Add `| .and a b => Evaluate v a /\ Evaluate v b` and `| .or a b => Evaluate v a \/ Evaluate v b` to `Evaluate`
- [ ] In `Semantics/Kripke.lean`: Add and/or cases to `IForces`: `| .and phi psi => IForces v bot_forces w phi /\ IForces v bot_forces w psi` and `| .or phi psi => IForces v bot_forces w phi \/ IForces v bot_forces w psi`
- [ ] In `Semantics/Kripke.lean`: Add and/or cases to `iforces_persistence`: `and` by IH on both conjuncts; `or` by IH on the disjunct that holds
- [ ] Run `lake build Cslib.Logics.Propositional.Semantics.Kripke` to verify semantics builds

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Defs.lean` -- formula type, subst, instances
- `Cslib/Logics/Propositional/Semantics/Basic.lean` -- Evaluate
- `Cslib/Logics/Propositional/Semantics/Kripke.lean` -- IForces, iforces_persistence

**Verification**:
- `lake build Cslib.Logics.Propositional.Defs` succeeds
- `lake build Cslib.Logics.Propositional.Semantics.Kripke` succeeds
- NOTE: Other Propositional modules will be broken at this point (pattern match exhaustion). This is expected; Phases 3-6 fix them.

---

### Phase 3: ND System Overhaul -- Remove botE, Add 6 Constructors, Update DerivedRules [COMPLETED]

**Goal**: Transform the ND system from 5 constructors (ax, ass, impI, impE, botE) to 10 constructors (ax, ass, andI, andE1, andE2, orI1, orI2, orE, impI, impE). Update `weak`, `subs`, `substAtom` for the new constructors. Make `botE` a derived rule under `[IsIntuitionistic T]`. Rewrite DerivedRules to use new primitives.

**Tasks**:
- [ ] In `NaturalDeduction/Basic.lean`: Remove `botE` constructor from `Theory.Derivation`
- [ ] In `NaturalDeduction/Basic.lean`: Add 6 new constructors following the signatures from the research report:
  - `andI {A B} (G) : Derivation G A -> Derivation G B -> Derivation G (A /\ B)`
  - `andE1 {A B} (G) : Derivation G (A /\ B) -> Derivation G A`
  - `andE2 {A B} (G) : Derivation G (A /\ B) -> Derivation G B`
  - `orI1 {A B} (G) : Derivation G A -> Derivation G (A \/ B)`
  - `orI2 {A B} (G) : Derivation G B -> Derivation G (A \/ B)`
  - `orE {A B C} (G) : Derivation G (A \/ B) -> Derivation (insert A G) C -> Derivation (insert B G) C -> Derivation G C`
- [ ] In `NaturalDeduction/Basic.lean`: Update `weak` -- remove botE case, add 6 new cases (andI, andE1, andE2 recurse on sub-derivations; orI1, orI2 recurse; orE recurses with insert_subset_insert for the two branch contexts)
- [ ] In `NaturalDeduction/Basic.lean`: Update `subs` -- remove botE case, add 6 new cases matching weak's structure
- [ ] In `NaturalDeduction/Basic.lean`: Update `substAtom` -- remove botE case, add 6 new cases
- [ ] In `NaturalDeduction/DerivedRules.lean`: Add `botE` as a derived rule requiring `[IsIntuitionistic T]`: derive from `ax (IsIntuitionistic.efq A)` + `impE`
- [ ] In `NaturalDeduction/DerivedRules.lean`: Rewrite `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE` as trivial wrappers around the new ND primitives (remove `[IsClassical T]` from andE1, andE2, orE)
- [ ] In `NaturalDeduction/DerivedRules.lean`: Rewrite `iffI` to use primitive `andI`, `iffE1`/`iffE2` to use primitive `andE1`/`andE2` (remove `[IsClassical T]` from iffE1, iffE2)
- [ ] In `NaturalDeduction/DerivedRules.lean`: Update all `DerivableIn`-level wrappers to match the updated base rules (remove `[IsClassical T]` where the base rule no longer requires it)
- [ ] Run `lake build Cslib.Logics.Propositional.NaturalDeduction.DerivedRules` to verify

**Timing**: 2.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` -- Derivation inductive, weak, subs, substAtom
- `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean` -- derived rules, wrappers

**Verification**:
- `lake build Cslib.Logics.Propositional.NaturalDeduction.DerivedRules` succeeds
- No `[IsClassical T]` on andE1, andE2, orE, iffE1, iffE2
- `botE` requires `[IsIntuitionistic T]`

---

### Phase 4: Hilbert Axiom Extension -- Axioms, Instances, Bridge Files [COMPLETED]

**Goal**: Extend the three propositional axiom inductives (MinPropAxiom, IntPropAxiom, PropositionalAxiom) with 6 and/or axiom constructors each. Add HasAxiom* instances for all three Hilbert tag types. Update FromHilbert.lean subst_preserves_* theorems and HilbertDerivedRules.lean.

**Tasks**:
- [ ] In `ProofSystem/Axioms.lean`: Add 6 new constructors to `PropositionalAxiom`:
  - `andI (phi psi)` : proves `phi -> (psi -> phi /\ psi)`
  - `andE1 (phi psi)` : proves `phi /\ psi -> phi`
  - `andE2 (phi psi)` : proves `phi /\ psi -> psi`
  - `orI1 (phi psi)` : proves `phi -> phi \/ psi`
  - `orI2 (phi psi)` : proves `psi -> phi \/ psi`
  - `orE (phi psi chi)` : proves `(phi -> chi) -> ((psi -> chi) -> ((phi \/ psi) -> chi))`
- [ ] In `ProofSystem/Axioms.lean`: Add same 6 constructors to `IntPropAxiom` and `MinPropAxiom`
- [ ] In `ProofSystem/Axioms.lean`: Update `MinPropAxiom.toIntProp` with 6 new cases
- [ ] In `ProofSystem/Axioms.lean`: Update `IntPropAxiom.toProp` with 6 new cases
- [ ] In `ProofSystem/Instances.lean`: Add `HasAxiomAndI`, `HasAxiomAndE1`, `HasAxiomAndE2`, `HasAxiomOrI1`, `HasAxiomOrI2`, `HasAxiomOrE` instances for `HilbertCl` (using `PropositionalAxiom` constructors)
- [ ] In `ProofSystem/IntMinInstances.lean`: Add same 6 instances for `HilbertInt` and `HilbertMin`
- [ ] In `NaturalDeduction/FromHilbert.lean`: Add 6 new cases to `subst_preserves_axiom`, `subst_preserves_intAxiom`, `subst_preserves_minAxiom` for the and/or axiom constructors
- [ ] In `NaturalDeduction/HilbertDerivedRules.lean`: Simplify `hilbertAndI`, `hilbertAndE1`, `hilbertAndE2`, `hilbertOrI1`, `hilbertOrI2`, `hilbertOrE` to use the new axioms directly (single/double modus ponens). Remove unnecessary classicality constraints.
- [ ] Run `lake build Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules` to verify

**Timing**: 2 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` -- 3 axiom inductives, 2 subsumption theorems
- `Cslib/Logics/Propositional/ProofSystem/Instances.lean` -- 6 new HasAxiom* instances for HilbertCl
- `Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean` -- 12 new HasAxiom* instances for HilbertInt, HilbertMin
- `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` -- subst_preserves_* theorems
- `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` -- simplified and/or rules

**Verification**:
- `lake build Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules` succeeds
- `lake build Cslib.Logics.Propositional.ProofSystem.IntMinInstances` succeeds

---

### Phase 5: ND-Hilbert Equivalence Bridge [COMPLETED]

**Goal**: Update `Equivalence.lean` so the ND-Hilbert correspondence holds level-by-level. Add cases for the 6 new ND constructors in `ndToHilbert` and for the 6 new axiom constructors in `hilbertToND`. Remove `botE` case from `ndToHilbert`.

**Tasks**:
- [ ] In `NaturalDeduction/Equivalence.lean`: Update `hilbertToND` (or its helper for axiom translation) to handle the 6 new axiom constructors (andI, andE1, andE2, orI1, orI2, orE). Each axiom maps to the corresponding ND derivation built from the new ND primitives.
- [ ] In `NaturalDeduction/Equivalence.lean`: Remove the `botE` case from `ndToHilbert`
- [ ] In `NaturalDeduction/Equivalence.lean`: Add 6 new cases to `ndToHilbert`:
  - `andI`: Two sub-derivations => use Hilbert andI axiom with two modus ponens
  - `andE1`: One sub-derivation => use Hilbert andE1 axiom with one modus ponens
  - `andE2`: Same pattern as andE1
  - `orI1`: One sub-derivation => use Hilbert orI1 axiom with one modus ponens
  - `orI2`: Same pattern as orI1
  - `orE`: Three sub-derivations (disjunction + two branches with extended contexts) => use deduction theorem on the two branches + Hilbert orE axiom with three modus ponens
- [ ] Verify the bridge theorem (hilbert_iff_nd or equivalent) still compiles
- [ ] Run `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence` to verify

**Timing**: 2 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` -- hilbertToND, ndToHilbert

**Verification**:
- `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence` succeeds
- Level-by-level correspondence: minimal ND <-> MinimalHilbert, ND + EFQ <-> IntuitionisticHilbert, ND + DNE <-> ClassicalHilbert

---

### Phase 6: Metalogic -- Soundness and Completeness [NOT STARTED]

**Goal**: Extend all soundness and completeness proofs with and/or cases. This covers classical (Soundness.lean, Completeness.lean), intuitionistic (IntSoundness.lean, IntCompleteness.lean), and minimal (MinSoundness.lean, MinCompleteness.lean) metalogic.

**Tasks**:
- [ ] In `Metalogic/Soundness.lean`: Add 6 cases to `prop_axiom_sound` for and/or axiom constructors: andI (intro twice, give pair), andE1 (project left), andE2 (project right), orI1 (inject left), orI2 (inject right), orE (case split on disjunction)
- [ ] In `Metalogic/IntSoundness.lean`: Add 6 cases to `int_axiom_sound` for and/or axiom constructors. These prove Kripke validity using `IForces` with `botForces = fun _ => False`. The orE case requires persistence reasoning.
- [ ] In `Metalogic/MinSoundness.lean`: Add 6 cases to `min_axiom_sound` for and/or axiom constructors. Same structure as IntSoundness but for MValid (arbitrary `botForces`).
- [ ] In `Metalogic/Completeness.lean`: Add and/or cases to the truth lemma or relevant function that pattern-matches on `Proposition` constructors
- [ ] In `Metalogic/IntCompleteness.lean`: Add and/or cases to the truth lemma
- [ ] In `Metalogic/MinCompleteness.lean`: Add and/or cases to the truth lemma
- [ ] Check MCS.lean, IntLindenbaum.lean, MinLindenbaum.lean for any formula pattern-matches that need updating (research report suggests these are formula-agnostic, but verify)
- [ ] Run `lake build Cslib.Logics.Propositional.Metalogic.MinCompleteness` (builds the entire metalogic dependency chain)

**Timing**: 2 hours

**Depends on**: 5

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/Soundness.lean` -- prop_axiom_sound
- `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean` -- int_axiom_sound
- `Cslib/Logics/Propositional/Metalogic/MinSoundness.lean` -- min_axiom_sound
- `Cslib/Logics/Propositional/Metalogic/Completeness.lean` -- truth lemma
- `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` -- truth lemma
- `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` -- truth lemma
- `Cslib/Logics/Propositional/Metalogic/MCS.lean` -- verify no changes needed
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` -- verify no changes needed (formula-agnostic)

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.Completeness` succeeds
- `lake build Cslib.Logics.Propositional.Metalogic.IntCompleteness` succeeds
- `lake build Cslib.Logics.Propositional.Metalogic.MinCompleteness` succeeds

---

### Phase 7: External Embeddings and CI Verification [NOT STARTED]

**Goal**: Update Modal/FromPropositional.lean and Temporal/FromPropositional.lean with and/or cases (using Lukasiewicz encoding to 3-constructor target types). Run the full CI verification pipeline.

**Tasks**:
- [ ] In `Cslib/Logics/Modal/FromPropositional.lean`: Add and/or cases to `toModal` using Lukasiewicz encoding into Modal.Proposition (which has only atom/bot/imp/box):
  - `| .and phi1 phi2 => .imp (.imp phi1.toModal (.imp phi2.toModal .bot)) .bot`
  - `| .or phi1 phi2 => .imp (.imp phi1.toModal .bot) phi2.toModal`
- [ ] In `Cslib/Logics/Modal/FromPropositional.lean`: Add `toModal_and` and `toModal_or` simp lemmas
- [ ] In `Cslib/Logics/Modal/FromPropositional.lean`: Update `modal_satisfies_toModal_iff_evaluate` induction with and/or cases. The Lukasiewicz encoding of and/or into imp/bot will need propositional-level equivalence reasoning to connect `Evaluate v (A /\ B)` (which is `Evaluate v A /\ Evaluate v B`) with `Evaluate v (neg (imp A (neg B)))` (which requires classical logic). If this coherence proof is not obtainable (because Lukasiewicz encoding is classically but not intuitionistically equivalent), mark the coherence theorem with `sorry` and document the gap for task 174 to resolve with proper Modal and/or constructors.
- [ ] In `Cslib/Logics/Temporal/FromPropositional.lean`: Add and/or cases to `toTemporal` using same Lukasiewicz encoding into Temporal.Formula (which has only atom/bot/imp/untl/snce):
  - `| .and phi1 phi2 => .imp (.imp phi1.toTemporal (.imp phi2.toTemporal .bot)) .bot`
  - `| .or phi1 phi2 => .imp (.imp phi1.toTemporal .bot) phi2.toTemporal`
- [ ] In `Cslib/Logics/Temporal/FromPropositional.lean`: Add `toTemporal_and` and `toTemporal_or` simp lemmas
- [ ] Run full CI pipeline:
  - `lake build` (full project, including all downstream Modal/Temporal/Bimodal modules)
  - `lake test`
  - `lake exe checkInitImports`
  - `lake exe lint-style`
- [ ] Fix any downstream breakage in Modal/Temporal/Bimodal modules caused by the Proposition constructor change (if pattern-matches exist there beyond the FromPropositional files)

**Timing**: 1 hour

**Depends on**: 6

**Files to modify**:
- `Cslib/Logics/Modal/FromPropositional.lean` -- toModal, simp lemmas, coherence proof
- `Cslib/Logics/Temporal/FromPropositional.lean` -- toTemporal, simp lemmas

**Verification**:
- `lake build` succeeds (full project)
- `lake test` passes
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional` succeeds (all Propositional modules)
- [ ] `lake build` succeeds (full project including Modal/Temporal/Bimodal)
- [ ] `lake test` passes
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] No `[IsClassical T]` constraints on andE1, andE2, orE, iffE1, iffE2 in DerivedRules.lean
- [ ] `botE` is a derived rule requiring `[IsIntuitionistic T]`, not a primitive constructor
- [ ] ND system has exactly 10 primitive constructors: ax, ass, andI, andE1, andE2, orI1, orI2, orE, impI, impE
- [ ] All three axiom inductives (MinPropAxiom, IntPropAxiom, PropositionalAxiom) have the 6 and/or axiom constructors
- [ ] ND-Hilbert equivalence bridge compiles for all three levels (minimal, intuitionistic, classical)

## Artifacts & Outputs

- `specs/173_propositional_five_primitive_refactor/plans/01_implementation-plan.md` (this plan)
- `specs/173_propositional_five_primitive_refactor/summaries/01_execution-summary.md` (post-implementation)
- Modified files across `Cslib/Foundations/Logic/`, `Cslib/Logics/Propositional/`, `Cslib/Logics/Modal/FromPropositional.lean`, `Cslib/Logics/Temporal/FromPropositional.lean`

## Rollback/Contingency

All changes are within Lean source files tracked by git. Rollback via `git checkout main -- Cslib/` restores the pre-refactor state. Each phase is committed independently, so partial rollback to any phase boundary is possible via `git revert`. If completeness proofs in Phase 6 prove intractable, the phase can be marked [PARTIAL] with `sorry`-annotated stubs and a follow-up task created. If the Lukasiewicz embedding coherence in Phase 7 cannot be proved, the coherence theorems can be left with `sorry` for tasks 174/176 to resolve with proper constructors.
