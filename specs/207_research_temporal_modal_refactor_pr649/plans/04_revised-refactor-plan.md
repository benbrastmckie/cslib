# Implementation Plan: Generic Deduction Theorem and MCS via listImp

- **Task**: 207 - Research refactoring Temporal/ and Modal/ implementations based on PR #649 review feedback
- **Status**: [IMPLEMENTING]
- **Effort**: 25 hours
- **Dependencies**: None (PR #649 must be merged first, but the generic files build independently)
- **Research Inputs**: reports/01_team-research.md, reports/02_reviewer-directed-research.md, reports/03_ideal-solution-research.md
- **Artifacts**: plans/04_revised-refactor-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

The PR #649 reviewer identified that CSLib duplicates the deduction theorem proof and MCS machinery across Modal, Temporal, and Bimodal logics (~890 LOC). The previous plan (v1, 03_refactor-plan.md) addressed only the MCS property extraction -- the "easy half" of the reviewer's vision. Round 3 research discovered the complete ideal solution: the Isabelle `listImp` approach makes the deduction theorem definitional rather than requiring induction on proof trees, while CSLib's existing `MinimalHilbert` class already IS the reviewer's `implication_logic`. This revised plan implements the FULL solution: a generic algebraic deduction theorem via `listImp`, plus generic MCS construction, both following from the Isabelle `Propositional_Logic_Class` pattern adapted to CSLib's tag-based proof system architecture.

The key insight is that CSLib can maintain BOTH representations: Type-valued `DerivationTree` for soundness (which needs pattern matching on constructors), and Prop-valued `ListDeriv` for metalogic (deduction theorem, MCS, completeness). The bridge is a simple per-logic induction on the tree that is far shorter than the current per-logic deduction theorem proofs.

### Research Integration

Three research rounds inform this plan:

- **Round 1** (team research, 4 teammates): Quantified ~890 LOC of duplication, evaluated FormulaFunctor, Mixin Property Classes, and Isabelle-Style approaches. Recommended phased Mixin approach. Confirmed `MinimalHilbert` = reviewer's `implication_logic`.
- **Round 2** (reviewer-directed): Line-by-line comparison of all four MCS files. Concluded the deduction theorem "cannot be genericized" due to tree induction -- but this was based on the false assumption that contextual derivation must use proof trees.
- **Round 3** (ideal-solution): Found the Isabelle `listImp` trick that makes the DT definitional. Verified CSLib has all prerequisites (MinimalHilbert, combinator library, DerivationSystem framework). Identified `list_flip_implication1/2` proofs as critical path. Provided complete file-by-file design with code sketches.

### Prior Plan Reference

This plan supersedes `plans/03_refactor-plan.md` (v1, 5 phases, 6 hours, MCS-only extraction). The v1 plan's Phase 1 (generic MCSProperties.lean) is preserved as Phase 6 below. All other v1 phases are replaced by the broader listImp-based design from Round 3 research.

### Roadmap Alignment

This plan advances the ROADMAP.md item "Abstract shared completeness infrastructure" (Phase 3). It specifically targets both the deduction theorem layer (the hard half, now made tractable by listImp) and the MCS property layer (the easy half, from v1).

## Goals & Non-Goals

**Goals**:
- Implement `listImp` definition and flip lemma proofs in `ListImplication.lean`
- Implement `ListDeriv` and the algebraic deduction theorem in `ListDeduction.lean`
- Implement set-level derivation in `SetDeduction.lean`
- Build `algebraicDerivationSystem` with automatic `HasDeductionTheorem` in `GenericMCS.lean`
- Create generic MCS bot/negation/membership lemmas in `MCSProperties.lean`
- Migrate Modal, Temporal, and Bimodal MCS files to use generic versions
- Pass full CI pipeline (`lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake`)
- Produce PRs suitable for upstream review (~300-500 LOC each)

**Non-Goals**:
- Replacing per-logic tree-level deduction theorem proofs in this PR (keep as alternative proofs; bridge + deletion is a follow-up)
- Introducing a generic `DerivationTree` type (positivity/height issues remain)
- Touching Bimodal's internal metalogic beyond the MCS wrapper layer (~51K LOC)
- Fixing the axiom name swap (`.imp_s` vs `.imp_k`) in Temporal/Bimodal (separate task)
- Connecting bridge theorems (`tree_to_listDeriv`) for each logic (follow-up PR)
- Unifying formula types across logics

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `list_flip_implication1/2` proofs are harder in Lean 4 than Isabelle's `meson` suggests | High | Medium | The combinator library already has `flip`, `b_combinator`, `identity`; budget extra time (6-8h); use `lean_multi_attempt` for tactic exploration |
| `listImp_axiom_s` inductive step requires complex S-combinator composition | Medium | Medium | Follow Isabelle proof structure step by step; the base case is just S; each step adds one layer of K/S composition |
| `list_deriv_monotonic` requires `removeAll`-based helper (~100 lines) | Medium | Medium | Isabelle proof is 60 lines; budget 80-120 lines in Lean 4; can use `sorry` temporarily and circle back |
| Breaking downstream imports in completeness files | High | Low | Use `alias`/`abbrev` to preserve all existing names; run scoped `lake build` after each logic migration |
| Bimodal cascading breakage (51K LOC) | High | Low | Touch Bimodal last; only modify thin MCS wrappers; use aliases only |
| Typeclass resolution slowdown from new files | Medium | Low | No new typeclasses introduced -- only parametric definitions over existing `MinimalHilbert`; benchmark build time |
| Temporal MCS fragility (`maxHeartbeats 1600000`) | Medium | Medium | Only replace wrapper lemmas; preserve temporal-specific proofs verbatim |
| `lake shake` flags new imports as unused | Low | Medium | Run `lake shake` incrementally; add `public import` where needed |

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
| 8 | 8 | 7 |

Phases are strictly sequential. Each builds on the prior phase's output.

---

### Phase 1: Add Missing Combinator [COMPLETED]

**Goal**: Add `implication_absorption` (`|- (phi -> phi -> psi) -> phi -> psi`) to the combinator library, which is required by the `list_flip_implication` proofs.

**Tasks**:
- [ ] Add `implication_absorption` theorem to `Cslib/Foundations/Logic/Theorems/Combinators.lean`
- [ ] Proof approach: derive from S and K (Isabelle proof: `meson axiom_k axiom_s modus_ponens`)
- [ ] Verify the combinator has signature `InferenceSystem.DerivableIn S (HasImp.imp (HasImp.imp phi (HasImp.imp phi psi)) (HasImp.imp phi psi))`
- [ ] Run `lake build Cslib.Foundations.Logic.Theorems.Combinators` to verify
- [ ] Run `lake exe lint-style`

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Theorems/Combinators.lean` -- ADD: `implication_absorption` (~15 LOC)

**Verification**:
- `lake build Cslib.Foundations.Logic.Theorems.Combinators` succeeds with zero warnings
- `lake exe lint-style` passes
- Theorem has the expected type signature

---

### Phase 2: ListImplication.lean -- listImp and Flip Lemmas [COMPLETED]

**Goal**: Create the foundational `ListImplication.lean` file defining the `listImp` function and proving the four key lemmas: `listImp_axiom_k`, `listImp_axiom_s`, `list_flip_implication1`, and `list_flip_implication2`. This is the CRITICAL PATH -- the entire plan depends on these proofs.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Metalogic/ListImplication.lean` with module header and copyright
- [ ] Import `Cslib.Foundations.Logic.Theorems.Combinators` (provides `identity`, `flip`, `b_combinator`, `imp_trans`, `implication_absorption`)
- [ ] Define `listImp : List F -> F -> F` (recursive: nil case = identity, cons case = imp)
- [ ] Prove `listImp_axiom_k`: `|- phi -> listImp Gamma phi` (induction on Gamma; uses K + `imp_trans`)
- [ ] Prove `listImp_axiom_s`: `|- listImp Gamma (phi -> psi) -> listImp Gamma phi -> listImp Gamma psi` (induction on Gamma; base = S axiom, step = S + B-combinator composition)
- [ ] Prove `list_flip_implication1`: `|- listImp (phi :: Gamma) chi -> listImp Gamma (phi -> chi)` (induction on Gamma; uses `flip`, `hypothetical_syllogism`/`b_combinator`, `implication_absorption`)
- [ ] Prove `list_flip_implication2`: `|- listImp Gamma (phi -> chi) -> listImp (phi :: Gamma) chi` (induction on Gamma; reverse direction of flip1)
- [ ] Add `Cslib.Foundations.Logic.Metalogic.ListImplication` to `Cslib.lean` barrel import
- [ ] Run `lake build Cslib.Foundations.Logic.Metalogic.ListImplication` to verify
- [ ] Run `lake exe checkInitImports` and `lake exe lint-style`

**Timing**: 6-8 hours (flip lemma proofs are nontrivial combinator manipulations)

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/ListImplication.lean` -- NEW: ~200 LOC
- `Cslib.lean` -- Add import line

**Verification**:
- `lake build Cslib.Foundations.Logic.Metalogic.ListImplication` succeeds with zero sorrys
- All four key lemmas typecheck with expected signatures
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes

**Notes**:
- This is the highest-risk phase. The Isabelle proofs use `meson` (resolution prover); Lean 4 requires manual combinator assembly. Budget extra time.
- If flip lemma proofs stall, use `lean_multi_attempt` and `lean_state_search` to explore tactic approaches.
- The `listImp_axiom_s` inductive step is the single hardest proof in the entire plan.

---

### Phase 3: ListDeduction.lean -- Algebraic Deduction Theorem [COMPLETED]

**Goal**: Create `ListDeduction.lean` defining `ListDeriv` (algebraic contextual derivation) and proving the deduction theorem, monotonicity, reflection, cut, and contextual modus ponens. The deduction theorem proof uses the flip lemmas from Phase 2.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Metalogic/ListDeduction.lean` with module header
- [ ] Import `Cslib.Foundations.Logic.Metalogic.ListImplication`
- [ ] Define `ListDeriv (Gamma : List F) (phi : F) : Prop := InferenceSystem.DerivableIn S (listImp Gamma phi)`
- [ ] Prove `list_deduction_theorem`: `ListDeriv (phi :: Gamma) psi <-> ListDeriv Gamma (phi -> psi)` (uses `list_flip_implication1/2`)
- [ ] Prove `list_deriv_reflection`: `phi in Gamma -> ListDeriv Gamma phi` (from `listImp_axiom_k` and identity)
- [ ] Prove `list_deriv_mp`: from `ListDeriv Gamma (phi -> psi)` and `ListDeriv Gamma phi`, derive `ListDeriv Gamma psi` (uses `listImp_axiom_s`)
- [ ] Define helper `list_implication_removeAll` for monotonicity proof
- [ ] Prove `list_deriv_monotonic`: if `set Sigma <= set Gamma` then `ListDeriv Sigma phi -> ListDeriv Gamma phi` (complex induction, ~80-120 LOC)
- [ ] Prove `list_deriv_cut`: from `ListDeriv (phi :: Gamma) psi` and `ListDeriv Delta phi`, derive `ListDeriv (Gamma ++ Delta) psi`
- [ ] Prove `list_deriv_weaken`: from `ListDeriv Gamma phi` and subset, derive `ListDeriv (Gamma ++ Delta) phi`
- [ ] Add to `Cslib.lean` barrel import
- [ ] Run `lake build Cslib.Foundations.Logic.Metalogic.ListDeduction`

**Timing**: 4-6 hours (monotonicity is the most effort-intensive proof)

**Depends on**: 2

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/ListDeduction.lean` -- NEW: ~250 LOC
- `Cslib.lean` -- Add import line

**Verification**:
- `lake build Cslib.Foundations.Logic.Metalogic.ListDeduction` succeeds with zero sorrys
- `list_deduction_theorem` has the expected biconditional type
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes

---

### Phase 4: SetDeduction.lean -- Set-Level Derivation [COMPLETED]

**Goal**: Create `SetDeduction.lean` lifting list-level derivation to set-level. This provides the interface used by the MCS machinery, which works with `Set F` rather than `List F`.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Metalogic/SetDeduction.lean` with module header
- [ ] Import `Cslib.Foundations.Logic.Metalogic.ListDeduction`
- [ ] Define `SetDeriv (Gamma : Set F) (phi : F) : Prop := exists L : List F, (forall x, x in L -> x in Gamma) /\ ListDeriv L phi`
- [ ] Prove `set_deduction_theorem`: `SetDeriv (insert phi Gamma) psi <-> SetDeriv Gamma (phi -> psi)`
- [ ] Prove `set_deriv_monotonic`: if `Sigma <= Gamma` then `SetDeriv Sigma phi -> SetDeriv Gamma phi`
- [ ] Prove `set_deriv_reflection`: `phi in Gamma -> SetDeriv Gamma phi`
- [ ] Prove `set_deriv_cut`: from `SetDeriv (insert phi Gamma) psi` and `SetDeriv Gamma phi`, derive `SetDeriv Gamma psi`
- [ ] Prove `set_deriv_mp`: from `SetDeriv Gamma (phi -> psi)` and `SetDeriv Gamma phi`, derive `SetDeriv Gamma psi`
- [ ] Add to `Cslib.lean` barrel import
- [ ] Run `lake build Cslib.Foundations.Logic.Metalogic.SetDeduction`

**Timing**: 2-3 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/SetDeduction.lean` -- NEW: ~150 LOC
- `Cslib.lean` -- Add import line

**Verification**:
- `lake build Cslib.Foundations.Logic.Metalogic.SetDeduction` succeeds with zero sorrys
- `set_deduction_theorem` matches the Isabelle equivalent
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes

---

### Phase 5: GenericMCS.lean -- Algebraic Derivation System with Free Deduction Theorem [COMPLETED]

**Goal**: Create `GenericMCS.lean` that builds a `DerivationSystem` from `ListDeriv` and proves `HasDeductionTheorem` for it automatically. This is the bridge between the new algebraic infrastructure and CSLib's existing `Consistency.lean` framework, making all existing MCS lemmas (`closed_under_derivation`, `implication_property`, `negation_complete`) available for free.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` with module header
- [ ] Import `Cslib.Foundations.Logic.Metalogic.SetDeduction` and `Cslib.Foundations.Logic.Metalogic.Consistency`
- [ ] Define `algebraicDerivationSystem : DerivationSystem F` with `Deriv := ListDeriv`, `weakening := list_deriv_monotonic`, `assumption := list_deriv_reflection`, `mp := list_deriv_mp`
- [ ] Prove `algebraic_has_deduction_theorem : HasDeductionTheorem algebraicDerivationSystem` (one-liner via `list_deduction_theorem`)
- [ ] Verify that `Consistency.closed_under_derivation`, `Consistency.implication_property`, `Consistency.negation_complete` all resolve with the algebraic system
- [ ] Prove convenience wrappers: `algebraic_mcs_closed_under_derivation`, `algebraic_mcs_implication_property`, `algebraic_mcs_negation_complete` (instantiate Consistency lemmas with algebraicDerivationSystem)
- [ ] Add to `Cslib.lean` barrel import
- [ ] Run `lake build Cslib.Foundations.Logic.Metalogic.GenericMCS`

**Timing**: 2-3 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` -- NEW: ~200 LOC
- `Cslib.lean` -- Add import line

**Verification**:
- `lake build Cslib.Foundations.Logic.Metalogic.GenericMCS` succeeds with zero sorrys
- `algebraic_has_deduction_theorem` typechecks as `HasDeductionTheorem algebraicDerivationSystem`
- All three Consistency lemmas instantiate without additional proof obligations
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes

---

### Phase 6: MCSProperties.lean -- Generic Bot/Negation/Membership Lemmas [COMPLETED]

**Goal**: Create generic MCS bot/negation/membership lemmas that are proved ONCE and reusable by all logics. This phase corresponds to the v1 plan's Phase 1, now built on top of the algebraic infrastructure from Phase 5.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Metalogic/MCSProperties.lean` with module header
- [ ] Import `Cslib.Foundations.Logic.Metalogic.GenericMCS`
- [ ] Implement `mcs_bot_not_mem`: If `S` is MCS (over algebraicDerivationSystem), then `bot not in S`
- [ ] Implement `mcs_neg_of_not_mem`: If `phi not in S` (MCS), then `(phi -> bot) in S`
- [ ] Implement `mcs_not_mem_of_neg`: If `(phi -> bot) in S` (MCS), then `phi not in S`
- [ ] Implement `mcs_mem_iff_neg_not_mem`: `phi in S <-> (phi -> bot) not in S` for MCS `S`
- [ ] Implement `mcs_mp_axiom`: Derive `psi in S` from `phi in S` and `ListDeriv [] (phi -> psi)` via `algebraic_mcs_closed_under_derivation`
- [ ] Implement `mcs_theorem_in_mcs`: Theorems (derivable from empty context) belong to every MCS
- [ ] Add to `Cslib.lean` barrel import
- [ ] Run `lake build Cslib.Foundations.Logic.Metalogic.MCSProperties`
- [ ] Run `lake exe checkInitImports` and `lake exe lint-style`

**Timing**: 2-3 hours

**Depends on**: 5

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/MCSProperties.lean` -- NEW: ~150 LOC
- `Cslib.lean` -- Add import line

**Verification**:
- `lake build Cslib.Foundations.Logic.Metalogic.MCSProperties` succeeds with zero sorrys
- All lemmas have type signatures matching what per-logic MCS files currently define
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes

---

### Phase 7: Per-Logic MCS Migration [PARTIAL]

**Goal**: Simplify Modal, Temporal, and Bimodal MCS files to delegate common lemmas to generic `MCSProperties.lean`. Preserve all existing API names via `alias` or direct delegation. Keep logic-specific lemmas unchanged.

**Tasks**:
- [ ] **Modal**: Add `import Cslib.Foundations.Logic.Metalogic.MCSProperties` to `Cslib/Logics/Modal/Metalogic/MCS.lean` *(deviation: deferred -- requires bridge theorem `tree_to_listDeriv` connecting modalDerivationSystem to algebraicDerivationSystem)*
- [ ] **Modal**: Replace `mcs_bot_not_mem`, `mcs_neg_of_not_mem`, `mcs_not_mem_of_neg`, `mcs_mem_iff_neg_not_mem`, `mcs_mp_axiom` bodies with calls to generic versions *(deviation: deferred -- same blocker)*
- [ ] **Modal**: Preserve modal-specific lemmas (`mcs_box_closure`, `mcs_box_box`, `mcs_box_diamond`, `mcs_box_mp`, `mcs_box_witness`, `iteratedDeduction`, etc.) unchanged *(deviation: skipped -- no changes made)*
- [ ] **Modal**: Verify `lake build Cslib.Logics.Modal` succeeds *(deviation: skipped -- no changes made)*
- [ ] **Temporal**: Add import to `Cslib/Logics/Temporal/Metalogic/MCS.lean` *(deviation: deferred -- requires bridge theorem)*
- [ ] **Temporal**: Replace common wrapper lemmas with generic calls *(deviation: deferred -- same blocker)*
- [ ] **Temporal**: Preserve temporal-specific lemmas *(deviation: skipped -- no changes made)*
- [ ] **Temporal**: Verify `lake build Cslib.Logics.Temporal` succeeds *(deviation: skipped -- no changes made)*
- [ ] **Bimodal**: Add import to `Cslib/Logics/Bimodal/Metalogic/Core/MaximalConsistent.lean` *(deviation: deferred -- requires bridge theorem)*
- [ ] **Bimodal**: Evaluate which wrappers can delegate to generic *(deviation: deferred -- same blocker)*
- [ ] **Bimodal**: Preserve all Bimodal list-based MCS definitions and helpers *(deviation: skipped -- no changes made)*
- [ ] **Bimodal**: Verify `lake build Cslib.Logics.Bimodal` succeeds *(deviation: skipped -- no changes made)*
- [ ] Run `lake exe lint-style` across all three logics *(deviation: skipped -- no changes made)*

**Phase 7 Deviation Note**: Per-logic MCS migration requires bridge theorems connecting each logic's `DerivationTree`-based derivation system to the `algebraicDerivationSystem`. This is explicitly listed in Non-Goals: "Connecting bridge theorems (`tree_to_listDeriv`) for each logic (follow-up PR)". The generic infrastructure (Phases 1-6) is complete and new logics can use it directly. Migration of existing logics is a follow-up task.

**Timing**: 3-4 hours

**Depends on**: 6

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/MCS.lean` -- SIMPLIFIED: ~-80 LOC
- `Cslib/Logics/Temporal/Metalogic/MCS.lean` -- SIMPLIFIED: ~-70 LOC
- `Cslib/Logics/Bimodal/Metalogic/Core/MaximalConsistent.lean` -- SIMPLIFIED: ~-80 LOC

**Verification**:
- `lake build Cslib.Logics.Modal` succeeds
- `lake build Cslib.Logics.Temporal` succeeds
- `lake build Cslib.Logics.Bimodal` succeeds
- All existing theorem names still resolve (downstream completeness files unaffected)
- `lake exe lint-style` passes for all three logics

---

### Phase 8: Full CI Verification and Cleanup [IN PROGRESS]

**Goal**: Run the complete CI pipeline, fix any remaining issues, and verify the entire project builds cleanly with the new generic metalogic infrastructure.

**Tasks**:
- [ ] Run `lake build` (full project build)
- [ ] Run `lake test` (CslibTests suite)
- [ ] Run `lake exe checkInitImports` (verify all files import Cslib.Init)
- [ ] Run `lake exe lint-style` (style linting)
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` (dependency analysis)
- [ ] Verify zero sorrys in all new files via `lean_verify` on key theorems
- [ ] Check for any build time regression (compare `lake build` time before/after)
- [ ] Fix any `lake shake` warnings (add `public import` where needed)
- [ ] Verify Propositional MCS is also covered (if it uses the same pattern, add delegation)
- [ ] Final review: confirm all new files follow CSLib conventions (copyright headers, namespace structure, docstrings)

**Timing**: 2-3 hours

**Depends on**: 7

**Files to modify**:
- Various files as needed based on CI feedback (primarily import adjustments)

**Verification**:
- Full `lake build` succeeds with zero errors and zero sorrys
- `lake test` passes
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lake shake` reports no unnecessary imports
- Build time does not regress significantly

## Testing & Validation

- [ ] `lake build Cslib.Foundations.Logic.Theorems.Combinators` -- implication_absorption added
- [ ] `lake build Cslib.Foundations.Logic.Metalogic.ListImplication` -- listImp + flip lemmas
- [ ] `lake build Cslib.Foundations.Logic.Metalogic.ListDeduction` -- algebraic DT + monotonicity
- [ ] `lake build Cslib.Foundations.Logic.Metalogic.SetDeduction` -- set-level derivation
- [ ] `lake build Cslib.Foundations.Logic.Metalogic.GenericMCS` -- algebraic DerivationSystem + free HasDT
- [ ] `lake build Cslib.Foundations.Logic.Metalogic.MCSProperties` -- generic bot/neg/membership
- [ ] `lake build Cslib.Logics.Modal` -- Modal migration succeeds
- [ ] `lake build Cslib.Logics.Temporal` -- Temporal migration succeeds
- [ ] `lake build Cslib.Logics.Bimodal` -- Bimodal migration succeeds
- [ ] `lake build` -- full project builds cleanly
- [ ] `lake test` -- all tests pass
- [ ] `lake exe checkInitImports` -- all files import `Cslib.Init`
- [ ] `lake exe lint-style` -- style checks pass
- [ ] `lake shake --add-public --keep-implied --keep-prefix` -- import analysis clean
- [ ] `lean_verify` on key theorems in new files confirms zero sorrys and no axiom leaks
- [ ] Verify no regression in heartbeat counts for Temporal/Bimodal builds

## Artifacts & Outputs

**New files** (~950 LOC total):
- `Cslib/Foundations/Logic/Theorems/Combinators.lean` -- MODIFIED: +15 LOC (`implication_absorption`)
- `Cslib/Foundations/Logic/Metalogic/ListImplication.lean` -- NEW: ~200 LOC (listImp, flip lemmas)
- `Cslib/Foundations/Logic/Metalogic/ListDeduction.lean` -- NEW: ~250 LOC (ListDeriv, DT, monotonicity, cut)
- `Cslib/Foundations/Logic/Metalogic/SetDeduction.lean` -- NEW: ~150 LOC (SetDeriv, set-level theorems)
- `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` -- NEW: ~200 LOC (algebraicDerivationSystem + free HasDT)
- `Cslib/Foundations/Logic/Metalogic/MCSProperties.lean` -- NEW: ~150 LOC (generic bot/neg lemmas)

**Simplified files** (~230 LOC removed):
- `Cslib/Logics/Modal/Metalogic/MCS.lean` -- SIMPLIFIED: ~-80 LOC
- `Cslib/Logics/Temporal/Metalogic/MCS.lean` -- SIMPLIFIED: ~-70 LOC
- `Cslib/Logics/Bimodal/Metalogic/Core/MaximalConsistent.lean` -- SIMPLIFIED: ~-80 LOC

**Net change**: ~965 LOC added, ~230 LOC removed = ~735 LOC net new

**Plan artifact**: `specs/207_research_temporal_modal_refactor_pr649/plans/04_revised-refactor-plan.md` (this file)

## Rollback/Contingency

1. **Phase-level revert**: Each phase creates new files or modifies existing files independently. Any single phase can be reverted via `git checkout` without affecting others (except that later phases depend on earlier ones).
2. **New files are additive**: The five new Foundations files (`ListImplication`, `ListDeduction`, `SetDeduction`, `GenericMCS`, `MCSProperties`) cannot break existing code -- they only add new definitions.
3. **MCS migration is independently revertible**: If Modal migration works but Temporal breaks, revert only the Temporal MCS file. The generic infrastructure remains usable.
4. **Bimodal safety valve**: If Bimodal migration causes cascading issues in the 51K LOC downstream, skip Bimodal migration entirely and keep existing thin wrappers.
5. **Flip lemma fallback**: If `list_flip_implication1/2` proofs prove intractable in Lean 4, the plan can be truncated after Phase 1 (combinator) and the v1 plan's MCS-only approach (Phases 6-7) can proceed independently using the existing per-logic `HasDeductionTheorem` proofs.
6. **Worst case**: Delete all new files and revert all modified files -- zero net change to the repository. The existing per-logic metalogic continues to work.
