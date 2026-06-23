# Implementation Plan: Generic Hilbert Proof-Search Tactic (v2)

- **Task**: 269 - hilbert_search_tactic
- **Status**: [COMPLETED]
- **Effort**: 8 hours
- **Dependencies**: Task 268 (normalization tags -- completed)
- **Research Inputs**: specs/269_hilbert_search_tactic/reports/01_team-research.md, specs/269_hilbert_search_tactic/reports/03_team-research.md
- **Artifacts**: plans/04_hilbert-search-plan-v2.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Build a generic bounded depth-first proof-search tactic (`hilbert_search`) for CSLib's
`InferenceSystem` typeclass, enabling automated Hilbert-style derivations across all
registered proof systems (propositional, modal, temporal, bimodal). The implementation uses
a MetaM-only architecture with `MVarId.apply` + `observing?` backtracking, eliminating the
need for `HasImpView`/`HasBoxView` typeclasses that do not exist in CSLib. Lean's unifier
handles formula matching transparently via `apply`, and typeclass availability is checked
implicitly by whether `apply` succeeds. Definition of done: the tactic closes
`DerivableIn S phi` goals for propositional, modal, and temporal systems at default fuel 30,
passes all CSLib CI checks, and includes a comprehensive test suite.

### Research Integration

This plan supersedes the v1 plan (02_hilbert-search-plan.md) based on Round 2 team research
(4 teammates). The following reports were integrated:

- **03_team-research.md** (synthesis): Architecture decision resolved in favor of MetaM-only.
  Four-priority rule stratification established. Fuel/depth parameters synthesized.
- **03_teammate-a-findings.md**: Verified working MetaM/TacticM prototype code patterns.
  `MVarId.apply` with `ApplyConfig { newGoals := .nonDependentOnly }` confirmed as the correct
  API. `mkConstWithFreshMVarLevels` required for universe polymorphism.
- **03_teammate-b-findings.md**: Confirmed absence of `HasImpView`/`HasBoxView` in CSLib.
  Documented `noncomputable` boundary and full typeclass hierarchy. Decisive evidence that
  term-mode generic search is not viable without new Foundations typeclasses.
- **03_teammate-c-findings.md**: CSLib contribution standards checklist. File structure,
  `public meta section` pattern, naming conventions, lint requirements, trace class
  registration, testing patterns (`success_if_fail_with_msg`, `#guard_msgs`), CI pipeline order.
- **03_teammate-d-findings.md**: Survey of ~85 theorems. Depth/branching analysis: depth 5
  covers ~75% of theorems, depth 8 with library covers ~85%. Golden test cases (Tier 1-3)
  with expected depths.

### Key Architecture Change from v1

The v1 plan used a two-layer architecture: a term-mode search core (Tier 1) returning
`Option (DerivableIn S phi)`, wrapped by a thin `TacticM` elaborator (Tier 2). Round 2
research found that the term-mode approach requires formula decomposition typeclasses
(`HasImpView`/`HasBoxView`) that do not exist in CSLib. The MetaM `apply`-based approach
eliminates this dependency entirely:

- `MVarId.apply` uses Lean's unifier to match the goal against axiom types
- `observing?` provides checkpoint/rollback for backtracking
- `mkConstWithFreshMVarLevels` handles universe polymorphism
- Typeclass availability is implicit: `apply HasAxiomK.K` fails and rolls back when
  `[HasAxiomK S]` is not available

The v1 Phase 2 (Zulip discussion) is also removed; the Round 2 research replaces this
by establishing the architecture with verified prototypes.

### Prior Plan Reference

v1: specs/269_hilbert_search_tactic/plans/02_hilbert-search-plan.md (superseded)

### Roadmap Alignment

The `hilbert_search` tactic is foundational cross-cutting infrastructure that enables automated
proof derivation across all proof systems in `Foundations/Logic/` and all logic modules
(`Propositional`, `Modal`, `Temporal`, `Bimodal`). It is novel infrastructure supporting the
overall mission of building shared automation for CSLib.

## Goals & Non-Goals

**Goals**:
- Implement a MetaM-based bounded DFS search function (`hilbertSearchCore`) generic over
  all `InferenceSystem` proof systems via `MVarId.apply` + `observing?`
- Implement a thin tactic wrapper exposing `hilbert_search (fuel)` syntax with default fuel 30
- Use four-priority rule stratification: assumptions, zero-subgoal axioms, one-subgoal derived
  rules, two-subgoal rules (MP last)
- Support axiom matching, local hypothesis scanning, and modus ponens chaining
- Provide configurable fuel with informative error messages on failure
- Include a trace class for debugging (`set_option trace.Cslib.Logic.hilbertSearch true`)
- Work across Propositional, Modal, and Temporal systems without per-type specialization
- Pass all CSLib CI checks (`lake build`, `lake test`, `checkInitImports`, `lint-style`,
  `lake shake`)

**Non-Goals**:
- Term-mode search function returning `Option (DerivableIn S phi)` (requires `HasImpView`
  typeclasses not in CSLib)
- `HasImpView`/`HasBoxView` typeclass additions to `Foundations/Logic/Connectives.lean`
  (separate Foundations contribution, out of scope)
- Context-relative goals `Gamma |- phi` (out of scope; `DerivableIn` is empty-context only)
- `hilbert_search?` verbose variant with `Try this:` proof reporting (Phase 2 feature)
- `@[hilbert_search_rule]` attribute for user-defined rules (Phase 2 feature)
- Registering `hilbert_search` as `@[simp]` or `@[aesop]`
- Proof-by-reflection / `decide`-based architecture

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| MP backward chaining exponential blowup from unconstrained `?phi` in `DerivableIn S (imp ?phi psi)` | H | M | Four-priority rule ordering ensures MP is tried last; add cycle detection via `HashSet Expr` of visited goals per search path; fuel limit bounds total work |
| Universe polymorphism unification failures with `MVarId.apply` on axiom methods | H | L | Use `mkConstWithFreshMVarLevels` (verified working by Teammate A prototype); `ApplyConfig { newGoals := .nonDependentOnly }` filters type-level goals |
| Typeclass inference timeout on deeply nested search | M | M | Default fuel 30 covers observed proof depths (max ~20 for `app2`); fuel decrement per rule application bounds total nodes |
| PR rejected on code style (meta section not fitting CSLib conventions) | M | L | Model on `Relation/Attr.lean` and `Semantics/LTS/Notation.lean` patterns; follow Teammate C's lint checklist |
| `docBlame` linter failures on meta section declarations | M | M | Add docstrings to all public declarations; use `@[nolint docBlame]` for internal helpers per CSLib convention |
| Performance on large bimodal formulas (8-12 subformulas) not tested | L | M | Register trace class for profiling; add performance test cases; fuel limit prevents runaway |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

---

### Phase 1: MetaM Search Core and Tactic Wrapper [COMPLETED]

**Goal**: Implement the complete MetaM-based bounded DFS search function and the tactic
wrapper in a single file, covering propositional and modal axioms.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Automation/HilbertSearch.lean` with copyright header, `module`, `public import Cslib.Init`, `public import Cslib.Foundations.Logic.ProofSystem`, `public import Cslib.Foundations.Logic.Theorems.Combinators`, `public import Cslib.Foundations.Logic.Theorems.Modal.Basic`
- [ ] Open `public meta section` block with `open Lean Meta Elab.Tactic in`
- [ ] Register trace class: `initialize registerTraceClass `Cslib.Logic.hilbertSearch`
- [ ] Implement `matchDerivableIn : Expr -> Option (Expr * Expr)` -- extract `(S, phi)` from `DerivableIn S phi` using `isAppOfArity ``InferenceSystem.DerivableIn 4` and `getAppArgs`
- [ ] Define axiom name arrays organized by priority tier:
  - Zero-subgoal axioms: `HasAxiomImplyK.implyK`, `HasAxiomImplyS.implyS`, `HasAxiomEFQ.efq`, `HasAxiomPeirce.peirce`, `HasAxiomK.K`, `HasAxiomT.T`, `HasAxiom4.four`, `HasAxiomB.B`, `HasAxiom5.five`, `HasAxiomD.D`
  - One-subgoal derived rules: `Theorems.Combinators.identity`, `Theorems.Combinators.b_combinator`, `Theorems.Modal.Basic.box_mono`, `Necessitation.nec`
  - Two-subgoal rules: `Theorems.Combinators.imp_trans`, `ModusPonens.mp`
- [ ] Implement `hilbertSearchCore : MVarId -> Nat -> MetaM Bool` as `partial def` with four-priority stratified search:
  - Priority 1: Assumption lookup -- iterate `getLCtx`, skip `isImplementationDetail`, check `isDefEq decl.type goalTy`, assign `goal.assign decl.toExpr` on match
  - Priority 2: Zero-subgoal axioms -- `mkConstWithFreshMVarLevels` + `MVarId.apply` with `{ newGoals := .nonDependentOnly }` + `observing?`; succeed if `newGoals.isEmpty`
  - Priority 3: One-subgoal rules -- same apply pattern, recursively call `hilbertSearchCore` on each non-assigned subgoal with `fuel - 1`
  - Priority 4: Two-subgoal rules -- same pattern with recursive calls on all subgoals
- [ ] Add `withTraceNode` calls at each search step, gated on `Cslib.Logic.hilbertSearch`
- [ ] Add cycle detection: pass `HashSet Expr` of visited goal types; skip goals already seen on current search path
- [ ] Implement tactic wrapper: `elab "hilbert_search" n:(num)? : tactic` with default fuel 30
- [ ] Implement error reporting: use `throwTacticEx` with fuel limit, pretty-printed goal type, and remediation hint ("try `hilbert_search {fuel * 2}`")
- [ ] Add docstrings to all public declarations (`hilbertSearchCore`, `matchDerivableIn`, tactic syntax)
- [ ] Close `end` for the meta section and namespace `Cslib.Logic.Automation`
- [ ] Run `lake exe mk_all --module` to register in `Cslib.lean`
- [ ] Run `lake build Cslib.Foundations.Logic.Automation.HilbertSearch`
- [ ] Verify with inline `example` proofs: `DerivableIn S (imp phi phi)` (identity, depth 1), `DerivableIn S (imp a (imp b a))` (ImplyK, depth 1)

**Timing**: 3 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Automation/HilbertSearch.lean` -- new file: core search + tactic
- `Cslib.lean` -- barrel import update via `lake exe mk_all --module`

**Verification**:
- `lake build Cslib.Foundations.Logic.Automation.HilbertSearch` compiles without errors
- Inline `example` proofs close identity and ImplyK goals
- No `sorry` in the file
- All declarations have docstrings or `@[nolint docBlame]`

---

### Phase 2: Comprehensive Test Suite [COMPLETED]

**Goal**: Create the test file with all golden test cases from the research, covering
positive tests (Tier 1 and Tier 2), negative tests, and depth-sensitive tests.

**Tasks**:
- [ ] Create `CslibTests/HilbertSearch.lean` with `module`, `public meta import Cslib.Foundations.Logic.Automation.HilbertSearch`, additional imports for modal/temporal proof systems as needed
- [ ] Wrap all tests in `namespace CslibTests.HilbertSearch`
- [ ] Implement Tier 1 positive tests (must pass at default fuel):
  - Test 1: `DerivableIn S (imp a (imp b a))` -- ImplyK axiom (depth 1)
  - Test 2: `DerivableIn S (imp a a)` -- identity rule (depth 1)
  - Test 3: `DerivableIn S b` from `h1 : DerivableIn S (imp a b)`, `h2 : DerivableIn S a` -- MP + assumptions (depth 1)
  - Test 4: `DerivableIn S (imp (box a) (box b))` from `h : DerivableIn S (imp a b)` -- box_mono (depth 2)
  - Test 5: `DerivableIn S (box (imp a a))` -- nec(identity) (depth 2)
  - Test 6: `DerivableIn S (bot -> phi)` under `[IntuitionisticHilbert S]` -- EFQ axiom (depth 1)
  - Test 7: `DerivableIn S (((phi -> psi) -> phi) -> phi)` under `[ClassicalHilbert S]` -- Peirce (depth 1)
  - Test 8: `DerivableIn S (imp (imp psi chi) (imp (imp phi psi) (imp phi chi)))` -- b_combinator (depth 3)
- [ ] Implement Tier 2 tests (should pass with library lemmas, may need higher fuel):
  - Test 9: `DerivableIn S (imp (imp phi psi) (imp (imp psi phi) (imp phi psi)))` -- contrapose_imp depth 4
  - Test 10: `DerivableIn S (imp (dia phi) (dia psi))` from `h : DerivableIn S (imp phi psi)` -- diamond_mono depth 5
- [ ] Implement negative tests:
  - `success_if_fail_with_msg "hilbert_search failed"` with `hilbert_search 0` on identity goal
  - Verify graceful failure at low fuel on deep goals
- [ ] Implement Tier 3 "must NOT hang" tests:
  - `hilbert_search 5` on `demorgan_conj_neg_backward` fails gracefully (not hangs)
  - `hilbert_search 5` on list induction goals fails gracefully
- [ ] Add docstrings to all test `example`/`theorem` declarations
- [ ] Run `lake test` to verify all tests pass

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `CslibTests/HilbertSearch.lean` -- new file: comprehensive test suite

**Verification**:
- All Tier 1 tests pass (tactic closes goals at default fuel)
- Tier 2 tests pass or are documented as known limitations
- Negative tests produce informative error messages
- Tier 3 tests fail gracefully within reasonable time
- `lake test` passes

---

### Phase 3: Temporal and Extended Axiom Coverage [COMPLETED]

**Goal**: Extend the axiom table to cover temporal axioms and additional connective axioms,
ensuring the tactic works across the full CSLib proof system hierarchy.

**Tasks**:
- [ ] Add temporal axiom entries to the zero-subgoal axiom array:
  `HasAxiomSerialFuture.serialFuture`, `HasAxiomSerialPast.serialPast`,
  `HasAxiomConnectFuture.connectFuture`, `HasAxiomConnectPast.connectPast`,
  `HasAxiomLeftMonoUntilG.leftMonoUntilG`, `HasAxiomLeftMonoSinceH.leftMonoSinceH`,
  `HasAxiomRightMonoUntilG.rightMonoUntilG`, `HasAxiomRightMonoSinceH.rightMonoSinceH`,
  and other BX axiom typeclasses as available
- [ ] Add temporal necessitation entries to one-subgoal rules: `TemporalNecessitation.tempNec`, `TemporalNecessitation.tempNecPast` (if these follow the nec pattern)
- [ ] Add bimodal axiom: `HasAxiomMF.MF`
- [ ] Add connective axioms (for logics that have them): `HasAxiomAndI.andI`, `HasAxiomAndE1.andE1`, `HasAxiomAndE2.andE2`, `HasAxiomOrI1.orI1`, `HasAxiomOrI2.orI2`, `HasAxiomOrE.orE`
- [ ] Import additional modules as needed (temporal theorems, bimodal proof systems)
- [ ] Add test cases for temporal goals: `until_mono_guard`, `since_mono_guard` style theorems
- [ ] Add test cases for bimodal goals if `BimodalTMHilbert` instances are available
- [ ] Run `lake build` to verify extended axiom table compiles
- [ ] Run `lake test` to verify existing + new tests pass

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Foundations/Logic/Automation/HilbertSearch.lean` -- extend axiom arrays, add imports
- `CslibTests/HilbertSearch.lean` -- add temporal/bimodal test cases

**Verification**:
- Extended axiom table compiles without errors
- Temporal axiom goals close at depth 1-2
- No regressions in Tier 1 tests
- `lake build` and `lake test` pass

---

### Phase 4: CI Verification and Cleanup [COMPLETED]

**Goal**: Pass the full CSLib CI pipeline and finalize for PR submission.

**Tasks**:
- [ ] Run `lake build` (full project build)
- [ ] Run `lake exe checkInitImports` (verify `import Cslib.Init` in new files)
- [ ] Run `lake exe lint-style` (style linting)
- [ ] Run `lake test` (test suite including new HilbertSearch tests)
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` (import minimization)
- [ ] Run `lake exe mk_all --module` (verify `Cslib.lean` barrel import is current)
- [ ] Fix any lint or style violations found
- [ ] Verify no `sorry` in any new file (grep or `lean_verify`)
- [ ] Verify all public declarations have docstrings (check `docBlame` linter output)
- [ ] Verify `topNamespace` compliance (all declarations inside `namespace Cslib.Logic.Automation`)
- [ ] Verify `defLemma` compliance (Prop-valued declarations use `lemma`/`theorem`)
- [ ] Verify `defsWithUnderscore` compliance (no underscores in Lean declaration names)

**Timing**: 1.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib.lean` -- barrel import update (if not already current)
- Any files with lint/style violations

**Verification**:
- All CI checks pass with zero errors
- No `sorry` in any new file
- `lake build` succeeds cleanly
- `lake test` passes
- `lake shake` produces no changes (imports already minimal)

## Testing & Validation

- [ ] `lake build Cslib.Foundations.Logic.Automation.HilbertSearch` compiles
- [ ] `hilbert_search` closes `DerivableIn S (imp phi phi)` (identity)
- [ ] `hilbert_search` closes `DerivableIn S (imp a (imp b a))` (ImplyK axiom)
- [ ] `hilbert_search` closes `DerivableIn S b` from MP hypotheses
- [ ] `hilbert_search` closes `DerivableIn S (imp (box a) (box b))` with box_mono hypothesis
- [ ] `hilbert_search` closes `DerivableIn S (box (imp a a))` (nec + identity)
- [ ] `hilbert_search` closes EFQ and Peirce axiom goals at depth 1
- [ ] `hilbert_search` closes b_combinator goal at depth 3
- [ ] `hilbert_search` chains `ModusPonens.mp` with local hypotheses
- [ ] `hilbert_search N` respects fuel bound N
- [ ] Depth exhaustion produces informative error message with remediation hint
- [ ] Goal mismatch (non-DerivableIn goal) produces clear error (if applicable)
- [ ] Low-fuel failure on deep goals terminates in bounded time (not hangs)
- [ ] `set_option trace.Cslib.Logic.hilbertSearch true` produces readable trace output
- [ ] `lake test` passes
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes
- [ ] No `sorry` in new files

## Artifacts & Outputs

- `Cslib/Foundations/Logic/Automation/HilbertSearch.lean` -- MetaM search core + tactic wrapper (single file)
- `CslibTests/HilbertSearch.lean` -- Comprehensive test suite (Tier 1-3 golden tests)
- `Cslib.lean` -- Barrel import update (via `lake exe mk_all --module`)

## Rollback/Contingency

All new code lives in the new `Cslib/Foundations/Logic/Automation/` directory and
`CslibTests/HilbertSearch.lean`. Rollback is straightforward: remove the `Automation/`
directory, the test file, and the barrel import from `Cslib.lean`. No existing files are
modified except `Cslib.lean` (barrel import addition via `mk_all`).

If the MetaM `apply`-based approach encounters unforeseen issues with specific axiom types
(e.g., temporal axioms with complex universe structure), the axiom table can be narrowed to
propositional + modal only (Phase 1 scope) while the problematic axioms are investigated.

The single-file architecture (no separate `HilbertSearchTactic.lean`) simplifies the rollback
surface compared to the v1 plan's two-file design.
