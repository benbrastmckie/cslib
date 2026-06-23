# Implementation Plan: Generic Hilbert Proof-Search Tactic

- **Task**: 269 - hilbert_search_tactic
- **Status**: [NOT STARTED]
- **Effort**: 10 hours
- **Dependencies**: Task 268 (normalization tags -- completed)
- **Research Inputs**: specs/269_hilbert_search_tactic/reports/01_team-research.md
- **Artifacts**: plans/02_hilbert-search-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Build a generic bounded depth-first proof-search tactic (`hilbert_search`) for CSLib's
`InferenceSystem` typeclass, enabling automated Hilbert-style derivations across all
registered proof systems (propositional, modal, temporal, bimodal). The implementation uses
a two-layer architecture: a term-mode search core (Tier 1) returning
`Option (DerivableIn S phi)`, wrapped by a thin `TacticM` elaborator (Tier 2) that provides
the user-facing `hilbert_search` syntax. Definition of done: the tactic closes
`DerivableIn S phi` goals for propositional and modal systems, passes all CI checks, and
has been discussed on Zulip.

### Research Integration

The team research (4 teammates) established the following key findings integrated into this plan:

- **Two-layer architecture** (consensus across teammates A, B, D): Term-mode Tier 1 search
  function at the `DerivableIn S phi` level is the core, with a thin `TacticM` Tier 2 wrapper.
  This matches CSLib's preference for term-mode definitions (only `Relation/Attr.lean` uses
  `Lean.Elab.*`).
- **Formula decomposition gap** (Critic): A genuine term-mode DFS cannot decompose formulas
  (`imp phi psi` into `phi` and `psi`) without `HasImpView`/`HasBoxView` typeclasses not
  currently in CSLib. Resolution: Tier 1 handles axiom dispatch and hypothesis MP chaining;
  full structural DFS belongs to Tier 2's MetaM layer using `whnf` + expression matching.
- **`DecidableEq F` constraint** (teammates C, D): All concrete CSLib formula types have
  `DecidableEq`. The search signature should require `[DecidableEq F]` from the start.
- **Scope calibration** (Critic): The full generic implementation covering 4 logic levels
  requires 600-1200 lines. This plan scopes Phase 1 to propositional + minimal modal
  (~300 lines), with modal/temporal as later phases.
- **`buildCompositionalProof` precedent** (teammate B): `ProofExtraction.lean:155-204`
  validates the fuel-based recursive term-mode pattern already in CSLib.
- **`observing?` pattern** (teammate A): BimodalLogic's non-destructive `observing?` +
  `goal.apply` pattern is directly portable for the TacticM axiom dispatch.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the following roadmap item implicitly: the `hilbert_search` tactic is
foundational cross-cutting infrastructure that enables automated proof derivation across all
proof systems in `Foundations/Logic/` and all logic modules (`Propositional`, `Modal`,
`Temporal`, `Bimodal`). It is novel infrastructure not currently listed as a specific roadmap
component but supports the overall mission of building shared automation for cslib.

## Goals & Non-Goals

**Goals**:
- Implement a term-mode bounded DFS search function generic over `[MinimalHilbert S]`
- Implement a thin `TacticM` wrapper exposing `hilbert_search (depth)` syntax
- Support axiom matching, local hypothesis scanning, and modus ponens chaining
- Provide configurable search depth with informative error messages on failure
- Work across Propositional, Modal (Phase 1 + 2), and extensibly for Temporal/Bimodal
- Pass all CSLib CI checks (`lake build`, `lake test`, `checkInitImports`, `lint-style`, `lake shake`)

**Non-Goals**:
- Full formula structural DFS decomposition at the term level (requires `HasImpView` typeclasses not yet in CSLib)
- Context-relative goals `Gamma |- phi` (out of scope; `DerivableIn` is empty-context only)
- Filling the bimodal-specific `boundedSearchWithProofStub` in `AxiomMatcher.lean`
- Registering `hilbert_search` as `@[simp]` or `@[aesop]`
- Temporal and bimodal logic support (deferred to future tasks)
- Proof-by-reflection / `decide`-based architecture (long-term direction, not Phase 1)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Universe polymorphism unification failures when calling `ModusPonens.mp` from term-mode | H | M | Prototype MP chaining early in Phase 1; test with concrete instances before building full search |
| `whnf` does not reliably expose `DerivableIn` structure at meta level | H | L | Test goal extraction in Phase 3 with multiple concrete systems; fall back to `matchAppOf` if needed |
| Lean typeclass inference timeout on deeply nested search | M | M | Cap default depth at 10; document that depth >15 may cause slowdowns; add visitLimit counter |
| PR rejected on code style (meta section not fitting CSLib conventions) | M | M | Model meta section on `Relation/Attr.lean` pattern; raise on Zulip before PR submission |
| `DecidableEq F` constraint too restrictive for some future formula types | L | L | All 4 current formula types have it; document the constraint; can be relaxed later |
| Zulip discussion reveals community preference for different architecture | M | L | Front-load Zulip discussion (Phase 2) before heavy implementation in Phase 4 |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |
| 5 | 6 | 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Term-Mode Search Core (Tier 1) [NOT STARTED]

**Goal**: Implement the term-mode bounded DFS search function for propositional systems
(`MinimalHilbert` and `ClassicalHilbert`), establishing the core search architecture.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Automation/HilbertSearch.lean` with module header, imports (`Cslib.Foundations.Logic.ProofSystem`, `Cslib.Foundations.Logic.Theorems`)
- [ ] Define `HilbertSearchResult` type alias or structure for search outcomes
- [ ] Implement `tryAxiomDispatch` function: given `[MinimalHilbert S]`, attempt to close a `DerivableIn S phi` goal by trying `HasAxiomImplyK.implyK`, `HasAxiomImplyS.implyS`, `HasAxiomEFQ.efq`, `HasAxiomPeirce.peirce` via direct application with `DecidableEq`-based formula matching
- [ ] Implement `tryHypothesisMP` function: given a list of `DerivableIn S psi` witnesses and a target `DerivableIn S phi`, attempt to find a `DerivableIn S (imp psi phi)` in the list and apply `ModusPonens.mp`
- [ ] Implement `hilbertSearch` main loop: fuel-based recursive DFS calling `tryAxiomDispatch`, `tryHypothesisMP`, with depth counter, returning `Option (DerivableIn S phi)`
- [ ] Test with `identity` (`phi -> phi`), `imp_trans` pattern, and `HasAxiomImplyK` instantiation using `#check` / `example` proofs
- [ ] Prototype universe polymorphism behavior: verify `ModusPonens.mp` calls work from term-mode with concrete Propositional instances
- [ ] Update `Cslib/Foundations/Logic/Automation.lean` barrel import if it exists, or create it
- [ ] Run `lake build Cslib.Foundations.Logic.Automation.HilbertSearch`

**Timing**: 3 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Automation/HilbertSearch.lean` - new file: core search functions
- `Cslib/Foundations/Logic/Automation.lean` - barrel import (create or update)

**Verification**:
- `lake build Cslib.Foundations.Logic.Automation.HilbertSearch` compiles without errors
- `example` proofs using `hilbertSearch` close `DerivableIn HilbertCl (imp phi phi)` goals
- No `sorry` in the file

---

### Phase 2: Zulip Discussion [NOT STARTED]

**Goal**: Post on the cslib Zulip to get community feedback on the architecture before
building the tactic wrapper, to avoid rework.

**Tasks**:
- [ ] Draft Zulip message covering: (a) two-layer architecture decision, (b) file location (`Foundations/Logic/Automation/` vs alternatives), (c) whether `HasImpView`/`HasBoxView` typeclasses should be added for future term-mode DFS, (d) Aesop rule set as complementary approach
- [ ] Post to appropriate Zulip stream (cslib or lean4)
- [ ] Document community feedback in the task directory

**Timing**: 0.5 hours (drafting; waiting for responses is async)

**Depends on**: 1

**Files to modify**:
- `specs/269_hilbert_search_tactic/` - Zulip discussion notes (if needed)

**Verification**:
- Zulip post submitted
- Key design questions listed and answered (or noted as pending)

---

### Phase 3: Modal Extension of Tier 1 [NOT STARTED]

**Goal**: Extend the term-mode search to support `ModalHilbert S` systems by adding
necessitation and axiom K dispatch.

**Tasks**:
- [ ] Add `tryNecessitation` function: if the goal formula matches `HasBox.box phi` pattern, attempt to prove `DerivableIn S phi` recursively and apply `Necessitation.nec`
- [ ] Add modal axiom dispatch entries: `HasAxiomK.K`, `HasAxiomT.T`, `HasAxiom4.four`, `HasAxiomB.B`, `HasAxiom5.five`, `HasAxiomD.D`
- [ ] Implement `hilbertSearchModal` extending `hilbertSearch` with the modal rules, parameterized by `[ModalHilbert S]`
- [ ] Handle formula matching for box/diamond patterns: since term-mode cannot inspect formula structure without `HasBoxView`, use `DecidableEq`-based matching against axiom instances (let Lean's unifier do the work via `Decidable` instance synthesis)
- [ ] Test with modal axiom instantiation examples: K-axiom, T-axiom, necessitation of propositional theorems
- [ ] Run `lake build Cslib.Foundations.Logic.Automation.HilbertSearch`

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Logic/Automation/HilbertSearch.lean` - extend with modal search functions

**Verification**:
- Modal search examples compile: `hilbertSearchModal` closes `DerivableIn HilbertK (AxiomK phi psi)` goals
- Necessitation rule applied correctly in examples
- No `sorry` in the file

---

### Phase 4: TacticM Wrapper (Tier 2) [NOT STARTED]

**Goal**: Implement the thin `TacticM` elaborator wrapping the Tier 1 search functions,
providing the user-facing `hilbert_search` tactic syntax.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Automation/HilbertSearchTactic.lean` with `meta section` pattern (modeled on `Relation/Attr.lean`)
- [ ] Implement `extractDerivableGoal`: MetaM function that pattern-matches goal type against `InferenceSystem.DerivableIn S phi` after `whnf`, returning `(S, phi)` pair
- [ ] Implement `tryAxiomMethods`: iterate `HasAxiom*` method names using `observing?` + `goal.apply` pattern from BimodalLogic
- [ ] Implement `tryLocalHypotheses`: scan `lctx` for hypotheses of type `DerivableIn S psi`, attempt `ModusPonens.mp` chaining
- [ ] Implement `searchProof`: core `TacticM Bool` loop dispatching strategies with fuel parameter
- [ ] Define syntax: `syntax "hilbert_search" (num)? : tactic`
- [ ] Implement `elab_rules` for `hilbert_search` with error messages: on goal mismatch report "goal must be `DerivableIn S phi`"; on depth exhaustion report depth and target formula
- [ ] Implement formula-directed decomposition at MetaM level using `whnf` + expression matching: for `imp phi psi` goals, create subgoals for `phi -> psi` via `ModusPonens.mp`; for `box phi` goals, try `Necessitation.nec`
- [ ] Update barrel import in `Automation.lean`
- [ ] Test with existing Combinators theorems: verify `hilbert_search` can close `identity`, `imp_trans`
- [ ] Run `lake build Cslib.Foundations.Logic.Automation.HilbertSearchTactic`

**Timing**: 2.5 hours

**Depends on**: 2, 3

**Files to modify**:
- `Cslib/Foundations/Logic/Automation/HilbertSearchTactic.lean` - new file: TacticM wrapper
- `Cslib/Foundations/Logic/Automation.lean` - update barrel import

**Verification**:
- `hilbert_search` closes `DerivableIn HilbertCl (imp phi phi)` in tactic mode
- `hilbert_search 5` respects depth parameter
- Error messages are informative on failure (depth reached, goal formula)
- `hilbert_search` does NOT trigger from `simp` or `aesop`

---

### Phase 5: Tests and Documentation [NOT STARTED]

**Goal**: Create a comprehensive test suite and add module documentation.

**Tasks**:
- [ ] Add positive test cases in `CslibTests/` or as `example` proofs:
  - `identity`: `DerivableIn S (imp phi phi)` for `MinimalHilbert`
  - `imp_trans`: `DerivableIn S (imp phi chi)` from hypotheses
  - K-axiom instantiation: `DerivableIn S (AxiomK phi psi)` for `ModalHilbert`
  - Necessitation: `DerivableIn S (box phi)` from `DerivableIn S phi`
  - Multi-step: combination of MP and axiom dispatch (depth 3-5)
- [ ] Add negative test cases:
  - Depth-limited failure: formula requiring depth > bound returns error
  - Goal mismatch: applying `hilbert_search` to non-`DerivableIn` goal gives clear error
- [ ] Add module docstring to `HilbertSearch.lean` explaining the two-layer architecture, search strategies, limitations (no context-relative goals, no structural DFS without `HasImpView`)
- [ ] Add docstrings to all public definitions per CSLib `docBlame` linter requirements
- [ ] Document that `hilbert_search` must NOT be registered as `@[simp]` or `@[aesop]`

**Timing**: 1 hour

**Depends on**: 4

**Files to modify**:
- `CslibTests/` or `Cslib/Foundations/Logic/Automation/HilbertSearch.lean` - test examples
- `Cslib/Foundations/Logic/Automation/HilbertSearchTactic.lean` - docstrings

**Verification**:
- All positive test cases pass (tactic closes goals)
- Negative test cases produce informative error messages
- All public definitions have docstrings
- `lake test` passes

---

### Phase 6: CI Verification and Cleanup [NOT STARTED]

**Goal**: Pass the full CSLib CI pipeline and finalize for PR submission.

**Tasks**:
- [ ] Run `lake build` (full project build)
- [ ] Run `lake exe checkInitImports` (verify `import Cslib.Init` in new files)
- [ ] Run `lake exe lint-style` (style linting)
- [ ] Run `lake test` (test suite)
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` (import minimization)
- [ ] Run `lake exe mk_all --module` (update `Cslib.lean` barrel import for new modules)
- [ ] Fix any lint or style violations found
- [ ] Verify no `sorry` in any new file (`lean_verify` or grep)
- [ ] Review Zulip feedback from Phase 2; incorporate any required changes

**Timing**: 1 hour

**Depends on**: 5

**Files to modify**:
- `Cslib.lean` - barrel import update
- Any files with lint/style violations

**Verification**:
- All CI checks pass with zero errors
- No `sorry` in any new file
- `lake build` succeeds cleanly

## Testing & Validation

- [ ] `lake build Cslib.Foundations.Logic.Automation.HilbertSearch` compiles
- [ ] `lake build Cslib.Foundations.Logic.Automation.HilbertSearchTactic` compiles
- [ ] `hilbert_search` closes `DerivableIn HilbertCl (imp phi phi)` (identity)
- [ ] `hilbert_search` closes modal axiom goals for `ModalHilbert` systems
- [ ] `hilbert_search` chains `ModusPonens.mp` with local hypotheses
- [ ] `hilbert_search N` respects depth bound N
- [ ] Depth exhaustion produces informative error message
- [ ] Goal mismatch produces informative error message
- [ ] `lake test` passes
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes
- [ ] No `sorry` in new files

## Artifacts & Outputs

- `Cslib/Foundations/Logic/Automation/HilbertSearch.lean` - Term-mode search core (Tier 1)
- `Cslib/Foundations/Logic/Automation/HilbertSearchTactic.lean` - TacticM wrapper (Tier 2)
- `Cslib/Foundations/Logic/Automation.lean` - Barrel import for automation module
- Test examples in `CslibTests/` or as inline `example` proofs
- Zulip discussion thread documenting community feedback

## Rollback/Contingency

All new code lives in the new `Cslib/Foundations/Logic/Automation/` directory. Rollback is
straightforward: remove the `Automation/` directory and its barrel import from `Cslib.lean`.
No existing files are modified except `Cslib.lean` (barrel import addition). If the Zulip
community requests a fundamentally different architecture, the term-mode Tier 1 (Phase 1)
can be preserved as a standalone utility while the tactic wrapper (Phase 4) is rewritten.
