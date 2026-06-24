# Implementation Plan: Task #323

- **Task**: 323 - Fix Intuitionistic Tableau Implementation Bugs
- **Status**: [COMPLETED]
- **Effort**: 4 hours
- **Dependencies**: None
- **Research Inputs**: specs/323_fix_intuitionistic_tableau_bugs/reports/01_bug-analysis.md
- **Artifacts**: plans/01_bug-fix-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Fix two bugs in the intuitionistic propositional tableau decision procedure. Bug 1: `isIntuitionisticallyClosed` only checks for T(bot) but misses complementary-pair T(phi)/F(phi) closure, causing valid formulas like `p -> p` to return `.openBranch`. Bug 2: `intTImpRule` uses Nat ordering (`>= w`) as a proxy for Kripke accessibility, but this incorrectly treats sibling worlds as accessible, causing the invalid formula `((p->bot)->q) v (p->r)` to close. The fix adds `Branch.hasContradiction` to the closure check, and replaces Nat ordering with explicit parent-child accessibility tracking using edge lists threaded through the expansion loop.

### Research Integration

The research report (01_bug-analysis.md) confirmed both bugs with `#eval` traces, identified the root causes in `Expansion.lean:67` and `Rules.lean:129`, proposed the `List (Nat x Nat)` edge-list approach for accessibility tracking, and analyzed the impact on soundness/completeness proofs. Key finding: all completeness and most soundness proofs are currently `sorry`-tagged, so signature changes do not break existing proofs -- only the `intClosed_unsatisfiable` lemma needs a new case, and `intRule_preserves_sat` needs updated comments.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Fix Bug 1: `isIntuitionisticallyClosed` returns correct closure results for complementary pairs
- Fix Bug 2: `intTImpRule` fires only along actual Kripke accessibility paths (parent-child)
- Thread accessibility edge lists through the expansion loop infrastructure
- Update soundness proof signatures and the `intClosed_unsatisfiable` lemma
- Update completeness proof signatures (sorry-tagged stubs)
- Verify all fixes with `#eval` tests and `lake build`

**Non-Goals**:
- Prove `intExpandBranches_closed_unsat` (remains sorry -- task 316 scope)
- Prove the truth lemmas for completeness (remain sorry)
- Modify the `IntuitionisticClosure` typeclass instance in `ClosureCondition.lean` (local fix preferred)
- Change the minimal tableau closure logic (already correct via `Branch.hasContradiction`)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Signature changes cascade to many files | M | M | Thread edges parameter additively; all downstream proofs are sorry'd so signatures update cleanly |
| Edge-list approach has performance regression on complex formulas | L | L | Fuel bound already exponential; edge list traversal is O(depth) which is bounded by world count |
| `intClosed_unsatisfiable` proof for complementary-pair case is harder than expected | M | L | Follow exact pattern from `minClosed_unsatisfiable` in Minimal/Soundness.lean which already handles this case |
| Breaking changes to `minimalTableau` path | M | L | `minimalTableau` uses `isMinimallyClosed` (already correct) and shares `intExpandBranches`; only signature threading needed |

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

### Phase 1: Add Accessibility Infrastructure and Fix intTImpRule [COMPLETED]

**Goal**: Add `isAccessible` helper and edge-list type to Rules.lean, update `intTImpRule` to use accessibility instead of Nat ordering, and update `intFImpRule` to return parent edge.

**Tasks**:
- [ ] Add `isAccessible` function to Rules.lean that checks reflexive-transitive closure of parent-child edges
- [ ] Add type alias `IEdges (Atom : Type*) := List (Nat x Nat)` for parent edge lists (child, parent)
- [ ] Modify `intTImpRule` signature: add `edges : List (Nat x Nat)` parameter; replace `(· >= w)` filter with `isAccessible edges w` filter
- [ ] Modify `intFImpRule` return type to also return the new parent edge `(newWorld, parentWorld)` as a third component
- [ ] Update `intApplyRule` and `intApplyRuleFull` to accept and pass edges; update `intFImpRule` call sites
- [ ] Update `IntRuleResult` to carry edges updates if needed (or return edge separately)
- [ ] Update docstrings for all modified functions to reflect accessibility-based semantics
- [ ] Fix the incorrect docstring on `isIntuitionisticallyClosed` (line 65-66) that says "complementary pairs do NOT close a branch"

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean` - Add `isAccessible`, edge type, update `intTImpRule`, `intFImpRule`, `intApplyRule`, `intApplyRuleFull`

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Rules` compiles without errors
- All function signatures are updated and consistent

---

### Phase 2: Thread Edges Through Expansion Loop and Fix Closure Check [COMPLETED]

**Goal**: Thread the edge list through `Expansion.lean` functions, fix `isIntuitionisticallyClosed` (Bug 1), and ensure the expansion loop correctly tracks and propagates accessibility.

**Tasks**:
- [ ] Fix `isIntuitionisticallyClosed`: add `|| Branch.hasContradiction b` (Bug 1 fix)
- [ ] Update `applyAllTImpRules` signature: add `edges : List (Nat x Nat)` parameter, pass to `intTImpRule`
- [ ] Update `applyPersistenceFixpoint` signature: add `edges` parameter, pass to `applyAllTImpRules`
- [ ] Update `intStepBranch` signature: add `edges` parameter, pass through to `intApplyRuleFull`; handle edge extraction from `intFImpRule` results
- [ ] Update `intExpandBranches`: add `edgeSets : List (List (Nat x Nat))` parallel list (one per branch); thread through `go` inner loop; update edge set when F(imp) creates new world; propagate to sub-branches on branching rules
- [ ] Update `intuitionisticTableau`: initialize with `edgeSets = [[]]` (empty edges for root)
- [ ] Update `minimalTableau`: same edge threading (shares `intExpandBranches`)
- [ ] Update all docstrings to reflect accessibility-based design

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` - Fix closure check, thread edges through all expansion functions

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion` compiles
- Add temporary `#eval` tests at bottom of file to verify:
  - `intuitionisticTableau (p.imp p) = .closed` (Bug 1 regression)
  - `intuitionisticTableau bug2Formula = .openBranch _` (Bug 2 regression)

---

### Phase 3: Update Soundness and Completeness Proofs [COMPLETED]

**Goal**: Update all proof signatures in Soundness.lean and Completeness.lean (both intuitionistic and minimal) to accommodate the new edges parameter, and extend `intClosed_unsatisfiable` to handle the complementary-pair case.

**Tasks**:
- [ ] Update `intClosed_unsatisfiable` in Intuitionistic/Soundness.lean to handle the new `|| Branch.hasContradiction b` disjunct: add a second case following the `minClosed_unsatisfiable` pattern from Minimal/Soundness.lean
- [ ] Update `intRule_preserves_sat` signature if `intApplyRuleFull` signature changed (add edges parameter)
- [ ] Update `intExpandBranches_closed_unsat` signature to include edges parameter (remains sorry)
- [ ] Update `intuitionisticTableau_sound` call site to pass edges
- [ ] Update Minimal/Soundness.lean: adjust `minimalTableau_sound` call to `intExpandBranches_closed_unsat` for new signature
- [ ] Update Intuitionistic/Completeness.lean: adjust sorry-tagged proof stubs for new signatures (`intTruthLemma`, `intuitionisticOpenBranch_countermodel`, `intuitionisticTableau_complete`)
- [ ] Update Minimal/Completeness.lean: adjust sorry-tagged proof stubs for new signatures (`minTruthLemma`, `minOpenBranch_countermodel`, `minimalTableau_complete`)
- [ ] Verify DecisionProcedure.lean files still compile (they call soundness/completeness theorems)

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` - Fix `intClosed_unsatisfiable`, update signatures
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` - Update sorry-tagged stubs
- `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean` - Update call signature
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` - Update sorry-tagged stubs

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.DecisionProcedure` compiles
- `lake build Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure` compiles
- `intClosed_unsatisfiable` proof is sorry-free (both T(bot) and complementary-pair cases handled)

---

### Phase 4: Full Verification and #eval Test Suite [COMPLETED]

**Goal**: Run the complete test matrix from the research report, verify `lake build` succeeds for the full project, and clean up any temporary test code.

**Tasks**:
- [ ] Run `lake build` for the full project to verify no regressions
- [ ] Add or verify `#eval` tests in a test file or at the end of DecisionProcedure.lean covering the full test matrix:
  - Valid formulas (must return `.closed`): `p -> p`, `(p /\ (p -> q)) -> q`, `p -> (q -> p)`, `(p -> (q -> r)) -> ((p -> q) -> (p -> r))`
  - Invalid formulas (must return `.openBranch`): `((p->bot)->q) v (p->r)`, `p v (p->bot)`, `((p->bot)->bot) -> p`, `(p->q) v (q->p)`, `(p->bot) v ((p->bot)->bot)`
- [ ] Verify minimal tableau still works correctly for the same test matrix (minimal valid = subset of intuitionistic valid)
- [ ] Remove any temporary `#eval` tests added during development
- [ ] Run `lake exe lint-style` and `lake exe checkInitImports` for CI compliance

**Timing**: 0.5 hours

**Depends on**: 3

**Files to modify**:
- Possibly `Cslib/Logics/Propositional/Tableau/Intuitionistic/DecisionProcedure.lean` - Temporary test additions (then removal)
- Possibly `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` - Temporary test additions (then removal)

**Verification**:
- `lake build` succeeds with zero errors
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- All `#eval` tests produce expected results
- `lake test` passes (if tableau tests exist in CslibTests)

## Testing & Validation

- [ ] Bug 1 regression: `intuitionisticTableau (p.imp p)` returns `.closed`
- [ ] Bug 1 regression: `intuitionisticTableau ((p.and (p.imp q)).imp q)` returns `.closed`
- [ ] Bug 2 regression: `intuitionisticTableau (((p.imp .bot).imp q).or (p.imp r))` returns `.openBranch _`
- [ ] No false negatives: known valid formulas all close
- [ ] No false positives: known invalid formulas all produce open branches
- [ ] Minimal tableau unaffected: `minimalTableau` still works correctly for its test cases
- [ ] `lake build` succeeds for the full project
- [ ] CI lint passes (`lake exe lint-style`, `lake exe checkInitImports`)

## Artifacts & Outputs

- `specs/323_fix_intuitionistic_tableau_bugs/plans/01_bug-fix-plan.md` (this file)
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean`
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean`
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean`
- Modified: `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean`
- Modified: `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean`
- `specs/323_fix_intuitionistic_tableau_bugs/summaries/01_bug-fix-summary.md` (post-implementation)

## Rollback/Contingency

All changes are in the `Cslib/Logics/Propositional/Tableau/` subtree. If the fix introduces regressions:
1. Revert the edge-threading changes and keep only the Bug 1 fix (which is a one-line addition)
2. For Bug 2, an alternative fallback is to use a simpler "parent map" (`Nat -> Option Nat`) instead of edge lists, or to use `Array` instead of `List` for performance
3. If proof updates are blocked, leave new signatures with `sorry` and document the blocker
4. `git checkout -- Cslib/Logics/Propositional/Tableau/` reverts all changes cleanly
