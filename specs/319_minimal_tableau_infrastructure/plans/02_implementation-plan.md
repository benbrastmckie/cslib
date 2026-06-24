# Implementation Plan: Task #319

- **Task**: 319 - Build dedicated Soundness and Completeness modules for the minimal propositional tableau
- **Status**: [IMPLEMENTING]
- **Effort**: 5 hours
- **Dependencies**: Tasks 316, 317 (partial -- shared sorry in `intExpandBranches_closed_unsat`)
- **Research Inputs**: specs/319_minimal_tableau_infrastructure/reports/01_minimal-tableau-research.md
- **Artifacts**: plans/02_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Build `Minimal/Soundness.lean` and `Minimal/Completeness.lean` for the minimal propositional tableau, then refactor `DecisionProcedure.lean` to import them. A critical prerequisite is fixing the `isMinimallyClosed` closure predicate, which currently only checks atomic formulas -- missing `.bot` (not atomic in CSLib) and causing `minimalTableau (bot -> bot)` to incorrectly return `openBranch`. The fix replaces the `MinimalClosure` instance with `Branch.hasContradiction` (all complementary T(phi)/F(phi) pairs). The soundness proof reuses `intRule_preserves_sat` and `intExpandBranches_closed_unsat` directly, requiring only a new `minClosed_unsatisfiable` lemma. The completeness proof constructs a countermodel with `botForces w = T(bot) at w on b`, with the truth lemma's bot case becoming near-trivial under the corrected closure.

### Research Integration

Key findings from the research report (01_minimal-tableau-research.md):

1. **Closure bug discovered and empirically verified**: `isMinimallyClosed` fails on `bot -> bot` because `.bot` is not atomic. Fix verified across 10 test cases with `Branch.hasContradiction`.
2. **Direct reusability**: `intRule_preserves_sat` works for any `botForces` (already parameterized). `intExpandBranches_closed_unsat` already parameterized by `closurePred` and `closed_unsat`.
3. **Countermodel design**: `minBotForces w = T(bot) at w on b`. Truth lemma bot case: F(bot) at w implies no T(bot) at w (by corrected closure catching all complementary pairs).
4. **Sorry inventory**: `intExpandBranches_closed_unsat` is sorry'd; this sorry is inherited by both intuitionistic and minimal soundness.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Fix the `isMinimallyClosed` closure predicate to handle all complementary pairs (not just atomic)
- Create `Minimal/Soundness.lean` with `minClosed_unsatisfiable` and `minimalTableau_sound`
- Create `Minimal/Completeness.lean` with countermodel construction, truth lemma, and `minimalTableau_complete`
- Refactor `DecisionProcedure.lean` to import new modules, keeping only Decidable instances
- Update barrel imports via `lake exe mk_all --module`

**Non-Goals**:
- Proving `intExpandBranches_closed_unsat` (inherited sorry, separate task)
- Creating separate `Minimal/Rules.lean` or `Minimal/Expansion.lean` (shared with intuitionistic)
- Changing the intuitionistic soundness/completeness proofs
- Proving the intuitionistic `intTruthLemma` (separate task)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Closure fix breaks downstream code | H | L | `isMinimallyClosed` only used by `minimalTableau`; change strengthens closure (more branches close), cannot break soundness |
| Truth lemma bot case requires F(bot)/T(bot) non-coexistence | M | M | Corrected closure catches all complementary pairs including T(bot)/F(bot), so open branch guarantees no such pair |
| `intExpandBranches_closed_unsat` sorry blocks full verification | M | H | Accept sorry dependency; document it; minimal module becomes sorry-free when intuitionistic loop invariant is proved |
| `Branch.hasContradiction` vs `MinimalClosure` API mismatch | L | L | `hasContradiction` returns Bool directly; wrap in a new closure-compatible definition |

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

### Phase 1: Fix `isMinimallyClosed` closure predicate [COMPLETED]

**Goal**: Replace the atom-only minimal closure with all-complementary-pair closure so that `minimalTableau` correctly decides minimal validity (including `bot -> bot`).

**Tasks**:
- [ ] Read `Cslib/Foundations/Logic/Tableau/ClosureCondition.lean` to understand `MinimalClosure` instance
- [ ] Read `Cslib/Foundations/Logic/Tableau/Branch.lean` to confirm `Branch.hasContradiction` checks all complementary T(phi)/F(phi) pairs
- [ ] Modify `isMinimallyClosed` in `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` (line 75-76) to use `Branch.hasContradiction b` instead of the `MinimalClosure` instance
- [ ] Update the docstring on `isMinimallyClosed` to reflect all-complementary-pair closure
- [ ] Verify with `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion` that the change compiles
- [ ] Verify with `lake build Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure` that downstream compiles

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` - Change `isMinimallyClosed` definition (lines 70-76)

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion` succeeds
- `lake build Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure` succeeds

---

### Phase 2: Create `Minimal/Soundness.lean` [COMPLETED]

**Goal**: Prove `minClosed_unsatisfiable` (a branch with any complementary T(phi)/F(phi) pair is unsatisfiable in any Kripke model) and `minimalTableau_sound` (if `minimalTableau phi = closed`, then `MValid phi`).

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean` with module docstring, copyright, and `import Cslib.Init`
- [ ] Import `Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness` (provides `intRule_preserves_sat`, `intBranchSatisfied`, `intExpandBranches_closed_unsat`)
- [ ] Define `minClosed_unsatisfiable`: Given `isMinimallyClosed b = true` (i.e., `Branch.hasContradiction b = true`), extract T(phi) at w and F(phi) at w from the contradiction, then derive `IForces val botForces (worldOf w) phi` and `¬ IForces val botForces (worldOf w) phi` for contradiction. This works for any `botForces`.
- [ ] Prove `minimalTableau_sound`: Instantiate `intExpandBranches_closed_unsat` with arbitrary `botForces`, `closurePred = isMinimallyClosed`, and `closed_unsat = minClosed_unsatisfiable`. Structure mirrors `intuitionisticTableau_sound`.
- [ ] Verify with `lake build Cslib.Logics.Propositional.Tableau.Minimal.Soundness`

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean` - New file (~80-120 lines)

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Minimal.Soundness` succeeds
- `lean_verify` on `minimalTableau_sound` shows sorry only from inherited `intExpandBranches_closed_unsat`

---

### Phase 3: Create `Minimal/Completeness.lean` [IN PROGRESS]

**Goal**: Construct a minimal Kripke countermodel from an open saturated branch and prove `minimalTableau_complete`.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` with module docstring, copyright, and `import Cslib.Init`
- [ ] Import `Cslib.Logics.Propositional.Tableau.Minimal.Soundness` (which transitively imports Expansion and Kripke)
- [ ] Define `minExtractValuation (b : IBranch Atom) (w : Nat) (p : Atom) : Prop` -- same as `intExtractValuation`: `b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w)`
- [ ] Define `minBotForces (b : IBranch Atom) (w : Nat) : Prop` -- `b.any (fun sf => sf.sign == .pos && sf.formula == .bot && sf.label == w)`
- [ ] State and prove `minTruthLemma`: For open saturated branch b, by induction on formula phi:
  - **atom p**: T(atom p) at w iff `minExtractValuation b w p` by definition
  - **bot**: T(bot) at w iff `minBotForces b w` by definition; F(bot) at w implies `not (minBotForces b w)` because branch is open (no complementary pair T(bot)/F(bot))
  - **imp phi psi**: T(imp) uses persistence saturation; F(imp) uses world-creating rule saturation
  - **and, or**: Standard cases using saturation and IH
- [ ] State and prove `minOpenBranch_countermodel`: From open saturated branch, apply truth lemma to show F(phi) at world 0 implies `not (IForces (minExtractValuation b) (minBotForces b) 0 phi)`
- [ ] State and prove `minimalTableau_complete`: By contrapositive via countermodel
- [ ] Verify with `lake build Cslib.Logics.Propositional.Tableau.Minimal.Completeness`

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` - New file (~200-300 lines)

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Minimal.Completeness` succeeds
- Truth lemma covers all formula constructors (atom, bot, imp, and, or)

---

### Phase 4: Refactor `DecisionProcedure.lean` and update barrel imports [NOT STARTED]

**Goal**: Slim down `DecisionProcedure.lean` to import the new Soundness and Completeness modules, keeping only the Decidable instances and bridge theorem. Update barrel imports.

**Tasks**:
- [ ] Edit `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean`:
  - Add `public import Cslib.Logics.Propositional.Tableau.Minimal.Completeness` (which transitively imports Soundness)
  - Remove `minBranchSatisfied` definition (lines 66-73) -- now handled in Soundness module or reuses `intBranchSatisfied` directly
  - Replace sorry'd `minimalTableau_sound` (lines 86-88) with a call to the proved version from `Minimal.Soundness`
  - Replace sorry'd `minimalTableau_complete` (lines 103-105) with a call to the proved version from `Minimal.Completeness`
  - Keep `minimalTableau_decides`, `instDecidableMValid`, `instDecidableDerivableMinPropAxiom` unchanged
  - Update module docstring to note that proofs are now in Soundness.lean and Completeness.lean
- [ ] Verify `lake build Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure` succeeds
- [ ] Run `lake exe mk_all --module` to update `Cslib.lean` barrel imports with new files
- [ ] Run `lake build` (full project build) to verify no regressions
- [ ] Run `lake exe checkInitImports` to verify all files import `Cslib.Init`

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` - Refactor to import new modules, remove sorry'd theorems and redundant definitions
- `Cslib.lean` - Updated by `lake exe mk_all --module`

**Verification**:
- `lake build` succeeds (full project)
- `lake exe checkInitImports` passes
- `DecisionProcedure.lean` reduced to ~50-60 lines
- No new sorries introduced (only inherited `intExpandBranches_closed_unsat`)

---

## Testing & Validation

- [ ] `lake build` succeeds with no new errors
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe mk_all --module` reports no missing imports
- [ ] `minimalTableau_sound` compiles with sorry only from inherited `intExpandBranches_closed_unsat`
- [ ] `minimalTableau_complete` compiles (may have sorry in truth lemma induction cases)
- [ ] `minimalTableau_decides` remains structurally correct (combines sound + complete)
- [ ] `instDecidableMValid` and `instDecidableDerivableMinPropAxiom` unchanged

## Artifacts & Outputs

- `specs/319_minimal_tableau_infrastructure/plans/02_implementation-plan.md` (this plan)
- `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean` (new, ~80-120 lines)
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` (new, ~200-300 lines)
- `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` (refactored, ~50-60 lines)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` (modified, closure fix)

## Rollback/Contingency

If the closure fix causes unexpected issues:
1. Revert `isMinimallyClosed` to the original `MinimalClosure` instance
2. Document the `bot -> bot` bug as a known issue
3. Proceed with Soundness/Completeness using the original closure, accepting the completeness gap

If the truth lemma proves too complex for a single dispatch:
1. Mark remaining cases with sorry
2. Document which induction cases are complete and which need work
3. Return `status: partial` with the sorry inventory
