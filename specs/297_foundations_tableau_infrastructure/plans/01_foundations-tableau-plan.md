# Implementation Plan: Task #297

- **Task**: 297 - Build shared tableau infrastructure in Foundations/Logic/Tableau/
- **Status**: [IMPLEMENTING]
- **Effort**: 8 hours
- **Dependencies**: None (parent metatask 296 is expanded; this is the root of the tableau dependency chain)
- **Research Inputs**: specs/297_foundations_tableau_infrastructure/reports/01_foundations-tableau-research.md
- **Artifacts**: plans/01_foundations-tableau-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Build shared, logic-neutral tableau infrastructure under `Cslib/Foundations/Logic/Tableau/`. The existing `PropositionalTableau.lean` (210 lines, imported by nothing) provides a starting point for propositional sign, signed formula, and rule application types. This plan refactors and extends that code into a proper module directory with 7 files plus a module root, introducing label-parameterized signed formulas, a `ClosureCondition` typeclass supporting classical/intuitionistic/minimal closure, generic branch operations, and a persistent-aware `RuleResult`. The namespace is `Cslib.Logic.Tableau` following the existing `Cslib.Logic` pattern.

### Research Integration

Key findings from the research report (01_foundations-tableau-research.md):
- `PropositionalTableau.lean` is imported by NO other file -- safe to refactor freely.
- Both `PropSign` (Foundations) and bimodal `Sign` are structurally identical (`pos | neg`); the bimodal version adds `flip`, `ReflBEq`, `LawfulBEq`, `Inhabited` which should be included in the unified type.
- The generic parameterization `SignedFormula (F : Type*) (L : Type*)` with `L = Unit` for classical and `L = WorldIndex` for intuitionistic/minimal is the correct abstraction.
- `RuleResult` should include a `persistent` variant from day one (needed by modal/temporal downstream tasks 299-301).
- `ClosureCondition` should use a `findClosure` method returning `Option ClosureReason` (not just `Bool`) to support proof extraction.
- Propositional rules in Foundations should be classical-only; intuitionistic/minimal override `impPos` in logic-specific modules.
- The decomposition-function approach (`andOf?`, `orOf?`, `impOf?`, `negOf?`) is correct for handling Lukasiewicz encodings and should be preserved.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances ROADMAP.md items:
- Extends the `Foundations/Logic/` infrastructure layer with tableau-specific types
- Provides the foundation for downstream tableau tasks (298: propositional decidability, 299-301: modal/temporal)
- Follows the "most general level" principle: all logic-neutral types in Foundations, logic-specific in Logics/

## Goals & Non-Goals

**Goals**:
- Unified `Sign` type replacing both `PropSign` and bimodal `Sign` with full API
- Generic `SignedFormula F L` parameterized over formula type and label type
- Generic `RuleResult F L` with linear, branching, persistent, and notApplicable variants
- Generic `Branch F L` type with label-aware operations
- `ClosureReason` and `ClosureCondition` typeclass with classical/intuitionistic/minimal instances
- Classical propositional rules refactored from `PropositionalTableau.lean`
- Module root `Tableau.lean` as import hub
- All files independently compilable with `lake build`

**Non-Goals**:
- Deleting `PropositionalTableau.lean` (defer to cleanup task)
- Migrating bimodal system to use the new types (defer to task 301 or separate)
- Implementing intuitionistic/minimal propositional rules (logic-specific, task 298)
- Tableau expansion algorithm, termination, or soundness/completeness proofs
- World-creation logic for intuitionistic `T(phi -> psi)` rule (belongs in Logics/)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Universe polymorphism complications with `F : Type*` and `L : Type*` | H | M | Follow CSLib `Type*` convention; test with concrete instantiations (Unit, Nat) in Phase 4 |
| `deriving` clauses fail for `SignedFormula F L` when L has complex constraints | M | M | Write instances manually if needed; bimodal already does this for its `SignedFormula` |
| Instance resolution issues with `BEq`/`Hashable` on generic `SignedFormula` | M | M | Require explicit `[DecidableEq F] [DecidableEq L]` constraints; derive `BEq` from `DecidableEq` |
| `ClosureCondition` instances need formula-specific `isAtom` predicate for minimal logic | L | M | Include `isAtom : F -> Bool` parameter in the minimal closure instance; defer full generic `IsAtomic` typeclass if needed |
| New module not properly wired into build | L | L | Run `lake exe mk_all --module` and verify imports in Phase 5 |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4 | 2 |
| 4 | 5 | 3, 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Sign and SignedFormula Foundation [COMPLETED]

**Goal**: Create the unified `Sign` type with full API and the generic `SignedFormula F L` structure. These are the leaf nodes of the import graph -- everything else depends on them.

**Tasks**:
- [ ] Create directory `Cslib/Foundations/Logic/Tableau/`
- [ ] Create `Cslib/Foundations/Logic/Tableau/Sign.lean` with:
  - Copyright header + `module` + `import Cslib.Init`
  - Module docstring referencing Smullyan1968, Fitting1983
  - `@[expose] public section` wrapper
  - `inductive Sign : Type where | pos | neg` with `deriving Repr, DecidableEq, BEq, Hashable, Inhabited`
  - `Sign.flip : Sign -> Sign` with `flip_pos`, `flip_neg` simp lemmas
  - `Sign.flip_flip` simp lemma
  - `ReflBEq Sign` and `LawfulBEq Sign` instances (follow bimodal pattern)
  - `Sign.isPos`, `Sign.isNeg` boolean helpers
- [ ] Create `Cslib/Foundations/Logic/Tableau/SignedFormula.lean` with:
  - Import `Sign.lean`
  - `structure SignedFormula (F : Type*) (L : Type*) where sign : Sign, formula : F, label : L`
  - `deriving DecidableEq, BEq, Hashable` (with appropriate universe annotations)
  - `SignedFormula.pos`, `SignedFormula.neg` constructors (with default label parameter)
  - `SignedFormula.flip` and `flip_flip` simp lemma
  - `SignedFormula.isPos`, `SignedFormula.isNeg` boolean helpers
  - `SignedFormula.withLabel` for relabeling
  - Namespace `Cslib.Logic.Tableau`
- [ ] Verify compilation: `lake build Cslib.Foundations.Logic.Tableau.Sign` and `lake build Cslib.Foundations.Logic.Tableau.SignedFormula`

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Tableau/Sign.lean` - New file: unified Sign type
- `Cslib/Foundations/Logic/Tableau/SignedFormula.lean` - New file: generic SignedFormula F L

**Verification**:
- Both files compile cleanly with `lake build`
- `Sign` has `DecidableEq`, `BEq`, `Hashable`, `Inhabited`, `ReflBEq`, `LawfulBEq`
- `SignedFormula` has `DecidableEq`, `BEq`, `Hashable` when F and L do
- `flip_flip` simp lemma works for both `Sign` and `SignedFormula`

---

### Phase 2: RuleResult and Branch Types [COMPLETED]

**Goal**: Define the generic `RuleResult F L` (4-variant inductive) and `Branch F L` (list alias with namespace helpers). These depend on `SignedFormula` and are needed by both the rule application (Phase 3) and closure detection (Phase 4).

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Tableau/RuleResult.lean` with:
  - Import `SignedFormula.lean`
  - `inductive RuleResult (F : Type*) (L : Type*) : Type _ where`
    - `| linear (formulas : List (SignedFormula F L))`
    - `| branching (branches : List (List (SignedFormula F L)))`
    - `| persistent (formulas : List (SignedFormula F L))`
    - `| notApplicable`
  - `RuleResult.isLinear`, `RuleResult.isBranching`, `RuleResult.isPersistent`, `RuleResult.isApplicable` boolean helpers
  - Brief module docstring explaining the 4 variants and their use cases
- [ ] Create `Cslib/Foundations/Logic/Tableau/Branch.lean` with:
  - Import `SignedFormula.lean`
  - `abbrev Branch (F : Type*) (L : Type*) := List (SignedFormula F L)`
  - `Branch.empty : Branch F L`
  - `Branch.contains` using `List.any` with `BEq`
  - `Branch.extend` (add single signed formula) and `Branch.extendMany` (add list)
  - `Branch.positives` / `Branch.negatives` (filter by sign)
  - `Branch.hasPosAt` / `Branch.hasNegAt` (sign + label queries)
  - `Branch.formulasAt` (all formulas at a given label)
  - `Branch.labels` (collect all distinct labels)
  - `Branch.findContradiction` (find complementary pair T(phi)/F(phi) at same label, returning `Option (F x L)`)
  - `Branch.hasContradiction` (boolean wrapper)
  - `Branch.hasBotPos` (check for T(bot) at any label, parameterized by `[HasBot F]`)
- [ ] Verify compilation of both files

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Logic/Tableau/RuleResult.lean` - New file: generic 4-variant rule result
- `Cslib/Foundations/Logic/Tableau/Branch.lean` - New file: branch type with label-generic operations

**Verification**:
- Both files compile cleanly
- `Branch.findContradiction` works with `[DecidableEq F] [DecidableEq L] [BEq (SignedFormula F L)]`
- `Branch.hasBotPos` requires `[HasBot F] [DecidableEq F] [DecidableEq L]`
- Branch operations tested conceptually with `L = Unit` (no label distinction)

---

### Phase 3: Closure Infrastructure [COMPLETED]

**Goal**: Define `ClosureReason`, the `ClosureCondition` typeclass, and three logic-strength instances (classical, intuitionistic, minimal). This is the key abstraction enabling logic-neutral tableau algorithms.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Tableau/Closure.lean` with:
  - Import `Branch.lean`
  - Import `Cslib.Foundations.Logic.Connectives` (for `HasBot`)
  - `inductive ClosureReason (F : Type*) (L : Type*) where`
    - `| botPos (l : L)` -- T(bot) at label l
    - `| contradiction (phi : F) (l : L)` -- T(phi) and F(phi) at same label
    - `| atomContradiction (p : F) (l : L)` -- T(p) and F(p) for atomic p at same label
  - `ClosureReason` docstring explaining the three closure modes
- [ ] Create `Cslib/Foundations/Logic/Tableau/ClosureCondition.lean` with:
  - Import `Closure.lean`
  - `class ClosureCondition (F : Type*) (L : Type*) where`
    - `findClosure : Branch F L -> Option (ClosureReason F L)`
  - `ClosureCondition.isClosed` (boolean) and `ClosureCondition.isOpen` (negation) derived helpers
  - **Classical instance**: `ClassicalClosure` -- checks T(bot) OR complementary T(phi)/F(phi) at same label
    - Takes `[DecidableEq F] [DecidableEq L] [BEq (SignedFormula F L)] [HasBot F]`
    - Uses `Branch.hasBotPos` and `Branch.findContradiction`
  - **Intuitionistic instance**: `IntuitionisticClosure` -- checks T(bot) ONLY
    - Takes `[DecidableEq F] [DecidableEq L] [BEq (SignedFormula F L)] [HasBot F]`
    - Only uses `Branch.hasBotPos`
  - **Minimal instance**: `MinimalClosure` -- checks complementary ATOMS T(p)/F(p) only
    - Takes `[DecidableEq F] [DecidableEq L] [BEq (SignedFormula F L)]` plus `isAtom : F -> Bool`
    - Scans branch for atomic formulas with complementary signs at same label
  - Docstring explaining the three closure modes and their logical justification
- [ ] Verify compilation of both files

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Foundations/Logic/Tableau/Closure.lean` - New file: ClosureReason inductive
- `Cslib/Foundations/Logic/Tableau/ClosureCondition.lean` - New file: typeclass + 3 instances

**Verification**:
- Both files compile cleanly
- Classical closure detects both T(bot) and complementary pairs
- Intuitionistic closure only detects T(bot)
- Minimal closure only detects complementary atoms (with user-provided `isAtom`)
- `ClosureCondition.isClosed` returns `Bool` correctly

---

### Phase 4: Propositional Rules [COMPLETED]

**Goal**: Refactor the 8 classical propositional rules from `PropositionalTableau.lean` into the new generic framework, parameterized over `SignedFormula F L` and returning `RuleResult F L`. Preserve the decomposition-function approach.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Tableau/PropositionalRules.lean` with:
  - Import `RuleResult.lean` (which transitively imports SignedFormula and Sign)
  - `inductive PropTableauRule : Type where` (keep the 8 constructors: andPos, andNeg, orPos, orNeg, impPos, impNeg, negPos, negNeg)
    - `deriving Repr, DecidableEq, BEq, Hashable`
  - `def applyPropRule {F : Type*} {L : Type*}` parameterized over:
    - `(andOf? : F -> Option (F x F))`
    - `(orOf? : F -> Option (F x F))`
    - `(impOf? : F -> Option (F x F))`
    - `(negOf? : F -> Option F)`
    - `(sf : SignedFormula F L) (rule : PropTableauRule) : RuleResult F L`
  - Rule bodies produce `RuleResult.linear` / `RuleResult.branching` / `RuleResult.notApplicable`
  - All results preserve the label from the input `sf` (classical rules don't create new worlds)
  - `def tryAllPropRules` -- tries all 8 rules on a signed formula, returns first applicable result
  - Module docstring with the 8-rule table from Smullyan's uniform notation
- [ ] Verify compilation: `lake build Cslib.Foundations.Logic.Tableau.PropositionalRules`
- [ ] Verify that the rule bodies are consistent with the existing `applyPropRule` in `PropositionalTableau.lean`

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Foundations/Logic/Tableau/PropositionalRules.lean` - New file: refactored classical propositional rules

**Verification**:
- File compiles cleanly
- All 8 rules produce correct `RuleResult` for the appropriate sign/connective combinations
- Results preserve the input label (no world creation in classical rules)
- `tryAllPropRules` returns `notApplicable` only when no rule matches
- No dependency on `ClosureCondition` (rules and closure are orthogonal)

---

### Phase 5: Module Root and Build Integration [IN PROGRESS]

**Goal**: Wire the new module into the CSLib build system. Create the module root import file, update `Cslib.lean` barrel import, add deprecation notice to `PropositionalTableau.lean`, and run the full CI verification pipeline.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Tableau.lean` as module root:
  - `import Cslib.Foundations.Logic.Tableau.Sign`
  - `import Cslib.Foundations.Logic.Tableau.SignedFormula`
  - `import Cslib.Foundations.Logic.Tableau.RuleResult`
  - `import Cslib.Foundations.Logic.Tableau.Branch`
  - `import Cslib.Foundations.Logic.Tableau.Closure`
  - `import Cslib.Foundations.Logic.Tableau.ClosureCondition`
  - `import Cslib.Foundations.Logic.Tableau.PropositionalRules`
  - Brief module docstring: "Shared tableau infrastructure for CSLib tableau calculi"
- [ ] Run `lake exe mk_all --module` to update `Cslib.lean` barrel import
- [ ] Add deprecation notice to `Cslib/Foundations/Logic/PropositionalTableau.lean`:
  - Add comment at top: `-- DEPRECATED: This file is superseded by Cslib.Foundations.Logic.Tableau. See task 297.`
  - Do NOT delete the file (deferred to cleanup)
- [ ] Run full CI verification pipeline:
  - `lake build` -- full project build
  - `lake exe checkInitImports` -- all files import Cslib.Init
  - `lake exe lint-style` -- style linting
  - `lake test` -- test suite
- [ ] Verify that all 7 new files + module root are importable via `import Cslib.Foundations.Logic.Tableau`

**Timing**: 1 hour

**Depends on**: 3, 4

**Files to modify**:
- `Cslib/Foundations/Logic/Tableau.lean` - New file: module root / import hub
- `Cslib.lean` - Updated via `lake exe mk_all --module` (adds Tableau imports)
- `Cslib/Foundations/Logic/PropositionalTableau.lean` - Add deprecation notice

**Verification**:
- `lake build` succeeds with zero errors
- `lake exe checkInitImports` passes (all new files import `Cslib.Init`)
- `lake exe lint-style` passes
- `lake test` passes
- `import Cslib.Foundations.Logic.Tableau` brings in all 7 sub-modules

## Testing & Validation

- [ ] Each file compiles independently with `lake build Cslib.Foundations.Logic.Tableau.{Module}`
- [ ] Full project builds with `lake build` after all phases
- [ ] `Sign` type has all expected instances: `DecidableEq, BEq, Hashable, Inhabited, ReflBEq, LawfulBEq`
- [ ] `SignedFormula` derives `DecidableEq, BEq, Hashable` when `F` and `L` do
- [ ] `flip_flip` simp lemma fires for both `Sign` and `SignedFormula`
- [ ] `Branch.findContradiction` correctly detects complementary pairs at the same label
- [ ] `ClosureCondition` instances behave correctly:
  - Classical: closes on T(bot) OR complementary T(phi)/F(phi)
  - Intuitionistic: closes on T(bot) only
  - Minimal: closes on complementary atoms only
- [ ] `applyPropRule` produces correct results for all 8 rule/sign/connective combinations
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes

## Artifacts & Outputs

- `Cslib/Foundations/Logic/Tableau/Sign.lean` (~80 lines)
- `Cslib/Foundations/Logic/Tableau/SignedFormula.lean` (~90 lines)
- `Cslib/Foundations/Logic/Tableau/RuleResult.lean` (~50 lines)
- `Cslib/Foundations/Logic/Tableau/Branch.lean` (~180 lines)
- `Cslib/Foundations/Logic/Tableau/Closure.lean` (~60 lines)
- `Cslib/Foundations/Logic/Tableau/ClosureCondition.lean` (~130 lines)
- `Cslib/Foundations/Logic/Tableau/PropositionalRules.lean` (~180 lines)
- `Cslib/Foundations/Logic/Tableau.lean` (~20 lines) -- module root
- Total estimated: ~790 lines (within 685-940 research estimate)

## Rollback/Contingency

All new files are additive -- no existing code is modified except a deprecation comment in `PropositionalTableau.lean`. To roll back:
1. Delete `Cslib/Foundations/Logic/Tableau/` directory and `Cslib/Foundations/Logic/Tableau.lean`
2. Re-run `lake exe mk_all --module` to remove from barrel import
3. Remove deprecation comment from `PropositionalTableau.lean`
4. `lake build` to verify clean state
