# Implementation Plan: Task #225

- **Task**: 225 - Implement GHA algebraic semantics with primitive bot on main
- **Status**: [COMPLETED]
- **Effort**: 7 hours
- **Dependencies**: None
- **Research Inputs**: specs/225_gha_semantics_refactor/reports/01_gha-semantics-research.md
- **Artifacts**: plans/01_gha-semantics-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This plan implements a generic algebraic semantics for propositional logic using Mathlib's
`GeneralizedHeytingAlgebra` / `HeytingAlgebra` / `BooleanAlgebra` class hierarchy. The work
creates `AlgEvaluate` with a primitive `bot_val` parameter (since GHA lacks bottom), proves
soundness for all three axiom tiers (MinPropAxiom/IntPropAxiom/PropositionalAxiom), and
consolidates the existing `Basic.lean` into `Bool.lean` to align with PR #648 file structure.
Bridge lemmas connect the existing `Evaluate` and `BoolEvaluate` to the new generic evaluator.
No downstream files (Kripke.lean, modal, temporal, bimodal) are modified.

### Research Integration

Key findings from the research report (01_gha-semantics-research.md):

- **Mathlib API mapping**: All 8 MinPropAxiom cases provable at GHA level using `le_himp`,
  `himp_himp`, `le_himp_iff`, `inf_le_left/right`, `le_sup_left/right`, `himp_inf_le`.
  ImplyS requires a 5-step chain: `himp_eq_top_iff` -> `himp_himp` -> `le_himp_iff` ->
  `himp_inf_self` -> `himp_inf_le`.
- **efq at HA level**: Direct via `bot_himp : bot => a = top` or `bot_le`.
- **Peirce at BA level**: Requires `himp_eq : x => y = y | x^c` to unfold to lattice operations,
  then BA reasoning with `compl_compl`, `sup_compl_eq_top`.
- **Downstream safety**: 6 files import `Semantics.Basic` directly. All reference `PL.Evaluate`
  and `PL.Valuation` by name; these must remain at the same qualified paths.
- **IForces bridge deferred**: The `iforces_eq` bridge requires defining upset Heyting algebra
  instances (Stone/Esakia duality). Too complex for this task; defer to a follow-up.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task does not directly correspond to a specific remaining ROADMAP.md item. It is
infrastructure work that strengthens the propositional semantics layer, supporting future
completeness proofs for discrete/continuous bimodal and temporal logics.

## Goals & Non-Goals

**Goals**:
- Create `Semantics/Algebra.lean` with `AlgEvaluate`, `GHAValid`, `HAValid`, `BAValid`
- Create `Semantics/Algebra/Soundness.lean` with soundness for all three axiom tiers
- Consolidate `Basic.lean` content into `Bool.lean` with re-exports
- Create bridge lemmas `prop_evaluate_eq` and `bool_evaluate_eq`
- Pass full CSLib CI pipeline (build, lint, test, shake)

**Non-Goals**:
- Modifying `Kripke.lean` or any completeness proofs
- Implementing the `iforces_eq` bridge (requires upset Heyting algebra, deferred)
- Touching downstream modal/temporal/bimodal files beyond import path changes
- Refactoring `SemanticConsequence.lean` to use algebraic semantics

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Peirce's law proof in BA is non-trivial (no direct Mathlib lemma) | M | M | Use `himp_eq` to reduce to lattice ops + `simp [compl_compl, sup_compl_eq_top]`; test with `lean_multi_attempt` before committing |
| ImplyS proof chain is multi-step at GHA level | M | L | Research identified exact 5-step chain; proof sketch verified symbolically |
| `Basic.lean` removal breaks transitive imports | H | L | `Bool.lean` already does `public import Basic.lean`; absorb content and update direct importers only |
| `lake shake` flags new unused imports in Algebra.lean | L | M | Import only what is needed; run shake before final commit |
| Naming collision between `Evaluate` and `AlgEvaluate` | M | L | Use `AlgEvaluate` naming (parallels existing `BoolEvaluate` convention) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3, 4 | 1 for Phase 3; 1, 2 for Phase 4 |
| 3 | 5 | 3, 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Consolidate Basic.lean into Bool.lean [COMPLETED]

**Goal**: Merge the Prop-valued `Evaluate`, `Valuation`, and `Tautology` definitions from
`Basic.lean` into `Bool.lean`, then remove `Basic.lean` and update all import paths.

**Tasks**:
- [ ] Move all definitions and theorems from `Basic.lean` into the top of `Bool.lean`
  (before the `BoolValuation`/`BoolEvaluate` section), preserving the module docstring
  from `Basic.lean` as a section comment
- [ ] Change `Bool.lean`'s import from `public import Cslib.Logics.Propositional.Semantics.Basic`
  to `public import Cslib.Logics.Propositional.Defs`
- [ ] Update all 5 direct importers to import `Semantics.Bool` instead of `Semantics.Basic`:
  - `Metalogic/Soundness.lean`
  - `Metalogic/StrongCompleteness.lean`
  - `Semantics/SemanticConsequence.lean`
  - `Logics/Modal/FromPropositional.lean`
  - `Logics/Temporal/ConservativeExtension.lean`
- [ ] Delete `Basic.lean`
- [ ] Update `Cslib.lean` barrel: remove `import Cslib.Logics.Propositional.Semantics.Basic`
- [ ] Run `lake exe mk_all --module` to regenerate barrel file
- [ ] Build verification: `lake build` (full build to catch transitive breakage)

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Bool.lean` - absorb Basic.lean content
- `Cslib/Logics/Propositional/Semantics/Basic.lean` - delete
- `Cslib/Logics/Propositional/Metalogic/Soundness.lean` - update import
- `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` - update import
- `Cslib/Logics/Propositional/Semantics/SemanticConsequence.lean` - update import
- `Cslib/Logics/Modal/FromPropositional.lean` - update import
- `Cslib/Logics/Temporal/ConservativeExtension.lean` - update import
- `Cslib.lean` - remove Basic import line

**Verification**:
- `lake build` succeeds with zero errors
- All downstream files compile (modal, temporal, bimodal)
- `PL.Evaluate`, `PL.Valuation`, `PL.Tautology` still accessible at same qualified names
- `BoolEvaluate_eq_iff` bridge lemma still works

---

### Phase 2: Create Semantics/Algebra.lean [COMPLETED]

**Goal**: Define the generic algebraic evaluator `AlgEvaluate` and validity predicates
`GHAValid`, `HAValid`, `BAValid`.

**Tasks**:
- [ ] Create directory `Cslib/Logics/Propositional/Semantics/Algebra/` (for future Soundness.lean)
- [ ] Create `Cslib/Logics/Propositional/Semantics/Algebra.lean` with:
  - Copyright header and module docstring
  - `import Cslib.Init`
  - `public import Cslib.Logics.Propositional.Defs`
  - `import Mathlib.Order.Heyting.Basic`
  - `import Mathlib.Order.BooleanAlgebra.Basic` (or `.Defs`)
  - `AlgEvaluate [GeneralizedHeytingAlgebra H] (v : Atom -> H) (bot_val : H) : PL.Proposition Atom -> H`
    mapping: atom -> v, bot -> bot_val, imp -> himp, and -> inf, or -> sup
  - `@[simp]` lemmas for each constructor case
  - `GHAValid phi` := for all H [GHA H], v, bot_val, AlgEvaluate v bot_val phi = top
  - `HAValid phi` := for all H [HA H], v, AlgEvaluate v bot phi = top
  - `BAValid phi` := for all H [BA H], v, AlgEvaluate v bot phi = top
- [ ] Add docstrings to all public definitions
- [ ] Add to `Cslib.lean` barrel file via `lake exe mk_all --module`
- [ ] Build verification: `lake build Cslib.Logics.Propositional.Semantics.Algebra`

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra.lean` - create new
- `Cslib.lean` - add import (via mk_all)

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra` succeeds
- All simp lemmas pass simpNF check
- No linter warnings

---

### Phase 3: Create Soundness.lean for Algebraic Semantics [COMPLETED]

**Goal**: Prove soundness of each axiom tier under the corresponding algebraic semantics:
MinPropAxiom is GHAValid, IntPropAxiom is HAValid, PropositionalAxiom is BAValid.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Semantics/Algebra/Soundness.lean` with:
  - `import Cslib.Init`
  - `public import Cslib.Logics.Propositional.Semantics.Algebra`
  - `public import Cslib.Logics.Propositional.ProofSystem.Derivation`
  - `public import Cslib.Logics.Propositional.ProofSystem.Axioms`
- [ ] Prove `min_alg_axiom_sound : MinPropAxiom phi -> GHAValid phi` (8 cases):
  - implyK: via `le_himp` or `himp_eq_top_iff` + trivial
  - implyS: via `himp_eq_top_iff` + `himp_himp` + `le_himp_iff` + `himp_inf_self` + `himp_inf_le`
  - andI: via `le_himp_iff` + `le_inf`
  - andE1: via `himp_eq_top_iff` + `inf_le_left`
  - andE2: via `himp_eq_top_iff` + `inf_le_right`
  - orI1: via `himp_eq_top_iff` + `le_sup_left`
  - orI2: via `himp_eq_top_iff` + `le_sup_right`
  - orE: via `himp_eq_top_iff` + `le_himp_iff` + distributivity
- [ ] Prove `int_alg_axiom_sound : IntPropAxiom phi -> HAValid phi` (9 cases):
  - Delegate 8 MinPropAxiom cases to `min_alg_axiom_sound` via `MinPropAxiom.toIntPropAxiom`
    (or direct case match delegating each min case)
  - efq: via `bot_himp` or `himp_eq_top_iff` + `bot_le`
- [ ] Prove `prop_alg_axiom_sound : PropositionalAxiom phi -> BAValid phi` (10 cases):
  - Delegate 9 IntPropAxiom cases via subsumption
  - peirce: via `himp_eq` to unfold all implications to `sup`/`compl`, then BA reasoning
- [ ] Prove derivation-level soundness theorems:
  - `min_alg_soundness` / `min_alg_soundness_derivable`
  - `int_alg_soundness` / `int_alg_soundness_derivable`
  - `prop_alg_soundness` / `prop_alg_soundness_derivable`
  (follow the existing pattern from Metalogic/Soundness.lean: induction on DerivationTree)
- [ ] Add docstrings to all theorems
- [ ] Add to `Cslib.lean` barrel file via `lake exe mk_all --module`
- [ ] Build verification: `lake build Cslib.Logics.Propositional.Semantics.Algebra.Soundness`

**Timing**: 2.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/Soundness.lean` - create new
- `Cslib.lean` - add import (via mk_all)

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.Soundness` succeeds
- All 10+9+8 axiom cases proved without sorry
- Derivation-level soundness follows by induction
- No linter warnings

---

### Phase 4: Bridge Lemmas [COMPLETED]

**Goal**: Create bridge lemmas connecting the existing `Evaluate` and `BoolEvaluate` to the
generic `AlgEvaluate`, demonstrating that the existing semantics are special cases.

**Tasks**:
- [ ] Add bridge lemmas to `Semantics/Algebra.lean` (after the validity definitions, in a
  new section that imports `Semantics.Bool` content transitively via Prop/Bool instances):
  - `prop_evaluate_eq : Evaluate v phi <-> AlgEvaluate (fun a => v a) False phi`
    Proof by induction on phi. Uses `Prop.instHeytingAlgebra` where `himp = (. -> .)`,
    `inf = And`, `sup = Or`, `bot = False`, `top = True`.
  - `bool_evaluate_eq : BoolEvaluate v phi = AlgEvaluate (fun a => v a) false phi`
    Proof by induction on phi. Uses `Bool.instBooleanAlgebra` where `himp = (!. || .)`,
    `inf = (. && .)`, `sup = (. || .)`.
- [ ] Alternative: if import circularity prevents placing bridges in `Algebra.lean`, create
  a dedicated `Semantics/Algebra/Bridge.lean` file
- [ ] Add docstrings explaining each bridge
- [ ] Update barrel file via `lake exe mk_all --module`
- [ ] Build verification: `lake build` on the relevant module

**Timing**: 1.5 hours

**Depends on**: 1, 2

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra.lean` - add bridge section (preferred)
  OR `Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean` - create new (fallback)
- `Cslib.lean` - add import if new file created

**Verification**:
- Bridge lemmas compile without sorry
- `prop_evaluate_eq` and `bool_evaluate_eq` are proven by structural induction
- No circular imports

---

### Phase 5: CI Verification and Cleanup [COMPLETED]

**Goal**: Run the full CSLib CI pipeline and fix any issues.

**Tasks**:
- [ ] `lake build` - full project build
- [ ] `lake exe checkInitImports` - verify all new files import `Cslib.Init`
- [ ] `lake exe lint-style` - style linting (fix issues if any)
- [ ] `lake lint` - environment linters (check docBlame, simpNF, etc.)
- [ ] `lake test` - run CslibTests suite
- [ ] `lake exe mk_all --module` - verify barrel file is up to date
- [ ] `lake shake --add-public --keep-implied --keep-prefix` - import minimization
- [ ] Fix any issues found by CI checks
- [ ] Verify no downstream breakage: spot-check that modal, temporal, bimodal modules compile

**Timing**: 1 hour

**Depends on**: 3, 4

**Files to modify**:
- Any files flagged by linters or shake (exact set determined at runtime)

**Verification**:
- All CI checks pass with zero errors
- `lake build` succeeds for the entire project
- No new linter warnings introduced

## Testing & Validation

- [ ] `lake build` succeeds (full project, no errors)
- [ ] `lake exe checkInitImports` passes (all new files have `import Cslib.Init`)
- [ ] `lake exe lint-style` passes (no style violations)
- [ ] `lake lint` passes (no docBlame, simpNF, or other linter issues)
- [ ] `lake test` passes (CslibTests suite)
- [ ] `lake shake` reports no unnecessary imports
- [ ] `PL.Evaluate`, `PL.Valuation`, `PL.Tautology` remain accessible at their current qualified paths
- [ ] `BoolEvaluate_eq_iff` bridge lemma still works after consolidation
- [ ] No downstream modal/temporal/bimodal files broken
- [ ] All soundness theorems proved without sorry

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Algebra.lean` - AlgEvaluate + validity defs + bridge lemmas
- `Cslib/Logics/Propositional/Semantics/Algebra/Soundness.lean` - Axiom tier soundness proofs
- `Cslib/Logics/Propositional/Semantics/Bool.lean` - Consolidated (absorbs Basic.lean content)
- `Cslib/Logics/Propositional/Semantics/Basic.lean` - Deleted
- Updated import paths in 5 downstream files

## Rollback/Contingency

All changes are additive (new files) or import-path mechanical (Basic->Bool consolidation).
Rollback strategy:
- **If consolidation breaks downstream**: Revert Bool.lean edits, restore Basic.lean from git,
  revert import changes. The new Algebra.lean files are independent and can remain.
- **If Peirce proof is blocked**: Mark Phase 3 as [PARTIAL], submit MinPropAxiom and IntPropAxiom
  soundness without PropositionalAxiom soundness. Create a follow-up task for the Peirce case.
- **If bridge lemmas have import circularity**: Move bridges to a separate
  `Algebra/Bridge.lean` file that imports both `Algebra.lean` and `Bool.lean`.
- **Full rollback**: `git checkout main -- Cslib/Logics/Propositional/Semantics/ Cslib.lean`
  restores all files to pre-implementation state.
