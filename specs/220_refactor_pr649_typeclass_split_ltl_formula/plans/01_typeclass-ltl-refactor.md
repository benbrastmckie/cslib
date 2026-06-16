# Implementation Plan: Refactor PR #649 Typeclass Split and LTL Formula

- **Task**: 220 - Refactor PR #649: typeclass split and LTL formula
- **Status**: [IMPLEMENTING]
- **Effort**: 4 hours
- **Dependencies**: None (targets PR branch `feat/temporal-formula-propositional`)
- **Research Inputs**: reports/01_team-research.md
- **Artifacts**: plans/01_typeclass-ltl-refactor.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This plan implements the follow-up commit for PR #649 based on reviewer feedback from ctchou and Matthew. The work adds `HasNext`, `FutureTemporalConnectives`, and `LTLConnectives` typeclasses to `Connectives.lean`; removes completeness-only content (Encodable/Countable/Infinite/Denumerable instances and manual BEq proofs) from `Temporal/Syntax/Formula.lean`; creates a new `LTL.Formula` inductive type with primitive `next`; and adds minimal omega-word satisfaction semantics. Definition of done: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`, and `lake exe mk_all --module` all pass cleanly.

### Research Integration

The team research report (4 teammates) confirmed:
- GenericMCS already satisfies Matthew's abstraction request; no new MCS machinery needed.
- The PR branch has a simplified `Connectives.lean` (no `HasBox`/`ModalConnectives`/`BimodalConnectives`), so restructuring `TemporalConnectives` to extend `FutureTemporalConnectives` is safe with no diamond risk.
- `HasNext` must be an independent primitive typeclass (not derived from `HasUntil`).
- `LTL.Formula` should be a new inductive `{atom, bot, imp, next, untl}` with `toTemporal` embedding.
- Keep `snce` in `Temporal.Formula`; LTL simply excludes it.
- Remove Encodable/Countable/Infinite/Denumerable and manual BEq from PR scope.
- Include minimal satisfaction relation definition over omega-words (no proof obligations).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the Temporal module infrastructure in the ROADMAP. Adding the LTL formula type and typeclass layer extends the connective hierarchy toward supporting discrete temporal completeness and future LTL-specific metalogic.

## Goals & Non-Goals

**Goals**:
- Add `HasNext` atomic typeclass and `FutureTemporalConnectives`/`LTLConnectives` bundles to `Connectives.lean`
- Restructure `TemporalConnectives` to extend `FutureTemporalConnectives` (safe on PR branch)
- Remove Encodable/Countable/Infinite/Denumerable instances and manual BEq proofs from `Temporal/Syntax/Formula.lean`
- Create `Cslib/Logics/LTL/Syntax/Formula.lean` with `{atom, bot, imp, next, untl}` inductive, `LTLConnectives` instance, derived connectives, scoped notation, and `toTemporal` embedding
- Create `Cslib/Logics/LTL/Semantics/Satisfies.lean` with basic satisfaction over `Nat -> (Atom -> Prop)`
- Pass full CI verification pipeline

**Non-Goals**:
- MCS / Lindenbaum construction for LTL (GenericMCS handles this when a proof system is added)
- LTL proof system, axiom typeclasses, or derivation trees
- LTS bridge (connecting `OmegaExecution` to LTL semantics)
- Past-time operators in LTL
- Countability or BEq instances for `LTL.Formula`
- Biconditional typeclass (`HasIff`)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Changing `TemporalConnectives` parent breaks downstream files | H | L | PR branch has no `BimodalConnectives`; only `Temporal/Syntax/Formula.lean` instance needs update |
| Removing Encodable imports breaks other Temporal modules | M | L | Research confirmed these are only used within the Countability section itself |
| `toTemporal` embedding type mismatch with `next` mapping | M | L | `next phi -> untl (toTemporal phi) bot` is well-typed; `lean_goal` verifies |
| `Finset.Basic` import needed elsewhere after removal | L | M | Verify no other definitions in Formula.lean depend on Finset before removing |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2 |
| 4 | 5 | 2, 3, 4 |

Phases within the same wave can execute in parallel.

### Phase 1: Typeclass Hierarchy in Connectives.lean [COMPLETED]

**Goal**: Add `HasNext`, `FutureTemporalConnectives`, `LTLConnectives` typeclasses and restructure `TemporalConnectives` parent.

**Tasks**:
- [ ] Add `HasNext` atomic typeclass after `HasSince` (line ~93)
- [ ] Add `FutureTemporalConnectives` bundle extending `PropositionalConnectives` and `HasUntil`
- [ ] Add `LTLConnectives` bundle extending `FutureTemporalConnectives` and `HasNext`
- [ ] Change `TemporalConnectives` to extend `FutureTemporalConnectives` and `HasSince` (instead of `PropositionalConnectives, HasUntil, HasSince`)
- [ ] Verify `lake build Cslib.Foundations.Logic.Connectives` compiles

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Connectives.lean` - Add 3 new typeclasses, modify 1 existing

**Verification**:
- `lake build Cslib.Foundations.Logic.Connectives` passes
- Typeclass hierarchy: `FutureTemporalConnectives extends PropositionalConnectives, HasUntil`; `LTLConnectives extends FutureTemporalConnectives, HasNext`; `TemporalConnectives extends FutureTemporalConnectives, HasSince`

---

### Phase 2: Clean Temporal Formula.lean [COMPLETED]

**Goal**: Remove completeness-only content (Encodable/Countable/Infinite/Denumerable instances and manual BEq proofs) and unnecessary imports.

**Tasks**:
- [ ] Remove `public import Mathlib.Logic.Encodable.Basic` (line 11)
- [ ] Remove `public import Mathlib.Logic.Denumerable` (line 12)
- [ ] Verify whether `public import Mathlib.Data.Finset.Basic` (line 13) is used elsewhere in the file; remove if not
- [ ] Remove the entire Countability section: `atom_injective`, `encodeNat`, `encodeNat_injective`, `Countable`, `Infinite`, `Denumerable` instances (lines 167-257)
- [ ] Remove the entire BEqLaws section: `beq_imp_eq`, `beq_untl_eq`, `beq_snce_eq`, `beq_refl`, `eq_of_beq`, `ReflBEq`, `LawfulBEq` instances (lines 259-333)
- [ ] Verify `TemporalConnectives` instance (line 139) still compiles after parent class change in Phase 1 (the instance fields `bot`, `imp`, `untl`, `snce` remain unchanged)
- [ ] Run `lake build Cslib.Logics.Temporal.Syntax.Formula` to confirm

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - Remove ~170 lines of imports and instances

**Verification**:
- `lake build Cslib.Logics.Temporal.Syntax.Formula` passes
- No references to `Encodable`, `Countable`, `Infinite`, `Denumerable`, `ReflBEq`, `LawfulBEq` remain
- `deriving DecidableEq, BEq` on the inductive is preserved

---

### Phase 3: Create LTL Formula Type [COMPLETED]

**Goal**: Create `Cslib/Logics/LTL/Syntax/Formula.lean` with the LTL formula inductive, `LTLConnectives` instance, derived connectives, scoped notation, and `toTemporal` embedding.

**Tasks**:
- [ ] Create directory `Cslib/Logics/LTL/Syntax/`
- [ ] Create `Formula.lean` with module header, `import Cslib.Init`, `import Cslib.Foundations.Logic.Connectives`, `import Cslib.Logics.Temporal.Syntax.Formula`
- [ ] Define `inductive LTL.Formula (Atom : Type u) : Type u` with constructors `{atom, bot, imp, next, untl}` and `deriving DecidableEq, BEq`
- [ ] Define derived connectives as `abbrev`s: `neg`, `top`, `or`, `and`, `iff`, `someFuture`, `allFuture`
- [ ] Add scoped notation (prefix/infix) for all connectives and temporal operators, scoped to `Cslib.Logic.LTL`
- [ ] Register `LTLConnectives` instance providing `bot`, `imp`, `untl`, `next`
- [ ] Add `Bot` and `Top` instances
- [ ] Define `toTemporal : LTL.Formula Atom -> Temporal.Formula Atom` mapping `next phi` to `untl (toTemporal phi) bot`
- [ ] Add docstring documenting Burgess convention and that `next` is primitive (not `untl phi bot`)
- [ ] Run `lake build Cslib.Logics.LTL.Syntax.Formula` to confirm

**Timing**: 1.5 hours

**Depends on**: 1

**Files to create**:
- `Cslib/Logics/LTL/Syntax/Formula.lean` - New LTL formula type (~150 lines)

**Verification**:
- `lake build Cslib.Logics.LTL.Syntax.Formula` passes
- `toTemporal` maps all five constructors correctly
- `LTLConnectives` instance resolves via typeclass synthesis

---

### Phase 4: Create LTL Satisfaction Semantics [COMPLETED]

**Goal**: Create minimal omega-word satisfaction relation to address ctchou's omega-execution request.

**Tasks**:
- [ ] Create directory `Cslib/Logics/LTL/Semantics/`
- [ ] Create `Satisfies.lean` with module header and `import Cslib.Logics.LTL.Syntax.Formula`
- [ ] Define `Satisfies (v : Nat -> Atom -> Prop) (i : Nat) : LTL.Formula Atom -> Prop` recursively over the five constructors
- [ ] Define `Valid (v : Nat -> Atom -> Prop) (phi : LTL.Formula Atom) : Prop := forall i, Satisfies v i phi`
- [ ] Define `Satisfiable (phi : LTL.Formula Atom) : Prop := exists v i, Satisfies v i phi`
- [ ] Add docstring noting this is basic satisfaction over omega-words; LTS bridge is future work
- [ ] Run `lake build Cslib.Logics.LTL.Semantics.Satisfies` to confirm

**Timing**: 30 minutes

**Depends on**: 2

**Files to create**:
- `Cslib/Logics/LTL/Semantics/Satisfies.lean` - Satisfaction relation (~50 lines)

**Verification**:
- `lake build Cslib.Logics.LTL.Semantics.Satisfies` passes
- No `sorry` or vacuous definitions

---

### Phase 5: CI Verification and Barrel Imports [COMPLETED]

**Goal**: Update barrel imports and pass full CI pipeline.

**Tasks**:
- [ ] Run `lake exe mk_all --module` to regenerate `Cslib.lean` with new LTL modules
- [ ] Run `lake build` (full project) to verify no regressions
- [ ] Run `lake exe checkInitImports` to verify all files import `Cslib.Init`
- [ ] Run `lake exe lint-style` to verify style compliance
- [ ] Fix any issues surfaced by CI checks

**Timing**: 45 minutes

**Depends on**: 2, 3, 4

**Files to modify**:
- `Cslib.lean` - Updated barrel imports (via `mk_all`)

**Verification**:
- `lake build` exits 0
- `lake exe checkInitImports` exits 0
- `lake exe lint-style` exits 0
- No regressions in existing Temporal modules

## Testing & Validation

- [ ] `lake build` passes with zero errors
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `TemporalConnectives` instance on `Temporal.Formula` still resolves
- [ ] `LTLConnectives` instance on `LTL.Formula` resolves
- [ ] `toTemporal` type-checks for all five constructors
- [ ] `Satisfies` definition compiles without sorry
- [ ] No downstream breakage in Temporal proof system or metalogic modules

## Artifacts & Outputs

- `Cslib/Foundations/Logic/Connectives.lean` - Modified (3 new typeclasses, 1 restructured)
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - Modified (removed ~170 lines)
- `Cslib/Logics/LTL/Syntax/Formula.lean` - New (~150 lines)
- `Cslib/Logics/LTL/Semantics/Satisfies.lean` - New (~50 lines)
- `Cslib.lean` - Updated barrel imports

## Rollback/Contingency

All changes are additive (new files, new typeclasses) except the `TemporalConnectives` parent change and Temporal Formula cleanup. If the parent change causes downstream issues:
1. Revert `TemporalConnectives` to its original `extends PropositionalConnectives, HasUntil, HasSince`
2. Keep `FutureTemporalConnectives` as an independent class (not a parent of `TemporalConnectives`)
3. `LTLConnectives` would still extend `FutureTemporalConnectives` independently

For the Formula cleanup, if removed instances are needed by other files not yet committed on the PR branch, re-add them in a separate section file.
