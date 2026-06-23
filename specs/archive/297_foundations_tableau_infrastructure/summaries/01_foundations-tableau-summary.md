# Implementation Summary: Task #297 — Shared Tableau Infrastructure

- **Task**: 297 - Build shared tableau infrastructure in Foundations/Logic/Tableau/
- **Status**: [IMPLEMENTED]
- **Session**: sess_1782238418_d0d7dd
- **Completed**: 2026-06-23

## What Was Built

Created 7 new Lean files + 1 module root under `Cslib/Foundations/Logic/Tableau/`:

| File | Lines | Description |
|------|-------|-------------|
| `Sign.lean` | ~115 | Unified two-valued sign type with full API |
| `SignedFormula.lean` | ~95 | Generic `SignedFormula F L` parameterized structure |
| `RuleResult.lean` | ~80 | Four-variant rule result inductive type |
| `Branch.lean` | ~115 | Branch type with label-generic operations |
| `Closure.lean` | ~65 | `ClosureReason` inductive type |
| `ClosureCondition.lean` | ~150 | `ClosureCondition` typeclass + 3 instances |
| `PropositionalRules.lean` | ~155 | Classical propositional rules refactored |
| `Tableau.lean` | ~35 | Module root re-exporting all components |

Total: ~810 lines across 8 files.

## Key Design Decisions

### Sign Type
The unified `Sign` type replaces both `PropSign` (Foundations) and the bimodal `Sign`. It provides the full API: `flip`, `isPos`, `isNeg`, simp lemmas `flip_pos`, `flip_neg`, `flip_flip`, plus `ReflBEq` and `LawfulBEq` instances.

### SignedFormula Parameterization
`SignedFormula (F : Type*) (L : Type*)` is label-parameterized:
- Classical: `L = Unit`
- Intuitionistic/minimal: `L = Nat` or a world-index type
- Modal: `L = WorldIndex`

Derives `DecidableEq`, `BEq`, `Hashable` when F and L do.

### RuleResult Variants
Four variants from day one including `persistent` (for modal/temporal box-rules in tasks 299-301). This avoids needing to refactor the type when modal rules are added.

### ClosureCondition Typeclass
The `ClosureCondition F L` typeclass uses `findClosure : Branch F L → Option (ClosureReason F L)` (not `Bool`) to support proof extraction. Three instances:
- `ClassicalClosure`: T(bot) OR T(phi)/F(phi) at same label
- `IntuitionisticClosure`: T(bot) only
- `MinimalClosure`: complementary atoms T(p)/F(p) via `IsAtomic F` typeclass

The `MinimalClosure` instance uses a new `IsAtomic F` typeclass (added to ClosureCondition.lean) to encode atomicity in a type-class-synthesizable way.

### PropositionalRules
Refactored from `PropositionalTableau.lean` using `RuleResult F L` and label-preserving results. The decomposition-function approach (`andOf?`, `orOf?`, etc.) is preserved. All 8 classical rules: andPos, andNeg, orPos, orNeg, impPos, impNeg, negPos, negNeg.

## Import Lessons Learned

Two critical lessons discovered during implementation:
1. Files using `Type*` structure parameters MUST have `import Cslib.Init` as a DIRECT import (not just transitive), when combined with the `module` keyword.
2. Types declared in files using `@[expose] public section` must be accessed via `public import`, not plain `import`, when used in field/parameter types.

## Plan Deviations

| Deviation | Description |
|-----------|-------------|
| Altered Phase 3 | `ClosureCondition.lean` adds `IsAtomic F` typeclass (not in original plan) to make `MinimalClosure` instance synthesizable. The original plan proposed `MinimalClosureConfig` as a struct argument, which is not instance-synthesizable. |
| Altered Phase 3 | Removed `[BEq L]` from `IntuitionisticClosure` and `[DecidableEq F]`, `[DecidableEq L]` from `ClassicalClosure` instances (unused; caught by lint). |
| Altered Phase 2 | Removed `[BEq L]` from `Branch.hasBotPos` (unused; only formula comparison needed). |
| Altered Phase 1 | Removed `Repr` from `SignedFormula` deriving clause (generated unused `prec` argument; caught by lint). |
| Altered Phase 3 | `Closure.lean` imports only `Cslib.Init` (not `Branch` or `SignedFormula`); `ClosureReason` does not use either type directly. `ClosureCondition.lean` imports `Branch` directly as required by lake shake. |

## CI Verification

All checks passed:

| Check | Result |
|-------|--------|
| `lake build Cslib.Foundations.Logic.Tableau` | PASS |
| `lake exe checkInitImports` | PASS |
| `lake lint` | PASS |
| `lake exe lint-style` | PASS |
| `lake shake` | PASS (only pre-existing `Conversions.lean` warning) |
| `lake exe mk_all --module` | PASS (Tableau entries added to Cslib.lean) |
| Sorry count in new files | 0 |
| Vacuous definitions | 0 |
| New axioms | 0 |

Note: `lake test` fails due to pre-existing `FragmentPredicates.lean` error (untracked file, unrelated to this task).

## Next Steps

This infrastructure supports:
- Task 298: Propositional decidability (via `ClosureCondition`, `applyPropRule`)
- Tasks 299-301: Modal/temporal tableau (via `RuleResult.persistent`, `Branch.labels`)
- Task 296 metatask: Completes root infrastructure phase
