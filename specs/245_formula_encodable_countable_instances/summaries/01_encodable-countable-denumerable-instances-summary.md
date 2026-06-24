# Implementation Summary: Task #245

- **Task**: 245 - Encodable/Countable/Denumerable instances for the LTL Formula type
- **Status**: [COMPLETED]
- **Date**: 2026-06-24
- **Session**: sess_1782337917_d3406f_245

## What Was Implemented

Added `Encodable`, `Countable`, `Infinite`, and `Denumerable` instances to
`Cslib/Logics/LTL/Syntax/Formula.lean`. Two `public import` lines were also added.

### File Modified

`Cslib/Logics/LTL/Syntax/Formula.lean`

**Import additions** (lines 12-13):
```lean
public import Mathlib.Data.W.Basic
public import Mathlib.Logic.Denumerable
```

**New declarations** (after line 97, before `LTLConnectives` instance):

- `Formula.wTag` (abbrev): Constructor tag type for W-type encoding.
- `Formula.wArity` (def): Arity function mapping tags to sub-formula count types.
- Two `instance` declarations (Fintype, Encodable) for `Formula.wArity`.
- `Formula.toW` (def): Embeds `Formula` into `WType (Formula.wArity)`.
- `Formula.fromW` (def): Decodes W-type back to `Formula`.
- `Formula.fromW_toW` (theorem): Left inverse property.
- `instance Encodable (Formula Atom)` via `Encodable.ofLeftInverse`.

**New declarations** (after `Bot`/`Top` instances):
- `instance Countable (Formula Atom)` via `Encodable.countable`.
- `private def iterNext`: Injects `ℕ` into `Formula Atom` via iterated `next`.
- `instance Infinite (Formula Atom)` via `Infinite.of_injective iterNext`.
- `instance Denumerable (Formula Atom)` via `Denumerable.ofEncodableOfInfinite`.

## Plan Deviations

**Deviation 1**: `deriving Encodable` approach replaced by manual WType-based encoding.

The plan's primary approach (`deriving Encodable`) fails in the `module`/`@[expose] public section`
CSLib context due to a known bug in the Lean `deriving Encodable` handler when used in this
context. The handler generates code with internal private declarations it cannot then access.

**Mitigation**: Used `Encodable.ofLeftInverse` with a WType-based encoding. The `Formula` type
is isomorphic to `WType (Formula.wArity)` where `Formula.wArity : (Atom ⊕ Fin 4) → Type`
maps each constructor tag to its sub-formula arity. The left inverse property
(`Formula.fromW_toW`) is proved by structural induction with `rfl` at leaves and
`congrArg₂` at binary constructor cases.

**Deviation 2**: `Mathlib.Tactic.DeriveEncodable` import replaced by `Mathlib.Data.W.Basic`.

The `DeriveEncodable` import was needed for the `deriving Encodable` approach.
The manual WType approach needs `Mathlib.Data.W.Basic` instead. `Mathlib.Logic.Denumerable`
was kept as planned (provides `Denumerable.ofEncodableOfInfinite`).

## CI Verification Results

| Check | Status | Notes |
|-------|--------|-------|
| `lake build Cslib.Logics.LTL.Syntax.Formula` | PASS | 708 jobs, no errors |
| `lake build` (full) | PASS (for LTL module) | Pre-existing failures in unrelated modules |
| `lake lint` (LTL/Syntax/Formula.lean) | PASS | No warnings |
| `lake exe lint-style` | PASS | No style issues |
| `lake shake --add-public --keep-implied --keep-prefix` | PASS | No redundant imports flagged |
| `lake exe checkInitImports` | PASS (for LTL module) | Pre-existing failures in unrelated modules |
| `Cslib.Init` import | PASS | Line 9: `public import Cslib.Init` |
| `#synth Encodable (Formula ℕ)` | PASS | `instEncodableFormula` |
| `#synth Countable (Formula ℕ)` | PASS | `instCountableFormulaOfEncodable` |
| `#synth Infinite (Formula ℕ)` | PASS | `instInfiniteFormula` |
| `#synth Infinite (Formula Empty)` | PASS | Unconditional (no Atom constraint) |
| `#synth Denumerable (Formula ℕ)` | PASS | `instDenumerableFormulaOfEncodable` |
| Sorry count | 0 | Zero sorries |
| New axioms | 0 | Only `propext`, `Classical.choice`, `Quot.sound` (standard) |

## Downstream Impact

The `Denumerable (Formula Atom)` instance (under `[Encodable Atom]`) allows callers of
`Cslib.Logics.Temporal.Metalogic.Completeness` and
`Cslib.Logics.Bimodal.Metalogic.BXCanonical.CanonicalModel` to discharge the
`[Denumerable (Formula Atom)]` hypothesis automatically via `inferInstance` when
`[Encodable Atom]` is in scope, eliminating the need to pass it explicitly.
