# Research Report: Docstring Conversion for GenericMCSBridge.lean

## File Overview

**Path**: `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean`

This is a documentation-only file (contains no Lean declarations, only comments). It provides
a gap analysis for the relationship between `algebraicDerivationSystem` and
`modalDerivationSystem` in normal modal logics.

## Current Comment Structure

The file contains three comment blocks:

| Lines | Syntax | Content | Status |
|-------|--------|---------|--------|
| 1-5 | `/- ... -/` | Copyright header | Correct -- copyright headers use plain block comments per Lean/Mathlib convention |
| 12-113 | `/-! ... -/` | Module docstring with full gap analysis | Already correct -- uses `/-!` format |
| 115-122 | `/- ... -/` | NOTE about the file being documentation-only | Needs conversion to `/-!` |

## CSLib Documentation Conventions

CSLib follows the Mathlib docstring convention:

- `/-! ... -/` -- Module docstrings: appear in generated documentation, used for section
  headers and module-level documentation. All substantive documentation blocks in `.lean` files
  should use this format.
- `/-- ... -/` -- Declaration docstrings: attached to the next declaration (`def`, `theorem`,
  `lemma`, `instance`, `structure`, etc.).
- `/- ... -/` -- Plain block comments: NOT included in generated documentation. Used for
  copyright headers and internal implementation notes not intended for users.

Evidence from CSLib codebase: Every file in `Cslib/Logics/Modal/` that has module-level
documentation uses `/-! ... -/`. The GenericMCSBridge.lean file is the only one in the Modal
directory with a substantive plain `/- ... -/` block comment (aside from copyright headers).

## Required Change

**One edit**: Convert the plain block comment at lines 115-122 from `/- ... -/` to `/-! ... -/`.

### Before (lines 115-122)

```lean
/- NOTE: This file contains no Lean code (only documentation).
   The gap analysis above explains why no bridge theorem is proved here.
   The two derivation systems are architecturally distinct:
   - `algebraicDerivationSystem` captures propositional contextual derivability
   - `modalDerivationSystem` additionally captures necessitation

   Future work: extend `ListDeriv` with a necessitation rule and prove equivalence.
-/
```

### After

```lean
/-! NOTE: This file contains no Lean code (only documentation).
   The gap analysis above explains why no bridge theorem is proved here.
   The two derivation systems are architecturally distinct:
   - `algebraicDerivationSystem` captures propositional contextual derivability
   - `modalDerivationSystem` additionally captures necessitation

   Future work: extend `ListDeriv` with a necessitation rule and prove equivalence.
-/
```

## Verification

- The copyright header at lines 1-5 should remain as `/- ... -/` (standard convention).
- The main module docstring at lines 12-113 is already `/-! ... -/` (no change needed).
- The NOTE block at lines 115-122 is the sole edit target.
- After the edit, `lake build` should succeed (docstring format change has no effect on compilation).

## Implementation Complexity

This is a single-character edit: insert `!` after `/-` on line 115. No risk of breaking
compilation or introducing lint failures. The change ensures the NOTE block appears in
generated documentation alongside the main gap analysis.
