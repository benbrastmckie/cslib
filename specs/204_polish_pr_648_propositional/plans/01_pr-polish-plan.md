# Implementation Plan: Polish PR #648

## Overview
Apply 4 review fixes to `feat/propositional-v2` branch, verify build, squash, and force-push.

## Phase 1: Apply All Edits on `feat/propositional-v2`

**Goal**: Checkout the branch and make all 4 changes.

### Step 1.1: Checkout branch
```bash
git checkout feat/propositional-v2
```

### Step 1.2: Remove `Aesop.BuiltinRules` import from `Defs.lean`
- File: `Cslib/Logics/Propositional/Defs.lean`
- Remove line: `public import Aesop.BuiltinRules`
- Rationale: No `aesop` tactic used; `grind` is Lean built-in. Import was accidental.

### Step 1.3: Remove Architecture section from `Defs.lean` docstring
- File: `Cslib/Logics/Propositional/Defs.lean`
- Remove the `## Architecture` section (references non-existent upstream files)
- Keep all other docstring sections (Main definitions, Notation, References)

### Step 1.4: Fix context variable naming in `NaturalDeduction/Basic.lean`
- File: `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`
- In `Theory.Derivation` constructors: rename `G` → `Γ` in `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`
- In `weak` function: update `@`-pattern matches that bind `G` to use `Γ`
- In `subs` function: update pattern matches similarly
- In `substAtom` function: update pattern matches similarly
- `impI` and `impE` already use `Γ` — leave unchanged

### Step 1.5: Fix copyright headers
- File: `Cslib/Logics/Propositional/Defs.lean`
  - Change: `Copyright (c) 2025 Thomas Waring, 2026 Benjamin Brast-McKie`
  - To: `Copyright (c) 2025 Thomas Waring, Benjamin Brast-McKie`
- File: `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`
  - Same change

## Phase 2: Verify and Push

### Step 2.1: Build verification
```bash
lake build Cslib.Logics.Propositional.Defs
lake build Cslib.Logics.Propositional.NaturalDeduction.Basic
```

### Step 2.2: CI checks
```bash
lake exe checkInitImports
lake exe lint-style
```

### Step 2.3: Squash and force-push
```bash
git add -A
git commit --amend  # squash into existing commit
git push --force origin feat/propositional-v2
```

## Verification Checklist
- [ ] `Aesop.BuiltinRules` import removed
- [ ] Architecture section removed from docstring
- [ ] All `G` renamed to `Γ` in constructors and pattern matches
- [ ] Copyright headers use single-year format
- [ ] `lake build` passes for both files
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] Squashed and force-pushed
