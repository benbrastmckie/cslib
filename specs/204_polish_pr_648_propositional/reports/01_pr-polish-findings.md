# PR #648 Polish Findings

Session: sess_1781489508_4a1c0f

## 1. Aesop.BuiltinRules Import

**Finding: REMOVE. The import is unnecessary.**

On the `feat/propositional-v2` branch, `Defs.lean` line 10 has `public import Aesop.BuiltinRules`.
However:

- **No `aesop` tactic usage anywhere** in either `Defs.lean` or `NaturalDeduction/Basic.lean`.
  The file uses `grind` exclusively for proof automation.
- **`grind` does not depend on Aesop**. `grind` is a Lean built-in tactic
  (`Lean.Elab.Tactic.Grind`), entirely independent of the Aesop library.
- **The main branch's `Defs.lean` does NOT have this import** -- it was added only on the PR
  branch, likely as an accidental leftover from experimentation.
- **Other CSLib files using `grind`** (e.g., `Cslib/Foundations/Logic/InferenceSystem.lean`) do
  not import Aesop.
- `Aesop.BuiltinRules` provides aesop-specific rule registrations (assumption, destructProducts,
  ext, intros, rfl, split, subst) plus `@[aesop]` attributes for `And`, `Or`, `Iff` types.
  None of this is needed by the PR's code.
- Being a `public import`, it unnecessarily forces all downstream importers of `Defs.lean` to
  also depend on Aesop, increasing compile time for no benefit.

**Action**: Remove `public import Aesop.BuiltinRules` from `Defs.lean`. The `lake shake` CI
check would likely flag this as unused anyway.

## 2. Architecture Section in Defs.lean Docstring

**Finding: REMOVE the Architecture section entirely.**

The `## Architecture` section in the `Defs.lean` module docstring references:

| Reference | Exists on PR branch? |
|-----------|---------------------|
| `NaturalDeduction/Basic.lean` | YES (part of this PR) |
| `ProofSystem/` directory | NO -- only on local dev branch |
| `NaturalDeduction/Equivalence.lean` | NO -- only on local dev branch |
| `hilbert_iff_nd`, `hilbert_iff_nd_min`, etc. | NO -- not defined in any PR file |
| `MinPropAxiom`, `IntPropAxiom`, `PropositionalAxiom` | NO -- not defined in any PR file |

The Architecture section describes a multi-layer proof system that spans future PRs (2-9 in the
roadmap). The PR description already contains this roadmap information. Including forward
references to non-existent files in a module docstring:

1. Will confuse users trying to navigate the codebase
2. Will produce broken doc-gen links
3. Creates documentation debt that must be maintained across PRs

**Action**: Remove the entire `## Architecture` section from the module docstring. The `## Main
definitions` and `## Notation` sections are sufficient. The PR description body already covers
the architectural roadmap.

## 3. Context Variable Naming: G vs Gamma

**Finding: Inconsistent. Standardize all to Gamma.**

The `Theory.Derivation` inductive on the PR branch uses **two different naming conventions**
for the context parameter:

| Constructor | Variable | Style |
|-------------|----------|-------|
| `ax` | `Γ` (implicit) | Greek (Gamma) |
| `ass` | `Γ` (implicit) | Greek (Gamma) |
| `andI` | `G` (explicit) | ASCII |
| `andE1` | `G` (explicit) | ASCII |
| `andE2` | `G` (explicit) | ASCII |
| `orI1` | `G` (explicit) | ASCII |
| `orI2` | `G` (explicit) | ASCII |
| `orE` | `G` (explicit) | ASCII |
| `impI` | `Γ` (explicit) | Greek (Gamma) |
| `impE` | `Γ` (implicit) | Greek (Gamma) |

The split is clear: the six renamed constructors (andI, andE1, andE2, orI1, orI2, orE) were
changed from implicit `{Γ}` to explicit `(G)`, and the variable was renamed from Gamma to G
in the process. The two unchanged constructors (impI, impE) retained `Γ`.

CSLib CONTRIBUTING.md section on variable names says: "Feel free to use variable names that make
sense in the domain." In logic, `Γ` (Gamma) is the standard notation for proof contexts
([Prawitz1965], [TroelstraVanDalen1988], [Gentzen1935]). The original file by Thomas Waring
used `Γ` consistently. The `impI` and `impE` constructors already use `Γ`.

**Note on downstream impact**: The variable name change from `Γ` to `G` also affects pattern
matches in `weak`, `subs`, `substAtom`, and `cut`. These use `@`-patterns that bind the
explicit context parameter. Changing `G` -> `Γ` in the constructor definitions will require
updating all pattern match sites that reference `G`. Specifically in the diff:

- `weak`: Uses patterns like `@andI _ _ _ A B G D₁ D₂` -- these `G` must become `Γ`
- `subs`: Uses patterns like `@andI _ _ _ A' B' _ E₁ E₂` -- uses `_` for context, no change
- `substAtom`: Uses patterns like `andI _ D₁ D₂` -- uses `_` for context, no change

**Action**: Rename all `G` to `Γ` in the Derivation constructors and all pattern match sites.
This is a mechanical find-and-replace within `NaturalDeduction/Basic.lean`.

## 4. Copyright Header Format

**Finding: Use single year with all authors. Fix the per-author date format.**

Current format on PR branch (in both `Defs.lean` and `NaturalDeduction/Basic.lean`):
```
Copyright (c) 2025 Thomas Waring, 2026 Benjamin Brast-McKie. All rights reserved.
```

Mathlib convention (confirmed across dozens of files): single year + all authors, no per-author
dates:
```
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Copyright (c) 2023 Mario Carneiro, Heather Macbeth. All rights reserved.
```

CSLib convention for multi-author files (confirmed from `Cslib/Logics/Modal/Denotation.lean`):
```
Copyright (c) 2026 Fabrizio Montesi, Benjamin Brast-McKie. All rights reserved.
```

The year in the copyright line indicates file creation, not modification. The `Authors:` line
lists all contributors. For `Defs.lean` and `NaturalDeduction/Basic.lean`, the original creation
year is 2025 (Thomas Waring's initial contribution).

**Action**: Change both files to:
```
Copyright (c) 2025 Thomas Waring, Benjamin Brast-McKie. All rights reserved.
Authors: Thomas Waring, Benjamin Brast-McKie
```

`Connectives.lean` (new file, single author) is already correct:
```
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Authors: Benjamin Brast-McKie
```

## Summary of Changes

| Item | File(s) | Action | Complexity |
|------|---------|--------|------------|
| Remove Aesop import | `Defs.lean` | Delete 1 line | Trivial |
| Remove Architecture section | `Defs.lean` | Delete ~16 lines of docstring | Trivial |
| Standardize G -> Gamma | `NaturalDeduction/Basic.lean` | Rename in ~6 constructors + pattern matches | Mechanical |
| Fix copyright headers | `Defs.lean`, `NaturalDeduction/Basic.lean` | Fix 2 copyright lines | Trivial |

All changes are mechanical. After applying, the implementation agent should:
1. Build with `lake build` to confirm no breakage
2. Run `lake shake --add-public --keep-implied --keep-prefix` to verify import minimality
3. Squash into a single commit and force-push to `feat/propositional-v2`
