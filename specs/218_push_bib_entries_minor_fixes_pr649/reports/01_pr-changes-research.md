# Task 218: Push Missing Bib Entries and Minor Fixes to PR #649

## Research Summary

PR #649 (`feat/temporal-formula-propositional`) is an open PR targeting `main`. It modifies 6 files: `Cslib.lean`, `Cslib/Foundations/Logic/Connectives.lean`, `Cslib/Logics/Propositional/Defs.lean`, `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`, `Cslib/Logics/Temporal/Syntax/Formula.lean`, and `references.bib`. The PR is stacked on PR #648 (`feat/propositional-v2`).

## Finding 1: Missing Bib Entries

All 7 bib entries exist on `main` but are **absent from the PR branch**. The PR branch's `references.bib` was forked before these entries were added to main. The entries must be restored because the PR branch's own Lean files reference them in docstrings.

### Entries to Restore (all 7 needed)

| BibKey | Type | Already on main | Referenced by (on PR branch) |
|--------|------|-----------------|------------------------------|
| `Church1956` | `@book` | Yes (line 141) | Connectives.lean, Defs.lean |
| `Gentzen1935` | `@article` | Yes (line 195) | Connectives.lean, Defs.lean, Basic.lean |
| `Johansson1937` | `@article` | Yes (line 277) | Connectives.lean, Defs.lean, Basic.lean |
| `McKinsey1939` | `@article` | Yes (line 287) | Connectives.lean |
| `Prawitz1965` | `@book` | Yes (line 400) | Connectives.lean, Defs.lean, Basic.lean |
| `TroelstraVanDalen1988` | `@book` | Yes (line 450) | Connectives.lean, Defs.lean, Basic.lean |
| `Wajsberg1938` | `@article` | Yes (line 299) | Connectives.lean |

### Implementation

Cherry-pick or manually add these 7 entries from main's `references.bib` into the PR branch's `references.bib`, maintaining alphabetical ordering.

### Note on Other Removed Entries

The PR branch also removes 6 additional bib entries. Two of these (`ChagrovZakharyaschev1997` with 36 references, `Heyting1930` with 1 reference) are still referenced by files **not touched by the PR** (Modal/*.lean, Propositional/Metalogic/*.lean, etc.). However, since PR #649 is stacked on PR #648 which presumably handles these, and the task description only lists the 7 entries above, this report focuses on those 7. The other removals (`Bentzen2023`, `Fitting1969`, `Herbrand1930`, `Trufas2024`) have 0 references in the codebase.

**Warning**: `ChagrovZakharyaschev1997` and `Heyting1930` should also be restored if PR #648 doesn't carry them. This is a potential blocker for PR merge — verify before submission.

## Finding 2: Defs.lean Architecture Docstring

The PR branch **removes** the `## Architecture` section from `Defs.lean` (lines 36-53 on main). This section documents the two-layer proof system architecture (Natural Deduction + Hilbert System + Bridge).

The task description says to "include Defs.lean architecture docstring" — this means the Architecture section should be **restored** on the PR branch.

### Content to Restore

```
## Architecture

Two proof systems are defined for this propositional language:

- **Layer 1 — Natural Deduction** (`NaturalDeduction/Basic.lean`): a `Theory.Derivation` inductive
  with 10 primitive constructors (axiom, assumption, conjunction intro/elim ×2, disjunction
  intro ×2/elim, implication intro/elim). The theory parameter controls logic strength: `MPL`
  (Johansson's minimal logic, [Johansson1937]), `IPL` (intuitionistic), and `CPL` (classical).

- **Layer 2 — Hilbert System** (`ProofSystem/`): an axiom predicate hierarchy
  (`MinPropAxiom` / `IntPropAxiom` / `PropositionalAxiom`) with sequent derivability and a
  Hilbert-style proof-theoretic treatment.

- **Bridge**: `NaturalDeduction/Equivalence.lean` establishes extensional equivalence between the
  two proof systems for all three logic strengths, in both closed-context (`hilbert_iff_nd`,
  `hilbert_iff_nd_min`, `hilbert_iff_nd_int`, `hilbert_iff_nd_cl`) and context-based forms
  (`hilbert_iff_nd_ctx`, `hilbert_iff_nd_ctx_min`, `hilbert_iff_nd_ctx_int`,
  `hilbert_iff_nd_ctx_cl`).
```

## Finding 3: NaturalDeduction/Basic.lean Γ→G Rename

The PR branch already contains the Γ→G rename. The diff shows all `G` variable names in the `Derivation` inductive constructors (andI, andE1, andE2, orI1, orI2, orE) being renamed to `Γ` for consistency with `ax`, `ass`, `impI`, and `impE` which already use `Γ`.

The rename also propagates to pattern matches in `weak` (lines 184-188) and `subs` (lines 263-268).

**Status**: Already done on PR branch. No additional work needed.

## Finding 4: Copyright Date Updates

The PR branch changes the copyright header from:
```
Copyright (c) 2025 Thomas Waring, 2026 Benjamin Brast-McKie.
```
to:
```
Copyright (c) 2025 Thomas Waring, Benjamin Brast-McKie.
```

This applies to both `Defs.lean` and `NaturalDeduction/Basic.lean`. The change removes the year 2026 from Benjamin's copyright attribution.

**Status**: Already done on PR branch. No additional work needed.

## Finding 5: Connectives.lean Changes on PR Branch

The PR branch makes several changes to Connectives.lean:
1. **Docstring rewrite**: Module header updated from "four logic levels" to "Propositional and Temporal Logic", removing references to Modal and Bimodal
2. **Removes `HasBox`**: Box modality class and its docstring removed
3. **Removes `ModalConnectives`**: Modal connectives bundled class removed
4. **Removes `BimodalConnectives`**: Bimodal connectives bundled class removed
5. **Removes `Heyting1930` and `ChagrovZakharyaschev1997` references**: From the docstring references section
6. **Updates `PropositionalConnectives` docstring**: Removes task-173 deferral language

These are intentional scope reductions for PR #649 (temporal formula only, no modal content).

## Implementation Plan Recommendations

### Phase 1: Restore 7 Bib Entries on PR Branch

1. Checkout `feat/temporal-formula-propositional`
2. Add the 7 bib entries to `references.bib` in alphabetical position
3. Each entry should match the exact content from main's `references.bib`

### Phase 2: Restore Architecture Docstring in Defs.lean

1. On the PR branch, restore the `## Architecture` section in `Defs.lean`'s module docstring
2. Place it after the `## Main definitions` section, before `## Notation`

### Phase 3: Verify No Additional Changes Needed

1. The Γ→G rename is already complete
2. The copyright date updates are already complete
3. Run `lake build` to verify everything compiles

### Risk: ChagrovZakharyaschev1997 and Heyting1930

These two entries are removed on the PR branch but referenced by files outside the PR's scope. If PR #648 doesn't carry them, they must also be restored. Recommend checking PR #648's references.bib before finalizing.
