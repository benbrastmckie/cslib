# Research Report: PR #633 Syntactic Sugar and Quality Review

- **Task**: 166 - PR #633 syntactic sugar and quality review
- **Date**: 2026-06-12
- **PR**: #633 (branch `pr1/foundations-logic`)
- **PR URL**: https://github.com/leanprover/cslib/pull/633

## Executive Summary

PR #633 adds 3,806 lines across 38 files covering Hilbert proof systems, metalogic
(completeness, soundness, MCS, Lindenbaum), ND equivalence, and Kripke semantics for
propositional logic, plus modifications to Modal and Foundations modules. The branch
diverged from main before task 165 (syntactic sugar refactor), so all Propositional
files use raw constructor calls (`.imp`, `.bot`, `Proposition.neg`, `.and`, `.or`,
`.iff`) where main now uses scoped notation (`->`, `bot`, `neg`, `and`, `or`, `iff`).

The PR's Modal files (`Basic.lean`, `Denotation.lean`, `LogicalEquivalence.lean`) use
a fundamentally different type definition (primitives: `not`, `and`, `diamond`, `impl`)
compared to main's Lukasiewicz convention (primitives: `bot`, `imp`, `box`). Sugar
changes to Modal files are NOT applicable in the same form and should be excluded from
this task, as they will be reconciled when the Lukasiewicz refactor PRs (#635, #637)
land.

## 1. Complete File List

### 1.1 Files in PR #633 Diff (vs main)

| # | File | Status | Sugar Needed | Estimated Replacements |
|---|------|--------|-------------|----------------------|
| 1 | `Cslib.lean` | Modified | No | 0 (module index) |
| 2 | `Cslib/Foundations/Data/HasFresh.lean` | Modified | No | 0 (no notation types) |
| 3 | `Cslib/Foundations/Data/ListHelpers.lean` | Modified | No | 0 |
| 4 | `Cslib/Foundations/Logic/ProofSystem.lean` | Modified | No | 0 (typeclass layer) |
| 5 | `Cslib/Foundations/Logic/Theorems.lean` | Modified | No | 0 (module file) |
| 6 | `Cslib/Foundations/Logic/Theorems/BigConj.lean` | Modified | No | 0 (typeclass layer) |
| 7 | `Cslib/Foundations/Logic/Theorems/Combinators.lean` | Modified | No | 0 (typeclass layer) |
| 8 | `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean` | Modified | No | 0 (typeclass layer) |
| 9 | `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` | Modified | No | 0 (typeclass layer) |
| 10 | `Cslib/Foundations/Logic/Theorems/Temporal/FrameConditions.lean` | Modified | No | 0 |
| 11 | `Cslib/Logics/Modal/Basic.lean` | Modified | **EXCLUDED** | 0 (different primitives) |
| 12 | `Cslib/Logics/Modal/Denotation.lean` | Modified | **EXCLUDED** | 0 (different primitives) |
| 13 | `Cslib/Logics/Modal/LogicalEquivalence.lean` | Added | **EXCLUDED** | 0 (Modal namespace, pattern-match bodies) |
| 14 | `Cslib/Logics/Propositional/Defs.lean` | Modified | **Yes** | 1 (add `iff` notation) |
| 15 | `Cslib/Logics/Propositional/Metalogic/Completeness.lean` | Added | **Yes** | ~10 |
| 16 | `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` | Modified | **Yes** | ~8 |
| 17 | `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` | Added | **Yes** | ~1 |
| 18 | `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` | Added | **Yes** | ~12 |
| 19 | `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean` | Added | No | 0 (clean) |
| 20 | `Cslib/Logics/Propositional/Metalogic/MCS.lean` | Modified | **Yes** | ~7 |
| 21 | `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` | Added | **Yes** | ~2 |
| 22 | `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` | Added | **Yes** | ~7 |
| 23 | `Cslib/Logics/Propositional/Metalogic/MinSoundness.lean` | Added | No | 0 (clean) |
| 24 | `Cslib/Logics/Propositional/Metalogic/Soundness.lean` | Added | No | 0 (clean) |
| 25 | `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | Modified | No | 0 (identical sugar) |
| 26 | `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean` | Added | **Yes** | ~34 |
| 27 | `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` | Added | **Yes** | ~9 (`.iff` -> `iff`) |
| 28 | `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` | Modified | **Yes** | ~8 |
| 29 | `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` | Added | **Yes** | ~39 |
| 30 | `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` | Modified | No | 0 (inductive return types) |
| 31 | `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` | Modified | **Yes** | ~4 |
| 32 | `Cslib/Logics/Propositional/ProofSystem/Instances.lean` | Modified | No | 0 |
| 33 | `Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean` | Added | No | 0 (identical to main) |
| 34 | `Cslib/Logics/Propositional/Semantics/Basic.lean` | Added | No | 0 (same raw count) |
| 35 | `Cslib/Logics/Propositional/Semantics/Kripke.lean` | Added | No | 0 (same raw count) |
| 36 | `CslibTests/HasFresh.lean` | Modified | No | 0 |
| 37 | `.github/CODEOWNERS` | Modified | No | 0 |
| 38 | `references.bib` | Modified | No | 0 |

**Total files needing sugar changes: 14** (13 Propositional files + 1 Defs notation addition)

### 1.2 Estimated Total Replacements: ~141

## 2. Applicable Replacements Per File

### 2.1 Replacement Rules

From task 165, the following replacements apply in the PL (Propositional Logic) namespace:

| Raw Form | Notation | Constraint |
|----------|----------|------------|
| `φ.imp ψ` / `Proposition.imp φ ψ` | `φ -> ψ` | NOT in Pi-type binder (`forall ... Axioms (phi.imp ...)`) |
| `.bot` / `Proposition.bot` | `bot` | NOT in Pi-type binder |
| `Proposition.neg φ` / `φ.neg` | `neg phi` | Safe everywhere (prefix) |
| `φ.and ψ` / `Proposition.and φ ψ` | `phi and psi` | Safe in expression position |
| `φ.or ψ` / `Proposition.or φ ψ` | `phi or psi` | Safe in expression position |
| `φ.iff ψ` / `Proposition.iff φ ψ` | `phi iff psi` | Requires adding `iff` notation first |

(Unicode symbols used in actual code: `→ ⊥ ¬ ∧ ∨ ↔`)

### 2.2 Constraint: Pi-Type Binder

Lines of the form:
```lean
(h_implyK : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
```
MUST keep `.imp` because `→` would be parsed as the function type arrow in Pi-type context.

Similarly for:
```lean
(h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
```
where `.imp` must stay.

**Affected files**: `HilbertDerivedRules.lean` (~50 lines), `Completeness.lean` (~4 lines).

### 2.3 Constraint: `change` Tactic

The `change` tactic parses `→` as function arrow. Example:
```lean
change Satisfies m w (φ → ψ)  -- FAILS
change Satisfies m w (φ.imp ψ) -- works
```
No `change` tactics with `.imp` were found in the Propositional files on this PR branch.

### 2.4 Constraint: Pattern-Match Arms

Pattern-match arms (`| .imp φ ψ =>`, `| .bot =>`) must keep raw constructors.
These are NOT counted as replaceable occurrences.

### 2.5 Constraint: Inductive Constructor Return Types

Axiom definitions in `Axioms.lean`, `Instances.lean`, `IntMinInstances.lean` use
raw constructors in inductive return types:
```lean
| implyK (φ ψ) : PropositionalAxiom (φ.imp (ψ.imp φ))
```
These MUST stay as-is (Lean parses `→` as Pi-type in this position).

### 2.6 Per-File Replacement Detail

**Defs.lean**: Add one line after line 85 (after `¬` notation):
```lean
@[inherit_doc] scoped infix:20 " ↔ " => Proposition.iff
```

**Completeness.lean** (~10 replacements):
- `Proposition.neg φ` -> `¬φ` (8 occurrences)
- `Proposition.bot` -> `⊥` (in expression positions, ~2-3 occurrences)
- `.imp` in non-Pi positions: `h_mcs (φ.imp ψ)` -> `h_mcs (φ → ψ)` (~2)
- Keep: `φ.imp (ψ.imp φ)` in `h_implyK` and `h_implyS` Pi-type binders
- Keep: all `.imp`/`.bot` in proof body where inside `DerivationTree` calls (these are list elements and constructor arguments that may need explicit type)

**DeductionTheorem.lean** (~8 replacements):
- `A.imp φ` -> `A → φ` in non-Pi positions
- `φ.imp ψ` -> `φ → ψ` in return types and hypotheses

**IntLindenbaum.lean** (~12 replacements):
- `Proposition.neg φ` -> `¬φ`
- `Proposition.bot` -> `⊥`
- `φ.imp ψ` -> `φ → ψ` (in set membership and `have` annotations)
- Keep: Pi-type binder contexts

**MCS.lean** (~7 replacements):
- `Proposition.imp φ ψ` -> `φ → ψ`
- `Proposition.neg φ` -> `¬φ`
- `Proposition.bot` -> `⊥`

**MinLindenbaum.lean** (~7 replacements): Same pattern as IntLindenbaum.

**MinCompleteness.lean** (~2 replacements):
- `Proposition.neg φ` -> `¬φ`
- `Proposition.bot` -> `⊥`

**IntCompleteness.lean** (~1 replacement):
- `Proposition.neg φ` -> `¬φ`

**Derivation.lean** (~4 replacements):
- `φ.imp ψ` -> `φ → ψ` in parameter annotations

**FromHilbert.lean** (~8 replacements):
- `A.imp B` -> `A → B`
- `Proposition.bot` -> `⊥`

**DerivedRules.lean** (~34 replacements):
- `Proposition.neg A` -> `¬A` (~15 occurrences)
- `A.and B` -> `A ∧ B` (~3)
- `Proposition.neg (Proposition.neg A)` -> `¬¬A` (~1)
- `A.or B` -> `A ∨ B` (~2)
- `A.iff B` -> `A ↔ B` (~6, after notation added)
- Various `.imp` in non-Pi positions
- Comments: update "neg" to "¬" in proof comments

**HilbertDerivedRules.lean** (~39 replacements):
- `Proposition.neg A` -> `¬A` (~7 non-Pi occurrences)
- `Proposition.bot` -> `⊥` (~5 non-Pi occurrences)
- `A.iff B` -> `A ↔ B` (~6, after notation added)
- Various `.imp` in non-Pi positions
- Keep: ALL Pi-type binder lines (~50+ lines with `∀ ... Axioms (φ.imp ...)`)
- This file has the highest raw constructor count but most are in constrained positions

**Equivalence.lean** (~9 replacements):
- `.iff` -> `↔` (~3)
- `Proposition.neg` -> `¬` (~2)
- `.imp` in non-Pi positions (~4)

## 3. Files Already Sugar-Applied (Delta Analysis)

Task 165 applied sugar to these files that overlap with PR #633:

| File | Task 165 Phase | Main Raw Count | PR Raw Count | Delta |
|------|---------------|----------------|--------------|-------|
| Completeness.lean | Phase 4 | 40 | 47 | +7 |
| IntLindenbaum.lean | Phase 4 | 21 | 33 | +12 |
| MinCompleteness.lean | Phase 4 | 2 | 4 | +2 |
| MinLindenbaum.lean | Phase 4 | 12 | 19 | +7 |
| Modal/Basic.lean | Phase 5 | 31 | 15 | -16 (different types!) |
| Modal/LogicalEquivalence.lean | Phase 5 | 2 | 4 | +2 |
| DerivedRules.lean | Phase 7 | 76 | 110 | +34 |
| HilbertDerivedRules.lean | Phase 7 | 87 | 126 | +39 |
| DeductionTheorem.lean | Phase 7 | 13 | 21 | +8 |
| MCS.lean | Phase 7 | 14 | 21 | +7 |
| FromHilbert.lean | Phase 7 | 16 | 24 | +8 |
| Derivation.lean | Phase 7 | 0 | 4 | +4 |
| Defs.lean | Phase 1 | 19 | 18 | -1 (notation added on main) |

**Note on raw count methodology**: The counts include ALL `.imp`/`.bot`/`.neg`/`.and`/`.or`/`.iff`
substrings, including those in constrained positions (Pi-type binders, pattern arms, inductive
return types). Actual replaceable occurrences are lower.

## 4. Review Comment Analysis

### Comment r3403944952 (xcthulhu)

**Location**: `Cslib/Logics/Propositional/Metalogic/Completeness.lean`, lines 42-45

**Comment**: "I think you can use the syntactic sugar for this defined here:
https://github.com/leanprover/cslib/blob/1f601a245d0b16c68c36c86ea2f7f133dc75ea0b/Cslib/Logics/Propositional/Defs.lean#L70-L73"

**Referenced Code** (PR branch lines 42-47):
```lean
/-! ## Axiom hypotheses for PropositionalAxiom -/

private def h_implyK :
    ∀ (φ ψ : PL.Proposition Atom),
    PropositionalAxiom (φ.imp (ψ.imp φ)) :=
  fun φ ψ => .implyK φ ψ
```

**Analysis**: The reviewer is correct that syntactic sugar should be used where possible.
However, **this specific line** (line 46: `φ.imp (ψ.imp φ)`) is inside a `∀`-quantified
type signature, where `→` would be parsed as the function type arrow (Pi type), not
`Proposition.imp`. This is the Pi-type binder constraint discovered during task 165.

**Proposed Fix**:
1. Apply syntactic sugar EVERYWHERE ELSE in the file (addressing the spirit of the review)
2. Add a brief comment explaining why `h_implyK`/`h_implyS` keep raw constructors:
   ```lean
   -- NB: `.imp` is needed here because `→` is parsed as function arrow inside `∀`
   ```
3. Respond to the review comment explaining the Pi-type constraint and noting that sugar
   has been applied throughout the rest of the file

**Alternative**: Restructure `h_implyK` to avoid the `∀` and allow notation. However,
this would be a more invasive change and the Pi-type constraint affects many more
definitions across the Hilbert proof system. Main also keeps `.imp` in these positions.

## 5. Quality Issues Found

### 5.1 Missing PL Biconditional Notation

The PR branch's `Defs.lean` is missing the `↔` scoped notation that task 165 added:
```lean
@[inherit_doc] scoped infix:20 " ↔ " => Proposition.iff
```
This should be added as a prerequisite, enabling `↔` replacement in DerivedRules.lean,
HilbertDerivedRules.lean, and Equivalence.lean (~12 replacements total).

### 5.2 Modal File Structural Divergence

The PR's Modal files use older primitives (`not`, `and`, `diamond`, `impl`) while main
uses Lukasiewicz (`bot`, `imp`, `box`). This is a known divergence -- PRs #635 and #637
handle the Modal refactor. **No sugar changes should be applied to Modal files in this
task.** The modal files should be handled separately after the Lukasiewicz PRs land.

### 5.3 Comment Style

Several proof comments use raw constructor names instead of notation:
- `-- h : neg (φ.imp ψ) ∈ S` should be `-- h : ¬(φ → ψ) ∈ S`
- `-- Derive neg ψ ∈ S` should be `-- Derive ¬ψ ∈ S`
- `-- A.or B = (A.imp bot).imp B` should be `-- A ∨ B = (¬A) → B`

These should be updated alongside the code sugar changes for consistency.

### 5.4 Reference Format

The PR's Completeness.lean uses the full Mathlib-style `[Author, *Title*][BibKey]`
reference format:
```
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997],
```
Main's version uses the abbreviated `CZ` form. The PR's format is actually the
**correct** Mathlib convention and should be kept.

### 5.5 Pre-existing TODO

`NaturalDeduction/Basic.lean` line 221 has a TODO about capture-avoiding substitution.
This exists on main as well and is not introduced by the PR. No action needed.

### 5.6 Documentation Coverage

All public definitions in the PR files have doc comments. Documentation quality is good.

### 5.7 No `sorry` Occurrences

No `sorry` found in any PR file. All proofs are complete.

## 6. Recommended Approach

### Cherry-Pick vs Manual Reapply

**Recommendation: Manual reapply** (NOT cherry-pick).

Cherry-pick of task 165 phases 4/5/7 is not feasible because:
1. The PR branch has fundamentally different Modal file structure (different primitives)
2. Multiple files exist on both branches with different content
3. Task 165 commits include non-overlapping files that would create merge conflicts
4. Task 165 phases touch `specs/` plan files that shouldn't be on the PR branch

### Implementation Order

1. **Phase A: Add `↔` notation to Defs.lean** (prerequisite)
   - Add `@[inherit_doc] scoped infix:20 " ↔ " => Proposition.iff` after the `¬` notation
   - Build to verify

2. **Phase B: Apply sugar to ProofSystem files** (low risk, 4 files)
   - `Derivation.lean`: 4 replacements
   - `Axioms.lean`: 0 (all in constrained positions)
   - `Instances.lean`: 0
   - `IntMinInstances.lean`: 0

3. **Phase C: Apply sugar to Metalogic files** (medium risk, 8 files)
   - `MCS.lean`: 7 replacements
   - `DeductionTheorem.lean`: 8 replacements
   - `Completeness.lean`: 10 replacements + Pi-type comment
   - `IntLindenbaum.lean`: 12 replacements
   - `MinLindenbaum.lean`: 7 replacements
   - `IntCompleteness.lean`: 1 replacement
   - `MinCompleteness.lean`: 2 replacements
   - `Soundness.lean`, `IntSoundness.lean`, `MinSoundness.lean`: 0 each

4. **Phase D: Apply sugar to NaturalDeduction files** (higher effort, 4 files)
   - `DerivedRules.lean`: 34 replacements
   - `HilbertDerivedRules.lean`: 39 replacements (many Pi-type exempt)
   - `FromHilbert.lean`: 8 replacements
   - `Equivalence.lean`: 9 replacements

5. **Phase E: Address review comment** (respond on GitHub)

6. **Phase F: CI verification**
   - `lake build`
   - `lake test`
   - `lake exe checkInitImports`
   - `lake exe lint-style`

### Scope Exclusions

- **All Foundations/ files**: Typeclass layer, notation not applicable
- **All Modal/ files**: Different primitive set, handled by PRs #635/#637
- **`Cslib.lean`**: Module index only
- **`CslibTests/HasFresh.lean`**: Test file, no notation types
- **`.github/CODEOWNERS`**: Not code
- **`references.bib`**: Not code

## 7. Risk Assessment

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `→` parsed as function arrow in overlooked Pi-type context | H | M | Build after each file; compare with main's version for reference |
| `⊥` notation not resolving in some contexts | M | L | Verify `Bot` instance is in scope via imports |
| `↔` notation not available in files that don't import Defs | M | L | All Propositional files import Defs transitively |
| PR merge conflicts with ongoing main changes | M | M | Work on PR branch directly; push promptly |
| Modal file sugar attempted incorrectly | H | L | Explicitly excluded from scope |
