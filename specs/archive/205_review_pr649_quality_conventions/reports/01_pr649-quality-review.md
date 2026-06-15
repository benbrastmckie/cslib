# PR #649 Quality and Convention Review

## Overview

PR #649 introduces `Cslib.Logics.Temporal.Syntax.Formula` (311 LOC) and
`Cslib.Foundations.Logic.Connectives` (93 LOC), with refactoring of
`Cslib.Logics.Propositional.Defs` and `Cslib.Logics.Propositional.NaturalDeduction.Basic`.

Baseline modules used for comparison:
- `Cslib.Logics.Modal.Basic` (424 LOC)
- `Cslib.Logics.Propositional.Defs` (pre-PR state)
- `Cslib.Logics.Propositional.NaturalDeduction.Basic` (pre-PR state)
- `Cslib.Foundations.Logic.InferenceSystem`
- `Cslib.Foundations.Logic.Connectives` (introduced by this PR)

---

## 1. Reference Style (Must-Fix)

### Finding: Formula.lean uses plain-text references instead of BibKey format

**PR code** (Formula.lean lines 35-38):
```
- Kamp, H. (1968). *Tense Logic and the Theory of Linear Order*. PhD thesis, UCLA.
- Gabbay, D., Pnueli, A., Shelah, S., and Stavi, J. (1980). On the temporal analysis...
```

**Established baseline** (Connectives.lean, Propositional/Defs.lean, NaturalDeduction/Basic.lean):
```
* [I. Johansson, *Der Minimalkalkül, ein reduzierter intuitionistischer Formalismus*][Johansson1937]
* [D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*][Prawitz1965]
```

**Issues**:
1. Uses `-` prefix instead of `*` prefix for reference list items.
2. Uses plain bibliographic format instead of Mathlib-style `[Author, *Title*][BibKey]` format.
3. The Gabbay et al. (1980) reference is cited but **does not exist in `references.bib`**.
   The Kamp (1968) reference does exist as `@phdthesis{Kamp1968,...}`.

**Recommendation**: Convert to BibKey format and add missing reference to `references.bib`:
```
* [H. Kamp, *Tense Logic and the Theory of Linear Order*][Kamp1968]
* [D. Gabbay, A. Pnueli, S. Shelah, J. Stavi,
  *On the temporal analysis of fairness*][GPSS1980]
```
Add `@inproceedings{GPSS1980,...}` to `references.bib`.

**Severity**: Must-fix. BibKey references are the consistent pattern across all other CSLib
module docstrings. The missing `references.bib` entry means the citation is unverifiable.

---

## 2. Redundant Mathlib Lemma (Must-Fix)

### Finding: `nat_pair_inj` duplicates `Nat.pair_eq_pair`

**PR code** (Formula.lean lines 160-164):
```lean
theorem nat_pair_inj {a b c d : ℕ} (h : Nat.pair a b = Nat.pair c d) :
    a = c ∧ b = d := by
  have := congr_arg Nat.unpair h
  simp only [Nat.unpair_pair] at this
  exact Prod.mk.inj this
```

**Mathlib** (`Mathlib.Data.Nat.Pairing`, available via `Mathlib.Logic.Encodable.Basic` import):
```lean
Nat.pair_eq_pair : Nat.pair a b = Nat.pair c d ↔ a = c ∧ b = d
```

The custom `nat_pair_inj` is exactly `(Nat.pair_eq_pair).mp`. It is transitively available
through the existing `Mathlib.Logic.Encodable.Basic` import -- no new import needed.

**Usage sites** (all in `encodeNat_injective`): Every call `nat_pair_inj h` should become
`Nat.pair_eq_pair.mp h`.

**Severity**: Must-fix. CSLib follows a reuse-first philosophy; re-proving existing Mathlib
lemmas violates this principle and creates maintenance burden.

---

## 3. Module Docstring Structure (Should-Fix)

### Finding: Formula.lean lacks standard docstring sections

**Baseline pattern** (Propositional/Defs.lean, NaturalDeduction/Basic.lean):
```
/-! # Module Title

## Main definitions
- `TypeName` : description
- `Function` : description

## Notation
...

## References
* [Author, *Title*][BibKey]
-/
```

**Formula.lean**:
```
/-! # Temporal Logic Formula

This module defines...

## Derived Temporal Operators
...

## References
...
-/
```

Missing sections:
- `## Main definitions` listing `Formula`, `encodeNat`, `encodeNat_injective`, etc.
- `## Notation` listing `¬ ∧ ∨ → ↔ U S 𝐅 𝐆 𝐏 𝐇`

The "Derived Temporal Operators" subsection is good and domain-appropriate, but should
appear after the standard sections.

**Severity**: Should-fix. The `## Main definitions` section is a standard Mathlib/CSLib
convention that helps reviewers and users navigate the module.

---

## 4. Docstring Conventions (Should-Fix)

### Finding: Constructor docstrings are terse but consistent

**Formula.lean**:
```lean
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Falsum / bottom. -/
  | bot
```

**Modal/Basic.lean**:
```lean
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Falsum / bottom. -/
  | bot
```

These match exactly. Good consistency.

### Finding: Derived connective docstrings are thorough

The `abbrev` docstrings in Formula.lean (e.g., `someFuture`, `allFuture`) provide
multi-line explanations with Burgess convention notes. This exceeds the baseline standard
(Modal/Basic.lean uses single-line docstrings for derived connectives). While not a
violation, consider whether the detailed convention notes belong in the module-level
docstring instead, keeping inline docstrings concise.

**Severity**: Nice-to-have. The detail is informative but creates verbosity that
contrasts with the baseline style.

---

## 5. Proof Quality (Good)

### Tactic usage patterns

The proofs in the PR scope are clean and appropriate:

- **`encodeNat_injective`** (lines 168-216): Uses structural induction with case analysis
  and `by decide` for discriminant elimination. Well-structured, each case is clear.
- **`beq_refl`** (lines 257-263): Clean induction with `rw` and `rfl`.
- **`eq_of_beq`** (lines 266-299): Uses `match` for pattern matching and `simp only`
  for boolean conjunction decomposition.
- **Instance proofs** (lines 221-232): Appropriately concise.

### Proof style consistency

The proofs follow the baseline patterns:
- Term-mode for simple proofs (e.g., `atom_injective`)
- Tactic-mode with `by` for complex proofs (e.g., `encodeNat_injective`)
- Appropriate use of `simp only` rather than bare `simp` where possible

**No issues identified with proof quality.**

---

## 6. Naming Conventions (Good)

### Theorem names

| PR Name | Pattern | Match? |
|---------|---------|--------|
| `Formula.atom_injective` | `Type.field_property` | Yes |
| `Formula.encodeNat` | `Type.actionVerb` | Yes |
| `Formula.encodeNat_injective` | `Type.function_property` | Yes |
| `Formula.beq_refl` | `Type.beq_property` | Yes |
| `Formula.eq_of_beq` | `Type.property_of_property` | Yes (Mathlib convention) |
| `Formula.beq_imp_eq` | `Type.beq_constructor_eq` | Yes |

All theorem names follow established Lean 4 / Mathlib naming conventions.

### Variable naming

- `φ₁`, `φ₂` for binary constructor arguments: matches Modal/Basic.lean
- `φ`, `ψ` for theorem variables: matches baseline
- `Atom` for the type parameter: matches baseline (`Atom` not `α`)

**No issues identified with naming conventions.**

---

## 7. Import Organization (Minor Issue)

### Finding: Inconsistent `public import` vs `import` for Cslib.Init

**Formula.lean**: `public import Cslib.Init`
**Connectives.lean** (this PR): `import Cslib.Init`
**Propositional/Defs.lean** (this PR modified): `import Cslib.Init`

The codebase is already inconsistent on this point (Modal/Basic.lean uses `public import`,
others use `import`). Within the PR itself there is inconsistency: Formula.lean uses
`public import` while Connectives.lean uses plain `import`.

**Severity**: Nice-to-have. Both patterns exist in the codebase. Upstream reviewers
may have a preference, but this is not a hard violation.

---

## 8. Section Organization (Good)

### Two `@[expose] public section` blocks

Formula.lean uses two `@[expose] public section` blocks (lines 41 and 121), closing
and reopening the same `Cslib.Logic.Temporal` namespace. The baselines use a single
block each.

This pattern is structurally motivated: the first section contains the core formula type
and basic instances, while the second contains structural properties (countability, BEq
laws). The section break creates a clean boundary between "core type" and "properties."

**Not a violation**, but reviewers should be aware this is unusual in the codebase.

---

## 9. Notation Conventions (Good)

### Notation registration

```lean
@[inherit_doc] scoped prefix:40 "¬" => Formula.neg
@[inherit_doc] scoped infix:36 " ∧ " => Formula.and
@[inherit_doc] scoped infix:35 " ∨ " => Formula.or
@[inherit_doc] scoped infix:30 " → " => Formula.imp
@[inherit_doc] scoped infix:30 " ↔ " => Formula.iff
```

This exactly matches the established pattern in Modal/Basic.lean:
```lean
@[inherit_doc] scoped prefix:40 "¬" => Proposition.neg
@[inherit_doc] scoped infix:36 " ∧ " => Proposition.and
@[inherit_doc] scoped infix:35 " ∨ " => Proposition.or
@[inherit_doc] scoped infix:30 " → " => Proposition.imp
```

Temporal-specific notations (`U`, `S`, `𝐅`, `𝐆`, `𝐏`, `𝐇`) are appropriately scoped
and use `@[inherit_doc]`.

**No issues identified.**

---

## 10. Typeclass Instance Pattern (Good)

### Connectives registration

```lean
/-- Register `Temporal.Formula` as an instance of `TemporalConnectives`. -/
instance : TemporalConnectives (Formula Atom) where
  bot := .bot
  imp := .imp
  untl := .untl
  snce := .snce
```

Matches the baseline pattern from Propositional/Defs.lean:
```lean
/-- Register `Proposition` as an instance of `PropositionalConnectives`. -/
instance : PropositionalConnectives (Proposition Atom) where
  bot := .bot
  imp := .imp
```

Both include a docstring explaining the registration. Good consistency.

---

## 11. Propositional Refactoring Quality (Good)

The PR's changes to `Propositional/Defs.lean` and `NaturalDeduction/Basic.lean` are
well-executed:

- Renamed `impl` to `imp` for consistency across all formula types
- Renamed `andE₁`/`andE₂` to `andE1`/`andE2`, `orI₁`/`orI₂` to `orI1`/`orI2`
  (removes subscript characters -- a pragmatic improvement)
- Made `Γ` explicit in rule constructors for better pattern matching
- Added `Bot` as a native constructor (removing `[Bot Atom]` typeclass dependency)
- Added BibKey references where previously informal citations existed
- Added `## Architecture` section documenting the two-layer proof system design

These are all improvements that increase consistency across the codebase.

---

## Summary Table

| Category | Finding | Severity |
|----------|---------|----------|
| Reference style | Plain-text format instead of BibKey `[Author][Key]` | **Must-fix** |
| Missing bib entry | Gabbay et al. (1980) not in `references.bib` | **Must-fix** |
| Redundant lemma | `nat_pair_inj` duplicates `Nat.pair_eq_pair` | **Must-fix** |
| Module docstring | Missing `## Main definitions` and `## Notation` sections | Should-fix |
| Derived abbrev docs | Verbose compared to baseline (convention notes inline) | Nice-to-have |
| Import consistency | `public import` vs `import` for `Cslib.Init` | Nice-to-have |
| Proof quality | Clean, well-structured, no issues | Pass |
| Naming conventions | Consistent with Lean 4 / Mathlib standards | Pass |
| Notation conventions | Matches Modal/Basic.lean pattern exactly | Pass |
| Typeclass instances | Follows established docstring + registration pattern | Pass |
| Propositional refactoring | High quality, improves codebase consistency | Pass |

---

## Recommendations for Upstream Review

1. **Before submitting**: Fix the three must-fix items (reference format, missing bib entry,
   redundant lemma).
2. **During review**: Highlight that the propositional refactoring (`impl` -> `imp`,
   explicit `Γ`, native `bot`) is a breaking change for downstream code that references
   the old constructor names.
3. **Post-merge**: Consider a follow-up PR to add `## Main definitions` sections to
   Formula.lean and other modules that lack them.
