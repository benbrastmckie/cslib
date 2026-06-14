# Teammate B Findings: Proof Quality, Naming Conventions, and Notation

## Summary

Comprehensive audit of proof style, naming conventions, notation consistency,
and code quality across `Cslib/Logics/Propositional/` and
`Cslib/Foundations/Logic/`. Zero sorries or admits found across the entire
scope. Overall quality is high with consistent patterns. The findings below
identify specific areas for improvement.

---

## 1. Proof Style and Tactic Usage

### 1.1 Completeness.lean: Truth Lemma Proof is Monolithic

**File**: `Cslib/Logics/Propositional/Metalogic/Completeness.lean`
**Lines**: 69-310 (241 lines)
**Priority**: HIGH

The `prop_truth_lemma` theorem is a single 241-line proof by structural
recursion. Each case (atom, bot, and, or, imp) contains substantial
derivation-tree construction via explicit `.modus_ponens`, `.weakening`,
`.ax`, and `.assumption` calls. The implication case alone (lines 198-309)
is 111 lines.

**Issues**:
- The proof is difficult to read and maintain as a single block.
- Each case repeats a common pattern: build a derivation tree via explicit
  constructors, then feed it to `prop_closed_under_derivation`.
- The `show (propDerivationSystem PropositionalAxiom).Deriv _ _` / `unfold`
  pattern appears 8 times, always followed by similar derivation-tree
  assembly.

**Recommendation**: Extract helper lemmas for each connective case:
```
prop_truth_lemma_and_forward
prop_truth_lemma_and_backward
prop_truth_lemma_or_forward
prop_truth_lemma_or_backward
prop_truth_lemma_imp_forward
prop_truth_lemma_imp_backward
```
This matches Mathlib's convention of decomposing large structural proofs.

### 1.2 StrongCompleteness.lean: Duplicated DNE Argument

**File**: `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean`
**Lines**: 89-169 (80 lines)
**Priority**: MEDIUM

The theorem `prop_not_SetDerivable_union_neg_consistent` has two branches
(lines 97-133 and 134-169) that both perform essentially the same
double-negation elimination argument. The `by_cases h_neg_in_L` split
produces nearly identical chains of `d_efq`, `d_k`, `d_step2`, `d_s2`,
`d_step3`, `d_neg_to_phi`, `d_peirce`, `d_phi`.

**Recommendation**: Extract a shared lemma that performs the DNE argument
given `L' ⊢ neg phi -> bot`, producing `L' ⊢ phi`. This would halve the
proof body.

### 1.3 Combinators.lean: `app2` (Vireo) Proof is 130+ Lines

**File**: `Cslib/Foundations/Logic/Theorems/Combinators.lean`
**Lines**: 140-271 (131 lines)
**Priority**: MEDIUM

The `app2` (double application / Vireo combinator) proof is extremely long,
using 5 multi-line "stages" of K/S manipulation. While the proof is
correct, it is the longest single proof in the Foundations module.

**Recommendation**: Consider whether term-mode combinators could shorten
this. At minimum, add a brief summary of the proof strategy in a comment
block above each stage (stages 3-5 have no explanatory comments).

### 1.4 Connectives.lean: De Morgan Proofs with Deeply Nested Types

**File**: `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean`
**Lines**: 292-407 (116 lines for `demorgan_conj_neg_backward`)
**Priority**: LOW

The De Morgan proofs use raw `HasImp.imp`/`HasBot.bot` encoding for
conjunction (`(phi -> (psi -> bot)) -> bot`) and disjunction
(`(phi -> bot) -> psi`). This is intentional (Lukasiewicz encoding for
generality), but the deeply nested `HasImp.imp` expressions become
difficult to read. Lines 323-354 contain a single B-combinator
instantiation spanning 30+ lines.

**Recommendation**: Add local abbreviations or notations within the proof
to improve readability, e.g.:
```lean
local notation "neg" φ => HasImp.imp φ HasBot.bot
local notation φ "and'" ψ => HasImp.imp (HasImp.imp φ (HasImp.imp ψ HasBot.bot)) HasBot.bot
```

### 1.5 Soundness.lean: Clean and Well-Structured

**File**: `Cslib/Logics/Propositional/Metalogic/Soundness.lean`
**Lines**: 1-93
**Priority**: N/A (positive)

The soundness proof is exemplary: `prop_axiom_sound` uses tactic-mode
`cases h_ax with` cleanly, and `prop_soundness` uses `match` on the
derivation tree. Only `peirce` requires classical reasoning (`by_contra`),
which is the minimal classical usage necessary. No improvements needed.

### 1.6 Bare `simp` Usage

**Priority**: LOW

Only 3 instances of bare `simp` (without explicit lemma lists) found, all
in `Foundations/Logic/Metalogic/Consistency.lean` (lines 91, 112, 251).
These are all trivial `simp at hx` or `simp at h` calls on list membership.

**Recommendation**: Convert to `simp only [List.mem_nil_iff]` or
`exact absurd hx (List.not_mem_nil _)` for clarity, though this is low
priority since the usage is unambiguous.

### 1.7 Classical Reasoning Usage

**Priority**: N/A (informational)

Classical reasoning is used appropriately throughout:
- `attribute [local instance] Classical.propDecidable` appears in
  `DeductionTheorem.lean` (line 49), `StrongCompleteness.lean` (line 55),
  `MinLindenbaum.lean` (line 43), `IntLindenbaum.lean` (line 31).
- `by_contra` / `by_cases` are used in metatheoretic proofs where classical
  meta-reasoning is standard (Lindenbaum's lemma, completeness arguments).
- No unnecessary classical reasoning found in proofs that could be
  constructive.

---

## 2. Naming Conventions

### 2.1 Inconsistent `soundness_tautology` Name

**File**: `Cslib/Logics/Propositional/Metalogic/Soundness.lean`
**Line**: 89
**Priority**: MEDIUM

```lean
theorem soundness_tautology
```

This breaks the naming pattern of sibling theorems:
- `prop_axiom_sound` (has `prop_` prefix)
- `prop_soundness` (has `prop_` prefix)
- `prop_soundness_derivable` (has `prop_` prefix)
- `soundness_tautology` (MISSING `prop_` prefix)

**Recommendation**: Rename to `prop_soundness_tautology` for consistency.

### 2.2 `completeness_iff_tautology` Missing Prefix

**File**: `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean`
**Line**: 248
**Priority**: MEDIUM

```lean
theorem completeness_iff_tautology
```

Same pattern break as above. All other theorems in this file use the
`prop_` prefix: `prop_strong_soundness`, `prop_strong_completeness`,
`prop_strong_completeness_iff`, `prop_compactness`, `prop_completeness`.

**Recommendation**: Rename to `prop_completeness_iff_tautology`.

### 2.3 Private Definition Name Collision Workaround

**File**: `Cslib/Logics/Propositional/Metalogic/Completeness.lean` (lines 43-52)
**File**: `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` (lines 59-67)
**Priority**: LOW

Two files define identical private helpers for the same purpose:
```lean
-- Completeness.lean
private def h_implyK
private def h_implyS

-- StrongCompleteness.lean
private def sc_h_implyK
private def sc_h_implyS
```

The `sc_` prefix in StrongCompleteness is a workaround for the name
collision. Both files provide the same definitions:
`fun phi psi => .implyK phi psi` and `fun phi psi chi => .implyS phi psi chi`.

**Recommendation**: Move these helpers to a shared location (e.g., the
`Axioms.lean` file) as non-private definitions, or use a section variable
pattern to avoid the repetition entirely.

### 2.4 `lem` Name is Misleading

**File**: `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean`
**Line**: 63
**Priority**: LOW

```lean
theorem lem {phi : F} -- In Minimal section
```

This theorem is marked as "Law of Excluded Middle" but the docstring reveals
it is actually `(phi -> bot) -> (phi -> bot)`, i.e., the identity on
`neg phi`. The real LEM (`phi or neg phi`) requires classical logic. The
name `lem` is confusing since this is merely an identity lemma in the
minimal fragment.

**Recommendation**: Rename to `neg_identity` or `identity_neg` and update
the docstring to remove the "Law of Excluded Middle" claim.

### 2.5 Variable Naming is Mostly Conventional

**Priority**: N/A (positive)

Variable naming follows standard logic conventions throughout:
- `phi`, `psi`, `chi` (or `φ`, `ψ`, `χ`) for formulas
- `v` for valuations
- `h` / `h_` prefix for hypotheses
- `d` / `d_` for derivation trees
- `S`, `M`, `Gamma` for sets/contexts
- `Atom` for the atomic type parameter

One minor inconsistency: `DeductionTheorem.lean` uses `A`, `B` for
formulas (line 128: `deductionTheorem ... A B`), while most other files use
`phi`, `psi`. This is acceptable since the deduction theorem follows a
different convention common in proof theory textbooks.

### 2.6 Axiom Subsumption Theorem Names

**File**: `Cslib/Logics/Propositional/ProofSystem/Axioms.lean`
**Lines**: 154, 167
**Priority**: LOW

```lean
theorem MinPropAxiom.toIntProp
theorem IntPropAxiom.toProp
```

The Mathlib convention would be `minPropAxiom_to_intPropAxiom` or
`MinPropAxiom.toIntPropAxiom`. The current `.toIntProp` is not a standard
Lean abbreviation -- it could mean "to intuitionistic proposition" or "to
integer proposition".

**Recommendation**: Rename to `MinPropAxiom.toIntPropAxiom` and
`IntPropAxiom.toPropositionalAxiom` for clarity.

---

## 3. Notation Consistency

### 3.1 Scoped Notations for Proposition Connectives

**File**: `Cslib/Logics/Propositional/Defs.lean`
**Lines**: 102-106
**Priority**: N/A (positive)

```lean
@[inherit_doc] scoped infix:36 " ∧ " => Proposition.and
@[inherit_doc] scoped infix:35 " ∨ " => Proposition.or
@[inherit_doc] scoped infix:30 " → " => Proposition.imp
@[inherit_doc] scoped infix:20 " ↔ " => Proposition.iff
@[inherit_doc] scoped prefix:40 " ¬ " => Proposition.neg
```

All notations are correctly scoped, use standard logic symbols, and have
appropriate precedence levels (negation > conjunction > disjunction >
implication > biconditional). The `@[inherit_doc]` attribute is consistently
applied.

### 3.2 Dual Encoding Issue in Foundations vs Propositional

**Files**: `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` and
`Cslib/Logics/Propositional/ProofSystem/Axioms.lean`
**Priority**: MEDIUM (architectural)

The Foundations theorems use the Lukasiewicz encoding throughout:
```lean
-- Conjunction: (phi -> (psi -> bot)) -> bot
-- Disjunction: (phi -> bot) -> psi
-- Negation: phi -> bot
```

While the Propositional module uses primitive constructors:
```lean
inductive Proposition where
  | and (a b : Proposition Atom)
  | or (a b : Proposition Atom)
```

with the `PropositionalConnectives` instance mapping only `bot` and `imp`:
```lean
instance : PropositionalConnectives (Proposition Atom) where
  bot := .bot
  imp := .imp
```

This means the Foundations theorems about `HasImp.imp phi (HasImp.imp psi HasBot.bot)` (Lukasiewicz and) are
not directly applicable to `Proposition.and phi psi` (primitive and) without
a bridge. The `HasAnd` and `HasOr` instances exist but the Foundations
theorems do not use them.

**Recommendation**: This is a known design tension documented in the
codebase. No immediate action needed, but consider adding bridge lemmas
(e.g., `lce_imp_HasAnd`, `rce_imp_HasAnd`) that connect the Lukasiewicz
theorems to the `HasAnd`/`HasOr` primitives.

### 3.3 ND System Uses `⊢` Notation Correctly

**File**: `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`
**Line**: 87
**Priority**: N/A (positive)

```lean
scoped notation Gamma:60 " ⊢ " A => ((Gamma, A) : Sequent)
```

The turnstile notation is properly scoped and does not conflict with other
notations.

### 3.4 Typeclass-Backed Notation is Consistent

**Priority**: N/A (positive)

All notation in the Propositional module is typeclass-backed:
- `Bot` instance provides `(bot : Proposition Atom)` via Lean's `Bot` class
- `Top` instance provides `(top : Proposition Atom)` via Lean's `Top` class
- Scoped infix notations for `and`, `or`, `imp`, `iff`, `neg`

No unscoped notation found that could conflict with other modules.

---

## 4. Code Quality Indicators

### 4.1 Duplicated Private Axiom Helper Pattern

**Files**: Multiple Metalogic files
**Priority**: MEDIUM

The following pattern is duplicated across 4 files:
```lean
private def h_implyK :
    forall (phi psi : PL.Proposition Atom),
    [AxiomType] (phi.imp (psi.imp phi)) :=
  fun phi psi => .implyK phi psi

private def h_implyS :
    forall (phi psi chi : PL.Proposition Atom),
    [AxiomType] ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi))) :=
  fun phi psi chi => .implyS phi psi chi
```

Occurrences:
- `Completeness.lean` lines 43-52 (h_implyK, h_implyS)
- `StrongCompleteness.lean` lines 59-67 (sc_h_implyK, sc_h_implyS)
- `IntLindenbaum.lean` lines 35-42 (int_h_implyK, int_h_implyS)
- `MinLindenbaum.lean` lines 47-54 (min_h_implyK, min_h_implyS)

**Recommendation**: Define these once per axiom system in the corresponding
`Axioms.lean` or add a utility module.

### 4.2 Instance Boilerplate in IntMinInstances.lean

**File**: `Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean`
**Lines**: 44-167 (123 lines)
**Priority**: LOW

The file contains 25 instance declarations that follow an identical pattern:
```lean
instance :
    HasAxiomFoo Propositional.HilbertBar
      (F := PL.Proposition Atom) where
  foo := (PL.DerivationTree.ax [] _ (.foo _ _))
```

Each is 3-4 lines of pure boilerplate. The classical version in
`Instances.lean` has the same pattern.

**Recommendation**: Consider a macro or `deriving` strategy to reduce the
boilerplate. This is low priority since the repetition does not cause
maintenance burden (instances rarely change).

### 4.3 Missing `@[simp]` Attributes

**Priority**: LOW

The following definitions could benefit from `@[simp]` attributes:

1. `Evaluate` (Semantics/Basic.lean line 38): `Evaluate v (.atom x) = v x`
   and `Evaluate v .bot = False` are natural simp lemmas.

2. `PropSetConsistent` / `PropSetMaximalConsistent` (MCS.lean lines 46-52):
   These are `abbrev`s so they unfold automatically, but explicit `@[simp]`
   lemmas for the membership conditions would help downstream proofs.

3. `IForces` (Kripke.lean line 81): `IForces v bf w (.atom p) = v w p` etc.
   would be useful simp lemmas for Kripke model proofs.

**Note**: Adding `@[simp]` to recursive functions like `Evaluate` and
`IForces` requires care to avoid looping. Consider `@[simp]` only on the
base cases (atom, bot).

### 4.4 No Dead Code Found

**Priority**: N/A (positive)

All private definitions appear to be used in their containing files.
No orphaned definitions or unused type aliases detected.

### 4.5 `@[expose] public section` Pattern

**Priority**: N/A (informational)

Every file in the audit scope uses `@[expose] public section` as its
top-level wrapper. This is a CSLib convention for making all definitions
public by default. The pattern is consistently applied.

### 4.6 Docstring Coverage

**Priority**: LOW

Docstring coverage is very good across the codebase. All major theorems and
definitions have docstrings. Module-level docstrings are comprehensive
with references. Minor gaps:

- `canonicalValuation` (Completeness.lean line 59): Has a docstring.
- `Valuation` (Semantics/Basic.lean line 33): Has a docstring.
- `Evaluate` (Semantics/Basic.lean line 38): Has a docstring.
- All `DerivationTree` constructors: Have docstrings.

No significant docstring gaps found.

### 4.7 Axioms.lean Docstring Count Mismatch

**File**: `Cslib/Logics/Propositional/ProofSystem/Axioms.lean`
**Lines**: 17-18, 34
**Priority**: LOW

The module docstring says "4 axiom schemata" but the actual inductive has
10 constructors (including the 6 and/or axioms added later). The docstring
for `PropositionalAxiom` correctly says "10 axiom constructors" (line 34),
but the module header is stale.

**Recommendation**: Update the module docstring from "4 axiom schemata" to
"10 axiom schemata".

---

## 5. Priority Summary

### HIGH Priority
1. **Completeness.lean truth lemma decomposition** (Section 1.1): 241-line
   monolithic proof should be split into 6 helper lemmas.

### MEDIUM Priority
2. **StrongCompleteness.lean duplicated DNE** (Section 1.2): Extract shared
   DNE helper to eliminate ~40 lines of duplication.
3. **`soundness_tautology` naming** (Section 2.1): Missing `prop_` prefix.
4. **`completeness_iff_tautology` naming** (Section 2.2): Missing `prop_`
   prefix.
5. **Duplicated private axiom helpers** (Section 4.1): 4 files repeat
   identical `h_implyK`/`h_implyS` definitions.
6. **Foundations vs Propositional encoding gap** (Section 3.2): Lukasiewicz
   vs primitive connective bridge lemmas needed.

### LOW Priority
7. **`lem` name misleading** (Section 2.4): Rename to `neg_identity`.
8. **Bare `simp` in Consistency.lean** (Section 1.6): 3 instances.
9. **`app2` proof length** (Section 1.3): 131-line combinator proof.
10. **De Morgan readability** (Section 1.4): Local abbreviations.
11. **Instance boilerplate** (Section 4.2): Repetitive patterns.
12. **Missing `@[simp]` attributes** (Section 4.3): Base cases.
13. **Axiom subsumption names** (Section 2.6): Non-standard abbreviations.
14. **Stale axiom count in docstring** (Section 4.7): "4" should be "10".
