# Teammate C Findings: Gaps, Shortcomings, and Blind Spots

**Task**: PR readiness review of `Logics/Propositional/` — deduction theorem, strong
soundness/completeness, and `noncomputable` usage.

---

## Key Findings

### 1. `noncomputable` Usage: Legitimate, Not a Design Flaw

The `noncomputable` occurrences fall into two structurally coherent groups:

**Group A — Deduction theorem constructions (Type-level `def`s):**
- `DeductionTheorem.lean`: `deductionWithMem`, `deductionTheorem` (Type-level, needed for
  height-based well-founded recursion), `noncomputable instance : HasHilbertTree`
- `NaturalDeduction/FromHilbert.lean`: `impI`, `hilbertCut` (wrappers around
  `deductionTheorem`)
- `NaturalDeduction/HilbertDerivedRules.lean`: `hilbertNegI`, `hilbertOrE` (indirect via
  `impI`)
- `NaturalDeduction/Equivalence.lean`: `ndToHilbert` (uses `deductionTheorem`)

**Group B — Helper derivation trees in metalogic files:**
- `IntLindenbaum.lean`: `intNegPhiImpPsi`, `lift_int_to_cl` (private)
- `MinLindenbaum.lean`: `liftMinToCl`
- `StrongCompleteness.lean`: `dne_from_neg_neg` (private)

**Root cause of Group A noncomputability**: `deductionWithMem` and `deductionTheorem` are
`def` (not `theorem`) because they produce `Type`-valued derivation trees, not `Prop`-valued
proofs. They use `by_cases` in tactic blocks (which requires `Classical.propDecidable`). The
`attribute [local instance] Classical.propDecidable` is applied in both files. This is the
standard CSLib/Mathlib pattern for metalogic constructions that must be `Type`-level for
pattern matching but need classical reasoning in the proof steps.

**Is noncomputable downstream computable code?** No. All downstream consumers wrap
derivation trees in `Nonempty` (`Deriv` and `Derivable` are Prop-level wrappers). The
semantic definitions (`Evaluate`, `IForces`, `IValid`, `MValid`, `SemanticEntails`) are all
fully computable definitions over Lean's native `Prop`. The instances in `Instances.lean`
and `IntMinInstances.lean` use the `DerivationTree` constructors directly (computable), not
the noncomputable deduction theorem functions.

**Would a Mathlib reviewer reject this?** No. The pattern (noncomputable Type-valued
function that constructs proof trees, wrapped in Nonempty for Prop-level use) is standard in
Mathlib for proof relevance separation. The local scoping of `Classical.propDecidable` via
`attribute [local instance]` is also correct practice.

**However, there is a legitimate design observation**: `deductionTheorem` and
`deductionWithMem` are `noncomputable def` but their noncomputability only arises from the
`by_cases` in tactic proofs. If rewritten in term mode using decidability of list membership
(Atom already has `DecidableEq`), they could potentially be made computable. This is a
low-priority refactor but worth noting for a perfectionist reviewer.

### 2. Asymmetric Handling: `HasHilbertTree` Instance Scope Issue

`DeductionTheorem.lean` declares `noncomputable instance : HasHilbertTree (PL.Proposition
Atom)` fixed to `PropositionalAxiom`. This is a **global unscoped instance** that will be
visible everywhere `DeductionTheorem.lean` is imported. This creates a potential issue: the
instance is hardcoded to `PropositionalAxiom` (classical), but the file contains parameterized
machinery for any axiom predicate. Any downstream code that imports `DeductionTheorem` will
find this global instance, potentially causing confusion if someone tries to use a different
axiom set with `HasHilbertTree`.

The comment says "fixed at PropositionalAxiom for backward compatibility" but this is
philosophically inconsistent with the parameterized design of the rest of the module. A
reviewer might ask: why is there a global `HasHilbertTree` instance when the deduction
theorem is fully parameterized? The instance appears to exist solely for the
`prop_has_deduction_theorem` proof, which uses it via a local `letI` anyway.

**Recommendation for reviewer to flag**: Should `noncomputable instance : HasHilbertTree`
be made local (using `local instance`) or removed, with callers using the `letI` pattern
directly?

### 3. ONE Existing TODO Tag Indicating Known Technical Debt

In `NaturalDeduction/Basic.lean` at line 251:
```
/-- Substitution of a family of derivations `D` for hypotheses in the context `Γ` of `E`. TODO:
this implementation is not capture avoiding. -/
def Theory.Derivation.subs
```

This is a documented known issue: the substitution is NOT capture avoiding. For a PR
reviewer, this raises the question: does any downstream code in this PR rely on `subs` in a
context where capture avoidance would matter? A careful reviewer would check whether any
of the completeness proofs use `subs`. Scanning the files: the completeness proofs use
`hilbertSubstitution` (from `FromHilbert.lean`), NOT `Theory.Derivation.subs`. So this
TODO does not affect correctness of the submitted results, but it is an existing gap the PR
should acknowledge.

### 4. `private` Helpers Without Corresponding Tests

Four helpers are marked `private`:
- `private noncomputable def dne_from_neg_neg` (StrongCompleteness.lean)
- `private noncomputable def lift_int_to_cl` (IntLindenbaum.lean)

Making them private is correct practice, but it means no external tests can verify their
behavior directly. The correctness argument is entirely via the public theorems that use them.
This is acceptable but worth noting: if `dne_from_neg_neg` or `lift_int_to_cl` have subtle
bugs, they would only manifest through incorrect public theorems.

### 5. Missing `@[simp]` Lemmas That Could Exist

The files define several key equivalences but none are tagged `@[simp]`:
- `prop_completeness_iff_tautology`: `Tautology φ ↔ Derivable PropositionalAxiom φ`
- `int_soundness_completeness`: `IValid φ ↔ Derivable IntPropAxiom φ`
- `min_soundness_completeness`: `MValid φ ↔ Derivable MinPropAxiom φ`
- `prop_strong_completeness_iff`, `int_strong_completeness_iff`,
  `min_strong_completeness_iff`

These biconditionals are exactly the kind of lemmas that downstream proofs would want to
`simp` with. Their absence as `@[simp]` lemmas is a gap. A Mathlib-style reviewer would ask
why these fundamental equivalences are not in the simp set.

### 6. Import Hygiene: `checkInitImports` Will Pass Transitively

The `lakefile.toml` sets `weak.linter.checkInitImports = false`, meaning the
`checkInitImports` linter is disabled at the project level. However, `lake exe
checkInitImports` (the custom script) checks transitively. The chain is:
- All Metalogic/Semantics files -> Derivation.lean -> Defs.lean -> `import Cslib.Init`

So `checkInitImports` passes via transitive import. This is correct, but the fact that only
`Defs.lean` has the explicit `import Cslib.Init` while all others use `public import` chains
could be fragile if the chain is ever broken.

### 7. Mathematical Completeness: Missing Int/Min Completeness Claims in Top-Level Doc

`Defs.lean` has an `## Architecture` section that documents the two proof systems and the
bridge. However, it does not mention that three variants of soundness/completeness are proved
(classical, intuitionistic, minimal). A PR reviewer documenting the contribution might expect
the top-level module doc to enumerate all major results.

### 8. Universe Polymorphism Inconsistency

`IntSoundness.lean` uses `IValid.{_, v}` (universe-polymorphic), while `ISemanticEntails`
in `SemanticConsequence.lean` is at `Type u`. The `int_strong_completeness` uses
`ISemanticEntails` (fixed universe `u`), while `int_completeness` calls
`ISemanticEntails_of_IValid (h_valid : IValid.{u, u} φ)`. This `{u, u}` universe
annotation is slightly restrictive. The definition `IValid` is `Type v`-quantified while
`ISemanticEntails` quantifies over `Type u`. The resulting theorems are universe-consistent,
but a reviewer may question why `IValid` and `MValid` use `v` (in `Kripke.lean`) while
`ISemanticEntails` uses `u` (in `SemanticConsequence.lean`), and whether `int_soundness_completeness`
should be stated at `{u, u}` specifically.

### 9. `DerivationTree` Is `Type _` Not `Prop`: No `decidable_mem` Concern

`DerivationTree` is in `Type _` by design (for computable height function). This is
architecturally sound. The `Deriv` Prop-wrapper correctly separates proof relevance. There
is no concern about universe issues here.

### 10. Missing Instances Entry for Propositional Logic

The CSLib Init/barrel file convention requires `lake exe mk_all --module` to update
`Cslib.lean` when new files are added. If these files are new additions, `Cslib.lean` must
be updated. This is a CI check that would catch missing registration.

---

## Recommended Approach

A PR reviewer should specifically verify:

1. **Run `lake exe lint-style`**: The files are long; check that line widths, header
   comments, and style linter pass. No evidence of style violations found in reading, but
   running the linter is required.

2. **Verify the global `noncomputable instance : HasHilbertTree`** is either justified (with
   explanation of why it must be global) or converted to `local instance`.

3. **Check whether the `@[simp]` absence is intentional**: Query the authors about whether
   `prop_completeness_iff_tautology` etc. should be `@[simp]` or at minimum `@[simp]`
   tagged for downstream use.

4. **Acknowledge the TODO** in `NaturalDeduction/Basic.lean` in the PR description.

5. **Verify `lake exe mk_all --module` has been run** to update `Cslib.lean`.

---

## Evidence/Examples

**Noncomputable root cause** (DeductionTheorem.lean, line 49):
```lean
attribute [local instance] Classical.propDecidable
```
This is the triggering declaration. Without it, `by_cases` in the tactic proofs would require
`Decidable` instances not available for generic `Atom : Type*`.

**Global HasHilbertTree instance** (DeductionTheorem.lean, lines 56-62):
```lean
noncomputable instance : HasHilbertTree (PL.Proposition Atom) where
  Tree := fun Γ φ => DerivationTree PropositionalAxiom Γ φ
  ...
```
This is hardcoded to `PropositionalAxiom` even though the file's other machinery is
fully parameterized over `{Axioms}`.

**Missing @[simp] example** (StrongCompleteness.lean, line 547):
```lean
theorem prop_completeness_iff_tautology {φ : PL.Proposition Atom} :
    Tautology φ ↔ Derivable PropositionalAxiom φ :=
```
This is a fundamental characterization lemma with no `@[simp]` tag.

---

## Confidence Level: High

All findings are grounded in direct reading of source files. The noncomputable analysis
is based on tracing the exact cause (`Classical.propDecidable` + `by_cases` in Type-level
`def`s) rather than conjecture. The global instance concern is concrete and verifiable.
The `@[simp]` gap is real and may require author justification.

No `sorry`, `admit`, or proof holes were found in any file. Zero-debt compliance confirmed.
