# Teammate B Findings: Repo Standards Comparison and Alternative Patterns

Task 190: Review quality of deduction theorem and strong soundness/completeness in
`Logics/Propositional/` for PR readiness, evaluating `noncomputable` usage against CSLib
repo standards.

---

## Key Findings

### 1. `noncomputable` Usage Is Established Repo Pattern — Not a Deviation

The `noncomputable` usage in the propositional files is **consistent with and expected by**
CSLib repo standards. Evidence across the codebase:

**In Modal Metalogic** (`Logics/Modal/Metalogic/`):
- `DeductionTheorem.lean`: `noncomputable instance : HasHilbertTree`, `noncomputable def deductionWithMem`, `noncomputable def deductionTheorem`
- `Completeness.lean`: `noncomputable def CanonicalModel`
- `MCS.lean`: `noncomputable def iteratedDeduction`

**In Temporal Metalogic** (`Logics/Temporal/Metalogic/`):
- `DeductionTheorem.lean`: `noncomputable instance : HasHilbertTree`
- `MCS.lean`: `noncomputable` throughout

**In Bimodal Metalogic** (`Logics/Bimodal/Metalogic/Core/`):
- `DeductionTheorem.lean`: Uses `noncomputable section ... end` (bulk declaration)
- `MaximalConsistent.lean`: Multiple `noncomputable def` entries
- `MCSProperties.lean`: Uses `noncomputable section ... end` block

**In Foundations** (`Foundations/Logic/`):
- `InferenceSystem.lean`: `noncomputable def DerivableIn.toDerivation`
- `MetalogicDeductionHelpers.lean`: `noncomputable def deductionAxiom/ImpSelf/AssumptionOther/MpUnderImp` — the shared helpers called by ALL logics

**Count**: 314 `noncomputable` occurrences across `Cslib/Logics/` alone.

The propositional files have:
- `DeductionTheorem.lean`: `noncomputable instance`, `noncomputable def deductionWithMem`, `noncomputable def deductionTheorem` (3 occurrences)
- `StrongCompleteness.lean`: `private noncomputable def dne_from_neg_neg` (1 occurrence)
- `NaturalDeduction/FromHilbert.lean`: `noncomputable def impI`, `noncomputable def hilbertCut` (2 occurrences)
- `NaturalDeduction/Equivalence.lean`: `noncomputable def ndToHilbert` (1 occurrence)
- `NaturalDeduction/HilbertDerivedRules.lean`: `noncomputable def hilbertNegI`, `noncomputable def hilbertOrE` (2 occurrences)
- `Metalogic/IntLindenbaum.lean`, `MinLindenbaum.lean`: `noncomputable def` entries

**Conclusion**: The propositional `noncomputable` count is proportionate with the complexity of the material and in perfect alignment with the pattern established by Modal, Temporal, and Bimodal logics.

### 2. Root Cause of `noncomputable` Is Legitimate and Documented

The propositional code correctly explains the source of noncomputability:

From `NaturalDeduction/Equivalence.lean` docstring:
> "The `ndToHilbert` direction is `noncomputable` because it uses `deductionTheorem`, which relies on `Classical.propDecidable`. The `hilbertToND` direction is computable."

From `NaturalDeduction/HilbertDerivedRules.lean` docstring:
> "Rules that use `impI` (the deduction theorem) are `noncomputable`."

The chain is:
1. `attribute [local instance] Classical.propDecidable` is needed for `by_cases` in the weakening case of `deductionTheorem`
2. This makes `deductionTheorem` and `deductionWithMem` noncomputable
3. Functions that call these inherit noncomputability

This is the **identical pattern** used in `Modal/Metalogic/DeductionTheorem.lean`,
`Temporal/Metalogic/DeductionTheorem.lean`, and `Bimodal/Metalogic/Core/DeductionTheorem.lean` — all use `attribute [local instance] Classical.propDecidable`.

### 3. `noncomputable` Cannot Be Eliminated Without Structural Redesign

The alternative approaches and their viability:

**Option A: Make derivation trees decidable** — requires decidable equality on atoms and formulas, but CSLib's `Atom : Type*` is left fully generic (no `DecidableEq` constraint). Enforcing this would break the universe-polymorphic design that allows instantiating at any atom type.

**Option B: Use `open Classical`** — would make the entire file classical without scoping. The current `attribute [local instance] Classical.propDecidable` is the **more disciplined** approach, limiting classical reasoning to where it is needed.

**Option C: Restructure using Prop-only proofs** — the deduction theorem proof requires pattern matching on `DerivationTree` constructors with `by_cases` on equality of formulas. Without decidable formula equality (which requires decidable `Atom`), the `by_cases` calls require classical choice, making noncomputability structurally unavoidable.

The `noncomputable` marking is **correct, expected, and cannot be reduced** without constraining the atom type universe or fundamentally changing the proof strategy.

### 4. Documentation Quality Meets or Exceeds Repo Standards

The propositional files provide:
- Section headers using `/-! ## ... -/` pattern (consistent with Modal, Temporal, Bimodal)
- Per-definition docstrings with `**bold**` for main results
- `## Main Results` sections in module-level docstrings
- `## Strategy` sections explaining proof approach
- `## References` sections with BibTeX keys (`[ChagrovZakharyaschev1997]`, `[Prawitz1965]`, `[TroelstraVanDalen1988]`, `[Johansson1937]`) — all verified present in `references.bib`
- Cross-references to sibling files (e.g., "modal deduction theorem pattern")

The documentation level is **higher than average** for the repo. For comparison:
- `CCS/Semantics.lean` has a brief module doc with no `## Strategy` or `## References`
- `Foundations/Logic/InferenceSystem.lean` (by another author) has a brief `/-! # Inference System Typeclass -/` with minimal per-definition docs

The propositional metalogic files consistently follow the full Mathlib-style documentation format that CONTRIBUTING.md requires.

### 5. Proof Style Is Tactic-Heavy With Well-Structured Pattern Matching

The propositional code uses:
- `match d with | .ax ... | .assumption ... | .modus_ponens ... | .weakening ...` structural induction (matches Modal pattern exactly)
- `termination_by d.height` with explicit `decreasing_by` (same as Modal)
- `letI :=` for local typeclass instances (matches Bimodal pattern)
- `by_cases` / `rcases` / `obtain` / `intro` (standard CSLib tactic style)
- `simp only [...]` with explicit lemma lists (no bare `simp` in proof-critical steps)

No "magic" automation (no `omega`, `decide`, `aesop` on logic-theoretic goals). This is appropriate for metalogic proofs where readability is critical.

### 6. Mathlib Comparison: CSLib Propositional Is a Novel Contribution

Mathlib does not have a standalone Hilbert-style propositional logic formalization with:
- Parameterized axiom predicates (supporting classical/intuitionistic/minimal simultaneously)
- Strong completeness via canonical models
- Deduction theorem by structural induction on derivation trees
- Equivalence with natural deduction

Mathlib's `FirstOrder.Language.Theory.IsMaximal` (in `Mathlib.ModelTheory.Satisfiability`) provides model-theoretic concepts for first-order logic but not the Hilbert proof-system approach used here. The CSLib propositional logic fills a genuine gap.

The closest Mathlib content is `Prop.instHeytingAlgebra` and `himp_iff_imp` — these are algebraic characterizations, not the syntactic proof-theoretic treatment that CSLib provides.

### 7. Structural Patterns Are Correctly Reusing Foundation Infrastructure

The propositional files correctly instantiate and reuse:
- `Cslib.Logic.Metalogic.DerivationSystem` (from `Foundations/Logic/Metalogic/Consistency.lean`)
- `Cslib.Logic.Metalogic.set_lindenbaum` (generic Zorn-based Lindenbaum)
- `Cslib.Logic.HasHilbertTree` with the 4 generic helper lemmas (from `Foundations/Logic/Metalogic/DeductionHelpers.lean`)
- `Cslib.Logic.Metalogic.SetMaximalConsistent.closed_under_derivation` (generic closure)

This matches the CONTRIBUTING.md reuse-first principle: the propositional code delegates all generic MCS reasoning to Foundations and only provides logic-specific instantiation.

### 8. Minor Observations

**`attribute [local instance] Classical.propDecidable` Scoping**: All three logics that use this (Modal, Temporal, Propositional) apply it at the module level within `@[expose] public section`. The propositional usage is consistent.

**No `set_option linter.flexible false` needed**: Unlike some Bimodal and Temporal files that suppress linters, the propositional files have no `set_option` directives. This indicates cleaner proof style.

**`private` modifier on `dne_from_neg_neg`**: This is a PR-friendly pattern — internal helpers are marked `private` to reduce namespace pollution. Matches Bimodal pattern (e.g., `private noncomputable def` in similar helper contexts).

**All files registered in `Cslib.lean`**: All 30 propositional files appear in the barrel import. No files missing from the module index.

---

## Recommended Approach

The `noncomputable` usage and overall code quality in `Logics/Propositional/Metalogic/DeductionTheorem.lean` and `Metalogic/StrongCompleteness.lean` meet CSLib PR standards. Specific recommendations:

1. **Do not attempt to eliminate `noncomputable`** — it is structurally necessary and matches the repo-wide pattern for all Hilbert-style metalogic proofs.

2. **Verify CI pipeline passes** — the files are already in `Cslib.lean`, so `lake exe checkInitImports` and `lake exe mk_all` should pass. The critical checks are `lake build` (no linter warnings), `lake lint`, and `lake exe lint-style`.

3. **No additional documentation is needed** — the files already exceed the repo documentation standard. If anything, the per-connective helper functions in `StrongCompleteness.lean` (e.g., `prop_truth_lemma_and`, `prop_truth_lemma_or`) are unusually well-documented.

4. **No structural refactoring is needed** — the code correctly follows the Modal/Temporal/Bimodal deduction theorem pattern, instantiates the Foundations MCS infrastructure, and uses the shared `HasHilbertTree` helpers.

---

## Evidence / Examples

**Exact pattern match with Modal**:

Modal `DeductionTheorem.lean` line 52:
```lean
noncomputable instance : HasHilbertTree (Proposition Atom) where ...
noncomputable def deductionWithMem ... : DerivationTree Axioms (removeAll Γ' A) (A → φ)
noncomputable def deductionTheorem ... : DerivationTree Axioms Γ (A → B)
```

Propositional `DeductionTheorem.lean` lines 56, 71, 130:
```lean
noncomputable instance : HasHilbertTree (PL.Proposition Atom) where ...
noncomputable def deductionWithMem ... : DerivationTree Axioms (removeAll Γ' A) (A → φ)
noncomputable def deductionTheorem ... : DerivationTree Axioms Γ (A → B)
```

The propositional code is a faithful adaptation of the modal pattern with propositional-specific simplifications (4 constructors vs 5 for modal, no necessitation case).

**`noncomputable` prevalence across repo**:
- 314 occurrences in `Cslib/Logics/`
- Propositional contributes ~15 occurrences total across all files
- Bimodal alone contributes 100+ occurrences

**References verified in `references.bib`**:
- `ChagrovZakharyaschev1997` — present
- `Prawitz1965` — present
- `TroelstraVanDalen1988` — present
- `Johansson1937` — present

---

## Confidence Level

**High** — The pattern analysis is based on direct code inspection of 20+ files across Modal, Temporal, Bimodal, Propositional, and Foundations directories. The `noncomputable` justification is directly confirmed by docstring text in the propositional files themselves and corroborated by the identical pattern in three other logic subdirectories.
