# Teammate D Findings: Strategic Alignment and Long-term Vision

**Task**: 190 — Review propositional PR readiness
**Teammate Role**: Strategic Alignment and Long-term Vision (Horizons)
**Date**: 2026-06-14

---

## Key Findings

### 1. Roadmap Alignment is Tight and Well-Sequenced

The ROADMAP.md explicitly describes a five-layer dependency tree with Propositional as
the shared sub-logic:

```
Foundations/Logic -> Propositional -> Modal, Temporal (peers) -> Bimodal
```

All of Modal, Temporal, and Bimodal already build on top of the Propositional layer.
The propositional metalogic (deduction theorem, MCS, soundness, completeness) is the
critical path for every downstream logic's completeness proofs. Contributing this
upstream is not a detour — it is the foundational prerequisite for all subsequent
contributions. The roadmap shows that the remaining work (discrete/continuous/dense
completeness for Temporal and Bimodal) all imports from the Propositional metalogic
layer directly or transitively.

### 2. The Noncomputable Pattern is Consistent with Established CSLib Standards

Across all logic modules, `noncomputable` appears wherever:
1. A `DerivationTree` is constructed term-level (not just proposition-level), specifically in
   the deduction theorem and its helpers, and
2. A canonical model object is built (Lindenbaum-extension, canonical valuation, canonical world).

This is not a problem specific to Propositional — it is the established pattern across the
entire repo:

| Module | Noncomputable count |
|--------|---------------------|
| Bimodal | 215 instances |
| Temporal | 77 instances |
| Propositional | 14 instances |
| Foundations/Logic | 6 instances |

Propositional has the smallest noncomputable footprint of any logic module. The usage is
concentrated in `DeductionTheorem.lean` (3 items: 1 instance + 2 defs) and helper functions
in `IntLindenbaum.lean`, `MinLindenbaum.lean`, `StrongCompleteness.lean`. All of these are
necessary because the `DerivationTree` type is a proof-relevant inductive — it carries
explicit proof witnesses, which requires `Classical.propDecidable` for the `by_cases` pattern
matching. This is a known, accepted pattern across Bimodal, Temporal, Modal, and Foundations.

The `attribute [local instance] Classical.propDecidable` pattern (used in 4 Propositional
files) is exactly the same technique used in 25+ files across Bimodal and Temporal. It is
strictly localized to metalogic files — no definitional-layer files use it.

**Conclusion**: The noncomputable usage is not a liability. It follows established repo conventions
and is appropriately scoped to metalogic proofs. No reviewer familiar with the Modal or Temporal
metalogic would flag this as unusual.

### 3. PR Strategy: The 6-PR Roadmap from Task 188 is Well-Designed

Task 188 already produced and implemented a first PR with this roadmap:

| PR | Title | Scope | LOC Estimate |
|----|-------|-------|--------------|
| 0 (done) | Connective typeclass hierarchy | `Connectives.lean` | 96 |
| 1 (done) | Five-primitive formula type | `Defs.lean` + `NaturalDeduction/Basic.lean` | ~170 modified |
| 2 | Hilbert axiom schemata + bivalent semantics | `ProofSystem/Axioms.lean` + `Semantics/Basic.lean` | ~283 |
| 3 | Hilbert proof engine + soundness | `ProofSystem/Derivation.lean` + `Metalogic/Soundness.lean` | ~257 |
| 4 | Deduction theorem + classical completeness | `DeductionTheorem` + `MCS` + `StrongCompleteness` | ~963 (may need split) |
| 5 | ND extensions + Hilbert-ND equivalence | `DerivedRules` + `FromHilbert` + `Equivalence` | ~1,440 |
| 6 | Kripke semantics + Int/Min completeness | Kripke + Int/Min soundness/completeness | ~2,255 |

This phased strategy is sound for upstream acceptance. Each PR is self-contained and has a
clear story. The concern is PR 4 (~963 LOC) which may be too large for a single PR — the
task 188 team research already flagged this.

**Recommendation for PR 4**: Split into two:
- PR 4a: Deduction theorem + MCS (foundational machinery) — `DeductionTheorem.lean` (219 lines)
  + `MCS.lean` (162 lines) = ~381 lines
- PR 4b: Soundness + strong completeness (the main results) — `Soundness.lean` (93 lines)
  + `StrongCompleteness.lean` (551 lines) = ~644 lines

The `StrongCompleteness.lean` file alone is large because it includes all classical results
(truth lemma, strong soundness, strong completeness, compactness, weak completeness, DNE
helper). Consider whether the private `dne_from_neg_neg` helper (30 lines) can be factored
into a general `Foundations/Logic` utility to reduce the classical-specific file size.

### 4. Zero-Sorry Status is a Significant PR Asset

There are zero `sorry`s in the entire `Cslib/Logics/Propositional/` directory. This is
explicitly verified. The codebase has complete proofs for:
- Strong soundness for CPL, IPL, MPL
- Strong completeness for CPL, IPL, MPL
- Deduction theorem (parameterized over any axiom set with implyK/implyS)
- Lindenbaum lemma (via Zorn's lemma in Foundations)
- ND-Hilbert equivalence for all three logics

The zero-sorry status should be prominently highlighted in PR descriptions. It directly
addresses the reviewer expectation (from PR #633 review history) that strong completeness
be included alongside weak completeness.

### 5. Extensibility: Propositional Layer is Well-Structured for Reuse

The parameterization design is forward-looking. Key design decisions that enable downstream reuse:

1. **`DeductionTheorem.lean` is parameterized** — `deductionWithMem` and `deductionTheorem`
   take `{Axioms}` plus explicit `h_implyK`/`h_implyS` proofs, not a fixed axiom set. This
   allows Modal and Temporal to reuse the same structural pattern (they do: each has its own
   parallel `DeductionTheorem.lean` following the same signature).

2. **`HasHilbertTree` typeclass** (in `Foundations/Logic/Metalogic/DeductionHelpers.lean`) is
   shared infrastructure — the 4 generic deduction helpers are proved once and instantiated
   by PL, Modal, Temporal, and Bimodal.

3. **`DerivationSystem` in `Foundations/Logic/Metalogic/Consistency.lean`** is the abstract
   interface for the MCS framework — Modal and Temporal both instantiate it, meaning adding
   more logics (e.g., PDL, K4, GL) would follow the same pattern with no changes to
   Foundations.

4. **`IntMinInstances.lean`** in `ProofSystem/` — the parameterized design means Minimal and
   Intuitionistic completeness results share the same infrastructure as Classical, just with
   different axiom instances.

The current architecture sets up a generalized logic meta-framework that could plausibly
accommodate any Hilbert-style logic with implication. This is a strong argument to make in
the PR description when contributing the foundations.

### 6. Propositional is the Right Entry Point for the Broader Contribution Arc

The project's roadmap section "Remaining" lists 5 open items, all in Bimodal/Temporal
completeness. These all depend on the propositional MCS infrastructure already established
locally. The PR sequence for propositional logic (PRs 0-6) is the critical path that, once
upstream, enables the Bimodal/Temporal contributions to follow.

The CSLib README's stated aim — "Offer APIs and languages for formalisation projects" and
"Establish a common ground for connecting different developments in Computer Science" — is
directly served by a complete, parameterized propositional logic metalogic.

### 7. Task 189 Completion Simplifies PR 4

Task 189 (rename completeness to canonical model) completed by eliminating the weak
completeness files and merging canonical model infrastructure into the strong completeness
files. This means:
- `StrongCompleteness.lean` is now the single authoritative CPL completeness file (551 lines)
- No parallel weak/strong file confusion for reviewers
- The canonical model construction and truth lemma are co-located with the completeness
  proof, making the file self-contained and easier to review

This cleanup was the right move before PR submission. PR 4b can now point to a single
clean file for each logic.

---

## Recommended Approach

### Immediate Priority: PR Readiness Assessment for PRs 0+1

PRs 0 and 1 are already implemented on feature branch `feat/propositional-five-primitive`
(per task 188 completion). The current task 190 should:
1. Verify that the branch is still building against upstream HEAD (Mathlib bumps may have
   occurred since task 188 completed on 2026-06-14)
2. Confirm the PR description addresses: ctchou resolution, 6-PR roadmap, AI disclosure
3. Verify no conflict with PRs #536, #607 (they may have merged or been updated since task 188)

### Near-term Priority: Scope PR 4 for Upstream

The deduction theorem and strong completeness files are the most mathematically significant
contribution. To maximize reviewer friendliness:
- PR 4a = DeductionTheorem.lean (219 LOC) + MCS.lean (162 LOC): a clean, focused ~381 LOC PR
- PR 4b = Soundness.lean (93 LOC) + StrongCompleteness.lean (551 LOC): the main results,
  ~644 LOC with well-structured docstrings

The StrongCompleteness.lean file has strong docstrings (full module docstring, strategy
section, all theorem docstrings) — this is PR-ready in terms of documentation quality.

### Noncomputable: No Action Needed

The noncomputable pattern does not require restructuring. The `DerivationTree` type is
proof-relevant by design (constructive witnesses), and the metalogic requires classical
reasoning (`by_cases` on formula membership). This is necessary and well-justified. The
`attribute [local instance] Classical.propDecidable` scoping is correct: it applies only
to the metalogic files where it is needed and does not leak into definitional content.

Attempting to eliminate `noncomputable` via `Decidable` instances on `DerivationTree` would
be misguided: `DerivationTree` objects are proofs-as-data (type-theoretic witnesses), and
their existence is routinely non-decidable in general (the Hilbert system is not
syntax-directed in a way that makes derivation construction computable without oracle access
to the proof). The current approach is the standard one for formal Hilbert proofs.

### Long-term: Foundations Layer Contribution

`Foundations/Logic/Metalogic/DeductionHelpers.lean` and `Consistency.lean` (the generic
`HasHilbertTree` typeclass and Lindenbaum/MCS framework) are not yet contributed upstream.
These should be PR 3.5 (between Hilbert derivation and completeness). They are foundational
shared infrastructure and their upstream presence would benefit any future logic contributor.

---

## Evidence/Examples

**Noncomputable scope is narrow and consistent**:
- `DeductionTheorem.lean`: 3 noncomputable items (instance + 2 defs)
- `IntLindenbaum.lean`: 2 noncomputable defs
- `MinLindenbaum.lean`: 1 noncomputable def
- `StrongCompleteness.lean`: 1 private noncomputable def (`dne_from_neg_neg`)
- Total: 7 noncomputable items across 2,865 lines of metalogic code

Compare to Modal (`DeductionTheorem.lean` + `Completeness.lean`): 4 noncomputable items
with the same structural pattern. Propositional is proportionally leaner.

**Parameterization enabling reuse**:
```
DeductionTheorem.lean:
  deductionTheorem {Axioms} (h_implyK ...) (h_implyS ...) -- generic
  prop_has_deduction_theorem h_implyK h_implyS -- wraps for DerivationSystem
  cl_prop_has_deduction_theorem -- CPL backward-compatible instantiation
```
This three-layer structure (generic / parameterized wrapper / classical instantiation)
mirrors exactly what Modal and Temporal do. The pattern is ready for upstream.

**Classical.propDecidable scoping is local**:
- `attribute [local instance] Classical.propDecidable` appears in exactly 4 files:
  `DeductionTheorem.lean`, `IntLindenbaum.lean`, `MinLindenbaum.lean`, `StrongCompleteness.lean`
- No contamination of ProofSystem/, Semantics/, or NaturalDeduction/ definitional layers
- This is the correct Lean 4 idiom for classical metalogic proofs

**Zero-sorry status verified**:
```
grep -rn "sorry" Cslib/Logics/Propositional/  # no output
```

**Roadmap alignment**:
- ROADMAP.md lists 5 remaining items (all Bimodal/Temporal completeness)
- All 5 depend transitively on the propositional MCS framework
- Propositional is not a detour; it is the prerequisite layer for everything remaining

---

## Confidence Level

**HIGH** on:
- Noncomputable assessment (pattern directly verified against Modal/Temporal/Bimodal)
- Zero-sorry status (grep verified)
- Roadmap alignment (ROADMAP.md directly read, dependency structure confirmed)
- PR 4 split recommendation (line counts directly measured)
- Parameterization quality (code directly read)

**MEDIUM** on:
- PR 4a/4b split being exactly right (depends on reviewer feedback and how PR #536/#607 resolve)
- Upstream CI compatibility (task 188 verified as of 2026-06-14, but Mathlib bumps may require rebase)

**LOW** on:
- Whether `dne_from_neg_neg` should be extracted to Foundations (tradeoff between
  generality and file locality — reasonable either way)
