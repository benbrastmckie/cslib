# Teammate C Findings: Propositional/ and Foundations/ — Critic Analysis

- **Task**: 266 - Research Propositional and Foundations Improvements
- **Role**: Teammate C (Critic — gaps, shortcomings, blind spots)
- **Date**: 2026-06-22
- **Agent**: research critic

---

## Key Findings

### 1. The "One Sorry" Gap Has Already Been Closed

The prior team research report (01_team-research.md) identified `ipl_conservative_over_mpl` as
containing a sorry as its primary Gap 1. **This sorry was resolved by Task 265**, which completed
on 2026-06-22 using the WithBot embedding approach. The current `Conservative.lean` contains a
complete, sorry-free proof (verified by grep: zero sorry occurrences in all of
`Cslib/Logics/Propositional/`). Any plan treating this as an open gap is working from stale
information.

**Evidence**: `specs/archive/265_track_conservative_lean_sorry/summaries/01_conservative-extension-summary.md` confirms "sorry filled" with complete proof. `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean:163` shows `ipl_conservative_over_mpl` as a complete theorem with no sorry.

### 2. Kripke Completeness for MPL and IPL Already Exists

The prior research listed "No Kripke completeness for IPL/MPL" as Gap 8. This is **wrong**.
Both `MinStrongCompleteness.lean` and `IntStrongCompleteness.lean` contain full strong
soundness/completeness for Kripke semantics:

- `min_soundness_completeness`: `MValid φ ↔ Derivable MinPropAxiom φ`
- `int_soundness_completeness`: `IValid φ ↔ Derivable IntPropAxiom φ`
- `min_strong_completeness`: `MSemanticEntails Γ φ → SetDerivable MinPropAxiom Γ φ`
- `int_strong_completeness`: `ISemanticEntails Γ φ → SetDerivable IntPropAxiom Γ φ`

The `KripkeBridge.lean` note about "only one direction" referred to the algebraic-to-Kripke
soundness direction via the upset algebra. The Kripke completeness proofs live elsewhere (via
canonical model construction with prime DCCS worlds). This gap was fabricated by the prior
research or is a misunderstanding of module organization.

**Evidence**: `Cslib/Logics/Propositional/Metalogic/MinStrongCompleteness.lean:322-334` and
`IntStrongCompleteness.lean:327-338`.

### 3. The ProofSystem.lean "Future Work" Comment Is Stale

`Cslib/Foundations/Logic/ProofSystem.lean:50` contains the comment:
> "derivation trees (not yet ported) and are future work."

This is stale. `Cslib/Logics/Propositional/ProofSystem/Instances.lean` and `IntMinInstances.lean`
already register full `InferenceSystem`, `ModusPonens`, all `HasAxiom*`, and bundled Hilbert
class instances (`ClassicalHilbert`, `IntuitionisticHilbert`, `MinimalHilbert`) for all three
propositional tag types (`HilbertCl`, `HilbertInt`, `HilbertMin`).

The comment implies something that has already been done. The documentation is misleading to
new contributors.

**Evidence**: `Cslib/Foundations/Logic/ProofSystem.lean:45-50` vs.
`Cslib/Logics/Propositional/ProofSystem/Instances.lean:46-118` and
`IntMinInstances.lean:44-167`.

### 4. The AlgComplete-to-Hilbert Bridge Remains a Real Gap

The `Semantics/Algebra/Completeness.lean` module contains:
> "Hilbert-level corollaries (`Derivable MinPropAxiom φ ↔ GHAValid φ`, etc.) require bridging
> the Hilbert axiomatic system with the natural deduction system. This equivalence is nontrivial
> and deferred."

The bridge module `NaturalDeduction/Equivalence.lean` already provides `hilbert_iff_nd_min`,
`hilbert_iff_nd_int`, `hilbert_iff_nd_cl`. The algebraic completeness theorems (`MPL.alg_complete`,
`IPL.alg_complete`, `alg_complete_classical`) are stated at the ND level (using
`Theory.Derivation`/`DerivableIn`). Composing the two would produce the missing corollaries:
- `Derivable MinPropAxiom φ ↔ GHAValid φ`
- `Derivable IntPropAxiom φ ↔ HAValid φ`
- `Derivable PropositionalAxiom φ ↔ BAValid φ`

These are straightforward compositions but no file in the module currently contains them.

**Evidence**: `Semantics/Algebra/Completeness.lean:28-32` (deferred note) +
`NaturalDeduction/Equivalence.lean` (bridge exists, unused for this purpose).

### 5. The Capture-Avoiding Substitution Defect Has Low Actual Impact

The TODO in `NaturalDeduction/Basic.lean:275-276`:
> "Substitution of a family of derivations `D` for hypotheses in the context `Γ` of `E`. TODO:
> this implementation is not capture avoiding."

This is a correctness defect, but `subs` is **only called internally within `Basic.lean`** (grep
confirms it is never called from outside the module). The current definition works correctly for
the cases where it is used (hypothesis substitution, not atom-level substitution), because the
propositional language has no binders — capture-avoidance is only meaningful when binding
constructs (lambda, quantifiers) are present. For propositional logic with finset contexts,
the concern is about context management, not variable capture in the linguistic sense.

The comment is misleading: propositional `Proposition Atom` has no binding operators, so the
traditional notion of capture-avoidance does not apply. The TODO may be referring to a context
management subtlety (whether `Γ'` and `Δ` can overlap in unexpected ways), but this is not
documented. This should be clarified or removed rather than treated as a critical correctness
defect.

**Evidence**: `NaturalDeduction/Basic.lean:275-302` (definition) + grep showing zero external
call sites for `.subs `.

### 6. `PropositionalConnectives` Bundling Is a Tombstoned Non-Issue

The comment in `Foundations/Logic/Connectives.lean:130` defers extending
`PropositionalConnectives` to include `HasAnd`/`HasOr` to "task 173." Task 173 is tombstoned,
meaning this work was intentionally deferred or abandoned. The practical question is: **does
anything actually need this bundling?**

Modal, Temporal, and Bimodal formula types lack native `HasAnd`/`HasOr` constructors and use
Lukasiewicz encodings for `∧` and `∨`. The comments in `Modal/Basic.lean`,
`Temporal/FromPropositional.lean`, and `Modal/FromPropositional.lean` explicitly acknowledge
this design choice. `PropositionalConnectives` already registers for `PL.Proposition` via
`HasAnd` and `HasOr` atomic instances in `Defs.lean`.

**Conclusion**: The bundling gap is a documentation/aspirational issue, not a functionality
gap. Extending the class would break existing code patterns or require interface stabilization
across four formula types. This is a scope risk that justifies deferral.

**Evidence**: `Cslib/Foundations/Logic/Connectives.lean:127-132` + `Defs.lean:118-124`.

### 7. Zero Test Coverage Is a Real Gap With Clear Remediation

`CslibTests/` contains 13 test files covering: Bisimulation, CCS, CLL, DFA, FreeMonad,
GrindLint, HasFresh, HML, ImportWithMathlib, LambdaCalculus, LTS, MLL, Reduction. **None
imports any `Cslib.Logics.Propositional.*` module.**

This means all Propositional/ theorems are exercised only by compilation type-checking. No
`#eval` or `example` tests verify computational behavior, no `decide` tests verify decidable
instances, and no smoke tests catch API breakage. This is a genuine gap because:
- `Bool.lean` (`BoolEvaluate`) and `Semantics/Bool.lean` have computable functions that could
  be tested
- `Proposition.subst` (the monad) could be unit-tested
- The Hilbert derivation trees (`DerivationTree`) are computable and could have height/structure
  tests

**Evidence**: `ls CslibTests/` shows no Propositional.lean test file.

### 8. The Scope of "Foundations/" Is Too Broad for One Task

`Cslib/Foundations/` has 66 files across 7 major subdirectories: Combinatorics, Control,
Data, Lint, Logic, Relation, Semantics, Syntax. The task description covers "Foundations/Logic/"
specifically (6 files + subdirectories). However, the task title says "Propositional/ and
Foundations/ improvements" without bounding to Logic/.

The genuine improvements needed in `Foundations/Logic/` are:
1. Fix the stale "future work" comment in `ProofSystem.lean:50`
2. Potentially extend `PropositionalConnectives` to include `HasAnd`/`HasOr` (but only if
   needed by downstream; currently not needed)

The `Foundations/Data/`, `Foundations/Semantics/`, `Foundations/Relation/` subdirectories
serve LTS, Bimodal, computability modules — they are not meaningfully within scope of
"propositional and foundations improvements" unless specific consumers are identified.

**Recommendation**: Scope the task to `Propositional/` + `Foundations/Logic/` only.

---

## Evidence/Examples With File Paths

| Finding | File | Lines | Evidence Type |
|---------|------|-------|---------------|
| sorry already cleared | `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean` | 163-171 | Complete proof |
| Kripke completeness MPL | `Cslib/Logics/Propositional/Metalogic/MinStrongCompleteness.lean` | 322-335 | `min_soundness_completeness` |
| Kripke completeness IPL | `Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean` | 327-338 | `int_soundness_completeness` |
| Stale ProofSystem comment | `Cslib/Foundations/Logic/ProofSystem.lean` | 45-50 | Text "not yet ported" |
| Instances exist | `Cslib/Logics/Propositional/ProofSystem/Instances.lean` | 46-118 | Full concrete instances |
| Alg-to-Hilbert bridge missing | `Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean` | 28-32 | "deferred" comment |
| subs call sites (none external) | `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | 275-302 | grep confirms internal only |
| No PropositionalConnectives consumers | `Cslib/Foundations/Logic/Connectives.lean` | 127-132 | No downstream need |
| Zero test files | `CslibTests/` | (directory) | 13 files, none PL |
| Task 265 resolved | `specs/archive/265_track_conservative_lean_sorry/summaries/01_conservative-extension-summary.md` | all | "sorry filled" |

---

## Recommended Priorities

### Priority 1 (High, Actionable): Bridge Algebraic Completeness to Hilbert Level

Create `Cslib/Logics/Propositional/Semantics/Algebra/HilbertBridge.lean` that composes:
- `MPL.alg_complete` + `hilbert_iff_nd_min` → `Derivable MinPropAxiom φ ↔ GHAValid φ`
- `IPL.alg_complete` + `hilbert_iff_nd_int` → `Derivable IntPropAxiom φ ↔ HAValid φ`
- `alg_complete_classical` + `hilbert_iff_nd_cl` → `Derivable PropositionalAxiom φ ↔ BAValid φ`

This is straightforward composition and eliminates the "deferred" note in Completeness.lean.

### Priority 2 (High, Quick Win): Fix Stale ProofSystem.lean Documentation

Update `Cslib/Foundations/Logic/ProofSystem.lean:50` to remove or correct the "not yet ported"
comment. The concrete instances for all three propositional tag types already exist.

### Priority 3 (Medium): Add Propositional Test Coverage

Create `CslibTests/Propositional.lean` with:
- `#eval` tests for `BoolEvaluate` on concrete formulas
- `decide` tests for `Proposition.IsBotFree`
- Example derivations using `DerivationTree`
- Smoke test that `prop_strong_completeness_iff` typechecks for a concrete atom type

### Priority 4 (Low, Clarify Only): Resolve the `subs` TODO Comment

Since propositional logic has no binding operators, "capture avoidance" in the traditional sense
is inapplicable. The TODO comment should be clarified to describe the actual concern (if any)
or removed. Do not treat this as a blocking correctness defect.

### Do Not Pursue (Scope Risks):

- **Sequent calculus (LK/LJ/G4ip)**: No roadmap item depends on it. CLL provides a template,
  but cut elimination (also needed) is stubbed there too. Net new work with no clear consumer.
- **Craig interpolation**: High difficulty, no downstream consumer identified.
- **CNF/DNF normal forms**: These would be useful for decidability, but decidability
  (`Tautology φ` is decidable via `Bool.lean`) already exists. Normal forms add complexity
  without filling an identified gap.
- **Extending Foundations/Data/, Foundations/Semantics/ scope**: No propositional connection.

---

## Confidence Level

| Finding | Confidence |
|---------|-----------|
| Sorry already cleared (Task 265 done) | High — verified in archive summary and source |
| Kripke completeness exists for MPL/IPL | High — read theorem statements directly |
| ProofSystem.lean comment is stale | High — instances file is unambiguous |
| Alg-to-Hilbert bridge is genuinely missing | High — Completeness.lean says "deferred" explicitly |
| subs capture-avoidance not critical | Medium — no external callers, but propositional language peculiarity argument requires confirmation |
| PropositionalConnectives bundling is non-issue | Medium — no consumer identified, but task 173 tombstone may have been premature |
| Zero test coverage is a real gap | High — directory listing is definitive |
| Scope too broad | High — 66 Foundations/ files vs. 6-10 logic files relevant to task |
