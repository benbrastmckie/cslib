# Research Report: Strong Completeness for Minimal, Intuitionistic, and Classical Propositional Logics

- **Task**: 183 - Establish strong completeness for the minimal, intuitionistic, and classical propositional logics
- **Started**: 2026-06-13T00:00:00Z
- **Completed**: 2026-06-13T00:00:00Z
- **Effort**: Team research (4 teammates, parallel)
- **Dependencies**: Tasks 182 (revert scope), existing CSLib propositional metalogic infrastructure
- **Sources/Inputs**: CSLib codebase (Consistency.lean, MCS.lean, IntLindenbaum.lean, MinLindenbaum.lean, Completeness.lean, IntCompleteness.lean, MinCompleteness.lean), prior art (Trufas 2024, Bentzen 2023, From & Jacobsen 2025), BimodalLogic algebraic infrastructure
- **Artifacts**: `specs/183_strong_completeness_propositional_logics/reports/01_team-research.md`
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Project Context

- **Upstream Dependencies**: `Cslib/Foundations/Logic/Metalogic/Consistency.lean` (generic MCS/Lindenbaum), `Cslib/Logics/Propositional/Metalogic/MCS.lean`, `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean`, `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean`, all three weak completeness files
- **Downstream Dependents**: Compactness theorem (free corollary), future parametric algebraic completeness
- **Alternative Paths**: Algebraic representation theorem (not recommended for this task; see Section 5)
- **Potential Extensions**: Stone duality, decidability via finite Lindenbaum-Tarski algebra, parametric algebraic completeness across modal/temporal/propositional logics

## Executive Summary

- **Strong completeness is not yet formalized in CSLib**: all three logics have weak completeness (`Valid phi -> Derivable Axioms phi`) but no semantic consequence from a set of assumptions (`Gamma |= phi -> Gamma |- phi`).
- **The direct MCS/Lindenbaum approach is the clear consensus strategy**: all four teammates converge on this conclusion; approximately 85-90% of the required infrastructure already exists in CSLib.
- **Three new semantic entailment definitions and one shared `SetDerivable` definition** are the primary missing ingredients, plus the three strong completeness theorems themselves.
- **Implementation order recommendation**: minimal logic first (no consistency side condition), then intuitionistic, then classical; each subsequent system requires slightly more complexity.
- **Compactness is a free corollary**: once strong completeness and strong soundness are established for each logic, compactness follows with no additional infrastructure.
- **The algebraic approach (BimodalLogic prior art) is deferred**: it is viable only for the classical case, lacks Mathlib support for Heyting algebras (intuitionistic), and would cost 5-10x more than the direct approach across all three logics.
- **Estimated total new code**: 400-660 lines across 3-4 new Lean files.

## Context and Scope

**What is strong completeness?**

Weak completeness (already proved for all three logics): `Valid phi -> Derivable Axioms phi`. Every valid formula with no assumptions is derivable from the empty context.

Strong completeness (the task goal): `Gamma |= phi -> SetDerivable Axioms Gamma phi`. If `phi` is a semantic consequence of an arbitrary (possibly infinite) set of premises `Gamma`, then `phi` is derivable from some finite subset of `Gamma`.

This is strictly stronger because it handles arbitrary sets of assumptions, not just the empty context. Weak completeness is the special case where `Gamma = {}`.

**Three separate logics, three separate theorems**:
- Minimal propositional logic (MPL): K + S + conjunction/disjunction axioms, Kripke semantics with arbitrary `bot_forces`
- Intuitionistic propositional logic (IPL): MPL + EFQ, Kripke semantics with `bot_forces = fun _ => False`
- Classical propositional logic (CPL): IPL + Peirce's law, bivalent semantics

All three share the same `DerivationTree`/`Deriv` infrastructure parameterized over the axiom predicate.

## Findings

### 1. Existing Infrastructure Inventory (from Teammate C, confirmed by Teammates A and B)

CSLib's existing propositional metalogic covers approximately 85-90% of what strong completeness requires:

**Fully in place (no modifications needed)**:
- `DerivationTree Axioms Gamma phi` and `Deriv Axioms Gamma phi` (Hilbert system with list contexts)
- `propDerivationSystem Axioms` (generic `DerivationSystem` instance for all three axiom predicates)
- `deductionTheorem` (parameterized, works for all three logics)
- `prop_lindenbaum` (extends consistent set to MCS via Zorn's lemma)
- `int_prime_exclusion` (extends IntDCCS to prime DCCS excluding a formula, via Zorn's lemma)
- `min_prime_exclusion` (extends MinTheory to prime MinTheory excluding a formula, via Zorn's lemma)
- `canonicalValuation`, `prop_truth_lemma` (classical canonical model machinery)
- `IntCanonicalWorld`, `intCanonicalVal`, `int_truth_lemma` (intuitionistic canonical model)
- `MinCanonicalWorld`, `minBotForces`, `minCanonicalVal`, `min_truth_lemma` (minimal canonical model)
- `iforces_persistence` (monotonicity of forcing under the preorder)
- All three soundness theorems: `prop_soundness`, `int_soundness`, `min_soundness`

**Key file locations**:
- `Cslib/Foundations/Logic/Metalogic/Consistency.lean` -- generic MCS/Lindenbaum
- `Cslib/Logics/Propositional/Metalogic/MCS.lean` -- classical-specific MCS wrappers
- `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` -- IntDCCS/IntPrimeDCCS/prime exclusion
- `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` -- MinTheory/MinPrimeTheory/prime exclusion
- `Cslib/Logics/Propositional/Metalogic/Completeness.lean` -- classical weak completeness
- `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` -- intuitionistic weak completeness
- `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` -- minimal weak completeness

### 2. Missing Ingredients (Gaps)

Four categories of new definitions and theorems must be added:

**Gap 1: `SetDerivable` (shared across all three logics)**
```lean
def SetDerivable (Axioms : PL.Proposition Atom -> Prop)
    (Gamma : Set (PL.Proposition Atom)) (phi : PL.Proposition Atom) : Prop :=
  exists (L : List (PL.Proposition Atom)),
    (forall x in L, x in Gamma) /\ Deriv Axioms L phi
```
Basic lemmas needed: `SetDerivable_of_mem`, `SetDerivable_weakening`, `SetDerivable_of_Derivable`, `SetDerivable_empty_iff_Derivable`.

**Gap 2: Three semantic entailment definitions**

Classical (bivalent):
```lean
def SemanticEntails (Gamma : Set (PL.Proposition Atom)) (phi : PL.Proposition Atom) : Prop :=
  forall v : Valuation Atom, (forall psi in Gamma, Evaluate v psi) -> Evaluate v phi
```

Intuitionistic (Kripke):
```lean
def ISemanticEntails (Gamma : Set (PL.Proposition Atom)) (phi : PL.Proposition Atom) : Prop :=
  forall (World : Type*) [Preorder World] (val : World -> Atom -> Prop),
    (forall {w w' : World} (p : Atom), w <= w' -> val w p -> val w' p) ->
    forall w, (forall psi in Gamma, IForces val (fun _ => False) w psi) ->
      IForces val (fun _ => False) w phi
```

Minimal (Kripke with arbitrary `bot_forces`):
```lean
def MSemanticEntails (Gamma : Set (PL.Proposition Atom)) (phi : PL.Proposition Atom) : Prop :=
  forall (World : Type*) [Preorder World] (val : World -> Atom -> Prop)
    (bot_forces : World -> Prop),
    (forall {w w' : World} (p : Atom), w <= w' -> val w p -> val w' p) ->
    (forall {w w' : World}, w <= w' -> bot_forces w -> bot_forces w') ->
    forall w, (forall psi in Gamma, IForces val bot_forces w psi) ->
      IForces val bot_forces w phi
```

**Gap 3: Three strong soundness theorems**
`SetDerivable Axioms Gamma phi -> SemanticEntails Gamma phi` (and analogues for IPC/MPC). These follow directly from the existing per-formula soundness theorems plus weakening and are low effort.

**Gap 4: Three strong completeness theorems** (the primary deliverable)
`SemanticEntails Gamma phi -> SetDerivable PropositionalAxiom Gamma phi` (and analogues). This is the main new proof work.

### 3. Proof Architecture: Uniform MCS/Lindenbaum Pattern

All three proofs follow the same high-level contrapositive argument:

1. Assume `Gamma |= phi` and `Gamma |-/- phi` (phi not set-derivable from Gamma).
2. Show a consistent/theory set containing all of Gamma can be built that excludes phi.
3. Extend to an MCS / prime DCCS / prime MinTheory via the appropriate Lindenbaum tool.
4. The truth lemma gives a countermodel: all of Gamma holds but phi does not.
5. Contradiction with `Gamma |= phi`.

The logics differ in steps 2-4 only:

| Step | Classical | Intuitionistic | Minimal |
|------|-----------|----------------|---------|
| Set to extend | `Gamma union {neg phi}` | `intDeductiveClosure(Gamma)` | `minDeductiveClosure(Gamma)` |
| Consistency required? | Yes (Peirce's law) | Yes (EFQ case split) | No |
| Lindenbaum tool | `prop_lindenbaum` | `int_prime_exclusion` | `min_prime_exclusion` |
| Extended to | MCS M | Prime DCCS T | Prime MinTheory T |
| Key property | Negation completeness | Disjunction property | Disjunction property |
| Canonical model | `canonicalValuation M` (single world) | `IntCanonicalWorld` at T (multi-world) | `MinCanonicalWorld` at T (multi-world) |
| Truth lemma | `prop_truth_lemma` | `int_truth_lemma` | `min_truth_lemma` |

**Critical subtleties identified by Teammate A**:

- *Classical*: The consistency of `Gamma union {neg phi}` when `phi` is not derivable from `Gamma` requires Peirce's law/DNE. The existing `prop_completeness` proof already contains this argument for the empty-context case; it extends directly to arbitrary `Gamma`.

- *Intuitionistic*: In IPC, `neg neg phi -> phi` fails. The intuitionistic proof requires a case split: if `Gamma` is Int-inconsistent, strong completeness holds trivially via EFQ. If `Gamma` is Int-consistent, `intDeductiveClosure(Gamma)` is a valid IntDCCS and `phi not in intDeductiveClosure(Gamma)` (since phi is not set-derivable). Then `int_prime_exclusion` gives a prime DCCS T excluding phi while containing all of Gamma.

- *Minimal*: The simplest case. `MinTheory` has no consistency requirement, so `minDeductiveClosure(Gamma)` is always a MinTheory regardless of whether Gamma is consistent. `min_prime_exclusion` then applies directly. No case split needed.

**Recommended implementation order**: Minimal first, then intuitionistic, then classical. This reflects increasing proof complexity due to consistency arguments.

### 4. Infrastructure Sharing

The following can be defined once and reused across all three systems:

- `SetDerivable Axioms Gamma phi` -- parameterized over `Axioms`, works for Min/Int/Cl
- `SetDerivable_of_mem` -- membership implies derivability
- `SetDerivable_weakening` -- monotone in `Gamma`
- `SetDerivable_of_Derivable` -- `Derivable Axioms phi -> SetDerivable Axioms {} phi`
- `SetDerivable_empty_iff` -- `SetDerivable Axioms {} phi <-> Derivable Axioms phi`

The semantic entailment definitions, strong soundness theorems, and strong completeness theorems are necessarily logic-specific (three copies each, but structurally parallel).

### 5. Compactness as a Free Corollary

Teammate B's central finding: **the compactness route to strong completeness is circular for propositional logics**. Compactness and completeness are equivalent at this level; proving compactness independently requires the same Lindenbaum/truth lemma machinery as proving completeness directly. There is no efficiency gain from the compactness detour.

The productive relationship runs in the opposite direction: once strong completeness and strong soundness are both established, **compactness follows for free**:

```
strong_completeness: Gamma |= phi -> Gamma |- phi
strong_soundness:    Gamma |- phi -> Gamma |= phi
  =>  Gamma |= phi <-> Gamma |- phi
  =>  Gamma consistent (no finite subset derives bot) <-> Gamma satisfiable
  =>  Gamma finitely satisfiable <-> Gamma satisfiable  (by def of SetDerivable)
  =>  Compactness theorem
```

This should be recorded as a corollary in the implementation, giving CSLib a compactness theorem for each of the three propositional logics at minimal additional cost.

### 6. Algebraic Approach: Deferred to Future Task (Teammate D)

The BimodalLogic project has a substantial algebraic completeness infrastructure (`LindenbaumQuotient.lean`, `BooleanStructure.lean`, `UltrafilterMCS.lean`, ~1,940 lines). CSLib has already ported this infrastructure to `Cslib/Logics/Bimodal/Metalogic/Algebraic/`.

However, this approach is **not recommended for Task 183**:

- **Classical only**: The Boolean algebra construction (`BooleanAlgebra LindenbaumAlg`) relies on `classical_merge` from Peirce's law. It is inherently classical. No analogous construction exists for IPL or MPL in the BimodalLogic codebase.
- **Heyting algebra gap**: The representation theorem for Heyting algebras (Esakia duality) is not in Mathlib. Building it for IPL from scratch would cost ~1,500 lines.
- **Implicative lattice gap**: MPL requires an implicative lattice structure that does not exist in Mathlib. Estimated ~2,000 lines.
- **Cost comparison**: Algebraic approach costs 500-700 lines for classical alone vs. 100-200 lines via the direct approach. For all three logics: ~4,000+ lines algebraic vs. ~600 lines direct.

The algebraic approach is valuable for a future refactoring task that unifies completeness across modal, temporal, and propositional logics via a parametric algebraic framework, but it is out of scope for Task 183.

### 7. Recommended File Organization

Two options, both viable:

**Option A (preferred by Teammate C): Minimal new files**
1. `Cslib/Logics/Propositional/Semantics/SemanticConsequence.lean` -- all 3 semantic entailment defs + `SetDerivable` + basic lemmas
2. `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` -- classical strong soundness + strong completeness
3. `Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean` -- intuitionistic strong soundness + strong completeness
4. `Cslib/Logics/Propositional/Metalogic/MinStrongCompleteness.lean` -- minimal strong soundness + strong completeness

**Option B (preferred by Teammate A): Subdirectory**
1. `Cslib/Logics/Propositional/Metalogic/StrongCompleteness/Defs.lean`
2. `Cslib/Logics/Propositional/Metalogic/StrongCompleteness/Classical.lean`
3. `Cslib/Logics/Propositional/Metalogic/StrongCompleteness/Intuitionistic.lean`
4. `Cslib/Logics/Propositional/Metalogic/StrongCompleteness/Minimal.lean`

Option A aligns better with the existing file organization pattern in CSLib (parallel to existing `Completeness.lean`, `IntCompleteness.lean`, `MinCompleteness.lean`).

### 8. Dependency Graph

```
Existing infrastructure (no changes):
  Consistency.lean -> MCS.lean -> Completeness.lean
  Consistency.lean -> IntLindenbaum.lean -> IntCompleteness.lean
  Consistency.lean -> MinLindenbaum.lean -> MinCompleteness.lean

New files (to be built):
  SemanticConsequence.lean
    |-- SetDerivable (parameterized over Axioms)
    |-- SemanticEntails, ISemanticEntails, MSemanticEntails
    |-- SetDerivable basic lemmas
    v
  MinStrongCompleteness.lean
    |-- Depends: MinLindenbaum.lean, MinCompleteness.lean, SemanticConsequence.lean
    |-- min_strong_soundness (easy)
    |-- min_strong_completeness (main work)
    |-- min_strong_completeness_iff (biconditional)
    |-- min_compactness (corollary)
    v
  IntStrongCompleteness.lean
    |-- Depends: IntLindenbaum.lean, IntCompleteness.lean, SemanticConsequence.lean
    |-- int_strong_soundness (easy)
    |-- int_strong_completeness (main work; includes EFQ case split)
    |-- int_strong_completeness_iff
    |-- int_compactness (corollary)
    v
  StrongCompleteness.lean
    |-- Depends: MCS.lean, Completeness.lean, SemanticConsequence.lean
    |-- prop_strong_soundness (easy)
    |-- prop_strong_completeness (main work; Peirce consistency argument)
    |-- prop_strong_completeness_iff
    |-- prop_compactness (corollary)
```

## Decisions

- **Strategy**: Direct MCS/Lindenbaum approach (unanimous consensus across all four teammates).
- **Implementation order**: Minimal -> Intuitionistic -> Classical (increasing complexity).
- **File organization**: Option A (parallel to existing Completeness files), 4 new files.
- **Compactness**: Prove as corollary of strong completeness + strong soundness, not as an independent prerequisite.
- **Algebraic approach**: Deferred to a future task; document as potential extension only.
- **Weak completeness**: Keep existing proofs in place; do not replace with corollaries from strong completeness (avoids risk and preserves existing stable code).

## Recommendations

1. **Phase 1 (SemanticConsequence.lean)**: Define `SetDerivable`, `SemanticEntails`, `ISemanticEntails`, `MSemanticEntails`, and the four basic `SetDerivable` lemmas. Approximately 80-120 lines. This file has no dependencies on the new completeness files and can be reviewed independently.

2. **Phase 2 (MinStrongCompleteness.lean)**: Implement minimal strong soundness, minimal strong completeness (via `min_prime_exclusion` + `min_truth_lemma`), and the compactness corollary. Approximately 100-150 lines. No consistency case split needed -- this is the cleanest of the three proofs.

3. **Phase 3 (IntStrongCompleteness.lean)**: Implement intuitionistic strong soundness, intuitionistic strong completeness (via `int_prime_exclusion` + `int_truth_lemma`, with EFQ case split), and the compactness corollary. Approximately 120-180 lines.

4. **Phase 4 (StrongCompleteness.lean)**: Implement classical strong soundness, classical strong completeness (via `prop_lindenbaum` + `prop_truth_lemma`, with Peirce-based consistency argument), and the compactness corollary. Approximately 100-150 lines.

5. **Phase 5 (optional biconditionals)**: Add `prop_strong_completeness_iff`, `int_strong_completeness_iff`, `min_strong_completeness_iff` combining strong soundness and strong completeness into biconditionals. Approximately 40-60 lines.

6. **Do not attempt the algebraic approach** for this task. It provides no benefits for IPL/MPL and costs significantly more than the direct approach even for CPL.

## Risks and Mitigations

**Risk 1 (Low): Classical consistency argument**
Showing `Gamma union {neg phi}` is consistent when `phi` is not derivable from `Gamma` requires Peirce's law to go from `(neg phi -> bot) -> bot` to `phi`. The existing `prop_completeness` proof handles the empty-context case; extending to arbitrary `Gamma` is a routine generalization.
*Mitigation*: Reference lines 318-398 of `Completeness.lean` directly; the argument structure is identical.

**Risk 2 (Medium): Intuitionistic case split**
The consistency of `Gamma union {neg phi}` cannot be proved in IPC without Peirce. Instead, a case split on whether `Gamma` is Int-consistent is required. If `Gamma` is inconsistent, strong completeness holds trivially via EFQ.
*Mitigation*: `int_consistent` (the Int axioms are consistent) is already proved. The pattern is `rcases Classical.em (IntConsistent Gamma) with h | h`.

**Risk 3 (Low): Universe polymorphism**
`IValid` and `MValid` use universe parameters. The semantic consequence definitions must match the universe levels used in the canonical model constructions.
*Mitigation*: Follow the universe parameters in `IntCompleteness.lean` and `MinCompleteness.lean` exactly.

**Risk 4 (Low): Set vs. List bridging in SetDerivable**
The proof that `phi in intDeductiveClosure(Gamma) <-> SetDerivable IntPropAxiom Gamma phi` requires unfolding the deductive closure definition against the List-based `Deriv`.
*Mitigation*: This is a direct unfolding; no new infrastructure is needed beyond the definition of `SetDerivable`.

**Risk 5 (None): MCS/Lindenbaum infrastructure**
The generic `set_lindenbaum`, `int_prime_exclusion`, and `min_prime_exclusion` are fully built and sorry-free. No changes needed.

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary (MCS/Lindenbaum direct approach, proof sketches) | completed | high |
| B | Alternatives (compactness route analysis) | completed | high |
| C | Critic (codebase audit, dependency graph, gap analysis) | completed | high |
| D | Horizons (algebraic representation theorem, BimodalLogic prior art) | completed | high |

## Synthesis: Conflicts Resolved

**Conflict 1: Proof strategy for strong completeness**

- Teammate A proposed the direct MCS/Lindenbaum approach.
- Teammate B investigated the compactness route as an alternative.
- *Resolution*: Teammates B and C both confirm the compactness route is not an independent shortcut for propositional logics -- it requires the same infrastructure as the direct approach. The direct MCS approach is unanimous. Compactness is a corollary, not a prerequisite.

**Conflict 2: Implementation order (classical vs. minimal first)**

- Teammate A ordered: Phase 2 minimal, Phase 3 intuitionistic, Phase 4 classical.
- Teammate C assessed classical as "LOW difficulty" (near-trivial lift from existing proof), minimal and intuitionistic as "MEDIUM".
- *Resolution*: The ordering disagreement is apparent, not real. Teammate A recommends minimal first because its Lindenbaum extension is simpler (no consistency side condition). Teammate C's "LOW" for classical refers to the conceptual similarity to the existing weak completeness proof, not the presence of consistency arguments. Minimal-first remains the recommended order: it provides the cleanest initial proof to validate the `SetDerivable` and `MSemanticEntails` infrastructure before tackling the consistency arguments in IPL and CPL.

**Conflict 3: Line count estimates**

- Teammate A estimated 440-660 lines total.
- Teammate B estimated 50-100 lines per logic (excluding definitions).
- Teammate C estimated 400-600 lines total.
- *Resolution*: Teammates A and C are closely aligned. Teammate B's lower estimate excludes the definition file (SemanticConsequence.lean). Synthesized estimate: **400-660 lines** across 4 new files, with the definitions file accounting for ~100 lines and each logic-specific file accounting for ~100-180 lines.

## Synthesis: Coverage Gaps

**Gap 1: Strong soundness proof details**

All teammates noted that strong soundness is needed and is easy, but no teammate provided a detailed proof sketch. Strong soundness states: if there is a finite list L drawn from Gamma that derives phi, then in every model satisfying all of Gamma, phi holds. This follows immediately from the existing per-formula soundness (`prop_soundness`) applied to L (which is a list, not a set), plus noting that all elements of L are in Gamma and hence satisfied.

**Gap 2: Connection between `intDeductiveClosure` and `SetDerivable`**

The proof of intuitionistic strong completeness requires showing `phi in intDeductiveClosure(Gamma) <-> SetDerivable IntPropAxiom Gamma phi`. This equivalence was noted by Teammates A and C but not proven. It is definitional: `intDeductiveClosure(Gamma)` is exactly the set of formulas `phi` such that some finite list drawn from `Gamma` derives `phi`. The implementer should verify the exact definition in `IntLindenbaum.lean` and confirm this holds by unfolding.

**Gap 3: Kripke semantic consequence and persistence at the initial world**

For the multi-world Kripke canonical models (IPL and MPL), the strong completeness proof builds a specific initial world T (a prime DCCS or prime MinTheory) from which all of Gamma is forced. Persistence (`iforces_persistence`) ensures that if phi is forced at T, it is forced at all worlds T' >= T. But `ISemanticEntails` quantifies over ALL worlds in ALL models. The proof must argue that the canonical model with T as the initial world witnesses the failure of `Gamma |= phi`. This argument is standard but requires care in the Lean proof.

## Appendix

### Papers

- Trufas, S. (2024). "Intuitionistic Propositional Logic in Lean." arXiv:2410.23765. Strong completeness for IPL formalized in Lean (both Kripke and algebraic semantics).
- Guo, Y., Chen, J., & Bentzen, B. (2023). "Verified completeness in Henkin-style for intuitionistic propositional logic." arXiv:2310.01916. Henkin-style completeness for IPL in Lean (weak completeness only).
- From, A.H. & Jacobsen, F.J. (2025). "Isabelle/HOL Locales for Completeness a la Fitting." ITP 2025, LIPIcs Vol. 352. Uses compactness route for first-order logic (propositional case: compactness follows from completeness).
- Rasiowa, H. & Sikorski, R. (1963). *The Mathematics of Metamathematics*. PWN/North-Holland. Algebraic completeness, Lindenbaum-Tarski algebras.
- Rasiowa, H. (1974). *An Algebraic Approach to Non-Classical Logics*. North-Holland. Algebraic completeness for intuitionistic and modal logics.
- Chagrov, A. & Zakharyaschev, M. (1997). *Modal Logic*. Oxford. Chapter 7: algebraic semantics for superintuitionistic logics.
- Esakia, L. (2019). *Heyting Algebras: Duality Theory*. Springer. Esakia duality (Heyting algebras vs. Esakia spaces).
- Stone, M.H. (1936). "The theory of representations for Boolean algebras." *Trans. Amer. Math. Soc.*, 40, 37-111.

### Codebases

- FormalizedFormalLogic/Foundation: https://github.com/FormalizedFormalLogic/Foundation (Lean 4 logic formalization, Kripke completeness for superintuitionistic logics)
- Bentzen's IPL formalization: https://github.com/bbentzen/ipl
- BimodalLogic algebraic infrastructure: `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Metalogic/Algebraic/`

### CSLib Key Files

| File | Purpose |
|------|---------|
| `Cslib/Foundations/Logic/Metalogic/Consistency.lean` | Generic `set_lindenbaum`, `DerivationSystem`, MCS properties |
| `Cslib/Logics/Propositional/Metalogic/MCS.lean` | Classical MCS wrappers: `prop_lindenbaum`, `prop_truth_lemma` location is Completeness.lean |
| `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` | `IntDCCS`, `IntPrimeDCCS`, `int_prime_exclusion`, `intDeductiveClosure` |
| `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` | `MinTheory`, `MinPrimeTheory`, `min_prime_exclusion`, `minDeductiveClosure` |
| `Cslib/Logics/Propositional/Metalogic/Completeness.lean` | `canonicalValuation`, `prop_truth_lemma`, `prop_completeness` |
| `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` | `IntCanonicalWorld`, `int_truth_lemma`, `int_completeness` |
| `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` | `MinCanonicalWorld`, `minBotForces`, `min_truth_lemma`, `min_completeness` |
| `Cslib/Logics/Propositional/Semantics/Kripke.lean` | `IForces`, `iforces_persistence`, `IValid`, `MValid` |
| `Cslib/Logics/Propositional/Semantics/Basic.lean` | `Valuation`, `Evaluate`, `Tautology` |
| `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` | `deductionTheorem`, `prop_has_deduction_theorem` |
