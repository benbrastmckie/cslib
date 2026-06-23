# Research Report: Task #280

**Task**: Proof System Triad Gap Analysis
**Date**: 2026-06-23
**Mode**: Team Research (4 teammates)

## Summary

CSLib's propositional proof system infrastructure is substantially mature for the Hilbert and natural deduction legs. The Hilbert system (axioms, derivation, MCS, deduction theorem, algebraic completeness for MPL/IPL/CPL, Kripke completeness, Glivenko, conservative extension) is fully closed with zero sorries — tasks 281-285 completed the Hilbert-primary architecture today. The ND system has a well-designed 10-constructor `Theory.Derivation` (as `Type u`, enabling Curry-Howard), full Hilbert-ND bridges for all three tiers, algebraic completeness, and structural rules. The sequent calculus leg is entirely absent (task 279, not started). Algebraic semantics are comprehensive with Lindenbaum-Tarski algebras, Kripke-algebraic bridges, and full algebraic completeness for all three tiers.

The genuine gaps for completing the proof system triad fall into six areas: (1) ND normalization and the subformula property, (2) Curry-Howard correspondence connecting ND to typed lambda calculus, (3) three-way equivalence theorem post-SC, (4) IPL decidability via cut-free LJ, (5) named Lindenbaum-Tarski algebra instances, and (6) a `Decidable (Derivable PropositionalAxiom φ)` instance. Items (3) and (4) are blocked on task 279 (sequent calculus). Items (1), (5), and (6) are independent and can start immediately.

## Key Findings

### 1. Hilbert System — Fully Closed (No New Tasks Needed)

All four teammates confirm the Hilbert leg is complete:
- Three axiom sets (PropositionalAxiom, IntPropAxiom, MinPropAxiom) with subsumption
- Parameterized derivation trees with height measure
- Deduction theorem, MCS machinery (Lindenbaum, implication property, negation completeness)
- Algebraic completeness for all three tiers (MPL, IPL, CPL) at both Hilbert and ND levels
- Strong soundness/completeness, compactness for CPL (via truth-table), IPL and MPL (via Kripke canonical model)
- Kripke-algebraic bridge, conservative extension (IPL over MPL), Glivenko theorem
- `Decidable (Tautology φ)` instance via Bool evaluation

**Confidence**: High (all teammates agree, zero sorries confirmed)

### 2. Natural Deduction — Strong Core, Missing Proof Theory

The ND system is well-developed as a combinatorial object:
- `Theory.Derivation`: 10 constructors (ax, ass, andI, andE1/2, orI1/2, orE, impI, impE), lives in `Type u`
- Full structural rules: weakening, cut (derived), substitution, atom substitution
- Complete `Theory.Equiv` congruence theory
- Derived rules: botE, negI, negE, topI, dne, iffI, iffE1, iffE2
- Complete Hilbert-ND bridge: `hilbert_iff_nd_ctx` (generic + 3 concrete corollaries per tier)

**Missing — ND Normalization**: No `isNormal` predicate, no `normalize` function, no Prawitz-style normalization theorem, no subformula property. The `Basic.lean` header cites [Prawitz1965] and [SorensenUrzyczyn2006] but only for system design, not for metatheory.

**Missing — Curry-Howard**: No type-theoretic interpretation of `Theory.Derivation`. The STLC formalization exists in `Languages/LambdaCalculus/LocallyNameless/Stlc/` with strong normalization, but there is no bridge between ND proofs and STLC terms. The `Derivation` type being `Type u` (not `Prop`) is precisely the design choice that enables this correspondence.

**Confidence**: High

### 3. Sequent Calculus — Entirely Absent (Task 279 Scope)

No LK or LJ exists for propositional logic. The only sequent calculus in CSLib is CLL (linear logic), which is one-sided with Multiset contexts and has cut elimination as an unimplemented TODO stub.

Task 279 (not started, depends on 280) covers: LK/LJ definition, cut elimination, soundness, completeness, and Hilbert/ND equivalence bridges.

**Critic's Warning**: Cut elimination for two-sided LK is a substantial proof (300-800 lines, 20-40 structural cases). Task 279 may need phasing: (1) LK/LJ definition + structural rules + soundness, (2) cut elimination (Hauptsatz), (3) equivalence bridges. This is a recommendation for task 279's planning phase, not a new task from 280.

**Confidence**: High

### 4. Algebraic Semantics — Comprehensive

Full Lindenbaum-Tarski construction for both ND-based and Hilbert-based quotient algebras. HeytingAlgebra and BooleanAlgebra instances. Kripke-algebraic bridge (`kripkeAlgBridge`). All metatheorems proved. The only gap: named standalone instances for the Lindenbaum algebras of MPL/IPL/CPL are not exported (used only implicitly in completeness proofs).

**Confidence**: High

### 5. Decidability — Present but Partially Disconnected

`instDecidableTautology` provides `Decidable (Tautology φ)` for `[Fintype Atom] [DecidableEq Atom]`. The bridge `prop_completeness_iff_tautology` gives `Tautology φ ↔ Derivable PropositionalAxiom φ`. But no `Decidable (Derivable PropositionalAxiom φ)` instance composes them — a one-liner gap.

For IPL/MPL, decidability requires a decision procedure (e.g., cut-free LJ proof search), which is blocked on task 279.

**Confidence**: High

### 6. Task 266 Status Anomaly

Task 266 shows `status: "implementing"` in state.json despite having a completion_summary and CI-green implementation committed. New tasks should treat 266 as effectively complete for dependency purposes, but the status should be resolved (via `/vet 266` or manual transition) before creating downstream tasks.

**Confidence**: High

## Synthesis

### Conflicts Resolved

1. **Curry-Howard scope** (Critic vs. others): The Critic correctly identified four possible interpretations of "Curry-Howard for ND" (documentation, isomorphism, new STLC, normalization). Resolution: Split into two separate tasks — normalization first (prerequisite), then Curry-Howard correspondence (connecting ND to a typed lambda calculus). The full isomorphism to the existing locally-nameless STLC is complex due to representation mismatch (Finset contexts vs. list contexts); a simpler approach defines the correspondence directly on `Theory.Derivation` with a purpose-built typed term language, or restricts to the {→, ∧} fragment initially.

2. **Cut elimination difficulty** (Critic): Task 279 bundles LK/LJ definition + cut elimination + bridges. The Critic recommends splitting into phases. Resolution: This is a planning recommendation for task 279, not a new task. Document it as context for `/plan 279`.

3. **Named Lindenbaum instances vs. Stone duality** (Teammate B): P5 (named instances, small) is high-value and independent. P6 (Stone duality, large) is mathematical enrichment beyond the triad's metatheoretic purpose. Resolution: Include P5, defer P6.

4. **ND ProofSystem tag types** (Critic): The ND system uses `Theory` parameterization, not tag types like the Hilbert system. No immediate consumer requires tag-type dispatch for ND. Resolution: Do not create a task. If needed later (e.g., for `InferenceSystem` uniform dispatch), it can be added when a concrete downstream use case exists.

### Gaps Identified

No significant gaps remain unaddressed by the proposed tasks. All four teammates converge on the same core gaps (normalization, Curry-Howard, three-way equivalence, IPL decidability).

### Proposed New Tasks

| # | Title | Scope | Dependencies | Independent? |
|---|-------|-------|-------------|--------------|
| P1 | ND normalization and subformula property | Medium | 266 | Yes |
| P2 | Curry-Howard correspondence (propositional ND ↔ typed terms) | Large | P1 | No (needs P1) |
| P3 | Three-way proof system equivalence (Hilbert ↔ ND ↔ SC) | Small | 279 | No (needs 279) |
| P4 | IPL decidability via cut-free LJ proof search | Medium | 279 | No (needs 279) |
| P5 | Named Lindenbaum-Tarski algebra instances for MPL/IPL/CPL | Small | 266 | Yes |
| P6 | `Decidable (Derivable PropositionalAxiom φ)` instance | Tiny | 266 | Yes |

### Dependency Graph

```
[266: Propositional improvements (effectively complete)]
    |
    ├──> P1: ND normalization [MEDIUM, independent]
    |        |
    |        └──> P2: Curry-Howard [LARGE, needs P1]
    |
    ├──> P5: Named Lindenbaum instances [SMALL, independent]
    |
    └──> P6: Decidable (Derivable) instance [TINY, independent]

[279: LK/LJ sequent calculus (not started, depends on 280)]
    |
    ├──> P3: Three-way equivalence [SMALL, needs 279]
    |
    └──> P4: IPL decidability via LJ [MEDIUM, needs 279]
```

**Critical path**: 280 → 279 → P3/P4 (SC-dependent tasks)
**Parallel path**: P1 → P2 (ND proof theory, independent of SC)
**Quick wins**: P5, P6 (small, independent, can start immediately)

### Recommendations

1. **Create P5 and P6 first** — small, high-confidence, zero risk, can merge quickly
2. **Create P1 next** — medium effort, well-understood math, prerequisite for P2
3. **Create P3 and P4 as blocked on 279** — will unblock after SC is complete
4. **Create P2 last** — largest scope, depends on P1, highest technical risk (representation bridging)
5. **Resolve task 266 status** before creating tasks that depend on it
6. **Document sequent representation decision** (two-sided Finset, cf. Critic's analysis) as context for task 279 planning — the choice cascades to bridges, cut elimination feasibility, and LJ formulation

### Strategic Context (from Horizons)

- CSLib has no competitors in the Lean 4 ecosystem for proof system infrastructure (Mathlib has none)
- The triad would make CSLib the first Lean 4 library with LK/LJ formalization
- The propositional triad generalizes to modal/temporal logics via CSLib's typeclass architecture
- The SC can serve as a backend for the planned `hilbert_search` tactic (task 269)
- The triad has pedagogical value as a formally verified proof theory textbook

## Teammate Contributions

| Teammate | Angle | Status | Confidence | Key Contribution |
|----------|-------|--------|------------|------------------|
| A | Primary Audit | completed | high | Comprehensive file inventory (39 files), gap identification with line-level precision |
| B | Gap Analysis & Task Proposals | completed | high | 6 concrete task proposals (P1-P6) with dependencies, Mathlib reuse analysis |
| C | Critic | completed | high | 4 high-risk findings (266 status, Curry-Howard ambiguity, SC representation cascade, cut elimination difficulty) |
| D | Horizons | completed | high | Roadmap alignment, ecosystem positioning, generalization strategy, dependency graph |

## References

- [Prawitz1965] Prawitz, D. (1965). *Natural Deduction: A Proof-Theoretical Study*
- [SorensenUrzyczyn2006] Sorensen, M. & Urzyczyn, P. (2006). *Lectures on the Curry-Howard Isomorphism*
- [Gentzen1935] Gentzen, G. (1935). *Untersuchungen über das logische Schließen*
- CLL template: `Cslib/Logics/LinearLogic/CLL/Basic.lean`
- Existing STLC: `Cslib/Languages/LambdaCalculus/LocallyNameless/Stlc/`
