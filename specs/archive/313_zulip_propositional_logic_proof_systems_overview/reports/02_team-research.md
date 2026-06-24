# Research Report: Task #313

**Task**: Zulip propositional logic proof systems overview
**Date**: 2026-06-23
**Mode**: Team Research (4 teammates)

## Summary

CSLib's propositional logic layer implements four distinct proof systems — Hilbert, Natural Deduction, Sequent Calculus (LK/LJ), and Tableau — across three logics (minimal, intuitionistic, classical). Each system exposes a different structural dimension: algebraic completeness (Hilbert), computational content (ND), structural proof theory (SC), and algorithmic decision procedures (Tableau). The equivalence theorems between systems are the machinery that lets results migrate freely. This report synthesizes a detailed codebase inventory, cross-system bridge analysis, gap identification, and strategic vision for a Zulip post.

## Current State: Complete Inventory

### Status Matrix

| System | Minimal (MPL) | Intuitionistic (IPL) | Classical (CPL) | Sorry Count |
|--------|:---:|:---:|:---:|:---:|
| **Hilbert** (ProofSystem/) | COMPLETE | COMPLETE | COMPLETE | 0 |
| **Natural Deduction** (NaturalDeduction/) | COMPLETE | COMPLETE | COMPLETE | 0 |
| **Sequent Calculus LK** (SequentCalculus/LK/) | — | — | COMPLETE | 0 (but CutElim excluded from build) |
| **Sequent Calculus LJ** (SequentCalculus/LJ/) | — | COMPLETE | — | 1 (cutAdmissibility) |
| **Tableau Classical** (Tableau/Classical/) | — | — | IN PROGRESS | ~8 sorry |
| **Tableau Intuitionistic** (Tableau/Intuitionistic/) | — | IN PROGRESS | — | ~6 sorry |
| **Tableau Minimal** (Tableau/Minimal/) | IN PROGRESS | — | — | 2 sorry |
| **Metalogic** (Metalogic/) | COMPLETE | COMPLETE | COMPLETE | 0 |
| **Algebraic Semantics** (Semantics/Algebra/) | — | COMPLETE | COMPLETE | 0 |
| **Conservative Extensions** (Semantics/Algebra/) | — | COMPLETE | PARTIAL (Glivenko) | 0 |

### Line Counts (sorry-free code)

| Component | Files | Lines | Status |
|-----------|:---:|:---:|:---:|
| Hilbert ProofSystem | 6 | 1,197 | Complete |
| Natural Deduction | 5 | 1,998 | Complete |
| Sequent Calculus LK | 4 | 1,632 | Complete (CutElim build-excluded) |
| Sequent Calculus LJ | 4 | 828 | Near-complete (1 sorry) |
| Tableau (all variants) | 11 | ~1,900 | In progress (~16 sorry) |
| Algebraic Semantics | 22 | 5,295 | Complete |
| Metalogic | 8 | ~2,000 | Complete |
| ProofSystemEquivalence | 1 | 126 | Complete |
| **Total** | **~61** | **~15,000** | |

## The Four Proof Systems

### 1. Hilbert System — The Algebraic Hub

**Architecture**: Parameterized over axiom predicates (`MinPropAxiom`/8, `IntPropAxiom`/9, `PropositionalAxiom`/10) with a single inference rule (modus ponens). The subsumption chain MPL ⊂ IPL ⊂ CPL is formally proved.

**Unique strengths**:
- Algebraic completeness: MPL ↔ GHA-validity, IPL ↔ HA-validity, CPL ↔ BA-validity
- Conservative extension proofs route through algebraic constructions (`WithBot`, `LowerSet`, `NonemptyLowerSet`)
- Fewest rules → easiest to establish soundness for new semantics
- Lindenbaum–Tarski algebra as a computable quotient type
- Fragment axiom predicates (`ImpAxiom`, `ConjImpAxiom`, `ConjImpBotAxiom`) support the conservative extension chain

**Best for**: Algebraic completeness, inter-logic conservativity, Glivenko's theorem.

### 2. Natural Deduction — The Computational Substrate

**Architecture**: 10-constructor inductive `Theory.Derivation` with `Finset` contexts. Logic strength controlled by theory parameter: empty = MPL, +EFQ = IPL (`[IsIntuitionistic T]`), +DNE = CPL (`[IsClassical T]`).

**Key design decision**: EFQ is a theory axiom, not a primitive constructor. This cleanly separates the three logics while sharing one `Proposition` type with modal/temporal extensions.

**Unique strengths**:
- Derivations are programs (Curry-Howard substrate, task 293 planned)
- Explicit derivation trees, not just derivability predicates
- Foundation for normalization (task 290 planned) and subformula property
- Most natural proof style for humans

**Best for**: Computational content, program extraction, constructive proofs.

### 3. Sequent Calculus — The Structural Mirror

**LK (Classical)**: All-additive Finset-based, 11 constructors, following Negri–von Plato. Cut elimination proved (873-line proof, zero sorry) **but currently excluded from the build due to unresolved build errors** (commented out in `LK.lean`). Soundness, completeness, and the Hilbert↔LK bridge are sorry-free and active.

**LJ (Intuitionistic)**: Single-conclusion sequents (`Γ ⊢ A`), 11 constructors. `cutAdmissibility` has 1 sorry (nested well-founded induction). The three-way IPL equivalence is independent of cut elimination and is sorry-free. Cut elimination is an independent structural property.

**Key structural insight**: The difference between LK (multi-conclusion) and LJ (single-conclusion) is exactly the structural signature of classical vs. intuitionistic logic.

**No minimal sequent calculus (LM) exists** — explicitly acknowledged in `ProofSystemEquivalence.lean`.

**Unique strengths**:
- Cut elimination → subformula property → bounded proof search → decidability
- Craig interpolation (future target)
- Structural comparison of logic strengths via succedent structure

**Best for**: Structural proof theory, decidability proofs, interpolation.

### 4. Tableau — The Decision Engine

**Architecture**: Generic signed-formula framework from `Foundations/Logic/Tableau/` with three closure conditions: `ClassicalClosure` (T(⊥) or T(p)/F(p)), `IntuitionisticClosure` (T(⊥) at any world), `MinimalClosure` (T(p)/F(p) for atoms only).

**Classical**: Single-world (L = Unit). Expansion rules in `classicalApplyOne`.
**Intuitionistic**: Multi-world (L = Nat). World-creating rules for F(φ→ψ) with persistence.
**Minimal**: Reuses intuitionistic expansion with `MinimalClosure`. T(⊥) does NOT close.

**All three have sorry-dependent Decidable instances**:
- `instDecidableTautologyTableau` (classical; `instDecidableTautology` in `Bool.lean` is the sorry-free fallback)
- `instDecidableIValid` (intuitionistic; **no sorry-free fallback exists** — this is novel)
- `instDecidableMValid` (minimal; **no sorry-free fallback exists** — this is novel)

**Sorry status**: ~16 sorry across 5 files. Pattern is uniform: loop induction for soundness, truth lemma + countermodel extraction for completeness.

**Minimal tableau**: Only `DecisionProcedure.lean` exists (no standalone Soundness/Completeness files). Task 319 will create these.

**Infrastructure reuse**: Designed for extension to modal (tasks 299/300) and temporal (task 301) tableau.

**Best for**: Decision procedures, countermodel generation, mechanizable proof search.

## Cross-System Equivalences

### Established Chains (sorry-free)

```
CPL:  Hilbert ↔ ND ↔ LK ↔ Tautology ↔ BAValid
      [hilbert_iff_nd_cl]  [nd_iff_lk]  [lk_iff_tautology]  [HilbertCompleteness]

IPL:  Hilbert ↔ ND ↔ LJ ↔ IValid ↔ HAValid
      [hilbert_iff_nd_int]  [nd_iff_lj]  [lj_iff_ivalid]  [HilbertCompleteness]

MPL:  Hilbert ↔ ND ↔ MValid ↔ GHAValid
      [hilbert_iff_nd_min]  [min_soundness_completeness]  [HilbertCompleteness]
```

### TFAE Theorems (ProofSystemEquivalence.lean)

- `cplProofSystemsTfae`: CPL three-way (Hilbert ↔ ND ↔ LK)
- `iplProofSystemsTfae`: IPL three-way (Hilbert ↔ ND ↔ LJ)
- `mplHilbertIffNd`: MPL two-way (Hilbert ↔ ND)

### Bridge Mechanism

The Hilbert↔ND bridge uses a generic `MinimalAxioms` typeclass with 6 concrete instantiations (context-based and closed, for all three logics). The ND↔SC bridges compose structural translations (`ndToLK`/`ndToLJ`) with semantic completeness.

### Pending Equivalences

| Missing Link | Status | Priority |
|---|---|---|
| Tableau ↔ Hilbert (all three logics) | Blocked on ~16 sorry in soundness/completeness | HIGH |
| LJ cut elimination | 1 sorry in `cutAdmissibility` | MEDIUM |
| LK cut elimination build integration | File exists (0 sorry) but excluded from build | MEDIUM |
| Minimal sequent calculus (LM) | Not planned | LOW |
| Tableau ↔ SC direct bridge | Not planned | LOW (transitivity via Hilbert suffices) |

## Conservative Extension Chain

### Proven Results (all sorry-free)

| Theorem | Statement | Method |
|---|---|---|
| `hilbertIplConservativeOverMpl` | IPL conservative over MPL for bot-free formulas | `WithBot` GHA embedding |
| `hilbertIplConservativeOverConjImp` | IPL conservative over IPL⟨∧,→,⊤⟩ for or-bot-free formulas | `LowerSet` Brouwerian |
| `hilbertIplConservativeOverConjImpBot` | IPL conservative over IPL⟨∧,→,⊥,⊤⟩ for or-free formulas | `NonemptyLowerSet` HA |
| `hilbertGlivenko` / `glivenko` | CPL ⊢ φ → IPL ⊢ ¬¬φ | Regular elements of Heyting algebra |

**Key insight**: Each conservativity result requires a distinct algebraic model construction. This is the algebraic layer's unique contribution.

### Chain Status

```
IPL⟨→,⊤⟩ ⊂ IPL⟨∧,→,⊤⟩ ⊂ IPL⟨∧,→,⊥,⊤⟩ ⊂ MPL ⊂ IPL ⊂ CPL
  [task 311]    [DONE]         [DONE]        [DONE]  [Glivenko]
  (awaits Diego)
```

**Gaps**:
- IPL conservative over IPL⟨→,⊤⟩ (task 311, depends on Diego embedding task 310 [IMPLEMENTING])
- Unified chain module (task 312, depends on 311)
- CPL/IPL: Glivenko gives ¬¬-translation, not full conservativity. This is the standard result but weaker than "CPL conservative over IPL for IPL formulas"

## Synthesis: Conflicts and Resolutions

### Conflict 1: Sorry Counts

Teammates reported different sorry counts for the tableau (A: "~8/~6/2", C: "11 total across 5 files"). After cross-referencing, Teammate C's count of 11 substantive sorries is more precise — it counts unique proof obligations rather than `sorry` keyword occurrences (some files have structural sorry propagation). **Resolution**: Use ~16 total sorry keyword occurrences, ~11 unique proof obligations.

### Conflict 2: LK Cut Elimination Status

Teammate A reported LK as "COMPLETE — 0 sorry". Teammate C identified that `CutElimination.lean` is excluded from the build. **Resolution**: The proof exists and has 0 sorry, but is commented out of `LK.lean` due to build errors. For the Zulip post, this should be stated precisely: "proved but not yet integrated into the build."

### Conflict 3: LJ Cut Elimination

Teammate A reported 1 sorry. Teammate D stated "cut elimination proven" for LJ. Teammate C clarified that `LJProof.cutElim` calls `cutAdmissibility` which has 1 sorry. **Resolution**: LJ cut elimination is *stated* with 1 sorry in the core lemma. The three-way IPL equivalence is independent of this and is sorry-free. These are separate claims.

### Conflict 4: Decidable Instances

Teammates A and D emphasized the tableau `Decidable` instances as novel contributions. Teammate C correctly noted these are sorry-dependent. **Resolution**: The instances are architecturally novel (especially `IValid` and `MValid` which have no alternative sorry-free fallback) but depend on completing the tableau soundness/completeness proofs.

## Gaps Identified

### Critical
1. **LK CutElimination build exclusion** — 873-line sorry-free proof excluded from build. Must determine if build errors are cosmetic (API drift) or substantive before the Zulip post.

### Important
2. **16 tableau sorries** — soundness/completeness proofs for all three logics need completion (tasks 316/317/319)
3. **No tableau↔SC bridge** — not strictly needed (transitivity through Hilbert suffices) but would strengthen the equivalence story
4. **No minimal sequent calculus** — MPL achieves only Hilbert↔ND, not four-way equivalence
5. **Conservative chain incomplete** — task 311 (Diego) and task 312 (unified chain) pending
6. **LJ cutAdmissibility sorry** — nested well-founded induction challenge

### Nice-to-have
7. No formal LK↔LJ comparison theorem
8. Minimal tableau needs standalone Soundness/Completeness files (task 319)

## Recommendations

### For the Zulip Post

The most compelling narrative is not "we have four proof systems" but:

> **"Four independently implemented proof systems are proven equivalent, and this equivalence is the mechanism by which algebraic results, structural proof theory, and computational decision procedures communicate."**

Structure the post around:
1. **What exists** — Hilbert, ND, LK, LJ are all sorry-free for soundness, completeness, and equivalence. Tableau infrastructure in place with decision procedures.
2. **The equivalence thesis** — TFAE theorems package three-way equivalences. Choose the right tool for the job.
3. **The conservative extension chain** — Algebraic methods proving fragment conservativity, Glivenko's theorem via regular elements of Heyting algebras.
4. **What's in progress** — Tableau soundness/completeness, Diego embedding, LK cut elimination build integration, LJ cut elimination.
5. **The trajectory** — Propositional as foundation for modal/temporal tableau (tasks 299/300/301), Curry-Howard (task 293), normalization (task 290).

### Honest Framing

- LK cut elimination: "proved but currently excluded from the build"
- LJ cut elimination: "stated, 1 sorry in the core lemma; the three-way equivalence is independent"
- Tableau: "algorithm infrastructure complete, mathematical proofs in progress"
- Conservative extensions: "three results proved, two more planned"
- Decidable(IValid)/Decidable(MValid): "structurally novel, depend on completing tableau proofs"

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Full inventory of all systems | completed | high |
| B | Cross-system bridges and conservative extensions | completed | high |
| C | Gaps, inconsistencies, blind spots | completed | high |
| D | Strategic vision and narrative framing | completed | high |

## References

All findings are based on direct source reads from the CSLib codebase. Key files:
- `Cslib/Logics/Propositional/ProofSystemEquivalence.lean` — TFAE theorems
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` — Hilbert↔ND bridges
- `Cslib/Logics/Propositional/SequentCalculus/LK/` and `LJ/` — Sequent calculus
- `Cslib/Logics/Propositional/Tableau/` — Three tableau variants
- `Cslib/Logics/Propositional/Semantics/Algebra/` — Algebraic semantics and conservative extensions
- `Cslib/Logics/Propositional/Metalogic/` — MCS/Lindenbaum completeness proofs
