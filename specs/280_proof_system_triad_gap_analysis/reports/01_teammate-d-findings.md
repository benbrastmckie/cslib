# Teammate D Findings: Horizons — Strategic Alignment and Long-Term Vision

**Task**: 280 — Proof System Triad Gap Analysis
**Angle**: Strategic Alignment and Long-Term Vision
**Date**: 2026-06-23

---

## Key Findings

### 1. The Triad Is Already Structurally Realized — The Gap Is Depth, Not Breadth

CSLib already contains all three proof system *types*: Hilbert (primary, fully developed),
natural deduction (well-scoped, in `NaturalDeduction/`), and sequent calculus (CLL/Basic.lean,
in `LinearLogic/`). What is missing is not the architectural commitment but the *metatheoretic
depth* for each leg:

- **Hilbert**: algebraic completeness and MCS are now Hilbert-primary (tasks 281-285 completed).
  The remaining gap is the Decidable instance for CPL (`Tautology φ` via Hilbert, not just Bool
  evaluation) and any proof-search automation.
- **ND**: the standalone ND system exists in `NaturalDeduction/Basic.lean` with Hilbert-ND
  bridges (`Equivalence.lean`). The gap is normalization (proof reduction, normal forms) and a
  proper Curry-Howard correspondence.
- **SC**: task 279 defines LK/LJ from scratch. The gap is everything: the system definition,
  cut elimination, soundness/completeness, and equivalence bridges to Hilbert and ND.

**Confidence**: high (direct codebase audit).

### 2. Tasks 281-285 Were Executed Today and Resolve the Hilbert Leg Entirely

All five Hilbert-primary tasks (281, 282, 283, 284, 285) were completed on 2026-06-23. The
current state of the Hilbert leg is:

- Hilbert derived structural rules: complete (`HilbertDerivedRules.lean`)
- Hilbert Lindenbaum algebra: complete (`Semantics/Algebra/HilbertLindenbaum.lean`)
- Hilbert algebraic completeness (MPL/IPL/CPL): complete (`HilbertCompleteness.lean`)
- Hilbert-primary conservative extension and Glivenko: complete
- ND metalogic as Hilbert corollaries: complete

This means the Hilbert leg is fully closed. New tasks should **not** touch Hilbert algebraic
completeness or MCS — those are done.

**Confidence**: high (read completion summaries for 281-285).

### 3. The ND Leg Has a Major Unrealized Metatheoretic Opportunity: Curry-Howard

CSLib's ND `Derivation` type is defined as a `Type` (not a `Prop`), which is precisely the
design choice that enables Curry-Howard. The existing `Theory.Derivation` is already a term
(proof term) not just a derivability predicate. However, there is currently no explicit
Curry-Howard statement connecting:

- `Theory.Derivation ∅ A` (an ND proof term of `A`) and
- a term of the corresponding type in the simply typed lambda calculus (`STLC.Typing Γ t τ`)

The STLC formalization in `Languages/LambdaCalculus/LocallyNameless/Stlc/Basic.lean` has
`Typing` as a `Prop`, and `StrongNorm.lean` proves strong normalization via saturated sets.
These live in separate namespaces with no bridge to propositional ND.

The missing bridge: a type isomorphism (or at least a translation) between
`Theory.Derivation ∅ (Proposition.imp A B)` and `STLC.Typing [] t (Ty.arrow τ_A τ_B)`.

This would be the first explicit Curry-Howard correspondence in a mature Lean 4 CS library.

**Confidence**: high (codebase audit shows `Derivation` is a `Type`, STLC `Typing` is `Prop`; no bridge exists).

### 4. SC Cut Elimination Would Be CSLib's First Complete LK/LJ Formalization in Lean 4

A search of Mathlib reveals no LK or LJ sequent calculus formalization. The CLL formalization
in `LinearLogic/CLL/CutElimination.lean` has cut elimination as a TODO with the functions
commented out. Task 279 targets classical LK and intuitionistic LJ.

This positions CSLib as a potential *first mover* for classical/intuitionistic sequent calculus
in the Lean 4 ecosystem. The CLL `Basic.lean` (Multiset-based contexts) provides a strong
template for the syntax layer. The challenge is the cut elimination proof itself, which is
typically the hardest theorem in proof theory formalizations.

**Confidence**: high (Mathlib search confirms no LK/LJ; CLL cut elimination is empty).

### 5. The Triad Has a Clear Generalization Path to Modal and Temporal Logics

The roadmap already anticipates this: Bimodal has a Hilbert proof system and tableau decision
procedure; temporal has a 26-axiom BX Hilbert system. The proof system generalization pattern
in CSLib is through typeclasses (`InferenceSystem`, `MinimalHilbert`, `ModusPonens`, etc.).

For each modal/temporal logic, the triad generalization requires:

- **Modal ND**: no standalone ND for modal logic exists. Adding one would require a modal
  extension of `Theory.Derivation` with a `Box` introduction rule (necessitation).
- **Modal SC**: no modal sequent calculus exists in CSLib or Mathlib. A modal LK would add
  sequent rules for box/diamond. Display calculus or nested sequents are alternatives.
- **Temporal SC**: no temporal sequent calculus is formalized anywhere in CSLib.

The key architectural decision: should modal/temporal SC be built by extending the
propositional LK/LJ from task 279, or should they be standalone? Given CSLib's typeclass
architecture (`InferenceSystem S F`), the LK/LJ design should be parameterized by a formula
type and axiom predicate from the start, mirroring how the Hilbert system is parameterized.

**Confidence**: high (architecture confirmed; no modal/temporal ND or SC found).

---

## Roadmap Alignment Analysis

### Current Roadmap Priorities

The roadmap (`specs/ROADMAP.md`) identifies six remaining items, all in the
bimodal/temporal completeness category (discrete, continuous, dense temporal completeness,
abstract shared completeness). None of these directly concern the proof system triad.

The current `TODO.md` dependency structure shows:

```
Wave 1: ... (propositional / bimodal porting)
Wave 2: ... , 280 [RESEARCHING]
Wave 3: 279 (sequent calculus) [blocked on 280]
```

Task 279 (LK/LJ) depends on task 280 (this research) and nothing else. This means the SC
leg can proceed immediately after this research completes.

### Roadmap Items the Triad Would Unlock

1. **Decidability**: task 266 (implementing) adds `Decidable (Tautology φ)` via Bool evaluation.
   A complete SC with cut elimination would provide an alternative decision procedure via
   proof search in LJ (terminating for PSPACE completeness of IPL, polynomial for CPL via
   tableaux). This is not in the current roadmap but would be a natural follow-on.

2. **Hilbert search tactic (task 269, planned)**: a generic `hilbert_search` tactic is planned
   for `InferenceSystem`. The sequent calculus adds a structural bridge: if LK/LJ is proven
   equivalent to the Hilbert system, then sequent proof search could be used as the backend
   for the `hilbert_search` tactic (sequent backward search terminates; Hilbert proof search
   does not without depth bound).

3. **Conservative extension results**: the Hilbert-primary conservative extension (IPL over MPL)
   is complete. The ND and SC versions would follow as corollaries via bridges, but these
   are low-value tasks. The abstract completeness infrastructure (task 41) would benefit from
   the pattern established by LK/LJ cut elimination.

4. **Teaching and pedagogical value**: CSLib is positioned as a computer science library.
   Having all three propositional proof systems with equivalence proofs creates a rare
   pedagogical resource: a formally verified textbook on proof theory that could support
   courses in logic, programming language theory, and formal methods.

### Items NOT Served by the Triad

The remaining roadmap items (discrete/continuous/dense temporal completeness, abstract
completeness infrastructure) are canonical model constructions, not proof system constructions.
The triad does not accelerate these. They are independent work streams.

---

## Generalization Strategy

### Recommended Abstraction Architecture

The key architectural recommendation is: **parameterize the SC from the start over the
same formula type and axiom predicate that the Hilbert and ND systems already use.**

Concretely:

1. **LK/LJ formula types**: use `PL.Proposition Atom` (the same type used by the Hilbert and
   ND systems). Do NOT define a new formula type.

2. **SC sequent type**: define `LKSequent Atom := Finset (Proposition Atom) × Finset (Proposition Atom)`
   for LK (two-sided). For LJ, restrict the succedent to `Option (Proposition Atom)`.

3. **SC inference rules**: parameterize over a classical/intuitionistic choice, mirroring
   how `Theory.Derivation` is parameterized by a `Theory` that controls EFQ.

4. **SC-to-Hilbert bridge**: `lk_iff_hilbert : LKDerivable ∅ {φ} ↔ Derivable PropositionalAxiom φ`
   This bridge lets all existing Hilbert metalogic corollaries apply to LK.

5. **SC-to-ND bridge**: `lk_iff_nd : LKDerivable ∅ {φ} ↔ DerivableIn MPL.theory φ`
   (via the existing Hilbert-ND bridge, i.e., the SC-ND bridge is the composition).

### Future-Proofing for Modal SC

When modal SC is eventually developed (a separate task stream), the design should:
- Extend `LKSequent` with an optional `Box` rule `Γ ⊢ Δ / □Γ ⊢ □φ`
- Or use a display calculus / nested sequent approach (Kashima, Poggiolesi)
- The key constraint: **modal LK must reduce to propositional LK** when modal rules are dropped

### Curry-Howard Generalization

If a Curry-Howard correspondence is established for propositional ND, the generalization to
modal ND would follow the pattern of typed lambda calculi with modal types (lax logic,
contextual modal type theory, S4-as-staged computation). This is a substantial research
direction that CSLib is not currently positioned to formalize quickly — it requires introducing
new type-theoretic machinery. The recommendation is:

- In the short term: establish the propositional Curry-Howard correspondence
- In the medium term: open a Zulip discussion about whether CSLib should host typed modal
  lambda calculi as a separate module (`Languages/ModalLambda/`)
- Do not try to generalize Curry-Howard to modal logic in the same task as the propositional version

---

## CSLib's Position in the Lean 4 Ecosystem

### What Mathlib Has (for proof theory)

Mathlib does NOT have:
- LK or LJ sequent calculus
- Any completeness proof for classical propositional logic via sequent calculus
- Any Curry-Howard correspondence statement between ND proof terms and typed lambda calculus
- Any cut elimination proof (CLL cut elimination exists as TODO in CSLib; not in Mathlib)

Mathlib DOES have:
- `Mathlib.Logic` — basic logical lemmas, no proof systems
- `Mathlib.Data.Finset.*` — foundational Finset infrastructure for sequent contexts
- `Mathlib.Order.Heyting.Basic` — Heyting algebras (used by CSLib's KripkeBridge)
- `Mathlib.Order.UpperLower.*` — upset algebras (used by CSLib's KripkeBridge)
- No `Mathlib.Logic.ProofTheory.*` namespace exists

**Strategic implication**: CSLib has an opportunity to establish a `Foundations/Logic/ProofTheory/`
namespace in the Lean 4 ecosystem before Mathlib does. Given the roadmap focus on modal/temporal
logics, a strong propositional proof system triad would also make CSLib attractive for
formalization projects in programming language theory (where SC and ND are standard tools).

### Comparison to Coq/Isabelle

| System | CPL Completeness | LK/LJ | ND | Curry-Howard |
|--------|-----------------|-------|-----|-------------|
| Coq (standard library) | No | No | Intrinsic (CIC) | Intrinsic |
| Isabelle/AFP | Yes (many) | Yes (Gentzen) | Yes | Partial (HOL) |
| Mathlib (Lean 4) | No | No | No | No |
| CSLib (current) | Yes (Hilbert-primary) | No | Yes | No |
| CSLib (after triad) | Yes | Yes | Yes | Yes (prop.) |

Isabelle's Archive of Formal Proofs has multiple sequent calculus entries and LK/LJ
formalizations (notably "Sequent Calculus" by Christian Urban, "Natural Deduction and
Sequent Calculus" entries). CSLib should not simply port these but should design with the
CSLib typeclass architecture in mind.

**Confidence**: high (Mathlib search; AFP entries are public knowledge).

---

## Creative Opportunities

### 1. SC as Decision Procedure Backend

Once LJ/LK is proven complete, the sequent proof search is terminating for propositional
logic (LK is PSPACE-complete, but for small formulas, backward proof search finds a proof or
a saturated open branch confirming non-derivability). This means:

```lean
-- Potential future API:
def prop_sc_decide (φ : Proposition Atom) [Fintype Atom] : Decidable (Tautology φ)
```

This would give an alternative, proof-theoretically motivated decidability instance that
complements the Boolean evaluation approach in `Bool.lean`. The SC version would also
*produce a proof term* (cut-free LK derivation) as a certificate.

### 2. Proof Complexity Formalization

Cut elimination length is a well-studied topic (Statman, Krajicek). A non-elementary blowup
from cut proofs to cut-free proofs is provable. Formalizing even the upper bound would be
novel in Lean 4 and fit naturally in a `ProofComplexity.lean` module once the triad is in place.

### 3. Propositional Calculi as a Testing Ground for the `hilbert_search` Tactic

Task 269 (planned) targets a generic `hilbert_search` tactic. The SC provides a natural
completeness guarantee: any propositional tautology has a proof, and backward proof search
in LJ terminates (subformula property). The tactic could use the SC completeness as a
theoretical guarantee, even if the implementation searches in the Hilbert system.

### 4. Showcase for Formal Methods Courses

Having all three proof systems formalized with equivalence bridges creates a unique
*curriculum-grade* artifact. A professor could assign students to prove a tautology using
each of the three systems and verify the result formally. This supports CSLib's broader
community and teaching mission.

---

## Recommended Task Priority Order

### Tier 1: Critical Path (Must Be Done Before Downstream Work)

| Priority | Task | Rationale |
|----------|------|-----------|
| 1 | **LK/LJ Sequent Calculus** (task 279) | Sole remaining triad gap; SC equivalence bridges enable downstream |
| 2 | **ND Normalization and Proof Reduction** (new) | Required for Curry-Howard; ND system is a `Type`, ready for this |

### Tier 2: High Value (Can Proceed in Parallel with Tier 1)

| Priority | Task | Rationale |
|----------|------|-----------|
| 3 | **Curry-Howard Correspondence** (new) | High novelty; connects ND `Derivation` to STLC `Typing` |
| 4 | **SC Decidability Instance** (new) | Complements Bool-based decidability; proof-theoretic motivation |

### Tier 3: Future Extensions (After Tier 1-2 Complete)

| Priority | Task | Rationale |
|----------|------|-----------|
| 5 | **Modal Natural Deduction** (new) | Generalization of ND to modal logics; architecture is ready |
| 6 | **Hilbert Search Tactic** (task 269, planned) | Benefits from SC completeness as guarantee |
| 7 | **SC Proof Complexity Upper Bound** (new) | Research-grade; low priority |

### Parallelization Opportunities

The following tasks can run in parallel once LK/LJ core is complete:
- SC soundness and SC completeness (both reduce to Hilbert)
- SC-to-Hilbert bridge and SC-to-ND bridge (ND bridge is a composition, but can be stated first)

The Curry-Howard task should wait for ND normalization (normalizing ND proof terms is required
to state the type-theoretic correspondence cleanly).

---

## Task Dependency Graph

```
[281-285 COMPLETED: Hilbert primary architecture]
          |
          v
[280: Gap analysis (this task)]
          |
          v
    ┌─────┴──────────────┐
    |                    |
    v                    v
[279: LK/LJ SC]    [NEW: ND Normalization]
(exists, not started)    (new task needed)
    |                    |
    v                    v
[NEW: SC Decidability] [NEW: Curry-Howard]
    |
    v
[269: Hilbert Search Tactic (planned)]
    |
    v
[Future: Modal ND / Modal SC]
```

---

## What This Research Does NOT Recommend

1. **Do not add sorry deferral tasks**: each new task should be completable to zero sorry.
   If cut elimination is too hard for one task, split the task rather than sorry the hard case.

2. **Do not create new formula types for SC**: the existing `PL.Proposition Atom` must be reused.
   Creating a parallel formula type would break the Hilbert-ND-SC bridge and is a debt violation.

3. **Do not generalize the SC to modal logic in the same task as LK/LJ**: the scope of task 279
   is already large (LK, LJ, cut elimination, soundness, completeness, two bridges). Modal SC
   should be a separate task stream opened after task 279 completes.

4. **Do not port Isabelle AFP sequent calculus directly**: the AFP design does not use
   CSLib's typeclass architecture. The design must be native to CSLib's `InferenceSystem` framework.

---

## Confidence Summary

| Finding | Confidence | Evidence |
|---------|-----------|---------|
| Tasks 281-285 close Hilbert leg | High | Completion summaries read directly |
| ND system is `Type`, enabling Curry-Howard | High | `NaturalDeduction/Basic.lean` line 117: `inductive Theory.Derivation ... : Ctx Atom → Proposition Atom → Type u` |
| No LK/LJ in Mathlib or Lean 4 ecosystem | High | Mathlib search, CLL CutElimination.lean is empty TODO |
| SC parameterization strategy is sound | High | Matches existing `InferenceSystem S F` architecture |
| Modal ND/SC would require new tasks | High | No modal ND or SC files found anywhere in CSLib |
| Curry-Howard bridge to STLC requires work | High | STLC `Typing` is `Prop`; ND `Derivation` is `Type`; no bridge |
| Proof complexity formalization is novel | Medium | Based on CSLib/Mathlib search; no AFP equivalents checked directly |
| SC as `hilbert_search` backend is viable | Medium | Subformula property of LJ guarantees termination; implementation TBD |
