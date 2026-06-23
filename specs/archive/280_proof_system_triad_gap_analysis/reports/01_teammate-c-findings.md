# Teammate C Findings: Critic — Blind Spots, Risks, and Scoping Issues
# Task 280: Proof System Triad Gap Analysis

**Angle**: Critic — identify risks, blind spots, conflicts, and prerequisite gaps  
**Date**: 2026-06-23  
**Codebase snapshot**: After tasks 266, 281-285 completed (Hilbert-primary architecture in place)

---

## Key Findings

### Finding 1: Task 266 is "implementing" but completion_summary says "complete" [HIGH RISK]

**Confidence**: High

The `state.json` shows task 266 as `"status": "implementing"` with a full `completion_summary` stating all 6 phases are done and CI is green. The most recent git commits show that implementation actually landed in commit `9fa736f3` and there is a summary file at `specs/266/summaries/01_propositional-foundations-summary.md` confirming all CI passed.

**Risk**: Any new tasks depending on 266 should depend on it as-if-complete, but the status marker may confuse dependency analysis. Any team member who reads `state.json` and sees `[IMPLEMENTING]` may wait before spawning tasks that should start now.

**Recommendation**: Resolve the status discrepancy before creating new tasks. Run `/vet 266` or manually transition to `[PR READY]`. New tasks scoped to propositional ND or sequent calculus should declare `"dependencies": [266]` but not be gated by it operationally.

---

### Finding 2: "Curry-Howard correspondence" for ND is architecturally ambiguous [HIGH RISK]

**Confidence**: High

The task description for 280 lists "natural deduction for the Curry-Howard correspondence" as one of three triad goals. After examining the codebase:

**What exists**: `Theory.Derivation` in `NaturalDeduction/Basic.lean` is `Type u` (not `Prop`). The inductive has 10 constructors: `ax`, `ass`, `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`, `impI`, `impE`. These are structurally the same constructors as simply typed lambda calculus (STLC) terms under the Curry-Howard correspondence. Specifically:
- `impI` corresponds to lambda abstraction
- `impE` corresponds to application
- `andI`/`andE1`/`andE2` correspond to pair/fst/snd
- `orI1`/`orI2`/`orE` correspond to inl/inr/case

**What does NOT exist**: There is no explicit functor/isomorphism between `Theory.Derivation` and any lambda calculus term type in `Cslib`. The `Stlc.Typing` type in `Languages/LambdaCalculus/LocallyNameless/Stlc/Basic.lean` uses a locally nameless representation that is architecturally different from the Finset-context ND derivations.

**The critical ambiguity**: "Curry-Howard for ND" could mean:
1. **Proof terms**: Show `Theory.Derivation` constructions already ARE proof terms (documentation task, no new code)
2. **Isomorphism theorem**: Prove a formal bijection `Theory.Derivation ≅ StlcTyping` (requires reconciling locally nameless Stlc vs. Finset ND)
3. **New STLC formulation**: Define a fresh STLC over `PL.Proposition` as the type language, with full correspondence machinery (new file, non-trivial)
4. **Normalization**: Prove strong normalization for ND derivations (corresponds to termination of STLC reduction)

These four interpretations span from documentation to a multi-month research project. **No task for 280 should be created without first deciding which interpretation is intended.** This is a scoping decision that must come from the task author, not be inferred by implementers.

---

### Finding 3: Sequent calculus representation decision is irreversible and cascades [HIGH RISK]

**Confidence**: High

Task 279 specifies "Finset-based contexts on both sides, following the CLL sequent calculus." Examining the CLL implementation:

```
-- CLL uses: Multiset Proposition (one-sided)
abbrev Sequent Atom := Multiset (Proposition Atom)
inductive Proof : Sequent Atom → Type u
```

CLL is **one-sided** (single multiset). LK is **two-sided** (antecedent + succedent). The task 279 description says "two-sided Gentzen-style" but also says "following CLL as template." These are architecturally different:

| Choice | LK formulation | Pros | Cons |
|--------|---------------|------|------|
| Two-sided `Finset × Finset` | `Γ ⊢ Δ` style | Standard textbook LK | Harder cut-elimination (must handle both sides) |
| Two-sided `List × List` | Multiset without quotienting | Explicit permutation | Structural rules are explicit constructors |
| One-sided `Multiset` | Negation-normal classical sequent | Matches CLL template | Requires negation closure; no intuitionistic LJ |
| Context + conclusion | `Γ ⊢ φ` (single conclusion) | Matches ND style | Not full LK; closer to G1 systems |

**Critical cascade risk**: The sequent representation choice determines:
1. Whether cut-elimination proof is feasible (one-sided CLL-style is significantly simpler)
2. Whether LJ (intuitionistic) can share the representation with LK (it cannot with one-sided)
3. Whether the `Sequent` abbreviation fits `InferenceSystem T (Sequent ...)` from Foundations
4. How bridge theorems `nd_iff_lk`, `hilbert_iff_lk` are stated

The `Theory.Derivation` ND uses `Finset (Proposition Atom) × Proposition Atom` as the sequent. An LK using `Finset × Finset` would have different typing for the `InferenceSystem` instance and require separate bridge lemmas.

**Recommendation**: Before creating any LK/LJ implementation tasks, explicitly decide the representation and document it. The decision cannot be changed without rewriting the entire sequent calculus module.

---

### Finding 4: Cut elimination for LK is a multi-month proof, not a single task [HIGH RISK]

**Confidence**: High

The CLL `CutElimination.lean` is a stub with commented-out TODO proofs:
```lean
-- TODO
-- def Proof.cutAdm ...
-- def Proof.cut_elim ...
```

This is the existing CLL cut elimination — it does not exist yet, and CLL has been in the repository (presumably since its introduction) without cut elimination. For classical propositional LK, Gentzen-style cut elimination (Hauptsatz) is well-understood but involves:
1. Measure definition (proof rank/grade)
2. Key lemma (reduce rank by one step)
3. Inductive argument (double induction on formula complexity and proof height)
4. 20-40 structural cases

In Lean 4, this typically requires 300-800 lines of case analysis depending on the sequent formulation. Even experienced formalizers have reported that this proof takes significant effort (Gentzen1935 itself has a 30-page proof).

**Blind spot in task 280**: Creating a single task "add LK + cut elimination" is likely too coarse. Cut elimination alone should be a separate task from:
- LK definition + basic structural rules
- Soundness with respect to semantics
- Equivalence bridge to Hilbert/ND

**Recommendation**: Split task 279 into at minimum two phases: (1) LK/LJ definition, structural rules, soundness; (2) Cut elimination (Hauptsatz). Treat cut elimination as a research task with unknown difficulty before committing to an implementation task.

---

### Finding 5: ND system has no `ProofSystem` tag type or `InferenceSystem` instance [MEDIUM RISK]

**Confidence**: High

The existing `Foundations/Logic/ProofSystem.lean` defines only Hilbert tag types:
- `Propositional.HilbertMin`, `Propositional.HilbertInt`, `Propositional.HilbertCl`
- Modal, Temporal, Bimodal Hilbert tags

The ND system in `NaturalDeduction/Basic.lean` uses a different `InferenceSystem` instance:
```lean
instance (T : Theory Atom) : InferenceSystem T (Sequent (Atom := Atom)) where
  derivation S := T.Derivation S.1 S.2
```

This instance is parameterized by `Theory`, not by a tag type. There is no opaque `Propositional.NDCl` or similar. If new tasks want to put ND into the `ProofSystem` typeclass hierarchy (with `ClassicalHilbert`-style bundled typeclasses), they would need to:
1. Define ND-specific axiom/rule typeclasses (HasNDImpI, HasNDAnd, etc.)
2. Define tag types (`Propositional.NDMin`, `Propositional.NDInt`, `Propositional.NDCl`)
3. Register instances

**This is missing infrastructure** that would need to be created before ND can participate in the same typeclass dispatch system as Hilbert systems. Whether this is actually needed depends on whether the triad goal requires ND to be dispatched through `ModusPonens`/`ClassicalHilbert` etc.

---

### Finding 6: "Algebraic completeness for MCS" is already done for Hilbert [LOW RISK — MISFRAMING]

**Confidence**: High

The task 280 description lists "Hilbert systems for algebraic completeness and MCS" as a triad goal. After examining the codebase:

**What already exists** (post tasks 281-285 and 266):
- `MPL.hilbert_alg_complete`, `IPL.hilbert_alg_complete`, `CPL.hilbert_alg_complete` — algebraic completeness for Hilbert (in `HilbertCompleteness.lean`)
- `hilbertGlivenko`, `hilbertIplConservativeOverMpl` — Hilbert-primary conservation theorems
- `prop_lindenbaum`, `prop_strong_completeness`, `prop_completeness_iff_tautology` — MCS-based completeness for classical PL
- `min_soundness_completeness`, `int_soundness_completeness` — Kripke completeness for minimal/intuitionistic PL
- `Decidable (Tautology φ)` instance — decidability

**What is genuinely missing from the Hilbert pillar**:
1. No MCS-based strong completeness via Hilbert derivability directly (the existing `prop_strong_completeness` uses `SetDerivable PropositionalAxiom`, which is a Hilbert concept, but it is stated in terms of `SetDerivable` not `DerivableIn (HilbertCl⇓·)`)
2. No Hilbert-tag-based `Completeness` theorem registered against `Propositional.HilbertCl` in the `InferenceSystem` dispatch system

**Risk**: The description of triad goal (1) as "Hilbert systems for algebraic completeness and MCS" may be asking for something that is 90% already done. New tasks for this pillar risk duplicating existing theorems under slightly different names.

---

### Finding 7: Potential merge conflict zone between tasks 266 and 279 [MEDIUM RISK]

**Confidence**: Medium

Task 266 modified:
- `Cslib/Foundations/Logic/Axioms.lean` (added DiaDuality axiom classes)
- `Cslib/Foundations/Logic/Connectives.lean` (added HasDia)
- `Cslib/Foundations/Logic/ProofSystem.lean` (documentation updates)
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` (docstring change)
- `Cslib/Logics/Propositional/Semantics/Bool.lean` (Decidable instance)
- `CslibTests/Propositional.lean` (new tests)

Task 279 would likely create:
- `Cslib/Logics/Propositional/SequentCalculus/Basic.lean` (new directory)
- `Cslib/Logics/Propositional/SequentCalculus/CutElimination.lean`
- Equivalence bridge files connecting to `NaturalDeduction/Basic.lean`

The overlap risk is: bridge files from 279 must `import` from `NaturalDeduction/Basic.lean`. If 266 has changed `Basic.lean` in ways that affect its public API (e.g., renaming lemmas), 279's bridge must use the post-266 API. Since 266 is effectively complete (implementation committed), this is a minor dependency risk, not a merge conflict risk.

**Lower risk than expected**: The actual file sets do not overlap. However, any new tasks creating files that import from both ND and Hilbert systems should verify they use post-266 naming conventions (e.g., `Theory.Derivation`, not some deprecated form).

---

### Finding 8: GenericMCS bridge is documented as NOT working for necessitation [MEDIUM RISK]

**Confidence**: High

Task 266 Phase 5 created `GenericMCSBridge.lean` and documented that `algebraicDerivationSystem` cannot replace `modalDerivationSystem` for necessitation-requiring MCS properties. This is a genuine architectural gap.

**Impact on 280's triad goal (1)**: If "Hilbert systems for MCS" includes extending MCS reasoning to the modal/temporal/bimodal Hilbert systems registered in `ProofSystem.lean`, then the GenericMCS bridge gap is a blocking dependency. The propositional Hilbert MCS works via `propDerivationSystem`. Modal MCS requires `modalDerivationSystem`. These cannot currently be unified.

**Recommendation**: New tasks scoped to "MCS for Hilbert systems" should explicitly state whether they address only propositional Hilbert (feasible now) or modal/temporal Hilbert (blocked by GenericMCS gap).

---

## Architectural Concerns

### Concern A: Two Lindenbaum algebras (ND-based and Hilbert-based) coexist

`Lindenbaum.lean` defines the ND-based Lindenbaum algebra over `DerivableIn T ({A} ⊢ B)`. `HilbertLindenbaum.lean` defines the Hilbert-based version over `Deriv Axioms`. Both exist and both are used. The ND version underpins `Theory.alg_complete`; the Hilbert version underpins `MPL.hilbert_alg_complete`.

Any new "bridge" task that claims to connect ND algebraic completeness to Hilbert algebraic completeness must navigate both Lindenbaum constructions. The current bridge (`derivableInMplIffDerivableMin` etc.) routes through algebra, not through a direct Lindenbaum quotient isomorphism.

### Concern B: Universe polymorphism assumptions

`MPL.hilbert_alg_complete` uses `GHAValid.{u, u}` with matching universe levels. The `Theory.Derivation` uses `universe u` for atoms. If any new task tries to bridge the two Lindenbaum algebras at the type level, it must carefully manage universe levels. The current algebraic route avoids this by going through `Prop`-valued validity predicates.

### Concern C: `DecidableEq Atom` constraint asymmetry

The ND system requires `[DecidableEq Atom]` (for `Finset.insert` operations). The Hilbert system does not (`MPL.hilbert_alg_complete` has no `DecidableEq` constraint). The Hilbert-ND bridge theorems (`hilbert_iff_nd_min` etc.) are in a context with `[DecidableEq Atom]`.

Any sequent calculus that uses `Finset` contexts (as task 279 specifies) will also need `[DecidableEq Atom]`. Bridge theorems to Hilbert will have this extra constraint. This is a minor annoyance, not a blocker.

### Concern D: `ProofSystem` typeclass is Hilbert-only; ND has no equivalent bundle

If the triad goal is to unify all three proof systems under a common typeclass (e.g., a `HasND` or `HasSC` that mirrors `ClassicalHilbert`), that typeclass does not exist. The ND system is parameterized by a `Theory`, not by tag types. Creating tag-based ND dispatch would require:
1. Defining `Propositional.NDMin`, `Propositional.NDInt`, `Propositional.NDCl` tag types
2. Defining `NDDerivation`-parameterized typeclasses (`HasNDImpI`, `HasNDAnd`, etc.)
3. Registering instances

This is substantial infrastructure work that has no obvious payoff unless the triad goal explicitly requires uniform dispatch.

---

## Overlap Analysis (Tasks 266, 279, and New Tasks)

### What 266 completed (verified from git history and summary)

- Documentation fixes in Foundations/Logic/{ProofSystem,InferenceSystem,Axioms,Connectives}.lean
- `HasDia` primitive added to Connectives.lean
- `AxiomDiaDualityFwd`, `AxiomDiaDualityBack` added to Axioms.lean
- `Decidable (Tautology φ)` instance in Semantics/Bool.lean
- `PropositionalTableau.lean` created in Foundations/Logic/
- `GenericMCSBridge.lean` created in Modal/Metalogic/ (gap analysis only, no proof)
- `CslibTests/Propositional.lean` created

### What 279 would touch (not yet started)

New files in `Cslib/Logics/Propositional/SequentCalculus/`:
- `Basic.lean` (LK/LJ definition)
- `CutElimination.lean` (Hauptsatz)
- `Equivalence.lean` (bridges to Hilbert and ND)

Imports from existing files:
- `Cslib.Logics.Propositional.Defs` (formula type)
- `Cslib.Logics.Propositional.NaturalDeduction.Basic` (for ND bridge)
- `Cslib.Foundations.Logic.InferenceSystem` (for InferenceSystem instance)

### Conflicts / ordering constraints

1. **266 must be PR-complete before 279 merges**: 279's bridge must use the post-266 ND API. If 266's changes to `NaturalDeduction/Basic.lean` (docstring only) are still in a local branch, 279 could create a merge conflict if it also touches `Basic.lean`.

2. **New tasks from 280 must not re-implement what 266 completed**: The Decidable instance, HasDia, PropositionalTableau, and algebraic completeness corollaries are done. New tasks should not duplicate these.

3. **Task 279 depends on 280 (per state.json)**: This is a research gate — 279 cannot start until 280 decides the design. This is correct ordering.

4. **No conflict between 279 and Hilbert files**: 279 creates a new directory; it does not modify ProofSystem.lean, Instances.lean, or any Hilbert-system files.

---

## Recommendations

### What to decide BEFORE creating new tasks

1. **Resolve task 266 status**: It is implemented but status shows `implementing`. Either vet it, mark PR READY, or confirm its deliverables are visible to downstream tasks. This is a blocking prerequisite for accurate dependency graphs.

2. **Nail down "Curry-Howard for ND"**: Decide among four interpretations (documentation, isomorphism theorem, new STLC formulation, normalization). The granularity and feasibility of any new task depends on this decision.

3. **Decide the sequent calculus representation**: One-sided vs. two-sided; `Finset` vs. `Multiset` vs. `List`. Document the choice in the task description before implementation begins. A wrong choice cannot be cheaply corrected.

4. **Separate cut elimination into its own task**: Do not bundle LK definition + cut elimination + bridges into one task. Cut elimination alone has unknown difficulty in Lean 4 for two-sided LK with `Finset` contexts.

### Recommended task granularity

| Proposed task | Scope | Effort estimate | Risk |
|---------------|-------|-----------------|------|
| LK/LJ definition + structural rules + soundness | ~200 lines | 4-6h | Low (mechanical) |
| LK cut elimination (Hauptsatz) | ~400-800 lines | 10-20h | High (unknown Lean 4 difficulty) |
| Hilbert ↔ LK equivalence bridges | ~100 lines | 2-4h | Medium (depends on representation) |
| ND ↔ LK equivalence bridges | ~100 lines | 2-4h | Medium (depends on representation) |
| Curry-Howard: proof term extraction | ~200 lines | 4-8h | Medium (representation mismatch with Stlc) |
| ND normalization (if required) | ~500+ lines | 20+h | High (research-level) |

### Do NOT create tasks for

- Re-implementing algebraic completeness (already done in 266/281-285)
- Re-implementing strong completeness (already in StrongCompleteness.lean)
- Re-implementing Glivenko/conservative extension (already in HilbertConservativeGlivenko.lean)
- Adding `ProofSystem` tag instances for ND unless there is a concrete downstream consumer

---

## Confidence Summary

| Finding | Confidence | Basis |
|---------|-----------|-------|
| Task 266 status mismatch | High | state.json + git log |
| Curry-Howard ambiguity | High | No Stlc↔ND functor in codebase |
| Sequent representation irreversibility | High | CLL architecture + LK theory |
| Cut elimination difficulty | High | CLL stub; known complexity |
| ND has no ProofSystem tag | High | ProofSystem.lean + Instances.lean |
| Hilbert algebraic completeness already done | High | HilbertCompleteness.lean + summary |
| Conflict risk between 266 and 279 | Medium | Low file overlap |
| GenericMCS gap blocks modal MCS | High | GenericMCSBridge.lean documentation |
