# Research Report: Task #314 -- LK Classical Sequent Calculus

**Task**: 314 -- Implement the classical sequent calculus LK for propositional logic
**Date**: 2026-06-23
**Session**: sess_1782245580_188995_314
**Parent**: Task 279 (expanded)

## Summary

This report provides the detailed research backing for implementing LK (classical propositional sequent calculus) in CSLib. The implementation creates 5 new files under `Cslib/Logics/Propositional/SequentCalculus/`, reusing the existing `Proposition` type, `Proposition.complexity`, `InferenceSystem` typeclass, `Theory.Derivation` (ND), and `hilbert_iff_nd_ctx` bridge. The recommended design is an all-additive Finset-based two-sided sequent calculus following G3cp (Negri & von Plato 2001), with cut elimination via lexicographic induction on (formula complexity, height sum) following Troelstra & Schwichtenberg (2000, Ch. 4). Completeness is obtained as a corollary through bridge composition with existing Hilbert completeness.

## Literature Proof Structure

### Primary Reference: G3cp Rules (Negri & von Plato 2001, Ch. 3)

The G3cp calculus has these features:
1. **Sequents**: `Gamma => Delta` where both sides are finite multisets (in our case, Finsets -- exchange/contraction free)
2. **Logical axiom**: `P, Gamma => Delta, P` (atomic P only in G3cp; we use `A in Gamma` and `A in Delta` for any formula)
3. **No structural rules as explicit rules**: weakening, contraction, exchange are admissible

**G3cp Rules (transcribed to CSLib notation)**:

| Rule | Premise(s) | Conclusion |
|------|-----------|------------|
| `ax` | -- | `{A} => {A}` |
| `botL` | -- | `{bot} ∪ Gamma => Delta` |
| `andL` | `{A, B} ∪ Gamma => Delta` | `{A ∧ B} ∪ Gamma => Delta` |
| `andR` | `Gamma => {A} ∪ Delta` and `Gamma => {B} ∪ Delta` | `Gamma => {A ∧ B} ∪ Delta` |
| `orL` | `{A} ∪ Gamma => Delta` and `{B} ∪ Gamma => Delta` | `{A ∨ B} ∪ Gamma => Delta` |
| `orR` | `Gamma => {A, B} ∪ Delta` | `Gamma => {A ∨ B} ∪ Delta` |
| `impL` | `Gamma => {A} ∪ Delta` and `{B} ∪ Gamma => Delta` | `{A → B} ∪ Gamma => Delta` |
| `impR` | `{A} ∪ Gamma => {B} ∪ Delta` | `Gamma => {A → B} ∪ Delta` |
| `weakL` | `Gamma => Delta` | `{A} ∪ Gamma => Delta` |
| `weakR` | `Gamma => Delta` | `Gamma => {A} ∪ Delta` |
| `cut` | `Gamma => {A} ∪ Delta` and `{A} ∪ Gamma' => Delta'` | `Gamma ∪ Gamma' => Delta ∪ Delta'` |

**Key structural results** (Negri & von Plato 2001, Theorems 3.1.1, 3.2.1-3.2.3):
1. Height-preserving invertibility of all rules (Theorem 3.1.1)
2. Height-preserving weakening admissibility (Theorem 3.2.1)
3. Height-preserving contraction admissibility (Theorem 3.2.2)
4. Cut admissibility (Theorem 3.2.3)

### Cut Elimination Strategy (Troelstra & Schwichtenberg 2000, Ch. 4)

**Definition 4.1.1**: The *level* of a cut is the sum of the depths (heights) of the derivations of the premises; the *rank* (or *cut-rank*) of a cut on formula `A` is `|A| + 1` where `|A|` is the complexity of `A`.

**Theorem 4.1.5 (Hauptsatz)**: Cut elimination holds for G3c + Cut.

**Proof structure** (three cases):
1. **Case 1**: At least one premise is an axiom -- immediate simplification
2. **Case 2**: Cut formula is not principal in either premise -- push cut upward, level decreases
3. **Case 3**: Cut formula is principal in both premises -- replace by cuts on subformulas, rank decreases

**Termination argument**: Lexicographic induction on `(rank, level) = (complexity(A) + 1, height_left + height_right)`. The rank strictly decreases in Case 3 (principal); the level strictly decreases in Cases 1 and 2 with rank bounded.

### ND-SC Translation (Negri & von Plato 2001, Ch. 6-8)

The ND-to-SC direction translates each ND constructor to a sequence of SC steps:
- ND `ax` (theory axiom) -> SC axiom followed by weakening
- ND `ass` (assumption) -> SC axiom
- ND `andI` -> SC `andR` on the two subderivations
- ND `andE1`/`andE2` -> SC `andL` then axiom
- ND `orI1`/`orI2` -> SC `orR` then axiom
- ND `orE` -> SC `orL` on the case derivations, using cut to connect
- ND `impI` -> SC `impR`
- ND `impE` -> SC `impL` with cut

The SC-to-ND direction uses the ND cut rule (`Theory.Derivation.cut`) and the existing ND weakening.

## Reuse Check Results

### Existing CSLib Infrastructure (All Confirmed Present)

| Component | Location | Status |
|-----------|----------|--------|
| `Proposition Atom` type | `Cslib/Logics/Propositional/Defs.lean` | Lines 81-92 |
| `Proposition.complexity` | `Cslib/Logics/Propositional/Tableau/Defs.lean` | Lines 125-131 |
| `InferenceSystem` typeclass | `Cslib/Foundations/Logic/InferenceSystem.lean` | Lines 42-48 |
| `Theory.Derivation` (ND) | `Cslib/.../NaturalDeduction/Basic.lean` | Lines 117-146 |
| `Theory.Derivation.weak` | `Cslib/.../NaturalDeduction/Basic.lean` | Lines 207-221 |
| `Theory.Derivation.cut` | `Cslib/.../NaturalDeduction/Basic.lean` | Lines 252-256 |
| `hilbert_iff_nd_ctx` | `Cslib/.../NaturalDeduction/Equivalence.lean` | Lines 332-343 |
| `hilbert_iff_nd_ctx_cl` | `Cslib/.../NaturalDeduction/Equivalence.lean` | Line 364-367 |
| `AxiomTheory` | `Cslib/.../NaturalDeduction/Equivalence.lean` | Lines 85-86 |
| `PropositionalAxiom` | `Cslib/.../ProofSystem/Axioms.lean` | Lines 48-78 |
| `Evaluate` / `Tautology` | `Cslib/.../Semantics/Bool.lean` | Lines 57-81 |
| `prop_soundness` | `Cslib/.../Metalogic/Soundness.lean` | Lines 63-77 |
| `Ctx Atom = Finset (Proposition Atom)` | `Cslib/.../NaturalDeduction/Basic.lean` | Line 101 |
| `Sequent = Ctx Atom x Proposition Atom` | `Cslib/.../NaturalDeduction/Basic.lean` | Line 108 |
| `PropositionalConnectives` instance | `Cslib/Logics/Propositional/Defs.lean` | Lines 114-115 |

### Mathlib Infrastructure (All Confirmed Available)

| Component | Module | Signature |
|-----------|--------|-----------|
| `Finset.insert_subset_insert` | `Mathlib.Data.Finset.Insert` | `a → s ⊆ t → insert a s ⊆ insert a t` |
| `Finset.subset_union_left` | `Mathlib.Data.Finset.Insert` | `s ⊆ s ∪ t` |
| `Finset.subset_union_right` | `Mathlib.Data.Finset.Insert` | `t ⊆ s ∪ t` |
| `Finset.union_subset` | `Mathlib.Data.Finset.Insert` | `s ⊆ u → t ⊆ u → s ∪ t ⊆ u` |
| `Finset.mem_insert_self` | `Mathlib.Data.Finset.Insert` | `a ∈ insert a s` |
| `Finset.mem_insert_of_mem` | `Mathlib.Data.Finset.Insert` | `a ∈ s → a ∈ insert b s` |
| `WellFounded.prod_lex` | `Mathlib.Order.RelClasses` | `WellFounded ra → WellFounded rb → WellFounded (Prod.Lex ra rb)` |
| `Prod.Lex.left` | `Init.WF` | `ra a1 a2 → Prod.Lex ra rb (a1, b1) (a2, b2)` |
| `Prod.Lex.right` | `Init.WF` | `rb b1 b2 → Prod.Lex ra rb (a, b1) (a, b2)` |

### No Prior Art in CSLib or Mathlib

- `lean_local_search("SequentCalculus")` returned zero results
- `lean_local_search("LKSequent")` returned zero results
- `lean_local_search("LKProof")` returned zero results
- `lean_leanfinder("sequent calculus cut elimination")` returned only ITauto-related results (not a full SC)

This confirms the SequentCalculus directory and all types must be created from scratch.

## Recommended LK Design

### Type Definitions

```lean
-- Defs.lean
structure LKSequent (Atom : Type u) [DecidableEq Atom] where
  ant : Finset (Proposition Atom)
  suc : Finset (Proposition Atom)

scoped notation:60 Gamma " ⊢ₛ " Delta => LKSequent.mk Gamma Delta
```

### LKProof Inductive

```lean
-- LK/Basic.lean
inductive LKProof : LKSequent Atom → Type u where
  | ax (A : Proposition Atom) (Gamma : Finset _) (Delta : Finset _) :
      LKProof (insert A Gamma ⊢ₛ insert A Delta)
  | botL (Gamma : Finset _) (Delta : Finset _) :
      LKProof (insert .bot Gamma ⊢ₛ Delta)
  | andL {A B} {Gamma Delta} :
      LKProof (insert A (insert B Gamma) ⊢ₛ Delta) →
      LKProof (insert (A ∧ B) Gamma ⊢ₛ Delta)
  | andR {A B} {Gamma Delta} :
      LKProof (Gamma ⊢ₛ insert A Delta) →
      LKProof (Gamma ⊢ₛ insert B Delta) →
      LKProof (Gamma ⊢ₛ insert (A ∧ B) Delta)
  | orL {A B} {Gamma Delta} :
      LKProof (insert A Gamma ⊢ₛ Delta) →
      LKProof (insert B Gamma ⊢ₛ Delta) →
      LKProof (insert (A ∨ B) Gamma ⊢ₛ Delta)
  | orR {A B} {Gamma Delta} :
      LKProof (Gamma ⊢ₛ insert A (insert B Delta)) →
      LKProof (Gamma ⊢ₛ insert (A ∨ B) Delta)
  | impL {A B} {Gamma Delta} :
      LKProof (Gamma ⊢ₛ insert A Delta) →
      LKProof (insert B Gamma ⊢ₛ Delta) →
      LKProof (insert (A.imp B) Gamma ⊢ₛ Delta)
  | impR {A B} {Gamma Delta} :
      LKProof (insert A Gamma ⊢ₛ insert B Delta) →
      LKProof (Gamma ⊢ₛ insert (A.imp B) Delta)
  | weakL {A} {Gamma Delta} :
      LKProof (Gamma ⊢ₛ Delta) →
      LKProof (insert A Gamma ⊢ₛ Delta)
  | weakR {A} {Gamma Delta} :
      LKProof (Gamma ⊢ₛ Delta) →
      LKProof (Gamma ⊢ₛ insert A Delta)
  | cut {A} {Gamma Delta} :
      LKProof (Gamma ⊢ₛ insert A Delta) →
      LKProof (insert A Gamma ⊢ₛ Delta) →
      LKProof (Gamma ⊢ₛ Delta)
```

**Design decisions**:
1. **All-additive (shared contexts)**: Every rule operates on the same `Gamma`/`Delta`. No context splitting (`Gamma1 ∪ Gamma2`). This means contraction is definitionally free and weakening is built in as an explicit constructor.
2. **Finset-based**: Exchange is definitionally free (`Finset` is set-based, not order-dependent). No structural exchange rule needed.
3. **Cut as constructor**: Include `cut` in the inductive. Cut elimination proves it is admissible (removable). The `cutFree` predicate identifies proofs without `cut`.
4. **Axiom uses `insert`**: `ax A Gamma Delta` proves `insert A Gamma ⊢ₛ insert A Delta`, allowing any surrounding context. This is stronger than `{A} ⊢ₛ {A}` and reduces weakening steps.
5. **Notation `⊢ₛ`**: Avoids conflict with the existing ND `⊢` notation.

### Why Shared-Context (Not Context-Splitting)

The parent task research (task 279) confirmed all-additive is optimal for CSLib:
- ND already uses shared contexts (`Theory.Derivation` shares `G : Ctx Atom`)
- Bridge proofs (ND <-> LK) are simpler when both systems use shared contexts
- With Finsets, context splitting requires `Gamma ∪ Gamma'` union bookkeeping that adds proof burden without mathematical benefit
- All rules in G3cp (Negri & von Plato) use shared contexts

### Height Function

```lean
def LKProof.height : LKProof seq → Nat
  | .ax _ _ _ => 0
  | .botL _ _ => 0
  | .andL d => 1 + d.height
  | .andR d1 d2 => 1 + max d1.height d2.height
  | .orL d1 d2 => 1 + max d1.height d2.height
  | .orR d => 1 + d.height
  | .impL d1 d2 => 1 + max d1.height d2.height
  | .impR d => 1 + d.height
  | .weakL d => 1 + d.height
  | .weakR d => 1 + d.height
  | .cut d1 d2 => 1 + max d1.height d2.height
```

### Monotone Context Weakening

The key structural lemma is monotone context admissibility:

```lean
def LKProof.mono {Gamma Gamma' Delta Delta'} (hL : Gamma ⊆ Gamma') (hR : Delta ⊆ Delta') :
    LKProof (Gamma ⊢ₛ Delta) → LKProof (Gamma' ⊢ₛ Delta')
```

This is proved by structural induction on the proof, using `Finset.insert_subset_insert` to thread the subset hypotheses through each constructor.

## Soundness Strategy

**Semantic validity for LK sequents**: For a valuation `v`, an LK sequent `Gamma ⊢ₛ Delta` is valid iff: if all formulas in `Gamma` evaluate to true under `v`, then some formula in `Delta` evaluates to true.

```lean
def LKSequent.valid (seq : LKSequent Atom) : Prop :=
  ∀ v : Valuation Atom, (∀ A ∈ seq.ant, Evaluate v A) → ∃ A ∈ seq.suc, Evaluate v A
```

Soundness is a straightforward induction on `LKProof`:
- `ax`: `A ∈ insert A Gamma` and `A ∈ insert A Delta`, so witness is `A`
- `botL`: the antecedent contains `bot`, so hypothesis `∀ A ∈ ..., Evaluate v A` gives `False`
- `andR`: by IH, some formula in `insert A Delta` is true and some in `insert B Delta` is true; case analysis yields `A ∧ B` true or some formula in `Delta` is true
- Other cases: similar straightforward case analysis

## Cut Elimination Strategy (Detailed)

### Termination Measure

The lexicographic pair `(Proposition.complexity A, d1.height + d2.height)` where `A` is the cut formula, `d1` and `d2` are the two premise proofs of the cut.

In Lean 4, this uses `WellFounded.prod_lex` with `Nat.lt` for both components:
```lean
termination_by (A.complexity, d1.height + d2.height)
```

### Case Analysis for Cut Elimination

Given a cut:
```
d1 : LKProof (Gamma ⊢ₛ insert A Delta)
d2 : LKProof (insert A Gamma ⊢ₛ Delta)
-- Goal: LKProof (Gamma ⊢ₛ Delta)  (cut-free)
```

**Case 1** (axiom premise): If `d1` or `d2` is an axiom, the cut is trivially removable (by weakening the other premise).

**Case 2** (non-principal): If the last rule of `d1` does not introduce `A` in the succedent, we push the cut into the subproof(s) of `d1`. The height of `d1`'s subproof is strictly less, so the level decreases. Similarly if `d2`'s last rule does not introduce `A` in the antecedent.

**Case 3** (principal on both sides): The cut formula `A` is introduced by the last rule of both `d1` and `d2`. This generates cases per connective:
- **A = B ∧ C**: `d1` ends with `andR` (producing `B` and `C` separately), `d2` ends with `andL` (consuming `B, C` together). Replace by two cuts on `B` and `C`, each with strictly lower complexity.
- **A = B ∨ C**: `d1` ends with `orR` (producing `B, C` together), `d2` ends with `orL` (two branches for `B` and `C`). Replace by cuts on `B` and `C`.
- **A = B → C**: `d1` ends with `impR` (producing `B` in antecedent, `C` in succedent), `d2` ends with `impL` (consuming via `B` proof and `C` hypothesis). Replace by cuts on `B` and `C`.
- **A = bot**: Impossible as principal on the right (there is no right rule for `bot`).

### Prerequisite Lemmas for Cut Elimination

1. **Height arithmetic**: For each constructor, the height of subproofs is strictly less than the height of the parent proof
2. **Monotone context weakening** (`mono`): needed when permuting cuts through rules
3. **`Finset.insert` commutativity lemmas**: `insert A (insert B S) = insert B (insert A S)` (follows from `Finset.insert_comm`)

### Estimated Complexity

The cut elimination proof has approximately:
- 3 top-level cases (axiom, non-principal, principal)
- 10 subcases for non-principal (one per rule constructor)
- 3 principal subcases (and, or, imp -- bot is vacuous)
- Total: ~16 case patterns, each following a uniform template

In Lean 4 lines: approximately 300-600 lines, depending on automation level. The `omega` tactic handles most termination obligations.

## Bridge Proof Strategy

### nd_iff_lk (ND <-> LK equivalence)

**Direction 1: ND -> LK** (`ndToLK`):

Given `T.Derivation Gamma A` (an ND derivation from context `Gamma` concluding `A`), produce `LKProof (Gamma ⊢ₛ {A})` (an LK proof with singleton succedent).

Translation of each ND constructor:
- `ax h_mem` (theory axiom: `A ∈ T`): In the LK translation, theory axioms need special handling. The most natural approach is to translate the ND theory `T` to an LK context, or to prove that for classical logic, every CPL theory axiom is LK-derivable.
- `ass h_mem` (assumption: `A ∈ Gamma`): `LKProof.ax A ...` with weakening to fill the rest of `Gamma`
- `andI G d1 d2`: compose `d1` and `d2` via `andR`, using `mono` to align contexts
- `andE1 G d`: from `d : LKProof (Gamma ⊢ₛ {A ∧ B})`, use `andL` and `ax`
- `andE2 G d`: similar
- `orI1 G d`, `orI2 G d`: use `orR` with appropriate weakening
- `orE G d dA dB`: use `orL` on the branches, compose with `cut`
- `impI Gamma d`: use `impR`
- `impE d1 d2`: from `d1 : Gamma ⊢ₛ {A → B}` and `d2 : Gamma ⊢ₛ {A}`, use `impL` and `cut`

**Theory handling**: For the CPL theory (`AxiomTheory PropositionalAxiom`), each axiom in the theory is a valid propositional formula. In the ND-to-LK direction, theory axioms (via `ax h_mem`) can be translated to LK proofs of `∅ ⊢ₛ {φ}` for each axiom `φ`, followed by weakening.

**Direction 2: LK -> ND** (`lkToND`):

Given `LKProof (Gamma ⊢ₛ Delta)`, produce something in the ND world. The challenge is that ND has single-conclusion sequents while LK has multiple conclusions.

The standard approach:
1. Define `lk_to_nd_single : LKProof (Gamma ⊢ₛ {A}) → T.Derivation Gamma A` for single-conclusion LK proofs
2. For the general case, use the disjunction encoding: `LKProof (Gamma ⊢ₛ {A1, ..., An})` implies `T.Derivation Gamma (A1 ∨ ... ∨ An)`

For the bridge, we only need the single-conclusion case because the ND system works with single conclusions. The bridge `nd_iff_lk` relates:
- `DerivableIn (AxiomTheory PropositionalAxiom) (Gamma ⊢ A)` (ND)
- `Nonempty (LKProof (Gamma ⊢ₛ {A}))` (LK)

### hilbert_iff_lk (Hilbert <-> LK)

Compose through ND:
```lean
theorem hilbert_iff_lk : Deriv PropositionalAxiom Gamma.toList φ ↔
    Nonempty (LKProof (Gamma ⊢ₛ {φ})) :=
  hilbert_iff_nd_ctx.trans nd_iff_lk
```

### Completeness as Corollary

LK completeness follows from Hilbert completeness + Hilbert-to-LK bridge:
1. Existing: `Tautology φ → Derivable PropositionalAxiom φ` (Hilbert completeness, via algebraic path in `Semantics/Algebra/HilbertCompleteness.lean`)
2. Hilbert-to-LK: `Derivable PropositionalAxiom φ → Nonempty (LKProof (∅ ⊢ₛ {φ}))`
3. Combining: `Tautology φ → Nonempty (LKProof (∅ ⊢ₛ {φ}))`

## File Layout

| File | Content | Est. Lines |
|------|---------|------------|
| `SequentCalculus/Defs.lean` | `LKSequent` type, `⊢ₛ` notation, semantic validity | 60-80 |
| `SequentCalculus/LK/Basic.lean` | `LKProof` inductive, height, `mono`, `cutFree` predicate, `InferenceSystem` | 200-300 |
| `SequentCalculus/LK/Soundness.lean` | `LKProof.soundness` | 80-120 |
| `SequentCalculus/LK/CutElimination.lean` | Hauptsatz: `cutElim` | 300-600 |
| `SequentCalculus/LK/Completeness.lean` | Bridge proofs, completeness corollary | 200-350 |

**Total estimated**: 840-1450 lines

## Tactic Survey Results

### Expected Tactics by Component

| Component | Primary Tactics | Notes |
|-----------|----------------|-------|
| Structural lemmas (mono, weakening) | `exact`, `apply`, `grind`, structural induction | Finset `insert_subset_insert` is the workhorse |
| Soundness | `simp`, `exact`, `intro`, `cases`, `constructor`, `grind` | Each case is 2-5 lines |
| Cut elimination | `termination_by`, `omega`, structural induction, `cases` | Lexicographic order via `Prod.Lex` |
| Bridge proofs | `exact`, `apply`, structural induction | One case per ND/LK constructor |

### Key Lemmas for Automation

- `Finset.insert_comm : insert a (insert b s) = insert b (insert a s)` -- essential for rewriting contexts
- `Finset.mem_insert_self`, `Finset.mem_insert_of_mem` -- for axiom cases
- `Finset.insert_subset_insert` -- threading subset through insert
- `Proposition.complexity` simp lemmas from `Tableau/Defs.lean` -- for termination obligations

## Notation Considerations

The existing codebase uses:
- `⊢` scoped in `Cslib.Logic.PL` for ND sequents (`Gamma ⊢ A`)
- `⇓` scoped for `InferenceSystem`

For LK, use `⊢ₛ` (subscript s for "sequent") to avoid conflict:
```lean
scoped notation:60 Gamma " ⊢ₛ " Delta => LKSequent.mk Gamma Delta
```

This follows the existing pattern of avoiding notation clashes between proof systems in the same namespace.

## Potential Blockers

### 1. Cut Elimination Termination (Medium Risk)

The Lean 4 termination checker may struggle with the lexicographic measure on `(complexity, height_sum)` when the recursive calls are nested inside case splits. Mitigation: define helper functions for each case (principal, commutative-left, commutative-right) and prove termination obligations separately.

If the termination checker cannot handle the full recursion directly, an alternative is to use `WellFounded.recursion` explicitly with `WellFounded.prod_lex` on `(Nat.lt, Nat.lt)`.

### 2. Theory Handling in Bridges (Low Risk)

The ND system is parameterized by a `Theory` (set of axioms). The LK system has no theory parameter -- all axioms of CPL should be directly derivable in LK. The bridge proof needs to show that for each axiom `φ ∈ AxiomTheory PropositionalAxiom`, the sequent `∅ ⊢ₛ {φ}` is LK-derivable. This requires proving 10 concrete LK derivations (one per `PropositionalAxiom` constructor).

### 3. Finset.insert Associativity/Commutativity (Low Risk)

Many proof goals will have `insert A (insert B Gamma)` vs `insert B (insert A Gamma)`. Since `Finset.insert_comm` exists, this is manageable via `simp [Finset.insert_comm]` or `rw [Finset.insert_comm]`.

## Recommendations

1. **Do NOT define a new `complexity` function** -- reuse `Proposition.complexity` from `Tableau/Defs.lean` by importing it
2. **Include `cut` as a constructor** in `LKProof`, not as an external combinator -- this is standard and makes cut elimination a theorem about the inductive type
3. **Use `insert` throughout** rather than `{A} ∪ Gamma` -- `insert` is the canonical Finset operation and avoids `singleton ∪` overhead
4. **Prove `mono` (monotone context weakening) early** -- it is needed in every subsequent proof
5. **Implement cut elimination as a function** `cutElim : LKProof seq → CutFreeLKProof seq` that produces a constructive witness, not just a Prop-level existence statement
6. **Start bridges with the ND->LK direction** which is more straightforward (each ND constructor maps cleanly to LK steps)
7. **For the LK->ND bridge**, only prove the single-conclusion case (`LKProof (Gamma ⊢ₛ {A}) → T.Derivation Gamma A`) since that is sufficient for the Iff statement
