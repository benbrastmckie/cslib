# Task 279: Teammate-B Findings — Alternatives Research

**Task**: Two-sided Gentzen-style sequent calculus (LK/LJ) for propositional logic with cut elimination
**Researcher Role**: ALTERNATIVES (approaches and patterns the primary researcher might overlook)
**Artifact**: 01, Teammate: b

---

## Key Findings

1. **Mathlib has NO existing sequent calculus formalization.** LeanSearch and LeanFinder found zero LK/LJ sequent calculus types in Mathlib. The only related Mathlib tactic infrastructure (`Mathlib.Tactic.ITauto`, `Mathlib.Tactic.Tauto`) is decision-procedure code, not proof-theoretic formalization. This is a gap that CSLib can meaningfully fill.

2. **`Relation.CutExpand` / `WellFounded.cutExpand` in Mathlib (`Mathlib.Logic.Hydra`) is a direct enabler for cut elimination termination.** This is the Hydra game well-foundedness result. It says: given a well-founded relation `r` on `α`, the `CutExpand r` relation on `Multiset α` is also well-founded. The `CutExpand r s' s` relation holds iff `s'` is obtained from `s` by removing one element `a` and adding a finite multiset of elements all smaller than `a` under `r`. This is exactly the structure of Gentzen's cut elimination: you replace a cut on formula `A` with cuts on strictly smaller formulas. This is a significant piece of prior art that was likely overlooked.

3. **CLL uses `Multiset`; ND uses `Finset`; two-sided LK/LJ will need to choose.** The key difference: CLL (one-sided sequent calculus) has one context and uses `Multiset` (tracking multiplicity for `weaken`/`contract` as explicit rules). ND uses `Finset` (contraction/weakening built into `ass` rule). Two-sided sequent calculus has both an antecedent and succedent, which adds another degree of freedom in the representation choice.

4. **The existing ND ↔ Hilbert bridge (`NaturalDeduction/Equivalence.lean`) provides a rich template and reusable pattern for bridge theorems.** The `MinimalAxioms` typeclass pattern, `AxiomTheory` wrapper, and `hilbert_iff_nd_ctx` family demonstrate exactly the design needed for `nd_iff_lk` / `hilbert_iff_lk`. The core bridge mechanism (translating derivation tree constructors one-to-one) can be directly adapted.

5. **The Tableau infrastructure is related but is NOT reusable for LK/LJ.** The propositional tableau (`Cslib.Foundations.Logic.Tableau.*`, `Cslib.Logics.Propositional.Tableau/`) is a refutation-based decision procedure with signed formulas and fuel-based expansion. It uses a `Branch F L = List (SignedFormula F L)` type that is fundamentally different from a two-sided sequent. Tableaux prove soundness/completeness indirectly; LK/LJ proves it directly via a rules-based derivation system. The closeness is conceptual, not structural.

6. **CLL cut elimination is currently a stub** — `CllElimination.lean` has only TODO comments and no actual implementation. This means there is no existing cut elimination proof in CSLib to reference or reuse.

---

## Alternative Approaches (With Trade-offs)

### 1. Context Representation: `Finset` vs `Multiset` vs `List`

#### Option A: `Finset` on both sides (recommended for CSLib alignment)

```lean
-- Two-sided sequent
structure Sequent (Atom) where
  ant : Finset (Proposition Atom)   -- antecedent Γ
  suc : Finset (Proposition Atom)   -- succedent Δ

-- Or inline as:
abbrev LKSequent (Atom) := Finset (Proposition Atom) × Finset (Proposition Atom)
```

**Pros:**
- Consistent with the existing ND system (`Ctx Atom = Finset (Proposition Atom)`)
- Contraction and weakening built-in (no explicit structural rules needed in LK/LJ)
- Bridge to ND is natural: the ND sequent `Γ ⊢ φ` becomes the LK sequent `Γ ⊢ {φ}` directly
- `Finset` operations (`union`, `insert`, `sdiff`, `image`) all available in Mathlib
- Avoids the `nodup` invariant management burden of `Multiset` used as a set

**Cons:**
- Cannot directly use `WellFounded.cutExpand` (which is over `Multiset`) for termination. The cut formula must be tracked separately. Can work around with `Finset.card` measure on formula complexity.
- Classical LK with multiple-conclusion is slightly awkward: the succedent side needs contraction as a rule (but with `Finset`, contraction is free)
- For LJ (intuitionistic), the succedent is exactly one formula — using `Finset` requires adding a side condition `|Δ| = 1` or just using `Option (Proposition Atom)` for the succedent

**Recommendation for LK**: Use `Finset` on both sides. For LJ: use `Finset` on antecedent, `Option (Proposition Atom)` or just `Proposition Atom` on succedent (matching how ND's `Theory.Derivation Γ A` works).

#### Option B: `Multiset` on both sides (matches CLL pattern)

```lean
-- Like CLL: Sequent Atom = Multiset (Proposition Atom)
-- For two-sided LK: use a pair
abbrev Antecedent Atom := Multiset (Proposition Atom)
abbrev Succedent Atom := Multiset (Proposition Atom)
```

**Pros:**
- Direct access to `WellFounded.cutExpand` (`Mathlib.Logic.Hydra`) for termination proofs
- Better for resource-sensitive logics and modular evolution to substructural logics
- Contraction and weakening are explicit rules, making the proof system more granular and pedagogically faithful to Gentzen's original LK

**Cons:**
- Inconsistent with ND's `Finset`-based approach — bridge to ND requires `Multiset.toFinset` and nodup management
- More work: must prove `Multiset.Nodup` invariants or prove structural rules separately
- `CLL` already uses this pattern for one-sided sequents; extending it to two-sided is possible but requires more infrastructure

**Recommendation**: Only use `Multiset` if cut elimination termination via `WellFounded.cutExpand` is the primary goal. Otherwise, `Finset` is simpler and more aligned.

#### Option C: `List` with explicit exchange

Not recommended: `List`-based sequents require explicit exchange rules. The existing Hilbert system already uses `List` (for `DerivationTree`), but this was a deliberate design trade-off and the bridge lemmas between `List` and `Finset` (e.g., `List.toFinset`, `Finset.toList`) are the most complex parts of the ND ↔ Hilbert bridge. Adding another `List`-based system would create further bridging complexity.

---

### 2. Cut Elimination Approaches

#### Option A: Direct structural induction with complexity measure (recommended)

Define a "cut complexity" measure `(grade(A), depth(p), depth(q))` and proceed by lexicographic induction. In Lean 4, encode as:

```lean
termination_by (grade A, p.depth, q.depth)
decreasing_by ...
```

or using `WellFoundedRelation` on a triple.

**Pros:**
- Standard approach, follows Gentzen's original 1935 proof
- Works with both `Finset` and `Multiset`
- Lean 4 has good support for lexicographic `termination_by` with multiple measures
- Allows you to compute the cut-free proof (returns `CutFreeProof`, not just `Nonempty`)

**Cons:**
- Key lemma structure is complex (must match on both proofs simultaneously)
- Requires mutual recursion or a large combined induction
- Lean 4's structural induction on two simultaneously decreasing arguments can require explicit well-founded recursion setup

#### Option B: Via `WellFounded.cutExpand` (Mathlib Hydra) — alternative for Multiset approach

If `Multiset` is used for sequents:

```lean
-- grade of formula A = number of connectives in A  
def formulaGrade : Proposition Atom → ℕ

-- The "cut complexity" as a multiset: all the grades of cut formulas
-- Each cut step replaces one cut with smaller cuts -> CutExpand relation

-- Then:
-- WellFounded.cutExpand (measure := InvImage ... formulaGrade)
```

**Pros:**
- Elegant: directly proves termination using Mathlib's `Mathlib.Logic.Hydra`
- Reduces cut elimination to showing each step produces a `CutExpand`-smaller sequent
- The `Relation.cutExpand_iff` theorem makes the condition explicit

**Cons:**
- Only works cleanly when `Multiset` is used for sequent contexts
- Requires setting up the mapping from proofs to multisets of cut formulas
- May not be simpler than direct induction in practice

**Key API (Mathlib.Logic.Hydra)**:
```lean
-- These are immediately usable:
WellFounded.cutExpand : WellFounded r → WellFounded (CutExpand r)
Relation.CutExpand : (α → α → Prop) → Multiset α → Multiset α → Prop
Relation.cutExpand_iff : CutExpand r s' s ↔ ∃ t a, (∀ a' ∈ t, r a' a) ∧ a ∈ s ∧ s' = s.erase a + t
```

#### Option C: Semantic cut elimination (Okada/Troelstra-Schwichtenberg method)

Prove cut-free completeness directly from semantics: show every valid sequent has a cut-free proof using a model-theoretic or phase-space argument.

**Pros:**
- Avoids the complex combinatorial induction entirely
- For classical logic, this reduces to: if `Γ ⊢ Δ` is valid, build a cut-free proof by completeness
- Okada's method using phase semantics applies to linear logic but also adapts to classical PL

**Cons:**
- Requires setting up the semantic framework (valuations or Kripke frames)
- The resulting proof is non-constructive (uses `Classical.choice`)
- Does not give a computable cut-elimination procedure
- Less standard for a CSLib pedagogical module
- CSLib already has semantics (`Semantics/Bool.lean`, `Semantics/Kripke.lean`) but they are for the Hilbert/ND systems, not directly for LK/LJ

**Recommendation**: Use Option A (direct structural induction) for classical LK and LJ. Consider noting in the module that `WellFounded.cutExpand` could be the basis of an alternative proof.

---

### 3. LK and LJ: Same File or Separate?

#### Option A: Separate files (recommended)

```
Cslib/Logics/Propositional/
  SequentCalculus/
    Basic.lean          -- shared types (Sequent, CutFreeProof)
    LK/
      Rules.lean        -- LK proof inductive
      CutElimination.lean
      Soundness.lean
      Completeness.lean
      Equivalence.lean  -- hilbert_iff_lk, nd_iff_lk
    LJ/
      Rules.lean        -- LJ proof inductive (succedent: Option or single formula)
      CutElimination.lean
      Soundness.lean
      Completeness.lean
      Equivalence.lean  -- hilbert_iff_lj, nd_iff_lj
```

**Pros:**
- Mirrors the NaturalDeduction/ directory structure
- Clean separation of classical and intuitionistic concerns
- Cut elimination for LK and LJ are structurally different (LK has full two-sided succedent; LJ restricts succedent to a single formula)
- Allows incremental implementation (LK first, LJ second)

**Cons:**
- More files to maintain, more barrel imports needed

#### Option B: Combined LK/LJ module

All in `Cslib/Logics/Propositional/SequentCalculus/Basic.lean` with a logic-strength parameter.

**Pros:**
- Smaller file count, single namespace

**Cons:**
- LK and LJ sequents have fundamentally different succedent types (`Finset` vs `Option`/singleton). A unified type would require a sum type or additional type parameter, complicating the inductive.
- Cut elimination proofs diverge substantially between LK and LJ
- Not recommended; the ND module itself is split into multiple files

**Recommendation**: Option A (separate `LK/` and `LJ/` subdirectories with shared `Basic.lean`). Follow the existing NaturalDeduction/ structure.

---

### 4. Bridge Strategies (hilbert_iff_lk, nd_iff_lk)

#### Option A: Compose bridges (Hilbert ↔ ND ↔ LK) — recommended

The existing `hilbert_iff_nd` provides a full bridge. The task only requires `hilbert_iff_lk` and `nd_iff_lk`, not `hilbert_iff_nd_iff_lk` as a three-way simultaneous theorem. The natural decomposition is:

1. Prove `nd_iff_lk` (ND ↔ LK)
2. Derive `hilbert_iff_lk` by composing with the existing `hilbert_iff_nd`

```lean
-- Step 1: nd_iff_lk (direct translation)
theorem nd_iff_lk (Γ : Ctx Atom) (φ : Proposition Atom) :
    DerivableIn T (Γ ⊢ φ) ↔ LK.Provable Γ {φ} := ...

-- Step 2: hilbert_iff_lk (compose with existing bridge)
theorem hilbert_iff_lk (φ : Proposition Atom) :
    Derivable PropositionalAxiom φ ↔ LK.Provable ∅ {φ} :=
  hilbert_iff_nd.trans nd_iff_lk
```

**Pros:**
- Leverages substantial existing work in `Equivalence.lean`
- Less proof work: the hard direction (ND → Hilbert, using deduction theorem) is already done
- Modular: if ND changes, only `nd_iff_lk` needs updating

**Cons:**
- Introduces ND as a middleman, which makes `hilbert_iff_lk` non-direct
- The composed proof is not informative about the direct LK/Hilbert relationship

**Key existing infrastructure to reuse:**
- `MinimalAxioms` typeclass — can extend with an `LKAxioms` typeclass similarly
- `hilbertToND` / `ndToHilbert` translation functions — can adapt pattern for `ndToLK` / `lkToND`
- `AxiomTheory` wrapper — can create `LKTheory`-style wrappers
- Context bridge lemmas (`finset_insert_toList_mem_cons`, `List.toFinset`, `Finset.toList`) — may be needed for context-type mismatches

#### Option B: Direct Hilbert ↔ LK translation

Build direct translation functions `hilbertToLK` and `lkToHilbert` without going through ND.

**Pros:**
- More self-contained; LK module does not depend on the ND module
- Could be more elegant for cut elimination (Hilbert proof → LK proof uses `cut` rule directly for modus ponens)

**Cons:**
- More work: must redo the deduction theorem and context management that ND ↔ Hilbert already proved
- The ND ↔ Hilbert bridge contains 400+ lines of carefully crafted Lean. Duplicating this work would violate the reuse-first principle.
- The natural direction Hilbert → LK (translating modus ponens to a CUT rule) requires knowing that the cut formula is smaller, complicating the cut-free version

**Recommendation**: Option A (compose via ND). Prove `nd_iff_lk` directly, then `hilbert_iff_lk := hilbert_iff_nd.trans nd_iff_lk` (or its symmetric form).

---

### 5. LJ Succedent Representation

This is an important alternative that the primary researcher may overlook.

#### Option A: `Finset` with card constraint

```lean
inductive LJ.Proof : Finset (Proposition Atom) → Finset (Proposition Atom) → Type where
-- + invariant that the succedent always has |Δ| ≤ 1
```

**Cons**: Invariant is not enforced by the type; requires runtime checks or separate lemmas.

#### Option B: Single formula succedent (matches ND design)

```lean
-- LJ sequent: Γ ⊢ φ (single conclusion, like ND)
inductive LJ.Proof : Finset (Proposition Atom) → Proposition Atom → Type where
  | ax {Γ φ} (h : φ ∈ Γ) : Proof Γ φ
  | cut {Γ φ ψ} : Proof Γ φ → Proof (insert φ Γ) ψ → Proof Γ ψ
  | impR {Γ φ ψ} : Proof (insert φ Γ) ψ → Proof Γ (φ → ψ)
  -- etc.
```

**Pros:**
- Directly corresponds to the ND system (`Theory.Derivation Γ A`), making `nd_iff_lj` trivial or definitional
- Avoids multi-conclusion succedent management entirely
- Consistent with the ND module's `abbrev Sequent = Ctx Atom × Proposition Atom`

**Cons:**
- Not the "standard" textbook presentation of LJ (which typically allows `∅` on the succedent)
- The rules for `∨`-right require choosing which disjunct to prove, baking in non-determinism

#### Option C: `Option (Proposition Atom)` succedent

```lean
-- Succedent: None = empty (absurdity), Some φ = proving φ
inductive LJ.Proof : Finset (Proposition Atom) → Option (Proposition Atom) → Type where
```

**Pros:**
- Captures the possibility of an empty succedent (for proving ⊥ directly)
- More faithful to LJ's definition

**Cons:**
- Notation awkward; bridge to ND (`Theory.Derivation`) requires unwrapping `Option`

**Recommendation**: Use **Option B** (single formula succedent) for LJ. This creates a direct correspondence with the existing ND system and makes `nd_iff_lj` nearly definitional. The rule that LJ differs from LK can be enforced structurally rather than invariantly.

---

## Evidence / Examples

### Mathlib Hydra Infrastructure (Immediately Usable)

```lean
import Mathlib.Logic.Hydra

-- Key theorem:
#check WellFounded.cutExpand
-- : {α : Type u_1} → {r : α → α → Prop} → WellFounded r → WellFounded (Relation.CutExpand r)

#check Relation.CutExpand
-- : {α : Type u_1} → (α → α → Prop) → Multiset α → Multiset α → Prop

-- For cut elimination with Multiset contexts:
-- r = InvImage (· < ·) formulaGrade
-- CutExpand r s' s  iff  s' = s.erase a + t where ∀ a' ∈ t, formulaGrade a' < formulaGrade a
```

### CLL's `Proof.cutFree` Pattern (Reusable)

The CLL module defines `Proof.cutFree` as a predicate on proofs (a `def`, not a separate inductive). For LK/LJ, consider:

```lean
-- Pattern from CLL:
def Proof.cutFree : ⇓Γ → Bool
  | .ax => true
  | .cut _ _ => false  -- cuts are not cut-free
  | .rule p q => p.cutFree && q.cutFree

abbrev CutFreeProof (Γ : Sequent Atom) := { q : ⇓Γ // q.cutFree }
```

This pattern is clean and works for LK/LJ too.

### ND ↔ Hilbert Bridge Template for ND ↔ LK

The key pattern from `hilbertToND`:

```lean
-- TEMPLATE: adapt hilbertToND → ndToLK
def ndToLK {Γ : Ctx Atom} {φ : Proposition Atom} :
    Theory.Derivation T Γ φ → LK.Proof Γ.toMultiset {φ}
  | .ax h => LK.Proof.ax (right_mem h)
  | .ass h => LK.Proof.ax (left_mem h)
  | .impE d₁ d₂ =>
    -- Use cut with the minor premise
    LK.Proof.cut (ndToLK d₁) (ndToLK d₂)
  | .impI d =>
    -- Use →-right rule
    LK.Proof.impR (ndToLK d)
  -- etc.
```

### Context Type Mismatches: Known Issue

The ND ↔ Hilbert bridge documents that `List ↔ Finset` bridging is the hardest part. For ND ↔ LK:
- ND uses `Finset` on the left, `Proposition` (single) on the right
- LK uses `Finset`/`Multiset` on both sides

The mismatch is smaller: only the succedent changes from singleton to `Finset`. Key lemmas needed:
- `Finset.mem_singleton` (for the succedent)
- `Finset.singleton_subset_iff`

---

## Confidence Levels

| Finding | Confidence |
|---------|-----------|
| Mathlib has no LK/LJ sequent calculus | High — exhaustive search via LeanSearch, LeanFinder found nothing |
| `WellFounded.cutExpand` is in Mathlib.Logic.Hydra | High — verified via LeanSearch |
| CLL cut elimination is an unimplemented TODO | High — read `CutElimination.lean` directly |
| `Finset` is optimal for alignment with ND | High — follows from ND's existing `Ctx Atom = Finset` |
| `Multiset` enables `WellFounded.cutExpand` use | High — by definition of `Relation.CutExpand` |
| Compose Hilbert ↔ LK via ND | High — reuse principle + existing 400+ line bridge |
| Option B (single succedent) for LJ is cleanest | High — matches ND's single-conclusion design |
| Tableau infrastructure is NOT reusable for LK | High — structurally incompatible (refutation vs. proof search, `List` vs. two-sided sequent) |
| File layout: separate `LK/` and `LJ/` subdirs | Medium — organization preference, but matches existing NaturalDeduction/ pattern |

---

## Summary of Recommendations

1. **Representation**: `Finset` on both sides for LK (two-sided). Single `Proposition Atom` succedent for LJ (aligning with ND).

2. **Cut elimination**: Direct structural induction with lexicographic measure `(formulaComplexity A, depth p, depth q)`. Document `WellFounded.cutExpand` as an alternative for `Multiset`-based variants.

3. **Bridge**: Prove `nd_iff_lk` directly; derive `hilbert_iff_lk := hilbert_iff_nd.trans nd_iff_lk`.

4. **File layout**: `Cslib/Logics/Propositional/SequentCalculus/{Basic,LK/Rules,LK/CutElimination,...,LJ/...}.lean`.

5. **Reuse**: The `MinimalAxioms` typeclass pattern and the `AxiomTheory` wrapper from `Equivalence.lean` are directly adaptable for the equivalence bridge. The CLL `CutFreeProof` subtype pattern `{ q : ⇓Γ // q.cutFree }` is reusable as-is.

6. **Do NOT reuse**: The tableau infrastructure (`Cslib.Foundations.Logic.Tableau.*`). The only overlap is conceptual (both are proof-search methods for propositional logic); the data structures and proof strategies are incompatible.
