# Research Report: Subformula Property as Corollary of Cut Elimination

**Task**: 329
**Session**: sess_1782300531_c471d6_329
**Date**: 2026-06-24

## 1. Executive Summary

The subformula property for LK is a standard textbook result: every formula appearing in a
cut-free proof is a subformula of some formula in the conclusion sequent. The infrastructure
needed to state and prove this is largely already in place in CSLib:

- `Proposition.subformulas` and `Proposition.IsSubformula` already exist in the Normalization file
- `LKProof`, `CutFreeLKProof`, `CutFree`, and `LKProof.cutElim` are complete in the LK files
- The proof is a straightforward structural induction on the cut-free proof tree

The main new work is:
1. Defining "all formulas appearing in an LK proof" (a `Finset`-valued recursive function)
2. Proving the subformula property for cut-free proofs by structural induction
3. Deriving the general case via `cutElim`

## 2. Existing Infrastructure

### 2.1 Proposition Type (Defs.lean)

```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (x : Atom)
  | bot
  | imp (a b : Proposition Atom)
  | and (a b : Proposition Atom)
  | or (a b : Proposition Atom)
```

Five constructors. Negation (`neg`), top, and iff are abbreviations.

### 2.2 Subformula Definitions (Normalization.lean, lines 63-145)

**REUSE**: These already exist and should be imported, not redefined.

```lean
-- Cslib.Logic.PL.Proposition.subformulas
def Proposition.subformulas : Proposition Atom → Finset (Proposition Atom)
  | φ@(.atom _) => {φ}
  | φ@.bot => {φ}
  | φ@(.imp A B) => insert φ (A.subformulas ∪ B.subformulas)
  | φ@(.and A B) => insert φ (A.subformulas ∪ B.subformulas)
  | φ@(.or A B) => insert φ (A.subformulas ∪ B.subformulas)

-- Cslib.Logic.PL.Proposition.IsSubformula
def Proposition.IsSubformula (A B : Proposition Atom) : Prop :=
  A ∈ B.subformulas
```

Available lemmas:
- `Proposition.self_mem_subformulas` / `IsSubformula.refl`
- `IsSubformula.trans`
- `IsSubformula.and_left`, `and_right`, `or_left`, `or_right`, `imp_left`, `imp_right`

### 2.3 LK Proof System (Basic.lean)

```lean
inductive LKProof : LKSequent Atom → Type u where
  | ax, botL, andL, andR, orL, orR, impL, impR, weakL, weakR, cut

-- Predicate: proof is cut-free
def CutFree : LKProof seq → Prop

-- Subtype: cut-free proofs
def CutFreeLKProof (seq : LKSequent Atom) : Type u :=
  { d : LKProof seq // CutFree d }
```

### 2.4 Cut Elimination (CutElimination.lean)

```lean
-- Hauptsatz: every LK proof has a cut-free version
theorem LKProof.cutElim {seq : LKSequent Atom} (d : LKProof seq) :
    Nonempty (CutFreeLKProof seq)
```

**Important**: `cutElim` returns `Nonempty (CutFreeLKProof seq)`, not a concrete
`CutFreeLKProof`. This means the final `LKProof.subformula_property` will also be
existential in nature. Also note that `cutElim` (and the `cutAdmissibility` machinery)
is `noncomputable`.

### 2.5 CutElimination Import Note

The barrel file `LK.lean` currently comments out `CutElimination`:
```lean
-- CutElimination excluded: has build errors requiring dedicated proof rewrite
-- public import Cslib.Logics.Propositional.SequentCalculus.LK.CutElimination
```

However, **`lake build Cslib.Logics.Propositional.SequentCalculus.LK.CutElimination` succeeds**.
The comment appears outdated. The new SubformulaProperty file should import CutElimination
directly (not through the barrel). Updating the barrel is out of scope for this task but should
be noted.

## 3. Design

### 3.1 File Location

`Cslib/Logics/Propositional/SequentCalculus/LK/SubformulaProperty.lean`

### 3.2 Imports

```lean
import Cslib.Init
public import Cslib.Logics.Propositional.SequentCalculus.LK.CutElimination
public import Cslib.Logics.Propositional.NaturalDeduction.Normalization
```

The Normalization import gives us `Proposition.subformulas`, `Proposition.IsSubformula`, and
all supporting lemmas. No circular dependency exists: CutElimination imports Basic + Tableau.Defs,
while Normalization imports NaturalDeduction.Basic. Both converge on Defs.lean but are otherwise
independent.

**Alternative**: If the import of Normalization is considered too heavy (it brings in the
entire NaturalDeduction infrastructure and Multiset.DershowitzManna), the subformula
definitions could be factored into a separate file
`Cslib/Logics/Propositional/Subformulas.lean`. However, that refactoring is out of scope for
this task and unnecessary unless build times are a concern. The simplest approach is to import
Normalization.

### 3.3 New Definitions

#### 3.3.1 `LKProof.formulas` -- All formulas appearing in a proof tree

This is the key new definition. It collects every formula that appears anywhere in the proof
tree: in sequent antecedents, sequent succedents, and principal formulas of rules.

```lean
def LKProof.formulas {seq : LKSequent Atom} : LKProof seq → Finset (Proposition Atom)
  | .ax A Γ Δ _ _ => Γ ∪ Δ
  | .botL Γ Δ _ => Γ ∪ Δ
  | .andL A B _ d => {A ∧ B} ∪ d.formulas
  | .andR A B _ d₁ d₂ => {A ∧ B} ∪ d₁.formulas ∪ d₂.formulas
  | .orL A B _ d₁ d₂ => {A ∨ B} ∪ d₁.formulas ∪ d₂.formulas
  | .orR A B _ d => {A ∨ B} ∪ d.formulas
  | .impL A B _ d₁ d₂ => {A → B} ∪ d₁.formulas ∪ d₂.formulas
  | .impR A B _ d => {A → B} ∪ d.formulas
  | .weakL A d => {A} ∪ d.formulas
  | .weakR A d => {A} ∪ d.formulas
  | .cut A d₁ d₂ => {A} ∪ d₁.formulas ∪ d₂.formulas
```

**Design decision**: The simplest and most correct definition tracks formulas through the
recursive structure. Every rule adds its principal formula(s) plus recursively collects from
sub-proofs. For leaf rules (ax, botL), the full sequent contexts Gamma and Delta are the
formulas.

**Alternative definition** (simpler, more suitable for cut-free proofs): Since each rule's
principal formula is already in the conclusion sequent's Gamma or Delta (by the membership
hypotheses), we could define formulas as just the union of the conclusion sequent's formulas:

```lean
-- Simpler alternative
def LKProof.conclusionFormulas {seq : LKSequent Atom} (_ : LKProof seq) :
    Finset (Proposition Atom) :=
  seq.ant ∪ seq.suc
```

But this doesn't capture formulas in sub-proofs (premise sequents may have formulas not in
the conclusion). A recursive definition is needed for the full subformula property.

**Recommended approach**: Actually, the cleanest statement avoids defining `formulas` altogether.
Instead, state the property directly about which formulas can appear in each sequent of the
proof tree:

#### 3.3.2 Subformula Property Statement (Recommended)

The standard textbook statement is: "Every formula appearing in a cut-free proof of
`Gamma |- Delta` is a subformula of some formula in `Gamma union Delta`."

For formalization, the cleanest approach defines the property recursively on the proof tree.
At each node, the conclusion sequent's formulas are all subformulas of the root conclusion.

```lean
/-- The subformula property for cut-free LK proofs: every formula appearing in any
sequent of a cut-free proof of `Gamma |- Delta` is a subformula of some formula
in `Gamma ∪ Delta`. -/
def CutFreeSubformulaProperty {Γ Δ : Finset (Proposition Atom)}
    (d : LKProof (Γ ⊢ₛ Δ)) (hcf : CutFree d) : Prop :=
  ∀ B ∈ d.formulas,
    ∃ C ∈ Γ ∪ Δ, B.IsSubformula C
```

**Simpler recommended statement** (avoiding the `formulas` function entirely):

Since every formula in a cut-free proof appears in some sequent, and every sequent's formulas
are subsets of the conclusion's formulas (possibly with inserted principal formulas), the
simplest correct statement focuses on the relationship at each rule application.

However, the most practically useful statement is:

```lean
/-- In a cut-free proof, every formula in any intermediate sequent is a subformula
of some formula in the conclusion. Proved by structural induction on the proof. -/
lemma CutFreeLKProof.subformula_property
    {Γ Δ : Finset (Proposition Atom)}
    (d : CutFreeLKProof (Γ ⊢ₛ Δ)) :
    ∀ B ∈ d.val.formulas,
      ∃ C ∈ Γ ∪ Δ, B.IsSubformula C
```

And the corollary via cut elimination:

```lean
/-- Subformula property for LK: every sequent provable in LK has a cut-free proof
satisfying the subformula property. -/
theorem LKProof.subformula_property
    {seq : LKSequent Atom} (d : LKProof seq) :
    ∃ d' : CutFreeLKProof seq,
      ∀ B ∈ d'.val.formulas,
        ∃ C ∈ seq.ant ∪ seq.suc, B.IsSubformula C
```

### 3.4 Proof Strategy

The core proof is by structural induction on the cut-free LK proof. CutFree ensures
`cut` is unreachable (the predicate is `False` for `cut`).

**Case analysis for each rule**:

For each rule, we need to show that every formula in `d.formulas` is a subformula of
some formula in `Gamma union Delta` of the conclusion.

1. **ax**: `formulas = Gamma ∪ Delta`. Every formula is already in the conclusion, so
   `IsSubformula.refl` suffices.

2. **botL**: Same as ax -- `formulas = Gamma ∪ Delta`.

3. **andL A B hAB d'**: The premise sequent is `insert A (insert B Gamma) |- Delta`.
   The conclusion is `Gamma |- Delta`. Since `A ∧ B ∈ Gamma`, both `A` and `B` are
   subformulas of `A ∧ B` (via `IsSubformula.and_left/and_right`), which is in `Gamma`.
   By IH on `d'`, every formula in `d'.formulas` is a subformula of something in
   `insert A (insert B Gamma) ∪ Delta`. For formulas that are subformulas of `A` or `B`,
   use transitivity with `IsSubformula.and_left/and_right`. For formulas in `Gamma ∪ Delta`,
   use `IsSubformula.refl`.

4. **andR A B hAB d₁ d₂**: The premises are `Gamma |- insert A Delta` and
   `Gamma |- insert B Delta`. Since `A ∧ B ∈ Delta`, similar reasoning using
   `IsSubformula.and_left/and_right` and transitivity.

5. **orL, orR, impL, impR**: Analogous to the and cases, using the appropriate
   `IsSubformula` lemmas.

6. **weakL A d'**: The premise is `Gamma |- Delta` and the conclusion is
   `insert A Gamma |- Delta`. By IH, every formula in `d'.formulas` is a subformula of
   something in `Gamma ∪ Delta ⊆ insert A Gamma ∪ Delta`. The `{A}` added by `formulas`
   is trivially in `insert A Gamma ∪ Delta`.

7. **weakR A d'**: Symmetric to weakL.

8. **cut**: CutFree is False, so this case is vacuously discharged.

**Key Finset lemmas needed**:
- `Finset.mem_union` / `Finset.mem_insert` -- for case-splitting membership
- `Finset.forall_mem_union` (in Mathlib.Data.Finset.Lattice.Basic) -- for splitting universals
- `Finset.mem_singleton` -- for singleton set membership
- `Finset.subset_union_left` / `subset_union_right` -- for subset lifting
- `Finset.mem_insert_self` / `Finset.mem_insert_of_mem` -- for insert membership

**Estimated complexity**: Medium. The proof is conceptually straightforward but requires
careful Finset membership bookkeeping for each of the 11 cases. Each connective case has
the same pattern: IH gives subformula of premise formulas, and inserted principal
subformulas can be lifted to the conclusion via transitivity with `IsSubformula` lemmas.

### 3.5 Alternative Simpler Design

An alternative is to avoid defining `LKProof.formulas` entirely and state the property
in terms of sequent contexts directly. Define:

```lean
/-- Every sequent in a cut-free proof has its context formulas as subformulas of
the conclusion. -/
def CutFreeLKProof.sequentsSubformulaClosed
    {Γ Δ : Finset (Proposition Atom)}
    (d : LKProof (Γ ⊢ₛ Δ)) (hcf : CutFree d) :=
  -- For each sub-proof of Γ' ⊢ₛ Δ', every formula in Γ' ∪ Δ' is a subformula
  -- of some formula in Γ ∪ Δ
```

But this requires traversing the proof tree to extract all intermediate sequents, which is
essentially equivalent to the `formulas` approach. The `formulas` function is the cleaner
design since it mirrors the natural deduction `Derivation.formulas` already in the codebase.

### 3.6 Recommended Approach

Use the `LKProof.formulas` approach for consistency with the existing pattern in
`Theory.Derivation.formulas` from the Normalization file. The parallel structure makes the
codebase more coherent.

## 4. API Summary

### New File: `SubformulaProperty.lean`

| Declaration | Type | Kind |
|------------|------|------|
| `LKProof.formulas` | `LKProof seq → Finset (Proposition Atom)` | `def` |
| `CutFreeLKProof.subformula_property` | see below | `lemma` |
| `LKProof.subformula_property` | see below | `theorem` |

**Statement of `CutFreeLKProof.subformula_property`**:
```lean
lemma CutFreeLKProof.subformula_property
    {Γ Δ : Finset (Proposition Atom)}
    (d : CutFreeLKProof (Γ ⊢ₛ Δ)) :
    ∀ B ∈ d.val.formulas,
      ∃ C ∈ Γ ∪ Δ, B.IsSubformula C
```

**Statement of `LKProof.subformula_property`**:
```lean
theorem LKProof.subformula_property
    {seq : LKSequent Atom} (d : LKProof seq) :
    ∃ d' : CutFreeLKProof seq,
      ∀ B ∈ d'.val.formulas,
        ∃ C ∈ seq.ant ∪ seq.suc, B.IsSubformula C
```

The second follows immediately from the first using `d.cutElim`.

## 5. Potential Blockers

1. **Pattern matching on `LKProof` with Finset quotient equations**: The CutElimination
   file documents this issue extensively (see "generic-sequent parameters" in the proof
   strategy section). The `formulas` function and the induction proof may need to use
   the same pattern of generic sequent parameters + subset hypotheses. However, since
   `formulas` is a simpler recursion (no mutual recursion, no well-founded recursion),
   this should be manageable.

2. **Noncomputability**: `cutElim` and `cutAdmissibility` are `noncomputable`. The
   `LKProof.subformula_property` theorem that uses `cutElim` will also need to be
   `noncomputable` or use `Nonempty`/`Exists` appropriately.

3. **Import weight**: Importing `Normalization.lean` brings in `Multiset.DershowitzManna`
   and the full NaturalDeduction infrastructure. If build times are a concern, the
   subformula definitions could be factored out. But this is a minor concern.

4. **Finset insert commutativity**: When the proof needs to show membership in
   `insert A (insert B Gamma) ∪ Delta`, managing insert-set equalities may require
   `Finset.insert_comm` or explicit rewriting. The existing codebase handles this
   routinely.

None of these are true blockers. All have known solutions in the existing codebase.

## 6. Lint Compliance

- All new declarations will have docstrings (docBlame)
- `CutFreeLKProof.subformula_property` uses `lemma` (Prop-valued, defLemma)
- `LKProof.subformula_property` uses `theorem` (Prop-valued)
- `LKProof.formulas` uses `def` (data-valued, correct)
- Names use lowerCamelCase with dots for namespace qualification
- `@[expose] public section` wrapper consistent with existing LK files

## 7. Related Work in CSLib

The codebase already has two independent subformula property proofs:

1. **Natural Deduction** (Normalization.lean): `Derivation.subformula_property` proved
   via strong normalization (Prawitz-style).

2. **Bimodal Logic** (Decidability/Saturation.lean): `subformula_property` for the
   bimodal tableau system.

This task adds a third instance, for the sequent calculus LK, completing the "textbook
trifecta" of subformula property proofs (natural deduction, sequent calculus, tableau).
