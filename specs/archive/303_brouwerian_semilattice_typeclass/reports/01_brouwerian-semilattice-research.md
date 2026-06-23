# Research Report: Brouwerian Semilattice Typeclass

## Task 303 -- Algebraic Semantics Chain

### 1. Executive Summary

This task defines `BrouwerianSemilattice`, a new typeclass capturing the algebraic semantics
of the conjunction-implication-verum fragment IPL(and,imp,top) of intuitionistic logic. Mathlib
has no such class: the gap between `SemilatticeInf` and `GeneralizedHeytingAlgebra` (which
requires `SemilatticeSup`) is real and confirmed by exhaustive search. The implementation is
straightforward: one class, one forgetful instance, an evaluator function, and approximately
20 algebraic lemmas -- all verified to compile in test snippets.

### 2. Mathlib Typeclass Hierarchy Analysis

#### 2.1 GeneralizedHeytingAlgebra (GHA)

**Definition** (Mathlib, `Mathlib.Order.Heyting.Basic`, line 139):
```lean
class GeneralizedHeytingAlgebra (α : Type*) extends Lattice α, OrderTop α, HImp α where
  le_himp_iff (a b c : α) : a ≤ b ⇨ c ↔ a ⊓ b ≤ c
```

Key observation: GHA extends `Lattice`, which bundles **both** `SemilatticeInf` and
`SemilatticeSup`. The adjunction axiom `le_himp_iff` only mentions `⊓` and `⇨`, but GHA
nonetheless **requires** `⊔` and proves `DistribLattice` as a consequence (line 367-369):

```lean
instance (priority := 100) GeneralizedHeytingAlgebra.toDistribLattice :
    DistribLattice α :=
  DistribLattice.ofInfSupLe fun a b c => by
    simp_rw [inf_comm a, ← le_himp_iff, sup_le_iff, le_himp_iff, ← sup_le_iff]; rfl
```

This proof uses `sup_le_iff` and `sup_le_iff`, confirming that `⊔` is structurally needed
for the `DistribLattice` conclusion.

#### 2.2 HImp

**Definition** (Mathlib, `Mathlib.Order.Notation.lean`, line 148):
```lean
class HImp (α : Type*) where
  himp : α → α → α
```

Pure syntax class -- provides the `⇨` notation. No axioms.

#### 2.3 The Gap

The Brouwerian semilattice fills this gap in the hierarchy:

```
SemilatticeInf + OrderTop + HImp + adjunction
       ↑ (forget ⊔)
GeneralizedHeytingAlgebra (= Lattice + OrderTop + HImp + adjunction)
       ↑ (add ⊥)
HeytingAlgebra
       ↑ (add excluded middle / complement)
BooleanAlgebra
```

**Confirmed non-existence**: `lean_leansearch`, `lean_loogle`, `lean_leanfinder`, and
`lean_local_search` all return no results for Brouwerian semilattice, implicative semilattice,
or relatively pseudo-complemented semilattice in Mathlib.

### 3. BrouwerianSemilattice Design

#### 3.1 Class Definition

```lean
class BrouwerianSemilattice (α : Type*) extends SemilatticeInf α, OrderTop α, HImp α where
  /-- The adjunction: `a ≤ b ⇨ c ↔ a ⊓ b ≤ c`. -/
  le_himp_iff (a b c : α) : a ≤ b ⇨ c ↔ a ⊓ b ≤ c
```

**Verified**: Compiles without error. Instance resolution correctly synthesizes
`PartialOrder`, `Preorder`, `LE`, `LT` from `SemilatticeInf`.

#### 3.2 Forgetful Instance

```lean
instance (priority := 100) GeneralizedHeytingAlgebra.toBrouwerianSemilattice
    [GeneralizedHeytingAlgebra α] : BrouwerianSemilattice α where
  le_himp_iff := GeneralizedHeytingAlgebra.le_himp_iff
```

**Verified**: Compiles. Priority 100 follows the Mathlib convention for "see note [lower
instance priority]" -- prevents this from being preferred over a direct `BrouwerianSemilattice`
instance when both are available.

**Diamond check**: The `SemilatticeInf` and `OrderTop` from the forgetful instance are
definitionally equal to those from `GeneralizedHeytingAlgebra`:
```lean
example : @BrouwerianSemilattice.toSemilatticeInf α
    (GeneralizedHeytingAlgebra.toBrouwerianSemilattice) =
    @Lattice.toSemilatticeInf α (GeneralizedHeytingAlgebra.toLattice) := rfl
```

#### 3.3 ofHImp Constructor

```lean
abbrev BrouwerianSemilattice.ofHImp [SemilatticeInf α] [OrderTop α]
    (himp : α → α → α)
    (le_himp_iff : ∀ a b c : α, a ≤ himp b c ↔ a ⊓ b ≤ c) :
    BrouwerianSemilattice α
```

Analogous to `HeytingAlgebra.ofHImp`. Useful for constructing instances when `HImp` is not
yet registered.

### 4. Algebraic Identities (Lemma Catalog)

All lemmas below have been verified to compile under `[BrouwerianSemilattice α]` alone,
with no `⊔` dependency. They mirror GHA lemmas but work in the strictly weaker setting.

#### 4.1 Core Adjunction Variants

| Lemma | Statement | GHA Equivalent |
|-------|-----------|----------------|
| `le_himp_iff` | `a ≤ b ⇨ c ↔ a ⊓ b ≤ c` | `le_himp_iff` |
| `le_himp_iff'` | `a ≤ b ⇨ c ↔ b ⊓ a ≤ c` | `le_himp_iff'` |
| `le_himp_comm` | `a ≤ b ⇨ c ↔ b ≤ a ⇨ c` | `le_himp_comm` |

#### 4.2 Basic Identities

| Lemma | Statement | Notes |
|-------|-----------|-------|
| `himp_self` | `a ⇨ a = ⊤` | `@[simp]` |
| `top_himp` | `⊤ ⇨ a = a` | `@[simp]` |
| `himp_top` | `a ⇨ ⊤ = ⊤` | `@[simp]` |
| `himp_eq_top_iff` | `a ⇨ b = ⊤ ↔ a ≤ b` | Deduction theorem, `@[simp]` |
| `le_himp` | `a ≤ b ⇨ a` | Weakening |
| `le_himp_iff_left` | `a ≤ a ⇨ b ↔ a ≤ b` | Uses `inf_idem` |

#### 4.3 Modus Ponens / Interaction

| Lemma | Statement | Notes |
|-------|-----------|-------|
| `himp_inf_le` | `(a ⇨ b) ⊓ a ≤ b` | Modus ponens |
| `inf_himp_le` | `a ⊓ (a ⇨ b) ≤ b` | Commutativity variant |
| `inf_himp` | `a ⊓ (a ⇨ b) = a ⊓ b` | `@[simp]` |
| `himp_inf_self` | `(a ⇨ b) ⊓ a = b ⊓ a` | `@[simp]` |

#### 4.4 Currying and Composition

| Lemma | Statement | Notes |
|-------|-----------|-------|
| `himp_himp` | `a ⇨ b ⇨ c = (a ⊓ b) ⇨ c` | Currying/uncurrying |
| `himp_left_comm` | `a ⇨ b ⇨ c = b ⇨ a ⇨ c` | Commutativity of currying |
| `himp_idem` | `b ⇨ b ⇨ a = b ⇨ a` | Idempotence |
| `himp_triangle` | `(a ⇨ b) ⊓ (b ⇨ c) ≤ a ⇨ c` | Transitivity |
| `le_himp_himp` | `a ≤ (a ⇨ b) ⇨ b` | Contraposition base |

#### 4.5 Monotonicity

| Lemma | Statement | Notes |
|-------|-----------|-------|
| `himp_le_himp_left` | `a ≤ b → c ⇨ a ≤ c ⇨ b` | Monotone in 2nd arg |
| `himp_le_himp_right` | `a ≤ b → b ⇨ c ≤ a ⇨ c` | Antitone in 1st arg |
| `himp_le_himp` | `a ≤ b → c ≤ d → b ⇨ c ≤ a ⇨ d` | Combined, `@[gcongr]` |

#### 4.6 Distribution

| Lemma | Statement | Notes |
|-------|-----------|-------|
| `himp_inf_distrib` | `a ⇨ b ⊓ c = (a ⇨ b) ⊓ (a ⇨ c)` | `⇨` distributes over `⊓` |

#### 4.7 Galois Connection

| Lemma | Statement | Notes |
|-------|-----------|-------|
| `gc_inf_himp` | `GaloisConnection (a ⊓ ·) (a ⇨ ·)` | The adjunction as GaloisConnection |

#### 4.8 Lemmas That Do NOT Transfer (Require `⊔`)

These GHA lemmas cannot be stated or proved in BrouwerianSemilattice:

- `sup_himp_distrib` -- uses `⊔`
- `sup_himp_self_left`, `sup_himp_self_right` -- use `⊔`
- `Codisjoint.*` lemmas -- `Codisjoint` requires `⊔`
- `GeneralizedHeytingAlgebra.toDistribLattice` -- proves `⊔` distributivity

### 5. BrouwerianEvaluate Design

#### 5.1 Design Decision: Work on Existing `PL.Proposition`

Two approaches were considered:

**Option A**: Define a new `BrouwerianFormula` inductive with only `atom`, `top`, `imp`, `and`.

**Option B**: Define `BrouwerianEvaluate` on existing `PL.Proposition`, defaulting `bot` and
`or` to `⊤`.

**Recommendation: Option B**. Reasons:
1. Task 302 will define `IsOrBotFree` predicate on `Proposition`.
2. Existing `AlgEvaluate` works on `Proposition` -- consistency.
3. `Proposition.top = imp bot bot` evaluates correctly: `⊤ ⇨ ⊤ = ⊤`.
4. Integration with downstream tasks (306, 308) that work with `Proposition`.
5. The `IsOrBotFree` independence lemma is the natural companion.

```lean
def BrouwerianEvaluate {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) : PL.Proposition Atom → H
  | .atom x => v x
  | .bot => ⊤         -- default for or-bot-free fragment
  | .imp a b => BrouwerianEvaluate v a ⇨ BrouwerianEvaluate v b
  | .and a b => BrouwerianEvaluate v a ⊓ BrouwerianEvaluate v b
  | .or a b => ⊤      -- default for or-bot-free fragment
```

**Key property**: On `IsOrBotFree` formulas, `BrouwerianEvaluate v A = AlgEvaluate v ⊤ A`
when the BS instance comes from a GHA (where `bot_val = ⊤`). This bridge connects BS
evaluation to the existing algebraic framework.

**Alternative**: If the planner prefers cleaner types, define `BrouwerianEvaluate` on a
new `BrouwerianFormula` type and provide an embedding from `{A : Proposition // IsOrBotFree A}`
to `BrouwerianFormula`. But this adds complexity without clear benefit given the downstream
task chain.

#### 5.2 Simp Lemmas

Standard `@[simp]` unfolding lemmas for each constructor, mirroring `AlgEvaluate_atom`,
`AlgEvaluate_imp`, etc.

### 6. Instances

#### 6.1 Required Instances

| Instance | Source | Priority |
|----------|--------|----------|
| `GeneralizedHeytingAlgebra.toBrouwerianSemilattice` | Forgetful | 100 |
| `BrouwerianSemilattice.prod` | Direct | default |
| `BrouwerianSemilattice.pi` | Direct | default |

All verified to compile.

#### 6.2 Not Needed

- No `Prop` instance needed (comes via GHA forgetful path)
- No `Bool` instance needed (same)
- No `WithBot` instance (task 307 handles free join completion)

### 7. File Location and Imports

**File**: `Cslib/Foundations/Order/BrouwerianSemilattice.lean`

**Imports needed**:
```lean
import Cslib.Init
public import Mathlib.Order.Heyting.Basic  -- for HImp, GHA, le_himp_iff
```

`Mathlib.Order.Heyting.Basic` already transitively imports `Mathlib.Order.BoundedOrder.Basic`
(for `OrderTop`) and `Mathlib.Order.Lattice` (for `SemilatticeInf`).

**New directory**: `Cslib/Foundations/Order/` does not yet exist and must be created.

**Barrel update**: `lake exe mk_all --module` after file creation.

### 8. BrouwerianEvaluate Placement

**Option A**: Place in `Cslib/Foundations/Order/BrouwerianSemilattice.lean` alongside the
typeclass. This keeps the file self-contained but requires importing `Cslib.Logics.Propositional.Defs`.

**Option B (Recommended)**: Place `BrouwerianEvaluate` in a separate file
`Cslib/Logics/Propositional/Semantics/Algebra/Brouwerian.lean`, following the existing pattern
where `AlgEvaluate` lives in `Semantics/Algebra.lean`.

This separation keeps `Cslib.Foundations.Order.BrouwerianSemilattice` as a pure order-theory
file with no logic dependencies, while the evaluator lives in the semantics module where it
belongs.

### 9. Naming Convention

Follow Mathlib convention: lemmas in `section BrouwerianSemilattice` with the same names as
their GHA counterparts (the different typeclass assumption disambiguates). This allows users
to switch between BS and GHA lemma sets by changing the typeclass assumption.

However, if there's concern about confusion during the transition period, a `bs_` prefix
could be used. The planner should decide based on CSLib convention preferences.

### 10. Lint Compliance Checklist

- [ ] All declarations have docstrings (docBlame)
- [ ] `Prop`-valued declarations use `theorem`/`lemma` (defLemma)
- [ ] Names use lowerCamelCase (defsWithUnderscore)
- [ ] `@[simp]` lemmas have verified LHS (simpNF)
- [ ] File imports `Cslib.Init` first
- [ ] `@[expose] public section` for visibility

### 11. Dependencies and Downstream Impact

**This task depends on**: Nothing (task 302 is independent).

**Downstream dependents**:
- **Task 306** (Brouwerian Soundness/Completeness): Uses `BrouwerianSemilattice` and
  `BrouwerianEvaluate` directly.
- **Task 307** (Free Join Completion): Constructs `SemilatticeSup` on top of
  `BrouwerianSemilattice` to get a full `GeneralizedHeytingAlgebra`.
- **Task 308** (IPL Conservative over Conj-Imp): Uses the bridge between BS and GHA evaluation.

### 12. Risk Assessment

**Low risk**. The implementation is straightforward:
- Class definition: 5 lines
- Forgetful instance: 3 lines
- Lemmas: ~20 lemmas, all verified to compile in test snippets
- Evaluator: ~10 lines
- Instances (Prod, Pi): ~8 lines total

**No sorries expected**. All proofs follow directly from the adjunction and standard
`SemilatticeInf` + `OrderTop` lemmas.

**Potential issue**: Naming conflicts with GHA lemmas if both are in scope. Mitigated by using
a section/namespace and relying on typeclass-based disambiguation.

### 13. Literature References

- **Rasiowa (1974)**: *An Algebraic Approach to Non-Classical Logics*. Defines implicative
  algebras (= Brouwerian semilattices with the adjunction). Chapter IV discusses the
  conjunction-implication fragment.

- **Kohler (1981)**: *Brouwerian semilattices*. Studies the variety of Brouwerian semilattices
  as an algebraic counterpart to the conjunction-implication fragment of IPL. Proves the
  free algebra construction that task 307 will formalize.

- **Nemitz (1965)**: *Implicative semi-lattices*. Original algebraic study of the class.
  The name "implicative semilattice" is used interchangeably with "Brouwerian semilattice"
  in the literature.
