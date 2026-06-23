# Research Findings: Task 279 - Propositional Sequent Calculus LK/LJ
## Teammate A (Primary Researcher)

## Key Findings

### 1. CLL Template Analysis

The CLL formalization in `Cslib/Logics/LinearLogic/CLL/Basic.lean` provides a **one-sided** sequent calculus using `Multiset` as the context representation. Key structural observations:

**Sequent representation:**
```lean
-- CLL uses one-sided sequents (only succedent):
abbrev Sequent Atom := Multiset (Proposition Atom)
```

**Proof inductive:**
```lean
inductive Proof : Sequent Atom → Type u where
  | ax : Proof {a, a^perp}
  | cut : Proof (a ::_m Gamma) → Proof (a^perp ::_m Delta) → Proof (Gamma + Delta)
  | one : Proof {1}
  | bot : Proof Gamma → Proof (bot ::_m Gamma)
  | parr : Proof (a ::_m b ::_m Gamma) → Proof ((a par b) ::_m Gamma)
  | tensor : Proof (a ::_m Gamma) → Proof (b ::_m Delta) → Proof ((a tens b) ::_m (Gamma + Delta))
  -- ... plus oplus, with, top, quest, weaken, contract, bang
```

**Key design patterns:**
- Sequent `Proof` is indexed by the sequent itself (the conclusion)
- Returns a `Type u` (proof-relevant), not `Prop`
- Uses `Multiset` operations (`::_m`, `+`) for context manipulation
- Structural rules (weakening, contraction, exchange) are handled: exchange is implicit via Multiset equality, weakening/contraction are explicit constructors for the exponential fragment only
- `cutFree` is a boolean predicate on proofs (not a separate inductive)
- `CutFreeProof` is defined as a `Subtype`: `{ q : Proof Gamma // q.cutFree }`
- CLL's `CutElimination.lean` is a **stub** -- cut elimination is not yet implemented (only TODO comments and commented-out signatures)

**InferenceSystem integration:**
```lean
instance : HasInferenceSystem (Sequent Atom) := ⟨Proof⟩
```
This enables `⇓Gamma` notation for proofs of sequent `Gamma`.

**Critical difference for LK/LJ:** CLL uses one-sided sequents. For LK, we need **two-sided** sequents (`Finset Gamma ⊢ Finset Delta` for classical, `Finset Gamma ⊢ phi` for intuitionistic). The CLL template is useful for the proof structure pattern but not directly instantiable.

### 2. Existing Propositional Infrastructure

**Formula type** (`Cslib/Logics/Propositional/Defs.lean`):
```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (x : Atom)
  | bot
  | imp (a b : Proposition Atom)
  | and (a b : Proposition Atom)
  | or (a b : Proposition Atom)
deriving DecidableEq, BEq
```

- Negation: `abbrev neg := fun phi => imp phi bot`
- Top: `abbrev top := imp bot bot`
- Connective typeclasses: `PropositionalConnectives`, `HasAnd`, `HasOr` are registered
- `Proposition.complexity` is defined in `Tableau/Defs.lean` as the number of connective occurrences -- reusable as a measure for cut elimination

**Natural Deduction system** (`NaturalDeduction/Basic.lean`):
```lean
abbrev Ctx (Atom) := Finset (Proposition Atom)
abbrev Sequent := Ctx Atom x Proposition Atom

inductive Theory.Derivation : Ctx Atom → Proposition Atom → Type u where
  | ax   -- from theory
  | ass  -- from context (Finset membership)
  | andI, andE1, andE2
  | orI1, orI2, orE
  | impI  -- intro: insert A Gamma ⊢ B → Gamma ⊢ A → B
  | impE  -- modus ponens
```
- Uses `Finset` for contexts (exchange/contraction/weakening are free)
- Parameterized by a `Theory` (set of propositions) controlling logic strength (MPL/IPL/CPL)
- Key operations: `weak`, `weakCtx`, `weakTheory`, `cut`, `subs`

**Hilbert system** (`ProofSystem/Derivation.lean`):
```lean
inductive DerivationTree (Axioms : Proposition Atom → Prop) :
    List (Proposition Atom) → Proposition Atom → Type _ where
  | ax, assumption, modus_ponens, weakening
```
- Uses `List` for contexts
- Parameterized by an axiom predicate: `PropositionalAxiom` (classical with Peirce), `IntPropAxiom` (intuitionistic), `MinPropAxiom` (minimal)
- Tag types: `Propositional.HilbertCl`, `Propositional.HilbertInt`, `Propositional.HilbertMin`

**Bridge proofs** (`NaturalDeduction/Equivalence.lean`):
- `hilbertToND`: structural translation, computable
- `ndToHilbert`: uses deduction theorem, noncomputable
- `hilbert_iff_nd_ctx`: the primary context-based equivalence
- `hilbert_iff_nd_min/int/cl`: specializations for each logic strength
- Uses `MinimalAxioms` typeclass to bundle K, S, and six connective axiom witnesses
- Context conversion uses `List.toFinset` / `Finset.toList` with `Finset.toList_toFinset` as bridge lemma

### 3. Proposed Implementation Approach

**LK sequent type (two-sided classical):**
```lean
/-- A two-sided sequent Gamma |- Delta. -/
structure LKSequent (Atom : Type u) [DecidableEq Atom] where
  /-- The antecedent (left side). -/
  ant : Finset (Proposition Atom)
  /-- The succedent (right side). -/
  suc : Finset (Proposition Atom)
deriving DecidableEq

notation Gamma " ⊢ₛ " Delta => LKSequent.mk Gamma Delta
```

**LK proof inductive:**
```lean
inductive LKProof : LKSequent Atom → Type u where
  /-- Identity: A |- A -/
  | ax (A : Proposition Atom) : LKProof ({A} ⊢ₛ {A})
  /-- Cut: from Gamma |- Delta, A and A, Gamma' |- Delta', derive Gamma ∪ Gamma' |- Delta ∪ Delta' -/
  | cut {A} : LKProof (Gamma ⊢ₛ insert A Delta) →
              LKProof (insert A Gamma' ⊢ₛ Delta') →
              LKProof ((Gamma ∪ Gamma') ⊢ₛ (Delta ∪ Delta'))
  -- Structural rules: FREE with Finset (weakening, contraction, exchange implicit)
  /-- Left weakening (explicit for Finset-based system) -/
  | weakL {A} : LKProof (Gamma ⊢ₛ Delta) → LKProof (insert A Gamma ⊢ₛ Delta)
  /-- Right weakening -/
  | weakR {A} : LKProof (Gamma ⊢ₛ Delta) → LKProof (Gamma ⊢ₛ insert A Delta)
  -- Logical rules (left)
  | botL : LKProof (insert bot Gamma ⊢ₛ Delta)
  | andL1 {A B} : LKProof (insert A Gamma ⊢ₛ Delta) →
                   LKProof (insert (A ∧ B) Gamma ⊢ₛ Delta)
  | andL2 {A B} : LKProof (insert B Gamma ⊢ₛ Delta) →
                   LKProof (insert (A ∧ B) Gamma ⊢ₛ Delta)
  | orL {A B} : LKProof (insert A Gamma ⊢ₛ Delta) →
                LKProof (insert B Gamma ⊢ₛ Delta) →
                LKProof (insert (A ∨ B) Gamma ⊢ₛ Delta)
  | impL {A B} : LKProof (Gamma ⊢ₛ insert A Delta) →
                 LKProof (insert B Gamma' ⊢ₛ Delta') →
                 LKProof (insert (A → B) (Gamma ∪ Gamma') ⊢ₛ (Delta ∪ Delta'))
  -- Logical rules (right)
  | topR : LKProof (Gamma ⊢ₛ insert top Delta)
  | andR {A B} : LKProof (Gamma ⊢ₛ insert A Delta) →
                 LKProof (Gamma ⊢ₛ insert B Delta) →
                 LKProof (Gamma ⊢ₛ insert (A ∧ B) Delta)
  | orR1 {A B} : LKProof (Gamma ⊢ₛ insert A Delta) →
                  LKProof (Gamma ⊢ₛ insert (A ∨ B) Delta)
  | orR2 {A B} : LKProof (Gamma ⊢ₛ insert B Delta) →
                  LKProof (Gamma ⊢ₛ insert (A ∨ B) Delta)
  | impR {A B} : LKProof (insert A Gamma ⊢ₛ insert B Delta) →
                  LKProof (Gamma ⊢ₛ insert (A → B) Delta)
```

**Design decisions:**
1. **Finset on both sides** (antecedent and succedent): Exchange and contraction are implicit. Only weakening needs explicit constructors.
2. **Additive presentation**: Each logical rule keeps the context intact on the side being decomposed (e.g., `andR` shares `Gamma` and `Delta`). This is the standard additive/Gentzen-style presentation and is simpler with Finset since contexts are idempotent.
3. **Context splitting for multiplicative rules**: `impL` and `cut` split contexts (multiplicative rules). With Finsets this becomes `Gamma ∪ Gamma'`, which is the additive presentation equivalent.
4. **Explicit weakening constructors**: Needed because Finset does not automatically add members. The alternative is to use `insert` in the conclusions of every rule, but explicit weakening is cleaner.

**Alternative: All-additive presentation (recommended):**

With Finsets, the cleanest approach is a **fully additive** presentation where EVERY rule shares the full context:

```lean
inductive LKProof : LKSequent Atom → Type u where
  | ax (A : Proposition Atom) : LKProof ({A} ⊢ₛ {A})
  | cut {A} : LKProof (Gamma ⊢ₛ insert A Delta) →
              LKProof (insert A Gamma ⊢ₛ Delta) →
              LKProof (Gamma ⊢ₛ Delta)
  | weakL {A} : LKProof (Gamma ⊢ₛ Delta) → LKProof (insert A Gamma ⊢ₛ Delta)
  | weakR {A} : LKProof (Gamma ⊢ₛ Delta) → LKProof (Gamma ⊢ₛ insert A Delta)
  | botL : LKProof (insert bot Gamma ⊢ₛ Delta)
  | andL {A B} : LKProof (insert A (insert B Gamma) ⊢ₛ Delta) →
                  LKProof (insert (A ∧ B) Gamma ⊢ₛ Delta)
  | orL {A B} : LKProof (insert A Gamma ⊢ₛ Delta) →
                LKProof (insert B Gamma ⊢ₛ Delta) →
                LKProof (insert (A ∨ B) Gamma ⊢ₛ Delta)
  | impL {A B} : LKProof (Gamma ⊢ₛ insert A Delta) →
                 LKProof (insert B Gamma ⊢ₛ Delta) →
                 LKProof (insert (A → B) Gamma ⊢ₛ Delta)
  | andR {A B} : LKProof (Gamma ⊢ₛ insert A Delta) →
                 LKProof (Gamma ⊢ₛ insert B Delta) →
                 LKProof (Gamma ⊢ₛ insert (A ∧ B) Delta)
  | orR {A B} : LKProof (Gamma ⊢ₛ insert A (insert B Delta)) →
                LKProof (Gamma ⊢ₛ insert (A ∨ B) Delta)
  | impR {A B} : LKProof (insert A Gamma ⊢ₛ insert B Delta) →
                  LKProof (Gamma ⊢ₛ insert (A → B) Delta)
```

This is the **recommended approach** because:
- No context splitting (no `Gamma ∪ Gamma'` complications)
- `andL` takes BOTH conjuncts together (single premise, matches standard Gentzen)
- `orR` takes BOTH disjuncts together (single premise)
- Simpler induction principles
- Cut rule has the cleanest form: shared context on both sides minus the cut formula
- Bridge proofs are simpler because ND also uses shared contexts

**LJ sequent type (intuitionistic):**
```lean
/-- An intuitionistic sequent Gamma |- A. -/
structure LJSequent (Atom : Type u) [DecidableEq Atom] where
  ant : Finset (Proposition Atom)
  suc : Proposition Atom
```

The LJ proof differs from LK in that the succedent is a single formula (not a Finset). This enforces the intuitionistic restriction: right rules produce at most one formula on the right.

**LJ proof inductive:**
```lean
inductive LJProof : LJSequent Atom → Type u where
  | ax (A) : LJProof ({A} ⊢ᵢ A)
  | cut {A} : LJProof (Gamma ⊢ᵢ A) → LJProof (insert A Gamma ⊢ᵢ B) → LJProof (Gamma ⊢ᵢ B)
  | weakL {A} : LJProof (Gamma ⊢ᵢ B) → LJProof (insert A Gamma ⊢ᵢ B)
  | botL : LJProof (insert bot Gamma ⊢ᵢ A)
  | andL {A B} : LJProof (insert A (insert B Gamma) ⊢ᵢ C) →
                  LJProof (insert (A ∧ B) Gamma ⊢ᵢ C)
  | orL {A B} : LJProof (insert A Gamma ⊢ᵢ C) → LJProof (insert B Gamma ⊢ᵢ C) →
                LJProof (insert (A ∨ B) Gamma ⊢ᵢ C)
  | impL {A B} : LJProof (Gamma ⊢ᵢ A) → LJProof (insert B Gamma ⊢ᵢ C) →
                 LJProof (insert (A → B) Gamma ⊢ᵢ C)
  | andR {A B} : LJProof (Gamma ⊢ᵢ A) → LJProof (Gamma ⊢ᵢ B) → LJProof (Gamma ⊢ᵢ A ∧ B)
  | orR1 {A B} : LJProof (Gamma ⊢ᵢ A) → LJProof (Gamma ⊢ᵢ A ∨ B)
  | orR2 {A B} : LJProof (Gamma ⊢ᵢ B) → LJProof (Gamma ⊢ᵢ A ∨ B)
  | impR {A B} : LJProof (insert A Gamma ⊢ᵢ B) → LJProof (Gamma ⊢ᵢ A → B)
```

Note: LJ is structurally very similar to the existing ND `Theory.Derivation` (which also uses `Finset Gamma ⊢ phi`). The key difference is that LJ has explicit `cut`, `weakL`, `botL`, and `andL` rules, and ND does not have `cut` as a primitive but does have `ax` (from theory).

### 4. Cut Elimination Strategy

**Approach overview:**

Cut elimination for LK/LJ with Finset-based contexts requires an induction on a suitable measure. The standard Gentzen Hauptsatz uses double induction on:
1. The **grade** (or complexity) of the cut formula
2. The **rank** (or sum of derivation heights above the cut)

**Formula complexity measure** (reuse `Proposition.complexity` from `Tableau/Defs.lean`):
```lean
def Proposition.complexity : Proposition Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp a b => 1 + a.complexity + b.complexity
  | .and a b => 1 + a.complexity + b.complexity
  | .or a b => 1 + a.complexity + b.complexity
```

**Proof height measure** (new, following CLL's pattern):
```lean
def LKProof.height : LKProof seq → Nat
  | ax _ => 0
  | cut d1 d2 => 1 + max d1.height d2.height
  | weakL d | weakR d => 1 + d.height
  | botL => 0
  | andL d => 1 + d.height
  | orL d1 d2 => 1 + max d1.height d2.height
  | impL d1 d2 => 1 + max d1.height d2.height
  | andR d1 d2 => 1 + max d1.height d2.height
  | orR d => 1 + d.height
  | impR d => 1 + d.height
```

**Termination measure for cut elimination:**

The lexicographic pair `(cut_formula.complexity, left_height + right_height)` decreases in every recursive call:
- **Principal case** (both premises introduce the cut formula): the complexity of the new cut formula decreases.
- **Commutative cases** (one premise introduces, the other does not): the height sum decreases.
- **Key case** (cut formula is active in both premises): complexity decreases strictly.

**Lean 4 implementation approach:**
- Define `cutElim` as a function `LKProof seq → LKProof seq` that recursively eliminates the topmost cut
- Use `WellFoundedRelation` with the lexicographic product `Nat ×ₗ Nat`
- Or: define via a fuel parameter (less elegant but simpler termination)
- Or: use `Nat.strongRecOn` on the complexity measure

**Key lemmas needed:**
1. **Weakening admissibility**: `LKProof (Gamma ⊢ₛ Delta) → Gamma ⊆ Gamma' → Delta ⊆ Delta' → LKProof (Gamma' ⊢ₛ Delta')`
2. **Height-preserving weakening**: weakening does not increase proof height
3. **Mix lemma** (optional but helpful): simultaneous elimination of multiple cuts on the same formula
4. **Principal case analysis**: for each pair of connective rules where the cut formula is the principal formula of both premises

**Recommendation:** For LK with Finset, the additive presentation makes cut elimination cleaner because there is no context splitting to track. The all-additive cut rule `cut : Proof (Gamma ⊢ insert A Delta) → Proof (insert A Gamma ⊢ Delta) → Proof (Gamma ⊢ Delta)` means the output sequent is exactly `Gamma ⊢ Delta` (no unions).

**CutFree predicate** (following CLL pattern):
```lean
def LKProof.cutFree : LKProof seq → Bool
  | cut _ _ => false
  | ax _ | botL => true
  | weakL d | weakR d | andL d | orR d | impR d => d.cutFree
  | orL d1 d2 | impL d1 d2 | andR d1 d2 => d1.cutFree && d2.cutFree

abbrev LKCutFreeProof (seq : LKSequent Atom) := { p : LKProof seq // p.cutFree }
```

### 5. Bridge Proof Strategy

**LK to ND bridge (`lk_to_nd`):**

The translation maps two-sided LK sequents to ND derivations. For `LKProof (Gamma ⊢ₛ Delta)`:
- Interpret the succedent `Delta = {B1, ..., Bn}` as `B1 ∨ ... ∨ Bn` (disjunction)
- Or more naturally: prove each `Bi` in `Delta` from `Gamma` is derivable in the corresponding ND theory
- Most direct approach: for LK, prove `lk_to_nd : LKProof (Gamma ⊢ₛ {A}) → CPL.Derivation Gamma A` (single-conclusion case), then derive the general case using classical disjunction

**ND to LK bridge (`nd_to_lk`):**

Map each ND constructor to an LK derivation:
- `ax h_mem_T` -> Use the theory axiom `A ∈ T`. For CPL theory, each axiom `A ∈ CPL` can be shown derivable as `⊢ₛ {A}` in LK.
- `ass h_mem` -> `ax A` followed by `weakL` to extend the context
- `andI` -> `andR`
- `andE1` -> `andL` + appropriate weakening
- `andE2` -> `andL` + appropriate weakening
- `orI1` -> `orR1`
- `orI2` -> `orR2`
- `orE` -> `orL` + `cut` (or use `impL` approach)
- `impI` -> `impR`
- `impE` -> `impL` + `cut` or a derived rule

**Hilbert to LK bridge (`hilbert_to_lk`):**

Each Hilbert axiom schema is derivable in LK:
- `implyK`: `{phi} ⊢ₛ {psi → phi}` by `impR`, `weakL`, `ax`
- `implyS`: derivable using `impR` and `impL` in combination
- `efq`: `{bot} ⊢ₛ {phi}` by `botL`, `weakR`
- `peirce`: requires the classical rule (multiple formulas on the right)
- `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`: straightforward

Modus ponens preserves LK derivability: if `⊢ₛ {A → B}` and `⊢ₛ {A}` then `⊢ₛ {B}` by `cut` and `impL`.

**LK to Hilbert bridge (`lk_to_hilbert`):**

Induction on LK proof. Each LK rule preserves Hilbert derivability:
- `ax` -> identity theorem in Hilbert system (K + S derive `phi → phi`)
- `weakL/weakR` -> Hilbert weakening
- `botL` -> EFQ axiom
- `impR` -> deduction theorem
- `impL` -> derived from MP and weakening
- `andL/andR/orL/orR` -> corresponding Hilbert axiom schemas

**Recommended bridge architecture:**

Use the **existing Hilbert-ND bridge** as the model. The cleanest path is:

1. `LKProof → ND.Derivation (CPL theory)` (LK to ND)
2. `ND.Derivation (CPL theory) → LKProof` (ND to LK)
3. Compose with existing `hilbert_iff_nd_cl` to get `hilbert_iff_lk`

This approach reuses the existing bridge infrastructure and only requires writing two new functions. The LJ case is analogous using IPL.

**For LJ:**
1. `LJProof → ND.Derivation (IPL theory)` (LJ to ND with IPL)
2. `ND.Derivation (IPL theory) → LJProof` (ND to LJ)
3. Compose with `hilbert_iff_nd_int` to get `hilbert_iff_lj`

## Evidence/Examples

### CLL Proof Structure (from `Basic.lean`)
```lean
-- File: Cslib/Logics/LinearLogic/CLL/Basic.lean, lines 190-206
inductive Proof : Sequent Atom → Type u where
  | ax : Proof {a, a⫠}
  | cut : Proof (a ::ₘ Γ) → Proof (a⫠ ::ₘ Δ) → Proof (Γ + Δ)
  | one : Proof {1}
  | bot : Proof Γ → Proof (⊥ ::ₘ Γ)
  -- ...
```

### ND Derivation Structure (from `NaturalDeduction/Basic.lean`)
```lean
-- File: Cslib/Logics/Propositional/NaturalDeduction/Basic.lean, lines 117-146
inductive Theory.Derivation {T : Theory Atom} : Ctx Atom → Proposition Atom → Type u where
  | ax {Γ : Ctx Atom} {A : Proposition Atom} (_ : A ∈ T) : Derivation Γ A
  | ass {Γ : Ctx Atom} {A : Proposition Atom} (_ : A ∈ Γ) : Derivation Γ A
  | andI, andE1, andE2, orI1, orI2, orE, impI, impE
```

### Bridge Pattern (from `Equivalence.lean`)
```lean
-- File: NaturalDeduction/Equivalence.lean, lines 332-343
theorem hilbert_iff_nd_ctx
    {Axioms : PL.Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    {Γ : Ctx Atom} {φ : PL.Proposition Atom} :
    Deriv Axioms Γ.toList φ ↔
    DerivableIn (AxiomTheory Axioms : Theory Atom) (Γ ⊢ φ) := by
  constructor
  · intro h; have := hilbert_to_nd_deriv h; rwa [Finset.toList_toFinset] at this
  · intro h; exact nd_to_hilbert_deriv h
```

### Axiom Hierarchy (from `Axioms.lean`)
```lean
-- Three axiom levels:
-- MinPropAxiom: K, S, andI, andE1, andE2, orI1, orI2, orE (8 axioms)
-- IntPropAxiom: + efq (9 axioms)
-- PropositionalAxiom: + peirce (10 axioms)
```

### Key Finset Operations Used in ND
```lean
-- Context as Finset: abbrev Ctx (Atom) := Finset (Proposition Atom)
-- Finset.insert for adding hypotheses
-- Finset.Subset for weakening
-- Finset union for cut contexts
```

## Reuse Check Results

**What already exists (REUSE):**
1. `PL.Proposition` -- formula type (Defs.lean) -- reuse directly
2. `PL.Ctx` = `Finset (Proposition Atom)` -- reuse for antecedent of LK/LJ
3. `Proposition.complexity` -- formula complexity measure (Tableau/Defs.lean) -- reuse for cut elimination
4. `Theory.Derivation` (ND system) -- target of bridge proofs
5. `DerivationTree` (Hilbert system) -- target of bridge proofs
6. `hilbert_iff_nd_ctx` bridge -- compose with new SC bridges
7. `InferenceSystem` typeclass -- register LK/LJ as instances
8. `PropositionalConnectives` / `HasAnd` / `HasOr` -- notation already set up
9. `Finset.insert`, `Finset.Subset`, `Finset.union` API from Mathlib

**What needs to be created (NEW):**
1. `LKSequent` type -- two-sided sequent structure
2. `LKProof` inductive -- classical sequent calculus proof
3. `LJSequent` type (or reuse existing `Sequent = Ctx x Proposition`)
4. `LJProof` inductive -- intuitionistic sequent calculus proof
5. `LKProof.height` / `LJProof.height` -- proof height measures
6. `LKProof.cutFree` / `LJProof.cutFree` -- cut-free predicates
7. `cutElim` -- cut elimination theorems
8. Bridge functions: `lk_to_nd`, `nd_to_lk`, `lj_to_nd`, `nd_to_lj`
9. Composed bridges: `hilbert_iff_lk`, `nd_iff_lk`, `hilbert_iff_lj`, `nd_iff_lj`
10. `InferenceSystem` instances for LK/LJ

**What does NOT exist in CSLib or Mathlib:**
- No sequent calculus formalization exists anywhere in CSLib (only CLL's one-sided variant)
- Mathlib has no sequent calculus formalization (confirmed by lean_leansearch and lean_leanfinder)
- The `itauto` tactic in Mathlib implements G4ip internally but does not expose a reusable sequent calculus API

**Key observation for LJ:** The existing `PL.Sequent = Ctx Atom x Proposition Atom` type from `NaturalDeduction/Basic.lean` has EXACTLY the same shape as an LJ sequent (`Finset antecedent, single conclusion`). However, reusing it directly is inadvisable because the ND module's `Sequent` is tied to the ND derivation system and its theory parameter. Defining a fresh `LJSequent` (or just using `Finset (Proposition Atom) x Proposition Atom`) is cleaner.

## File Organization Recommendation

```
Cslib/Logics/Propositional/SequentCalculus/
  Defs.lean          -- LKSequent, LJSequent types
  LK/
    Basic.lean       -- LKProof inductive, InferenceSystem instance
    CutElimination.lean  -- Hauptsatz for LK
    Soundness.lean   -- LK soundness (LK → semantics)
    Completeness.lean -- LK completeness (semantics → LK)
  LJ/
    Basic.lean       -- LJProof inductive, InferenceSystem instance
    CutElimination.lean  -- Hauptsatz for LJ
  Equivalence.lean   -- Bridges: lk_iff_nd, lk_iff_hilbert, lj_iff_nd, lj_iff_hilbert
```

## Tactic Survey Results

For the bridge proofs and structural lemmas:
- `grind` -- excellent for Finset equalities (already used extensively in CLL and ND)
- `simp` with Finset lemmas -- for insert/union/subset manipulations
- `aesop` -- may help with routine case analysis in bridge translations
- `omega` -- for height/complexity arithmetic in cut elimination
- `induction ... with` -- essential for structural induction on proofs

## Confidence Level

| Area | Confidence | Notes |
|------|-----------|-------|
| CLL Template Analysis | High | Thoroughly read, well-documented |
| Propositional Infrastructure | High | All key files read, API mapped |
| Implementation Approach | High | Additive Finset-based design is standard and proven |
| Cut Elimination Strategy | Medium | Correct approach identified; termination proof details need careful work |
| Bridge Proof Strategy | High | Clear composition path through existing bridges |
