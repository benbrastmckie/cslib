# Research Report: Prawitz-Style Normalization for ND Derivations (Task 290)

- **Task**: 290 -- ND Normalization and Subformula Property
- **Date**: 2026-06-23
- **Session**: sess_1750723200_orchestrate_batch_290
- **Status**: Research complete

## 1. Executive Summary

This task formalizes Prawitz-style normalization for the `Theory.Derivation` inductive type in
`Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`. The existing infrastructure is
well-suited: `Derivation` is `Type u` (enabling computable functions), has 10 constructors
matching the Prawitz presentation, and the `subs` (substitution) operation needed for reduction
steps is already defined. The five connective-redex patterns are all matchable via nested
pattern matching on the inductive.

**Key finding**: A direct recursive normalization function is feasible but requires a custom
well-founded measure (the auto-generated `sizeOf` includes formula sizes, which can grow
during reduction). The recommended approach is a "normalize-then-recurse" strategy using
a decreasing measure on redex count or derivation grade, following Prawitz Ch. IV-V.

**Dependency status**: Task 266 is completed and archived. Its deliverables (documentation
fixes, `HasDia`, decidable tautology, propositional tableau) do not directly affect this task.
The ND `Derivation` type and `subs` operation needed here were already in place before task 266.

## 2. Existing CSLib Infrastructure

### 2.1 The `Theory.Derivation` Type

**File**: `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`, line 117

```lean
inductive Theory.Derivation {T : Theory Atom} : Ctx Atom → Proposition Atom → Type u where
  | ax {Γ : Ctx Atom} {A : Proposition Atom} (_ : A ∈ T) : Derivation Γ A
  | ass {Γ : Ctx Atom} {A : Proposition Atom} (_ : A ∈ Γ) : Derivation Γ A
  | andI {A B} (G : Ctx Atom) : Derivation G A → Derivation G B → Derivation G (A ∧ B)
  | andE1 {A B} (G : Ctx Atom) : Derivation G (A ∧ B) → Derivation G A
  | andE2 {A B} (G : Ctx Atom) : Derivation G (A ∧ B) → Derivation G B
  | orI1 {A B} (G : Ctx Atom) : Derivation G A → Derivation G (A ∨ B)
  | orI2 {A B} (G : Ctx Atom) : Derivation G B → Derivation G (A ∨ B)
  | orE {A B C} (G : Ctx Atom) : Derivation G (A ∨ B) →
      Derivation (insert A G) C → Derivation (insert B G) C → Derivation G C
  | impI {A B} (Γ : Ctx Atom) : Derivation (insert A Γ) B → Derivation Γ (A → B)
  | impE {Γ} {A B} : Derivation Γ (A → B) → Derivation Γ A → Derivation Γ B
```

Key properties:
- **Universe**: `Type u` (not `Prop`), so computable functions on derivations are possible.
- **Contexts**: `Finset (Proposition Atom)`, giving implicit contraction and exchange.
- **Theory parameter**: Controls logic strength (MPL = empty, IPL = efq, CPL = dne).
- **10 constructors**: Matches Prawitz's presentation exactly (bot-elimination is derived).

### 2.2 The `Proposition` Type

**File**: `Cslib/Logics/Propositional/Defs.lean`, line 81

```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (x : Atom) | bot | imp (a b) | and (a b) | or (a b)
```

- `DecidableEq` instance derived automatically.
- `sizeOf` auto-generated: `sizeOf (imp A B) = 1 + sizeOf A + sizeOf B`, etc.
- Negation, top, biconditional are `abbrev`s (definitional reductions).

### 2.3 Substitution (`subs`)

**File**: `Basic.lean`, line 281

```lean
def Theory.Derivation.subs {Γ Γ' Δ : Ctx Atom} {B : Proposition Atom}
    (Ds : ∀ A ∈ Γ', T⇓(Δ ⊢ A)) : T.Derivation Γ B → T.Derivation (Γ \ Γ' ∪ Δ) B
```

This is the structural substitution operation that replaces hypotheses in a derivation.
It traverses the derivation tree and replaces each `ass` whose formula is in `Γ'` with the
corresponding derivation from `Ds`. It depends on `Classical.choice` and `Quot.sound`
(due to `Finset` membership decisions) but is **not** marked `noncomputable`.

### 2.4 Cut Rule

**File**: `Basic.lean`, line 252

```lean
def Theory.Derivation.cut {Γ Δ : Ctx Atom} {A B : Proposition Atom}
    (D : T⇓(Γ ⊢ A)) (E : T⇓(insert A Δ ⊢ B)) : T⇓((Γ ∪ Δ) ⊢ B)
```

This uses `impE` and `impI` rather than `subs`. For normalization, `subs` is the more
appropriate tool since it performs direct substitution.

### 2.5 Weakening

**File**: `Basic.lean`, line 207

```lean
def Theory.Derivation.weak {T T'} {Γ Δ} {A} (hTheory : T ⊆ T') (hCtx : Γ ⊆ Δ) :
    T.Derivation Γ A → T'.Derivation Δ A
```

Weakening is structural recursion on the derivation. Essential for the normalization function
since reductions may need to adjust contexts.

### 2.6 Existing Analogues in CSLib

- **Cut Elimination (LJ)**: `Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean`
  uses lexicographic induction on `(sizeOf A, d₁.height + d₂.height)`. The `cutAdmissibility`
  theorem is stated but the proof is incomplete (marked as a follow-up). This is the closest
  structural analogue to normalization.

- **Strong Normalization (STLC)**: `Cslib/Languages/LambdaCalculus/LocallyNameless/Stlc/StrongNorm.lean`
  uses Tait's saturated sets method for the simply-typed lambda calculus. This proves
  termination of full beta-reduction, not normalization in the proof-theoretic sense.

- **Confluence**: `Cslib/Foundations/Relation/Confluence.lean` provides `Diamond.toConfluent`
  and Newman's lemma. Could be reused if we define reduction as a relation and prove confluence
  separately, though this is not strictly needed for a direct normalization function.

- **Subformula closure (Bimodal)**: `Cslib/Logics/Bimodal/Syntax/Subformulas.lean` defines
  `Formula.subformulas` for bimodal logic. The propositional logic module has no corresponding
  definition yet. We need to define `Proposition.subformulas` for the subformula property.

## 3. Prawitz-Style Normalization: Proof Structure

### 3.1 Maximal Formulas and Redexes (Prawitz Ch. IV)

A **maximal formula** in a derivation is a formula occurrence that is both:
1. The conclusion of an introduction rule, and
2. The major premise of the immediately following elimination rule.

The five redex patterns in CSLib's `Derivation`:

| Redex | Pattern | Reduction |
|-------|---------|-----------|
| imp-redex | `impE (impI Γ d_body) d_arg` | `subs {A ↦ d_arg} d_body` |
| and-redex-L | `andE1 Γ (andI Γ d₁ d₂)` | `d₁` |
| and-redex-R | `andE2 Γ (andI Γ d₁ d₂)` | `d₂` |
| or-redex-L | `orE Γ (orI1 Γ d) d₁ d₂` | `subs {A ↦ d} d₁` |
| or-redex-R | `orE Γ (orI2 Γ d) d₁ d₂` | `subs {B ↦ d} d₂` |

**Verified**: All five patterns compile as nested pattern matches on `Theory.Derivation`.

### 3.2 Context Arithmetic for Reductions

The imp-redex reduction requires:
- `d_body : T.Derivation (insert A Γ) B`
- `d_arg : T.Derivation Γ A`
- Result: `T.Derivation Γ B`
- Via `subs` with `Γ' = {A}`, `Δ = Γ`: result context `(insert A Γ) \ {A} ∪ Γ = Γ`.

**Verified**: `(insert A Γ) \ {A} ∪ Γ = Γ` for Finsets (proved via `ext; simp; tauto`).

The or-redex-L reduction requires:
- `d : T.Derivation Γ A`
- `d₁ : T.Derivation (insert A Γ) C`
- Result: `T.Derivation Γ C`
- Same pattern as imp-redex: substitute `d` for `A` in `d₁`.

The and-redex reductions are trivial (just projecting a sub-derivation).

### 3.3 The `isNormal` Predicate

A derivation is **normal** if it contains no maximal formula. This is a recursive predicate
on the derivation tree:

```lean
def Theory.Derivation.isNormal : T.Derivation Γ A → Prop
  | .ax _ => True
  | .ass _ => True
  | .andI _ d₁ d₂ => d₁.isNormal ∧ d₂.isNormal
  | .andE1 _ (.andI _ _ _) => False  -- and-redex
  | .andE1 _ d => d.isNormal
  | .andE2 _ (.andI _ _ _) => False  -- and-redex
  | .andE2 _ d => d.isNormal
  | .orI1 _ d => d.isNormal
  | .orI2 _ d => d.isNormal
  | .orE _ (.orI1 _ _) _ _ => False  -- or-redex
  | .orE _ (.orI2 _ _) _ _ => False  -- or-redex
  | .orE _ d d₁ d₂ => d.isNormal ∧ d₁.isNormal ∧ d₂.isNormal
  | .impI _ d => d.isNormal
  | .impE (.impI _ _) _ => False     -- imp-redex
  | .impE d₁ d₂ => d₁.isNormal ∧ d₂.isNormal
```

This should be `Decidable` (derivable via `DecidableEq` on `Proposition`, since we can
pattern-match on the constructor heads). Making it `Bool`-valued or providing a `Decidable`
instance is straightforward.

### 3.4 Termination of Normalization

**Challenge**: A single reduction step can **increase** the size of the derivation.
The imp-redex `impE (impI Γ d_body) d_arg` reduces to `subs {A ↦ d_arg} d_body`, which
replaces every occurrence of `ass (A ∈ insert A Γ)` in `d_body` by `d_arg`. If `A` appears
`n` times in `d_body`, the result contains `n` copies of `d_arg`, potentially much larger.

**Prawitz's approach** (Ch. IV, sec. 3): Define the **degree** of a derivation as the maximum
complexity (formula size) of its maximal formulas. A reduction step on a maximal formula of
maximal degree reduces the degree, since substitution introduces no new maximal formulas of
the same or higher degree. The key insight:

1. **Grade** = maximum formula complexity among all maximal formulas.
2. **Reducing the topmost redex of maximum grade** decreases the grade (or reduces the count
   of redexes at that grade).
3. The measure `(grade, redex_count_at_grade)` decreases lexicographically.

**Alternative approach** (simpler for Lean 4): Instead of tracking grade explicitly, define
a **weight** function that combines:
- The sum of formula complexities of all maximal formulas in the derivation.
- This strictly decreases under any single reduction step (proved by Prawitz).

### 3.5 Recommended Termination Strategy

**Option A: Direct recursive function with WellFoundedRelation**

Define `normalize` as a recursive function with `termination_by` on a custom measure.
The measure would be a tuple `(maxGrade d, redexCount d)` under lexicographic ordering.
This requires proving that each reduction step decreases this measure.

**Option B: Iterative approach with fuel**

Use `Nat.rec` with a bound on the number of reduction steps. Prove that the bound
`totalRedexWeight d` suffices. This avoids complex well-founded recursion but produces
a less elegant statement.

**Option C: Relation-based approach using `Relation.ReflTransGen`**

Define one-step reduction as a relation `Reduces : Derivation Γ A → Derivation Γ A → Prop`,
prove it is well-founded (via the weight measure), then use `WellFounded.fix` to extract
the normalization function. This is the cleanest from a mathematical perspective and
connects to the existing `Cslib/Foundations/Relation/Confluence.lean` infrastructure.

**Recommendation**: Option A for the implicational fragment milestone, potentially refactored
to Option C for the full connective extension. Option A is most directly implementable.

## 4. Proposed Module Structure

### 4.1 File Location

`Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`

This follows the existing module organization (all ND files under `NaturalDeduction/`).

### 4.2 Definitions to Add

1. **`Proposition.subformulas`**: List of subformulas of a proposition (including itself).
   Pattern: follow the existing `Cslib.Logic.Bimodal.Formula.subformulas`.

2. **`Proposition.IsSubformula`**: `A.IsSubformula B` iff `A` appears in `B.subformulas`.

3. **`Theory.Derivation.height`**: Height (depth) of a derivation tree. Already tested
   as computable.

4. **`Theory.Derivation.isNormal`**: The normality predicate (no maximal formulas).

5. **`Theory.Derivation.maxGrade`**: Maximum complexity of maximal formulas. Returns 0
   for normal derivations.

6. **`Theory.Derivation.reduceTop`**: Single-step reduction of the topmost redex of
   maximum grade. Returns `none` if normal.

7. **`Theory.Derivation.normalize`**: Iterated reduction to normal form.

8. **`Theory.Derivation.normalize_isNormal`**: The result is normal.

9. **`Theory.Derivation.subformula_property`**: Every formula in a normal derivation
   is a subformula of the conclusion or a hypothesis.

### 4.3 Phased Implementation Plan (Suggested)

**Phase 1: Subformula infrastructure and `isNormal` predicate**
- Define `Proposition.subformulas`, `Proposition.IsSubformula`
- Define `Theory.Derivation.height`
- Define `Theory.Derivation.isNormal` (Bool-valued or Decidable Prop)
- Basic lemmas: `isNormal` of leaf derivations, composition

**Phase 2: Single-step reduction**
- Define single-step reduction function `reduceStep`
- Prove correctness: `reduceStep` preserves the derivation's sequent
- Prove: `reduceStep` decreases the normalization measure

**Phase 3: Normalization function (implicational fragment first)**
- Restrict to `→`-only derivations as milestone
- Define `normalize` via well-founded recursion
- Prove `normalize_isNormal`

**Phase 4: Full connective extension**
- Extend to `∧`, `∨`, `→` (all five redex types)
- The structure is the same; the additional cases are simpler than `→`

**Phase 5: Subformula property**
- Define the formulas occurring in a derivation
- Prove that normal derivations satisfy the subformula property
- This requires a careful induction on the structure of normal derivations

## 5. Technical Challenges and Blockers

### 5.1 Termination Proof (Medium-High Difficulty)

The core challenge is proving that the normalization measure decreases. The key lemma:

> When reducing a maximal formula of grade `g`, the resulting derivation has no new
> maximal formulas of grade >= `g`.

This requires showing that `subs` does not introduce new intro-elim pairs at the
substitution sites. The argument is: the substituted derivation `d_arg` replaces
`ass` nodes (which are neither introductions nor eliminations), so no new redexes
of the same or higher grade can appear at those positions.

**Lean 4 encoding**: This requires induction on the derivation structure through `subs`,
which means we need a simultaneous induction on the derivation and the measure. This is
technically involved but follows standard proof theory patterns.

### 5.2 Context Equality Proofs

Each reduction step requires a proof that the result context equals the expected context.
For imp-redex: `(insert A Γ) \ {A} ∪ Γ = Γ`. For and-redex: trivial (same context).
For or-redex: same as imp-redex.

These are simple `Finset` lemmas that can be closed by `ext; simp; tauto` or similar.
The main nuisance is threading the `▸` (rewrite) through the types.

### 5.3 The `ax` Constructor

The `ax` constructor introduces formulas from the theory `T`. In IPL, this includes
`⊥ → A` for all `A`. An `ax` node is neither an introduction nor an elimination, so
it creates no redexes. However, when proving the subformula property, we must account
for theory axioms: formulas from `T` may not be subformulas of the conclusion or hypotheses.

**Resolution**: The subformula property for normal derivations typically restricts to
derivations in MPL (minimal logic, `T = ∅`), or else states that every formula is a
subformula of the conclusion, a hypothesis, **or a theory axiom**. The task description
says "IPL and MPL", so we should state the theorem for both:
- For MPL (`T = ∅`): strict subformula property (no axioms to worry about).
- For IPL: subformula property modulo the efq axiom schema.

### 5.4 Potential Blocker: Well-Founded Measure Encoding

The lexicographic measure `(maxGrade, redexCountAtGrade)` requires:
1. Defining `maxGrade` computably.
2. Defining `redexCountAtGrade` computably.
3. Proving that reduction decreases this pair lexicographically.

Item 3 is the most work-intensive. An alternative is to use `totalRedexWeight` (sum of
formula sizes of all maximal formulas), which is simpler to define but requires a subtler
decrease argument.

**Mitigation**: Start with the implicational fragment where only imp-redexes exist,
making the measure argument simpler. Then extend.

### 5.5 No Blocker from Task 266 Dependency

Task 266 is completed and archived. Its changes (HasDia, decidable tautology, etc.) are
orthogonal to this normalization task. The `Theory.Derivation` type and `subs` operation
that this task depends on were already in place.

## 6. Reuse Check Results

### 6.1 CSLib Reuse

| Component | Status | Notes |
|-----------|--------|-------|
| `Theory.Derivation` | Exists | 10-constructor inductive, `Type u` |
| `Derivation.subs` | Exists | Structural substitution, computable |
| `Derivation.weak` | Exists | Weakening, computable |
| `Derivation.cut` | Exists | Cut via `impE`/`impI`, less suitable than `subs` |
| `Proposition.subformulas` | **Missing** | Need to define for PL (exists for Bimodal) |
| `Derivation.height` | **Missing** | Need to define (exists for `DerivationTree` in Hilbert) |
| `Derivation.isNormal` | **Missing** | Core new definition |
| `Derivation.normalize` | **Missing** | Core new definition |
| `Confluence` infrastructure | Exists | Could be reused if we go relation-based |

### 6.2 Mathlib Reuse

| Component | Status | Notes |
|-----------|--------|-------|
| `WellFounded` / `WellFoundedRelation` | Available | For termination of `normalize` |
| `Prod.Lex` / lexicographic ordering | Available | For the `(grade, count)` measure |
| `Finset` API | Available | Extensively used in context arithmetic |
| Normalization for ND | **Not in Mathlib** | No proof-theoretic normalization exists |

### 6.3 External References

No Lean 4 formalization of Prawitz-style ND normalization exists in Mathlib or other
publicly available Lean 4 libraries. The closest Lean 4 work is:
- CSLib's own STLC strong normalization (Tait method, different structure)
- CSLib's LJ cut elimination (similar induction structure, incomplete proof)

Coq and Agda have formalizations (e.g., Pfenning's lecture notes formalized in Agda,
various Coq developments), but these use different representation choices.

## 7. Recommendations

1. **Start with the implicational fragment** (`→` only) as the task description suggests.
   This isolates the hardest reduction (imp-redex with substitution) and the termination
   argument, while avoiding the combinatorial explosion of five redex types.

2. **Use `subs` for reductions**, not `cut`. The `subs` operation directly substitutes
   a derivation for a hypothesis, which is exactly what Prawitz's reduction rules require.

3. **Define `isNormal` as `Bool`-valued** for computability, with a corresponding `Prop`
   version and decidability proof.

4. **Use a custom `Nat`-valued measure** for termination rather than relying on `sizeOf`.
   The auto-generated `sizeOf` includes formula parameters and is not monotonically
   decreasing under reduction.

5. **State the subformula property for MPL first**, then extend to IPL with the
   "modulo theory axioms" qualification.

6. **Consider splitting into two files** if the full development is large:
   - `Normalization/Defs.lean`: `isNormal`, `reduceStep`, `normalize`
   - `Normalization/SubformulaProperty.lean`: subformula property corollary

   However, if the total is under ~500 lines, a single file
   `NaturalDeduction/Normalization.lean` is cleaner.
