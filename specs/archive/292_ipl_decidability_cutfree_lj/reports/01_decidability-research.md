# Research Report: IPL Decidability via Cut-Free LJ Proof Search

**Task**: 292 — IPL decidability via cut-free LJ proof search  
**Session**: sess_1782245580_188995_292  
**Date**: 2026-06-23

## Executive Summary

Task 292 asks for `Decidable (Nonempty (LJProof (Gamma |- A)))` via bounded backward proof search over cut-free LJ, then lifting to `Decidable (DerivableIn IPL (Gamma |- A))` via `nd_iff_lj`. The implementation is feasible but involves substantial formalization work. An important pre-existing result must be considered: CSLib already has `Decidable (IValid phi)` and `Decidable (Derivable IntPropAxiom phi)` via the intuitionistic tableau decision procedure (in `Tableau/Intuitionistic/DecisionProcedure.lean`). However, these only cover closed (empty-context) derivability. Task 292 extends this to derivability FROM A CONTEXT, which is a genuinely new capability.

**Critical blocker**: `cutAdmissibility` in `CutElimination.lean` currently has a `sorry`. The decidability proof via proof search does NOT depend on cut admissibility itself (proof search works on cut-free rules directly), but `LJProof.cutElim` (which converts arbitrary LJ proofs to cut-free ones) does depend on it. The decidability result only needs the cut-free fragment, so it can proceed independently.

## Current Infrastructure

### LJ Proof System (Task 315, completed)

- **File**: `Cslib/Logics/Propositional/SequentCalculus/LJ/Basic.lean`
- **Type**: `LJProof : @Sequent Atom -> Type u` with 11 constructors
- **Cut-free**: `LJCutFree : LJProof seq -> Prop` and `CutFreeLJProof : Sequent -> Type u`
- **Sequent**: `Sequent = Ctx Atom * Proposition Atom` where `Ctx Atom = Finset (Proposition Atom)`

### Key Bridges (Task 315, completed)

- `nd_iff_lj`: `DerivableIn (AxiomTheory IntPropAxiom) (Gamma |- A) <-> Nonempty (LJProof (Gamma |- A))`
- `lj_iff_ivalid`: `IValid phi <-> Nonempty (LJProof (empty |- phi))`
- `hilbert_iff_lj`: Hilbert derivability <-> LJ provability

### Existing Decidability (Intuitionistic Tableau)

- `instDecidableIValid`: `Decidable (IValid phi)` via tableau
- `instDecidableDerivableIntPropAxiom`: `Decidable (Derivable IntPropAxiom phi)` (empty context only)

### LJ Constructor Analysis (Relevant to Proof Search)

| Constructor | Reduces weight? | Notes for search |
|-------------|----------------|------------------|
| `ax` | Base case | `A in Gamma` and goal is `A` |
| `botL` | Base case | `bot in Gamma` |
| `andL` | Yes | Decomposes conjunction in context |
| `andR` | Yes | Decomposes conjunction in goal |
| `orL` | Yes | Decomposes disjunction in context, branches |
| `orR1` | Yes | Disjunction goal, left |
| `orR2` | Yes | Disjunction goal, right |
| `impL` | **No** | Principal `A -> B` stays in context |
| `impR` | Yes | Decomposes implication in goal |
| `weakL` | N/A | Adds formula; not used in cut-free search |
| `cut` | N/A | Not used in cut-free search |

The critical observation: `impL` does NOT reduce formula weight because the implication `A -> B` remains in `Gamma` in both premises. This means pure weight-based termination is insufficient. Loop detection is required.

## Literature Proof Structure

The decidability proof follows Negri & von Plato (2001), Theorem 2.5.7, and Troelstra & Schwichtenberg (2000), Theorem 4.2.6.

### Proof Outline

1. **Subformula property**: In cut-free LJ, every formula appearing in a proof is a subformula of the endsequent formulas.

2. **Finite search space**: Since contexts are subsets of the subformula closure (a finite set), there are only finitely many distinct sequents that can appear in a proof search.

3. **Loop detection for impL**: The `impL` rule doesn't reduce formula weight, so the same sequent can recur. But since there are finitely many distinct sequents, any infinite branch must revisit a sequent. When a loop is detected, the branch can be pruned.

4. **Termination argument**: The search tree is finite because:
   - All rules except `impL` strictly reduce formula weight
   - `impL` applications that produce an already-seen sequent are pruned
   - The number of distinct sequents is bounded by `2^|Sub(Gamma, A)| * |Sub(Gamma, A)|`

5. **Decidability**: Exhaustive search over the finite tree yields either a proof or confirms underivability.

### Key Sub-results Needed

1. `Proposition.subformulas : Proposition Atom -> Finset (Proposition Atom)` -- subformula set for a proposition
2. `Sequent.subformulas : Sequent -> Finset (Proposition Atom)` -- subformula closure of a sequent
3. Subformula property lemma: all formulas in a cut-free proof are subformulas of the endsequent
4. Well-founded measure combining formula weight + history set
5. The bounded search function itself
6. Correctness: search finds a proof iff one exists

## Approach Analysis

### Approach A: Direct Proof Search Function (Recommended)

Define a decidable backward search function that:
1. Computes `Sub(Gamma, A)` = all subformulas of formulas in `Gamma` and `A`
2. Maintains a history set of sequents already on the current search path
3. At each step, tries all applicable cut-free rules bottom-up
4. For `impL`, checks if the resulting sequent is already in history (loop detection)
5. Uses `Finset.card (Powerset Sub \ History)` as a well-founded measure

**Termination measure**: Use a pair `(fuel, weight)` where:
- `fuel` = number of distinct sequents not yet visited on this path (decreases with each `impL` application)
- `weight` = total formula weight of current sequents (decreases with all other rules)

This requires lexicographic well-founded induction.

**Advantages**: Directly produces a constructive decision procedure; proof structure matches the literature.

**Challenges**: 
- The `impL` rule requires tracking which sequents have been visited, and the fuel argument is about the set of possible sequents minus visited ones
- Need to show the search is complete (every proof can be found by the procedure)
- The sequent type uses `Finset`, so equality comparison is decidable

### Approach B: Via Existing Tableau + Bridge

Compose `instDecidableIValid` with a reduction from context-based derivability to closed validity.

The reduction: `Nonempty (LJProof (Gamma |- A))` is decidable if we can reduce to a closed problem. The standard trick: `Gamma |- A` iff `|- conj(Gamma) -> A` (where `conj` forms a big conjunction). But this only works if `Gamma` is non-empty, and requires care with the empty case.

However, this approach has a problem: we need `Decidable (Nonempty (LJProof (Gamma |- A)))`, not just `Decidable (IValid (...))`. The bridge `lj_iff_ivalid` only covers the empty context case. For context-based: `nd_iff_lj` gives `DerivableIn ... <-> Nonempty LJProof`, and the existing `int_strong_completeness` gives `ISemanticEntails <-> SetDerivable`. We'd need to show the deduction theorem for LJ or use the semantic route.

Actually, this can work via the deduction theorem:
- `Nonempty (LJProof ({A1,...,An} |- B))` iff `Nonempty (LJProof (empty |- A1 -> ... -> An -> B))` (via iterated `impR` / `impL`)
- Then use `lj_iff_ivalid` to get `IValid (A1 -> ... -> An -> B)`
- Then use `instDecidableIValid` to decide

**Advantages**: Much simpler; reuses existing infrastructure.

**Disadvantages**: 
- Requires proving the deduction theorem for LJ (iterated `impR`/`impL`)
- The task description specifically asks for "bounded backward proof search procedure" -- this approach sidesteps that
- The result would be nonconstructive (goes through Kripke semantics)

### Approach C: Hybrid

Implement the proof search as the primary result, but also provide the bridge via Approach B as a corollary.

### Recommendation

**Approach A** is recommended for alignment with the task description and literature fidelity. The task explicitly asks for "bounded backward proof search procedure" with termination via well-founded measure. Approach B could be provided as a simpler alternative or corollary.

However, Approach A is a substantial formalization effort (estimated 500-800 lines). Consider whether Approach B (estimated 100-200 lines) achieves the essential goal of producing `Decidable (Nonempty (LJProof (Gamma |- A)))` more efficiently.

## Detailed Design for Approach A

### Phase 1: Subformula Infrastructure

```lean
-- Subformulas of a proposition
def Proposition.subformulas : Proposition Atom -> Finset (Proposition Atom)

-- Subformula closure of a sequent
def Sequent.subClosure (s : @Sequent Atom) : Finset (Proposition Atom) :=
  s.1.biUnion Proposition.subformulas ∪ s.2.subformulas

-- Self-membership
lemma Proposition.mem_subformulas_self (A) : A ∈ A.subformulas

-- Transitivity
lemma Proposition.subformulas_trans : B ∈ A.subformulas -> C ∈ B.subformulas -> C ∈ A.subformulas
```

### Phase 2: Subformula Property for Cut-Free LJ

```lean
-- All formulas in a cut-free proof are subformulas of the endsequent
lemma cutFree_subformula_property {d : LJProof (Gamma |- A)} (hcf : LJCutFree d) :
    <forall formulas in d, they are in Sequent.subClosure (Gamma |- A)>
```

This is stated informally because the precise statement requires defining "formula appearing in a proof tree."

### Phase 3: Proof Search Function

```lean
-- Search state: current sequent + visited sequents on this path
structure SearchState (Atom : Type*) [DecidableEq Atom] where
  sequent : @Sequent Atom
  visited : Finset (@Sequent Atom)  -- sequents already on search path
  bound : Finset (Proposition Atom) -- subformula closure

-- Search result
inductive SearchResult (Atom : Type*) [DecidableEq Atom] where
  | found : LJProof seq -> SearchResult Atom
  | notFound : SearchResult Atom

-- The main search function with fuel
def boundedSearch (fuel : Nat) (Gamma : Ctx Atom) (A : Proposition Atom) 
    (visited : Finset (@Sequent Atom)) : SearchResult Atom
```

### Phase 4: Correctness (Soundness + Completeness of Search)

```lean
-- If search finds a proof, it's valid
lemma boundedSearch_sound : boundedSearch fuel Gamma A visited = .found d -> <d is valid>

-- If a cut-free proof exists, search finds one (with enough fuel)
lemma boundedSearch_complete : CutFreeLJProof (Gamma |- A) -> 
    exists fuel, boundedSearch fuel Gamma A empty = .found _
```

### Phase 5: Decidable Instance

```lean
instance : Decidable (Nonempty (LJProof (Gamma |- A))) := ...
instance : Decidable (DerivableIn (AxiomTheory IntPropAxiom) (Gamma |- A)) := ...
```

## Feasibility Assessment

### Blockers

1. **cutAdmissibility sorry**: The `cutAdmissibility` in `CutElimination.lean` has a `sorry`. This does NOT block the decidability proof (which works on cut-free proofs directly), but it does mean that `LJProof.cutElim` is not fully proved. The decidability result can work with `CutFreeLJProof` directly.

2. **Finset-based sequent equality**: The task requires comparing sequents for equality (loop detection). Since `Ctx Atom = Finset (Proposition Atom)` and `Proposition` has `DecidableEq`, sequent equality `(Gamma1, A1) = (Gamma2, A2)` is decidable. This is fine.

3. **Universe polymorphism**: `Proposition Atom` is in `Type u` and `LJProof` is in `Type u`. The search function needs to work at the same universe level.

### Complexity Estimate

| Component | Lines (est.) | Difficulty |
|-----------|-------------|------------|
| Subformula infrastructure | 80-120 | Medium |
| Subformula property for cut-free LJ | 80-120 | Medium-Hard |
| Proof search function | 150-250 | Hard |
| Soundness of search | 50-80 | Medium |
| Completeness of search | 100-150 | Hard |
| Decidable instances + lifting | 30-50 | Easy |
| **Total** | **490-770** | **Hard** |

### Key Technical Challenges

1. **Well-founded recursion**: The termination argument uses a lexicographic order on `(distinct_remaining_sequents, formula_weight)`. Lean 4's `termination_by` with `WellFoundedRelation` on `Nat * Nat` (lexicographic) should work.

2. **impL loop detection**: The critical insight is that `impL` can only be applied to implications in the current context, and each application either adds the consequent `B` to the context (increasing the set of visited formulas) or loops. Since all formulas are subformulas of the endsequent, the context can only grow within the subformula closure.

3. **Completeness of search**: Must show that if a cut-free proof exists, the search finds it. This requires showing the search explores all relevant branches (i.e., the search is not too aggressive in pruning).

4. **Weakening in proofs found**: The search function produces proofs in the cut-free fragment. However, `weakL` is also cut-free. The search might need to account for weakening explicitly or work with a set-based representation where weakening is implicit.

## Alternative Simplified Approach

For a shorter implementation that still delivers `Decidable (Nonempty (LJProof (Gamma |- A)))`:

1. Define `conjoin : Finset (Proposition Atom) -> Proposition Atom` that forms the conjunction of all formulas in a finite set
2. Prove the LJ deduction theorem: `Nonempty (LJProof (Gamma |- A)) <-> Nonempty (LJProof (empty |- conjoin Gamma -> A))`
3. Use `lj_iff_ivalid` and `instDecidableIValid` to decide the closed case
4. Lift via the deduction theorem

This is about 100-150 lines but doesn't implement the proof search procedure the task requests.

## Reuse Check Results

| Concept | CSLib Status | Mathlib Status |
|---------|-------------|---------------|
| `Proposition.subformulas` | Not defined for PL (exists for bimodal, temporal) | N/A |
| `Decidable (IValid phi)` | EXISTS via tableau | N/A |
| `Decidable (Derivable IntPropAxiom phi)` | EXISTS (closed only) | N/A |
| `Decidable (Nonempty (LJProof (Gamma |- A)))` | NOT DEFINED | N/A |
| LJ deduction theorem | NOT DEFINED | N/A |
| Bounded proof search for LJ | NOT DEFINED | N/A |
| Well-founded lexicographic order | Mathlib `Prod.Lex` | EXISTS |

## Tactic Survey Results

For the kinds of proof goals expected in this formalization:

- **omega**: Useful for natural number arithmetic in termination arguments
- **simp**: Useful for Finset manipulation (`Finset.mem_insert`, `Finset.mem_union`, etc.)
- **decide**: NOT useful (proof objects are in Type, not Prop with Decidable)
- **aesop**: May help with routine membership goals
- **Finset.induction**: Key tactic for induction over finite sets in subformula proofs

## Recommendations

1. **Primary approach**: Approach A (direct proof search) for literature fidelity
2. **File**: `Cslib/Logics/Propositional/SequentCalculus/LJ/Decidability.lean`  
   (Note: task description says `Decidability.lean` directly under `SequentCalculus/`, but placing it under `LJ/` is more consistent with the existing organization)
3. **Dependencies**: Import `LJ/Basic.lean` and `LJ/CutElimination.lean` (for `CutFreeLJProof`)
4. **Does NOT depend on sorry-free cutAdmissibility**: The proof search works on cut-free rules directly
5. **The `weakL` constructor**: In the proof search, weakening is implicit because contexts are `Finset`s -- any context formula can be used without explicit weakening. The search should NOT use `weakL` in its output proofs; instead, membership proofs handle context management.
6. **Task description correction**: The task says "lift via nd_iff_lk" but the correct bridge is `nd_iff_lj` (LJ, not LK -- this is intuitionistic)

## Open Questions for Planning

1. Should the search procedure also handle the cut-free restriction explicitly (producing `CutFreeLJProof`), or produce `LJProof` that happens to be cut-free?
2. Should `weakL` be excluded from the search output? (Yes, recommended -- it's not needed in set-based contexts)
3. Is Approach B (deduction theorem) an acceptable alternative if Approach A proves too complex?
4. Should the file go under `LJ/Decidability.lean` or `SequentCalculus/Decidability.lean`?
