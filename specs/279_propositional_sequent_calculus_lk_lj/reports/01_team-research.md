# Research Report: Task #279

**Task**: Propositional Sequent Calculus LK/LJ
**Date**: 2026-06-23
**Mode**: Team Research (4 teammates)

## Summary

Task 279 delivers the third pillar of CSLib's proof-system triad: two-sided Gentzen-style sequent calculi (LK classical, LJ intuitionistic) with cut elimination, soundness, completeness, and equivalence bridges to the existing Hilbert and natural deduction systems. This would be the first LK/LJ formalization in Lean 4 and enables four downstream tasks (291 three-way equivalence, 292 IPL decidability via cut-free proof search, 293 Curry-Howard, and future modal sequent calculi). The task is large (estimated 2,000–3,600 lines across 6–8 files) and should be implemented in 4–6 phases, with LK definitions and bridges first, cut elimination second, and LJ following the same pattern.

## Key Findings

### 1. Existing Infrastructure (High Confidence)

**Formula type** (`Defs.lean`): `Proposition Atom` with `atom/bot/imp/and/or`, `DecidableEq`, and `Proposition.complexity` (from `Tableau/Defs.lean`) reusable as cut-rank measure.

**Natural deduction** (`NaturalDeduction/Basic.lean`): `Theory.Derivation` uses `Finset`-based contexts (`Ctx Atom = Finset (Proposition Atom)`) and single-conclusion sequents (`Ctx × Proposition`). Parameterized by `Theory` for MPL/IPL/CPL strength. This is the primary template for the LK/LJ design.

**Hilbert system** (`ProofSystem/Derivation.lean`): `DerivationTree` uses `List`-based contexts with `PropositionalAxiom`/`IntPropAxiom`/`MinPropAxiom` predicates. The existing ND-Hilbert bridge (`hilbert_iff_nd_ctx` in `Equivalence.lean`) provides the composition pattern for `hilbert_iff_lk`.

**CLL template** (`LinearLogic/CLL/Basic.lean`): One-sided `Multiset`-based sequent calculus. Useful for structural patterns (`HasInferenceSystem` instance, `cutFree` predicate, `CutFreeProof` subtype) but NOT for rule structure — CLL is one-sided, has no free structural rules, uses formula duality for cut, and its `CutElimination.lean` is a 34-line TODO stub. The CLL template transfers far less than initially expected.

**No prior art**: Exhaustive search via LeanSearch, LeanFinder, and Loogle confirms zero LK/LJ sequent calculus formalizations in Mathlib or the broader Lean 4 ecosystem.

### 2. Recommended LK Design: All-Additive Finset-Based (High Confidence)

Use a fully additive presentation where every rule shares the full context. With `Finset` on both sides, exchange and contraction are definitionally free. Only weakening needs explicit constructors.

```lean
structure LKSequent (Atom : Type u) [DecidableEq Atom] where
  ant : Finset (Proposition Atom)
  suc : Finset (Proposition Atom)

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

This all-additive form has no context splitting (`Gamma ∪ Gamma'`), simpler induction principles, and the cleanest cut rule form. Bridge proofs are also simpler because ND uses shared contexts.

### 3. Recommended LJ Design: Single-Conclusion (High Confidence)

Use `Finset` on the left and a single `Proposition Atom` on the right, matching the existing ND system's `Sequent = Ctx × Proposition` shape. This makes `nd_iff_lj` nearly definitional.

```lean
inductive LJProof : Finset (Proposition Atom) → Proposition Atom → Type u where
  | ax (A) : LJProof ({A}) A
  | cut {A} : LJProof Gamma A → LJProof (insert A Gamma) B → LJProof Gamma B
  | weakL {A} : LJProof Gamma B → LJProof (insert A Gamma) B
  | botL : LJProof (insert bot Gamma) A
  | andL {A B} : LJProof (insert A (insert B Gamma)) C →
                  LJProof (insert (A ∧ B) Gamma) C
  | orL {A B} : LJProof (insert A Gamma) C → LJProof (insert B Gamma) C →
                LJProof (insert (A ∨ B) Gamma) C
  | impL {A B} : LJProof Gamma A → LJProof (insert B Gamma) C →
                 LJProof (insert (A → B) Gamma) C
  | andR {A B} : LJProof Gamma A → LJProof Gamma B → LJProof Gamma (A ∧ B)
  | orR1 {A B} : LJProof Gamma A → LJProof Gamma (A ∨ B)
  | orR2 {A B} : LJProof Gamma B → LJProof Gamma (A ∨ B)
  | impR {A B} : LJProof (insert A Gamma) B → LJProof Gamma (A → B)
```

Do NOT use `Finset × Finset` with cardinality constraints for LJ — this is awkward and non-standard.

### 4. Cut Elimination Strategy (Medium Confidence)

Use syntactic cut elimination (Gentzen's original method) with lexicographic induction on `(formula_complexity, left_height + right_height)`:

- **Principal case** (both premises introduce the cut formula): complexity decreases strictly
- **Commutative cases** (one premise introduces, other does not): height sum decreases
- Define explicit `LKProof.height : LKProof seq → Nat` function
- Reuse `Proposition.complexity` from `Tableau/Defs.lean` for cut rank
- Use `termination_by` with lexicographic measure or `WellFoundedRelation`

**Key prerequisite lemmas**:
1. Height-preserving weakening admissibility
2. Monotone context weakening (`Gamma ⊆ Gamma' → LKProof (Gamma ⊢ Delta) → LKProof (Gamma' ⊢ Delta)`)
3. Principal case analysis for each connective pair

**Alternative noted**: `WellFounded.cutExpand` from `Mathlib.Logic.Hydra` provides an elegant termination argument if `Multiset`-based contexts are used. Since we chose `Finset` for alignment with ND, this doesn't apply directly, but could be noted as an alternative approach.

**Lean 4 challenges**: The termination checker needs explicit `sizeOf` lemmas for recursive calls. Each connective pair generates cases — approximately 100 combinations for LK, though most are short or symmetric. Proving `decreasing_by` obligations may require `omega` and explicit height arithmetic lemmas.

### 5. Bridge Proof Strategy: Compose via ND (High Confidence)

The cleanest path reuses the existing Hilbert-ND bridge infrastructure:

1. Prove `nd_to_lk` and `lk_to_nd` (structural translation)
2. Derive `hilbert_iff_lk := hilbert_iff_nd.trans nd_iff_lk`

This avoids duplicating the ~400-line deduction theorem machinery in the Hilbert-ND bridge. For LJ, the analogous path is `hilbert_iff_lj := hilbert_iff_nd_int.trans nd_iff_lj`.

**Completeness ordering** (to avoid circularity):
1. Define LK/LJ inductively
2. Prove soundness by induction on derivation (no reference to completeness)
3. Prove Hilbert → LK simulation (every Hilbert axiom is LK-derivable, MP maps to cut)
4. Extract completeness as corollary: semantics → Hilbert (existing) → LK (step 3)
5. `hilbert_iff_lk` = conjunction of step 3 and the reverse from step 4

### 6. Scope and Phasing (High Confidence)

**Estimated size**: 2,000–3,600 lines across 6–8 files.

| Component | Lines | Risk |
|-----------|-------|------|
| LK definition + notation | 80–120 | Low |
| LK structural admissibility | 150–250 | Medium |
| LK soundness | 100–150 | Low |
| LK cut elimination | 400–800 | **High** |
| LJ definition + structural | 230–370 | Medium |
| LJ cut elimination | 400–800 | **High** |
| Bridge proofs (all) | 400–700 | Medium |
| File headers, notation | 100–150 | Low |

**Recommended phasing**:
- Phase 1: LK definition, structural lemmas, `InferenceSystem` instance
- Phase 2: LK soundness + Hilbert → LK bridge
- Phase 3: LK cut elimination (Hauptsatz)
- Phase 4: LJ definition, structural lemmas, soundness
- Phase 5: LJ cut elimination
- Phase 6: Full bridge proofs (`nd_iff_lk`, `nd_iff_lj`), completeness corollaries

### 7. Strategic Value (High Confidence)

- **Downstream tasks**: 291 (three-way equivalence), 292 (IPL decidability via cut-free proof search), 293 (Curry-Howard)
- **Triple decidability certification**: Algebraic (task 289, done), tableau (tasks 297–298, implementing), cut-free proof search (tasks 279+292) — exceptional for any proof assistant library
- **Modal extension path**: LK generalizes cleanly to G3K/G3S4/G3S5 for modal logic (add box rules to LK skeleton). Temporal/bimodal NOT suited for sequent calculi (require cyclic proofs — tableau is correct there)
- **Adjacent opportunities**: Craig interpolation, Herbrand's theorem, Glivenko's theorem via SC

## Synthesis

### Conflicts Resolved

| Conflict | Resolution | Rationale |
|----------|-----------|-----------|
| File organization (flat vs. subdirectories) | Subdirectories `LK/` and `LJ/` | Task size warrants separation; mirrors ND structure |
| LK + LJ scope (split vs. keep) | Keep as one task, phase strictly | Dependencies (291, 292) need both; phasing provides checkpoints |
| Multiset vs. Finset | Finset | Alignment with ND system outweighs `cutExpand` convenience |
| CLL template fitness | Limited — use ND as primary template | CLL is one-sided, no free structural rules, cut elimination is a stub |
| Completeness proof order | Via Hilbert bridge (not direct) | Avoids circularity; reuses existing completeness results |

### Gaps Identified

1. **Notation scoping**: The existing `Γ ⊢ A` notation in PL namespace will conflict with two-sided `Γ ⊢ Δ`. Need distinct scoped notations (`⊢ₛ` for LK, `⊢ᵢ` for LJ, or namespace isolation).

2. **Task 280 dependency**: Listed in state.json but task 280 is archived/completed. The dependency is benign but should be cleared.

3. **`topR` rule**: Teammate A's design includes `topR` for top on the right. Need to verify `top` is defined in `Defs.lean` (it is: `abbrev top := imp bot bot`).

4. **`lake exe mk_all` step**: Adding new files requires barrel import updates — must be included in implementation phases.

5. **Cut elimination termination proof**: No reference implementation exists anywhere in CSLib (CLL's is a stub). This is the highest-risk component. Define `Proof.height` and prove size lemmas before attempting the main theorem.

### Recommendations

1. **Start with LK**: Definition + structural lemmas + soundness + Hilbert bridge. This is independently valuable and unblocks downstream tasks.

2. **Use the all-additive presentation**: Shared contexts everywhere, no `Gamma ∪ Gamma'` complications. Cleanest cut rule form.

3. **LJ succedent = single `Proposition Atom`**: Matches ND's `Sequent` type for near-definitional `nd_iff_lj`.

4. **Compose bridges via ND**: `hilbert_iff_lk := hilbert_iff_nd.trans nd_iff_lk`. Saves ~400 lines of deduction theorem duplication.

5. **Order proofs to avoid circularity**: Soundness first → Hilbert simulation → completeness as corollary.

6. **Cut elimination is the hard part**: Define height function and prove prerequisite lemmas first. Consider sorry-stub approach for initial phases, then fill in the proof.

7. **File layout**:
```
Cslib/Logics/Propositional/SequentCalculus/
├── Defs.lean              -- LKSequent type, shared notation
├── LK/
│   ├── Basic.lean         -- LKProof inductive, InferenceSystem instance
│   ├── Soundness.lean     -- LK soundness
│   ├── CutElimination.lean -- Hauptsatz for LK
│   └── Completeness.lean  -- LK completeness (via bridge)
├── LJ/
│   ├── Basic.lean         -- LJProof inductive
│   ├── Soundness.lean     -- LJ soundness
│   └── CutElimination.lean -- Hauptsatz for LJ
└── Equivalence.lean       -- hilbert_iff_lk, nd_iff_lk, hilbert_iff_lj, nd_iff_lj
```

## Reuse Check Results

**Reuse directly**:
- `PL.Proposition` — formula type
- `PL.Ctx = Finset (Proposition Atom)` — antecedent type
- `Proposition.complexity` — cut-rank measure (from Tableau/Defs.lean)
- `Theory.Derivation` (ND) and `DerivationTree` (Hilbert) — bridge targets
- `hilbert_iff_nd_ctx` bridge — compose for `hilbert_iff_lk`
- `InferenceSystem` / `HasInferenceSystem` typeclass
- `PropositionalConnectives` / `HasAnd` / `HasOr` — notation
- `Finset.insert`, `Finset.Subset`, `Finset.union` API (Mathlib)

**Must create new**:
- `LKSequent` type (two-sided)
- `LKProof` inductive (classical rules)
- `LJProof` inductive (intuitionistic rules)
- `LKProof.height` / `LJProof.height` — proof height measures
- `LKProof.cutFree` / `LJProof.cutFree` — cut-free predicates
- `cutElim` — cut elimination theorems (both LK and LJ)
- Bridge functions: `lk_to_nd`, `nd_to_lk`, `lj_to_nd`, `nd_to_lj`
- Composed bridges: `hilbert_iff_lk`, `nd_iff_lk`, `hilbert_iff_lj`, `nd_iff_lj`

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary (CLL template, infrastructure, design) | completed | high |
| B | Alternatives (Mathlib prior art, representations, bridges) | completed | high |
| C | Critic (scope risk, circularity, CLL fitness, technical pitfalls) | completed | high |
| D | Horizons (roadmap alignment, modal extensions, decidability) | completed | high |

## References

- `Cslib/Logics/LinearLogic/CLL/Basic.lean` — CLL template (structural patterns only)
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` — Primary design template
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` — Bridge proof template
- `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` — Hilbert system
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` — Axiom hierarchy
- `Cslib/Logics/Propositional/Tableau/Defs.lean` — `Proposition.complexity` measure
- `Mathlib.Logic.Hydra` — `WellFounded.cutExpand` (alternative termination argument)
