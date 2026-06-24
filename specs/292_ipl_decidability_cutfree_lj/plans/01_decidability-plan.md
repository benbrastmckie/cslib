# Implementation Plan: Task #292

- **Task**: 292 - IPL decidability via cut-free LJ proof search
- **Status**: [COMPLETED]
- **Effort**: 8 hours
- **Dependencies**: Task 315 (LJ infrastructure, completed)
- **Research Inputs**: specs/292_ipl_decidability_cutfree_lj/reports/01_decidability-research.md
- **Artifacts**: plans/01_decidability-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Formalize the decidability of intuitionistic propositional logic derivability from a context
via bounded backward proof search over the cut-free fragment of LJ. The implementation defines
a `Proposition.subformulas` function, constructs a fuel-bounded backward search procedure that
applies cut-free LJ rules bottom-up with loop detection for the `impL` rule, proves soundness
and completeness of the search, and derives `Decidable (Nonempty (LJProof (Gamma |- A)))` and
`Decidable (DerivableIn (AxiomTheory IntPropAxiom) (Gamma |- A))` via the existing `nd_iff_lj`
bridge.

### Research Integration

Key findings from the research report integrated into this plan:

1. **Existing infrastructure**: CSLib already has `Decidable (IValid phi)` via tableau for
   empty-context validity. This task extends decidability to context-based derivability
   (`Gamma |- A`), which is a genuinely new capability.
2. **impL loop detection**: The `impL` rule does not reduce formula weight (the principal
   implication stays in context). Termination requires tracking visited sequents on the
   current search path and pruning when a loop is detected.
3. **Subformula property**: All formulas in a cut-free LJ proof are subformulas of the
   endsequent. This bounds the search space: contexts are subsets of the finite subformula
   closure, so only finitely many distinct sequents can appear.
4. **cutAdmissibility sorry**: The existing `cutAdmissibility` has a sorry, but this does NOT
   block the decidability proof. Proof search works on cut-free rules directly without
   needing cut elimination.
5. **weakL exclusion**: The search procedure does not use `weakL` in its output proofs.
   Weakening is implicit because contexts are `Finset`s -- any formula present in the context
   can be used directly.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Define `Proposition.subformulas : Proposition Atom -> Finset (Proposition Atom)` with
  self-membership and transitivity lemmas
- Define `Sequent.subClosure` computing the subformula closure of a sequent
- Implement a bounded backward proof search function over cut-free LJ rules
- Prove soundness: if search finds a proof, it is a valid `LJProof`
- Prove completeness: if a cut-free proof exists, search finds one
- Derive `Decidable (Nonempty (LJProof (Gamma |- A)))`
- Derive `Decidable (DerivableIn (AxiomTheory IntPropAxiom) (Gamma |- A))` via `nd_iff_lj`

**Non-Goals**:
- Proving `cutAdmissibility` sorry-free (separate task)
- Implementing the deduction theorem approach (Approach B from research)
- Decidability for LK or classical logic
- Optimizing the search procedure for computational efficiency

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Well-founded recursion on fuel/weight pair is hard to express | H | M | Use simple `Nat` fuel parameter with explicit bound computation; avoid complex well-founded recursion in favor of `decreasing_by omega` |
| Completeness proof for search is complex (must show all cut-free proofs are findable) | H | M | Structure the search to mirror the proof tree exactly; use induction on `CutFreeLJProof` |
| `impL` loop detection interacts subtly with context changes | M | M | Use visited-sequent set; bound fuel by `2^|SubClosure|` to guarantee termination |
| `Finset` operations create complex simp goals | M | H | Rely on `Finset.mem_insert`, `Finset.mem_union`, `Finset.subset_insert` simp lemmas |
| Universe polymorphism issues with search function | L | L | Keep everything in `Type u` consistent with existing `LJProof` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Subformula Infrastructure and Search Skeleton [COMPLETED]

**Goal**: Define `Proposition.subformulas`, `Sequent.subClosure`, and the basic type
signatures for the bounded proof search function. Establish the file structure with
correct imports and module header.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/SequentCalculus/LJ/Decidability.lean` with
  module header, imports (`LJ.Basic`, `LJ.Completeness`), and copyright
- [ ] Define `Proposition.subformulas : Proposition Atom -> Finset (Proposition Atom)`
  recursively over the 5 constructors (atom, bot, imp, and, or), returning a `Finset`
  that includes the formula itself and all proper subformulas
- [ ] Prove `Proposition.mem_subformulas_self`: every formula is in its own subformula set
- [ ] Prove `Proposition.subformulas_trans`: if `B in A.subformulas` and
  `C in B.subformulas` then `C in A.subformulas`
- [ ] Prove helper lemmas: `imp_left_mem_subformulas`, `imp_right_mem_subformulas`,
  `and_left_mem_subformulas`, `and_right_mem_subformulas`, `or_left_mem_subformulas`,
  `or_right_mem_subformulas`
- [ ] Define `Sequent.subClosure (s : @Sequent Atom) : Finset (Proposition Atom)` as
  the union of subformulas of all context formulas and the goal formula
- [ ] Prove `Sequent.mem_subClosure_of_mem_ctx`: if `A in Gamma` then
  `A in (Gamma |- C).subClosure`
- [ ] Prove `Sequent.goal_mem_subClosure`: the goal formula is in the subformula closure
- [ ] Define `Proposition.complexity` (if not already available) or reuse existing
  `Proposition.complexity` from `Tableau/Defs.lean`
- [ ] Define the search result type: `inductive SearchResult` with `found` (carrying an
  `LJProof`) and `notFound` constructors
- [ ] Verify with `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.Decidability`

**Timing**: 2.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Decidability.lean` - new file (create)

**Verification**:
- File compiles with `lake build` (scoped module build)
- `Proposition.subformulas` is defined and key lemmas type-check
- `Sequent.subClosure` is defined with membership lemmas

---

### Phase 2: Bounded Proof Search Function [COMPLETED]

**Goal**: Implement the core backward proof search function that systematically tries all
applicable cut-free LJ rules bottom-up, with fuel-based termination and loop detection
for `impL`.

**Tasks**:
- [ ] Define the fuel computation: `searchFuel (s : @Sequent Atom) : Nat` that returns a
  bound sufficient to explore all non-looping proof search branches (based on subformula
  closure size and formula complexity)
- [ ] Implement `ljSearch (fuel : Nat) (Gamma : Ctx Atom) (A : Proposition Atom)
  (visited : Finset (@Sequent Atom)) : Option (LJProof (Gamma |- A))` with the following
  search strategy:
  - Base cases: check `fuel = 0` (return `none`); check `A in Gamma` (return `ax`);
    check `bot in Gamma` (return `botL`)
  - Goal decomposition (right rules): match on `A` and try `andR`, `orR1`/`orR2`, `impR`
  - Context decomposition (left rules): iterate over `Gamma` and try `andL`, `orL`, `impL`
  - For `impL`: check if the resulting sequent `(insert B Gamma |- C)` is in `visited`;
    if so, skip (loop detected); otherwise recurse with the sequent added to `visited`
  - For all other rules: recurse with `fuel - 1` (formula weight decreases)
- [ ] Prove `ljSearch_sound`: if `ljSearch fuel Gamma A visited = some d` then `d` is a
  valid `LJProof (Gamma |- A)` (this should be automatic from the return type)
- [ ] Prove auxiliary lemmas about fuel sufficiency for each rule case
- [ ] Verify the search function compiles and terminates (use `decreasing_by omega` or
  explicit `Nat.lt` arguments)
- [ ] Add strategic `sorry` markers for completeness-related lemmas to be filled in Phase 3
- [ ] Verify with `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.Decidability`

**Timing**: 3 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Decidability.lean` - add search function

**Verification**:
- Search function compiles and terminates
- Soundness is trivially satisfied by the return type (`Option (LJProof ...)`)
- Basic test cases: `ljSearch` finds proofs for simple sequents like
  `{A} |- A` (identity), `{bot} |- A` (explosion), `{A, A -> B} |- B` (modus ponens)

---

### Phase 3: Completeness, Decidability Instances, and Bridge [COMPLETED]

**Goal**: Prove completeness of the search procedure (if a cut-free proof exists, search
finds one), derive the `Decidable` instances, and compose with `nd_iff_lj` for the final
IPL decidability result.

**Tasks**:
- [ ] Prove `ljSearch_complete`: if `Nonempty (CutFreeLJProof (Gamma |- A))` then
  `ljSearch (searchFuel (Gamma |- A)) Gamma A empty` returns `some _`.
  Strategy: induction on the `CutFreeLJProof`, showing that for each rule used in the
  proof, the search procedure tries that rule and succeeds recursively.
  Key insight: the fuel bound is large enough to cover all branches, and the visited-set
  loop detection only prunes branches that correspond to infinite (non-terminating) paths,
  which cannot occur in a finite proof tree.
- [ ] Prove `ljSearch_complete_aux`: auxiliary induction lemma with explicit fuel and
  visited-set parameters, showing that a cut-free proof tree can be replayed by the search
- [ ] Define `instDecidableLJDerivable`:
  ```
  instance : Decidable (Nonempty (LJProof (Gamma |- A)))
  ```
  by running `ljSearch` with sufficient fuel and empty visited set, then case-splitting
  on the result
- [ ] Define `instDecidableDerivableInIPL`:
  ```
  instance : Decidable (DerivableIn (AxiomTheory IntPropAxiom) (Gamma |- A))
  ```
  using `decidable_of_iff` with `nd_iff_lj`
- [ ] Remove any remaining `sorry` markers from Phase 2
- [ ] Add module documentation with literature references (Negri & von Plato 2001,
  Troelstra & Schwichtenberg 2000)
- [ ] Run full CI verification:
  - `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.Decidability`
  - `lake exe checkInitImports`
  - `lake exe lint-style`
- [ ] Update `Cslib.lean` barrel import if needed (`lake exe mk_all --module`)

**Timing**: 2.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Decidability.lean` - add completeness
  proof, decidability instances, and bridge composition

**Verification**:
- Zero `sorry` in the final file (verified by `lean_verify` or `grep sorry`)
- `Decidable (Nonempty (LJProof (Gamma |- A)))` instance resolves
- `Decidable (DerivableIn (AxiomTheory IntPropAxiom) (Gamma |- A))` instance resolves
- All CI checks pass

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.Decidability` compiles
      without errors or warnings
- [ ] `lean_verify` confirms zero `sorry` and no axiom usage beyond standard foundations
- [ ] `Decidable (Nonempty (LJProof (Gamma |- A)))` instance is synthesized by Lean
- [ ] `Decidable (DerivableIn (AxiomTheory IntPropAxiom) (Gamma |- A))` instance is
      synthesized by Lean
- [ ] `lake exe checkInitImports` passes (file imports `Cslib.Init`)
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes (no regressions)

## Artifacts & Outputs

- `Cslib/Logics/Propositional/SequentCalculus/LJ/Decidability.lean` - main implementation
- `specs/292_ipl_decidability_cutfree_lj/plans/01_decidability-plan.md` - this plan
- `specs/292_ipl_decidability_cutfree_lj/summaries/01_decidability-summary.md` - execution
  summary (created during implementation)

## Rollback/Contingency

If the direct proof search approach (Approach A) proves too complex:

1. **Partial rollback**: Keep the subformula infrastructure from Phase 1, which is independently
   useful. Mark Phases 2-3 as [BLOCKED].

2. **Fallback to Approach B** (deduction theorem): If proof search completeness cannot be
   formalized within the time budget, implement the simpler deduction theorem approach:
   - Prove `Nonempty (LJProof (Gamma |- A)) <-> Nonempty (LJProof (empty |- conjoin Gamma -> A))`
   - Use existing `lj_iff_ivalid` and `instDecidableIValid` for the closed case
   - This produces the same `Decidable` instances with ~150 lines instead of ~600

3. **Sorry-gated delivery**: If completeness proof is partially done, deliver with strategic
   `sorry` markers on the completeness lemma and document exactly what remains. The
   `Decidable` instances would then be `noncomputable` with sorry-dependency noted.

The subformula infrastructure (Phase 1) has no rollback risk -- it is a clean addition to the
LJ module.
