# Implementation Summary: Fragment Syntactic Predicates and Independence Lemmas

- **Task**: 302 - Fragment Syntactic Predicates and Independence Lemmas
- **Status**: Implemented
- **Date**: 2026-06-23
- **Session**: sess_1750704037_impl302
- **Phases**: 1/1 completed

## What Was Done

Created `Cslib/Logics/Propositional/Semantics/Algebra/FragmentPredicates.lean` with:

### Predicate Definitions (3)
- `Proposition.IsOrFree`: Bool-valued, returns `false` only for `.or`
- `Proposition.IsOrBotFree`: Bool-valued, returns `false` for `.bot` and `.or`
- `Proposition.IsImpTopOnly`: Bool-valued, returns `true` only for `.atom` and `.imp`

All follow the established `IsBotFree` recursive pattern from Conservative.lean.

### Subsumption Hierarchy (4 lemmas)
- `IsImpTopOnly_implies_IsOrBotFree`
- `IsOrBotFree_implies_IsOrFree`
- `IsOrBotFree_implies_IsBotFree`
- `IsOrBotFree_iff` (biconditional with IsOrFree ∧ IsBotFree)

### Connective Closure (5 lemmas)
- `imp_isOrFree`, `and_isOrFree`
- `imp_isOrBotFree`, `and_isOrBotFree`
- `imp_isImpTopOnly`

### Substitution Closure (3 theorems)
- `subst_preserves_isOrFree`
- `subst_preserves_isOrBotFree`
- `subst_preserves_isImpTopOnly`

### Independence (Morphism) Lemmas (3 theorems)
- `coe_AlgEvaluate_orFree`: for or-free A, `f (AlgEvaluate v b A) = AlgEvaluate (f ∘ v) b' A`
  when f preserves `⊓`, `⇨`, and `f b = b'`
- `coe_AlgEvaluate_orBotFree`: for or-bot-free A, morphism holds preserving only `⊓`, `⇨`
  (no bot constraint needed)
- `coe_AlgEvaluate_impTopOnly`: for imp-top-only A, morphism holds preserving only `⇨`

## Plan Deviations

**Deviation: renamed independence lemmas to morphism form.**

The plan specified `AlgEvaluate_orFree_independent_of_sup` using a two-GHA-instance formulation.
However, Lean 4 does not support two instances of the same typeclass on the same type in a
natural way: when `[inst₁ inst₂ : GeneralizedHeytingAlgebra H]`, the elaborator collapses
both instances to the same operations (hypotheses like `h_inf` become trivial `rfl`). Instead,
the morphism form `coe_AlgEvaluate_orFree` (following the exact pattern of the existing
`coe_AlgEvaluate` in Conservative.lean) is both:
1. Simpler to prove (standard structural induction)
2. More directly useful for downstream embedding tasks (305-311)

The plan's contingency clause explicitly allowed this pivot:
> "If the two-instance independence formulation proves too unwieldy in practice, the
> implementation agent may pivot to simpler per-construction embedding lemmas."

## Verification Results

- `lake build Cslib.Logics.Propositional.Semantics.Algebra.FragmentPredicates`: PASS
- `lake exe checkInitImports`: PASS
- `lake exe lint-style`: PASS
- `lake lint` (for FragmentPredicates): PASS (no warnings)
- `lean_verify` on all 3 independence theorems: axioms = [propext] only (no new axioms)
- Zero sorry in modified files
- Zero vacuous definitions
- Barrel import (`Cslib.lean`): updated via `lake exe mk_all --module`

Note: `lake build` (full project) fails due to pre-existing `BrouwerianSemilattice` error
(task 303, unrelated to this task). Confirmed pre-existing by git stash test.

## Key Technical Points

1. The morphism form exactly mirrors `coe_AlgEvaluate` from Conservative.lean (the WithBot
   embedding lemma), making all three independence lemmas consistent with existing architecture.
2. `IsOrBotFree_iff` proof uses `rw [iha, ihb]` after unfolding with `simp only [...]`.
3. Substitution closure requires `{Atom Atom' : Type u}` (same universe level) to match
   `Proposition.subst` definition.
4. All proofs use `simp only` with explicit lemma names to avoid flexible simp warnings.
