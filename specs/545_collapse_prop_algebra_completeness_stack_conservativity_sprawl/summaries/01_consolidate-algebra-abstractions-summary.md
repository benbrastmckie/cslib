# Implementation Summary: Consolidate Propositional Algebra Completeness Stack & Conservativity Sprawl

- **Task**: 545 - Collapse propositional-algebra completeness stack and fragment-conservativity sprawl
- **Status**: Implemented (all 5 phases complete)
- **Plan**: `plans/01_consolidate-algebra-abstractions.md`

## What Was Built

**Part B (fragment-conservativity sprawl, phases 1-3)**: introduced a generic
`structure FragmentConservativity P` (fields `Ax`, `hard`, `sub`) mirroring the existing
`CanAlgComplete` structure-by-reuse idiom, in a new
`Cslib/Logics/Propositional/Semantics/Algebra/FragmentConservativity.lean`. It carries three
generic derived theorems (`fragmentConservativity_derivableOfDerivableInt`,
`fragmentConservativity_iff`, `fragmentConservativity_nd`) plus the relocated
`liftDerivationTree`/`derivable_mono` combinators.

A sibling `FragmentConservativityInstances.lean` supplies the four instances
(`fragmentConservativityConjImp`, `…Imp`, `…ConjImpBot`, `…OrImp`), each reusing its fragment's
retained hard-direction proof verbatim (`OrImp`'s stays the sequent-calculus route via
`hilbert_iff_lj` → `LJProof.cutElim` → `cutFreeLJ_toOrImp`, untouched). The `4 × 3 = 12`
per-fragment boilerplate theorems (subsumption/biconditional/ND-corollary) are re-homed there as
one-line applications of the generic core to the matching instance, preserving every prior public
name and signature exactly. The four original `*Conservative.lean` files now retain only their
hard-direction proof and supporting machinery.

**Part A (completeness stack, phase 4)**: `CanAlgComplete.lean`'s docstring now declares it the
single documented terminal interface for fragment algebraic completeness (cross-referencing
`FragmentConservativity` as its conservativity-side sibling). `MPL.hilbert_alg_complete`
(`HilbertCompleteness.lean`) and `conjImp_brouwerian_complete` (`BrouwerianCompleteness.lean`) are
reclassified in their docstrings as load-bearing internal inputs — text only, visibility/name/
signature unchanged (20+ and 14+ external use-sites respectively, verified unchanged throughout).
The four zero-consumer `*_iff_chain` restatements (`impAxiom_iff_chain`, `conjImpAxiom_iff_chain`,
`orImpAxiom_iff_chain`, `minAxiom_iff_chain`) were deleted from `ConservativeChain.lean` after a
repo-wide grep confirmed zero external use-sites.

**Phase 5**: full CI gate green — `lake build` (3253/3253), `lake test`, `lake exe
checkInitImports`, `lake lint` (zero warnings), `lake exe lint-style`, `lake exe mk_all --module`
(no diff), and `lake shake`. Phase 3's boilerplate removal left several now-genuinely-dead
imports (`HilbertConservativeGlivenko`/cross-fragment imports in the four per-fragment files);
these were found via `lake shake` and cleaned up, and three downstream consumers
(`ClassicalImpCompleteness.lean`, `LiftViaMorphism.lean`, `MplConservativeChain.lean`) were
repointed to import `FragmentConservativity.lean` directly instead of transitively.

## Files Modified

**New**:
- `Cslib/Logics/Propositional/Semantics/Algebra/FragmentConservativity.lean`
- `Cslib/Logics/Propositional/Semantics/Algebra/FragmentConservativityInstances.lean`

**Modified**:
- `Cslib/Logics/Propositional/Semantics/Algebra/ImpConservative.lean`
- `Cslib/Logics/Propositional/Semantics/Algebra/ConjImpConservative.lean`
- `Cslib/Logics/Propositional/Semantics/Algebra/ConjImpBotConservative.lean`
- `Cslib/Logics/Propositional/Semantics/Algebra/OrImpConservative.lean`
- `Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean`
- `Cslib/Logics/Propositional/Semantics/Algebra/CanAlgComplete.lean`
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean`
- `Cslib/Logics/Propositional/Semantics/Algebra/BrouwerianCompleteness.lean`
- `Cslib/Logics/Propositional/Semantics/Algebra/MplConservativeChain.lean`
- `Cslib/Logics/Propositional/Semantics/Algebra/LiftViaMorphism.lean`
- `Cslib/Logics/Propositional/Metalogic/ClassicalImpCompleteness.lean`
- `Cslib.lean` (barrel)

## Verification

- Zero `sorry`/`admit`/vacuous-def in all touched files.
- Zero new axioms introduced.
- Every nonzero-use-site public name preserved (verbatim signature, one canonical defining
  location each — confirmed by repo-wide grep before/after).
- `MPL.hilbert_alg_complete` (8 real use-sites incl. `Foundations/Logic/ProofSystem.lean`) and
  `conjImp_brouwerian_complete` (6 real use-sites) stay public, unchanged in signature/visibility.
- Full CI pipeline green (see Phase 5 above).

## Plan Deviations

1. **Phase 2** (altered): the re-homed 4×3 boilerplate theorems were NOT defined alongside the
   four instances in `FragmentConservativityInstances.lean` within Phase 2 itself, as the plan's
   task list literally sequenced. They were deferred to Phase 3 and defined there atomically with
   removing the bespoke bodies from the four per-fragment files. Reason: the instance a boilerplate
   one-liner needs is defined in `FragmentConservativityInstances.lean`, which is necessarily
   downstream of the four per-fragment files (it imports them for the hard-direction theorems) —
   defining the same theorem name in both the per-fragment file and the downstream instances file
   simultaneously would be a duplicate-declaration error. Phase 2 delivered the four instances
   alone, verified green; Phase 3 completed the re-homing.
2. **Phase 3** (altered): `ConservativeChain.lean`'s import list was updated (three individual
   fragment imports collapsed to one `FragmentConservativityInstances` import) even though the
   plan's literal Phase 3 file list did not name it. This was a necessary mechanical consequence
   of relocating the 12 boilerplate names downstream — `ConservativeChain.lean` consumes 8 of the
   12 relocated names and needs to resolve them transitively. Verified green by `lake build`.
3. **Phase 5** (altered/expanded): the plan's Phase 5 task list did not anticipate specific dead
   imports, but `lake shake` surfaced several genuinely dead imports as a direct consequence of
   Phase 3's boilerplate removal (an import's sole in-file consumer was deleted). These were fixed
   as part of satisfying the Phase 5 `lake shake` gate item, touching `ConjImpConservative.lean`,
   `ConjImpBotConservative.lean`, `OrImpConservative.lean`, `ClassicalImpCompleteness.lean`,
   `LiftViaMorphism.lean`, and `MplConservativeChain.lean`'s import lines only (no proof-content
   changes). One pre-existing unrelated dead import in `ConservativeChain.lean`
   (`ClassicalConjImpBotCompleteness`, doc-comment-only reference, predating this task) was left
   untouched as out of scope.

No phase was blocked; no sorry, admit, or vacuous definition was introduced at any point.
