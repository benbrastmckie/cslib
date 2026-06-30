# Implementation Summary: Reconcile Parallel Int/Min Decidability Routes

- **Task**: 422 - Reconcile parallel Int/Min decidability routes (tableau vs FMP)
- **Status**: [COMPLETED]
- **Plan**: plans/01_reconcile-decidability-routes.md
- **Phases**: 4/4 completed
- **Date**: 2026-06-29

## Summary

Reconciled the two parallel `Decidable` routes for `Derivable IntPropAxiom φ` and
`Derivable MinPropAxiom φ` that existed on `main` after tasks 411 (Int FMP) and 421
(Min FMP). The fix was a low-risk demotion-plus-documentation pass:

1. Demoted the two FMP `noncomputable instance`s to named `noncomputable def`s, making the
   tableau `instance`s the sole registered `Decidable` instances per proposition class.
2. Added mutually cross-referenced "Two Routes — Distinct Roles" docstrings to all four
   module headers.
3. Added infrastructure cross-reference docstrings to `int_fin_truth_lemma`,
   `min_fin_truth_lemma`, and the parametric `truthLemma` in Scheme.lean, recording the
   explicit "factoring deferred" decision.
4. Ran full CI verification and axiom audits.

## Phase Outcomes

### Phase 1: Demote FMP instances [COMPLETED]
- `IntDecidability.lean:430`: `noncomputable instance instDecidableDerivableIntPropAxiom'`
  demoted to `noncomputable def decidableDerivableIntPropAxiomFMP`
- `MinDecidability.lean:382`: `noncomputable instance instDecidableDerivableMinPropAxiom'`
  demoted to `noncomputable def decidableDerivableMinPropAxiomFMP`
- Main Results list in each header updated to reference the new `def` names
- New docstrings added to each `def` (lint-clean; no `defsWithUnderscore` or `docBlame`)
- Pre-edit grep confirmed zero external consumers of either primed instance
- `lake build` green on both modules; scoped CI clean

### Phase 2: Two-Routes Header Docstrings [COMPLETED]
- All four module headers carry a "Two Decision Routes — Distinct Roles" section:
  - `IntDecidability.lean`: Route 1 (FMP, sorry-free) + Route 2 (tableau, 317-tainted)
  - `MinDecidability.lean`: same, with Min-specific note on `minFinBotForces`
  - `Tableau/Intuitionistic/DecisionProcedure.lean`: extended existing sorry notes with
    all 4 task-317 sorry locations; cross-references FMP route
  - `Tableau/Minimal/DecisionProcedure.lean`: added "Notes on sorry" section (was missing);
    cross-references FMP route
- All cross-references use correct post-Phase-1 names (`decidableDerivable…FMP`)

### Phase 3: Infrastructure Cross-Reference Docstrings [COMPLETED]
- `int_fin_truth_lemma` docstring extended with:
  - Analogy to parametric `truthLemma` in `Scheme.lean:234` (317-owned sorry)
  - Disjoint carrier comparison (`Finset`-carrier `IntFinWorld φ` vs `Nat` branch labels)
  - Shared Lindenbaum substrate note (`int_imp_witness`, `int_prime_exclusion`)
  - Explicit "factoring deferred" rationale
- `min_fin_truth_lemma` docstring extended analogously (with `minFinBotForces` note)
- `truthLemma` in `Scheme.lean` received a light cross-reference comment pointing to
  the FMP truth lemmas and the "factoring deferred" decision in the module headers

### Phase 4: Full CI + Axiom Verification [COMPLETED]
See verification details below.

## Verification Results

### Axiom Audit

| Declaration | Axioms | sorryAx? |
|-------------|--------|----------|
| `decidableDerivableIntPropAxiomFMP` | `{propext, Classical.choice, Quot.sound}` | No |
| `decidableDerivableMinPropAxiomFMP` | `{propext, Classical.choice, Quot.sound}` | No |
| `instDecidableDerivableIntPropAxiom` | `{propext, sorryAx, Classical.choice, Quot.sound}` | Yes (pre-existing 317) |
| `instDecidableDerivableMinPropAxiom` | `{propext, sorryAx, Classical.choice, Quot.sound}` | Yes (pre-existing 317) |

### CI Pipeline

| Step | Result | Notes |
|------|--------|-------|
| `lake build` (scoped, 4 modules) | GREEN | All 4 modules build cleanly |
| `lake build` (repo-wide) | PARTIAL* | Only failure: pre-existing `ProofSystemMorphism.lean` (untracked WIP file, not task 422's scope) |
| `lake exe checkInitImports` | GREEN | All files import `Cslib.Init` |
| `lake exe lint-style` | GREEN | No style issues in modified files |
| `lake shake --add-public --keep-implied --keep-prefix` | GREEN | No import minimization suggestions |
| `lake lint` | GREEN | No `defsWithUnderscore`, `docBlame`, or `defLemma` warnings for our new declarations |
| New sorries introduced | 0 | All sorry occurrences in modified files are pre-existing 317 sorries in Scheme.lean |
| New axioms introduced | 0 | No `axiom` declarations added |

*The `ProofSystemMorphism.lean` build error is a pre-existing untracked WIP file
(explicitly listed in the orchestrator task instructions as out of scope). The 4 files
modified by task 422 all build cleanly, and all modules that import them build cleanly.

### Instance Registration Audit

Exactly one registered `Decidable` instance per proposition class (confirmed via lack of
instance resolution warnings and successful build):
- `instDecidableDerivableIntPropAxiom` — sole registered instance for `Derivable IntPropAxiom φ`
- `instDecidableDerivableMinPropAxiom` — sole registered instance for `Derivable MinPropAxiom φ`

FMP results accessible by name:
- `Cslib.Logic.PL.decidableDerivableIntPropAxiomFMP` (noncomputable def)
- `Cslib.Logic.PL.decidableDerivableMinPropAxiomFMP` (noncomputable def)

## Files Modified

- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Metalogic/IntDecidability.lean`
  (Phase 1: demotion; Phase 2: header docstring; Phase 3: truth lemma docstring)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Metalogic/MinDecidability.lean`
  (Phase 1: demotion; Phase 2: header docstring; Phase 3: truth lemma docstring)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Intuitionistic/DecisionProcedure.lean`
  (Phase 2: header docstring with two-routes section)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean`
  (Phase 2: header docstring with two-routes section + Notes on sorry)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
  (Phase 3: light cross-reference note on truthLemma)

## Plan Deviations

None. All phases executed as specified. Phase 3 was executed serially after Phase 2
(same files, different docstring regions) rather than in parallel — consistent with the
plan's note on parallelism.

## Sorry Inventory

Sorries in scope for task 422 (all pre-existing; none introduced by this task):
- `Scheme.lean:255` (was :246 before docstring addition) — parametric `truthLemma`; tracked under task 317
- `Scheme.lean:528` (was :519 before docstring addition) — open-branch countermodel structural; tracked under task 317
- `Completeness.lean:113` — `IValid → forcing` bridge; tracked under task 317
- `Minimal/Completeness.lean:110` — `MValid → forcing` bridge; tracked under task 317
