# Implementation Summary: Task #379 - CPL Conservative over Classical ⟨∧,→,⊥,⊤⟩ Fragment

- **Task**: 379
- **Status**: [IMPLEMENTED]
- **Plan**: plans/01_classical-conjimpbot-conservativity.md
- **Session**: sess_1782560395_aeb7ef_379

## Deliverables

### New Module

`Cslib/Logics/Propositional/Metalogic/ClassicalConjImpBotCompleteness.lean`

Declarations (all CI-green, zero sorry, zero new axioms):

- `classicalConjImpBot_soundness` — every CPL⟨∧,→,⊥,⊤⟩-derivable formula is a tautology
- `classicalConjImpBot_imp_self` — identity `⊢ φ → φ` (S K K)
- `classicalConjImpBot_imp_trans` — composition in the empty context
- `classicalConjImpBot_peirce_mp` — Peirce case lemma
- `classicalConjImpBot_imp_trans_ctx` — in-context composition
- `classicalConjImpBot_weaken_ctx` — in-context K-weakening
- `classicalConjImpBot_exfalso` — EFQ helper: `Γ ⊢ ⊥ → φ` via `.efq`
- `classicalConjImpBot_kalmar` — IsOrFree Kalmár truth lemma (atom/bot/imp/and; or excluded)
- `classicalConjImpBot_elim_atom` — one-step atom elimination
- `classicalConjImpBot_collapse` — full literal context collapse
- `classicalConjImpBot_completeness` — **primary deliverable**: every or-free CPL tautology is CPL⟨∧,→,⊥,⊤⟩-derivable
- `cpl_conservative_over_classicalConjImpBot` — CPL conservative over CPL⟨∧,→,⊥,⊤⟩ for or-free formulas
- `derivablePropOfDerivableClassicalConjImpBot` — subsumption
- `classicalConjImpBot_iff_chain` — biconditional chain edge

### Updated Module

`Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean` — added:
- `public import` of the new metalogic module
- Classical column doc table (CL-A through CL-C)
- Note that all three towers (MPL/IPL/CPL) are now structurally symmetric at the ⟨∧,→,⊥,⊤⟩ rung

### Barrel

`Cslib.lean` updated via `lake exe mk_all --module`.

## Proof Strategy

The `classicalConjImpBot_kalmar` truth lemma adds exactly **one new inductive case** over
the task-378 `classicalConjImp_kalmar` (which handled atom/imp/and over `IsOrBotFree`):

- **`bot` TRUE side**: vacuous — `BoolEvaluate v ⊥ = false` always, so the hypothesis
  `false = true` is discharged by `absurd hv (by decide)`.
- **`bot` FALSE side**: immediate — `Γ ⊢ ⊥ → goal` is exactly `classicalConjImpBot_exfalso`
  (the EFQ axiom `.efq goal`).

All other cases (atom, imp, and, or-excluded) are mechanically transcribed from task 378,
retargeting `ClassicalConjImpAxiom` → `ClassicalConjImpBotAxiom` and
`IsOrBotFree` → `IsOrFree`.

## CI Verification

- `lake build Cslib.Logics.Propositional.Metalogic.ClassicalConjImpBotCompleteness`: PASS
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.ConservativeChain`: PASS
- `lake lint` (new file): zero warnings in docBlame, defLemma, defsWithUnderscore, simpNF categories
- `lake exe lint-style` (new file): PASS (no style issues)
- `lake shake` (new file): PASS (no unused imports)
- `lake exe mk_all --module`: PASS (barrel updated)
- `lean_verify classicalConjImpBot_completeness`: axioms = [propext, Classical.choice, Quot.sound] only
- `lean_verify cpl_conservative_over_classicalConjImpBot`: axioms = [propext, Classical.choice, Quot.sound] only
- `lake test`: pre-existing Bimodal/Modal failures only (not introduced by this task)
- `checkInitImports`: `import Cslib.Init` present on line 9 of new module; tool fails on pre-existing
  Bimodal build failure, not on our file

## Plan Deviations

- Phases 1-5 were implemented in a single pass rather than separate dispatches (all phases
  succeeded together; no per-phase blocking was needed).
- `litCtx_congr'` is defined as a private local copy (same approach as task 378) rather than
  importing from task 352, because the task-352 version is also private. Named `litCtx_congr'`
  consistent with the task-378 pattern.
- ConservativeChain.lean received a `public import` of the new Metalogic module rather than
  just a doc comment, to make the classical chain accessible from the chain capstone module.
  No circular dependency was introduced (Metalogic only imports from Semantics/Algebra leaves).
