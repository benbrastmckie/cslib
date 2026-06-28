# Implementation Summary: Task #378 - CPL Conservative over Classical Conjunction-Implication Fragment

- **Task**: 378 - Prove CPL is conservative over CPL⟨∧,→,⊤⟩ (CL-B rung)
- **Status**: IMPLEMENTED
- **Session**: sess_1782560395_aeb7ef_378
- **Date**: 2026-06-27

## What Was Done

Created `Cslib/Logics/Propositional/Metalogic/ClassicalConjImpCompleteness.lean` (new module)
implementing the full CL-B conservativity chain for or-bot-free classical formulas.

All phases were completed in a single dispatch (the implementation was straightforward enough
to handle all phases without intermediate commits):

### Deliverables

1. **`classicalConjImp_soundness`** — every `ClassicalConjImpAxiom`-derivable formula is a
   tautology, routing through `ClassicalConjImpAxiom.toPropAxiom` and CPL soundness.

2. **Derived helpers** — `classicalConjImp_imp_self`, `classicalConjImp_imp_trans`,
   `classicalConjImp_peirce_mp`, `classicalConjImp_imp_trans_ctx`,
   `classicalConjImp_weaken_ctx`.

3. **`Proposition.atomsConjImp`** — new atom collector covering `atom`, `imp`, and `and`
   sub-formulas (extends `Proposition.atoms` which only recurses into `imp`).

4. **`private litCtx_congr'`** — local copy of the valuation congruence lemma (the original
   in `ClassicalImpCompleteness` is `private` and not importable).

5. **`classicalConjImp_kalmar`** — the ∧-extended Kalmár / Tarski–Bernays truth lemma with
   `atom`, `imp`, and **`and`** cases. The `and` case discharge:
   - TRUE subcase: nested DT construction using `andI` to build `a → (b → goal)` then compose
     with `andE1`/`andE2`-based approach; IHa-TRUE/IHb-TRUE applied in order.
   - FALSE left: compose `andE1 a b` with `ihaF` via `classicalConjImp_imp_trans_ctx`.
   - FALSE right: compose `andE2 a b` with `ihbF` via `classicalConjImp_imp_trans_ctx`.

6. **`classicalConjImp_elim_atom`** and **`classicalConjImp_collapse`** — atom elimination
   and context collapse, mechanical mirrors of the task-352 versions.

7. **`classicalConjImp_completeness`** — `φ.IsOrBotFree = true → Tautology φ → Derivable ClassicalConjImpAxiom φ`.

8. **`cpl_conservative_over_classicalConjImp`** — CPL conservative over CPL⟨∧,→,⊤⟩ for
   or-bot-free formulas.

9. **`derivablePropOfDerivableClassicalConjImp`** — subsumption direction.

10. **`classicalConjImp_iff_chain`** — biconditional `Derivable ClassicalConjImpAxiom φ ↔ Derivable PropositionalAxiom φ` (for `φ.IsOrBotFree = true`).

### Barrel

`Cslib.lean` updated via `lake exe mk_all --module`.

## Plan Deviations

- **Phases 1–5 completed in a single dispatch** (not separate commits per phase). The
  implementation was clean enough to write the complete file at once.
- **`litCtx_congr'`** (with trailing prime) used instead of `litCtx_congr` to avoid
  name clash with the private version in the imported `ClassicalImpCompleteness` module.
- **`classicalImp_weaken_ctx` not needed in the `and` case** — the TRUE subcase uses
  `classicalConjImp_imp_trans_ctx` directly instead.

## Verification

- Scoped build: `lake build Cslib.Logics.Propositional.Metalogic.ClassicalConjImpCompleteness` ✓
- No sorries in new module ✓
- No new axioms: only `propext`, `Classical.choice`, `Quot.sound` (standard math axioms) ✓
- `lean_verify` on `classicalConjImp_kalmar`, `classicalConjImp_completeness`,
  `cpl_conservative_over_classicalConjImp`: no `sorryAx` ✓
- Barrel updated: `ClassicalConjImpCompleteness` in `Cslib.lean` ✓
- `lake exe checkInitImports`: no issues ✓
- `lake exe lint-style`: no issues in new module ✓
- `lake lint`: no environment linter issues in new module ✓
- `lake shake`: blocked by pre-existing build failures in Modal/Bimodal modules (task 363) ✓
- Pre-existing failures (Modal Tableau Soundness, Bimodal modules): not caused by this task ✓

## Files Changed

- `Cslib/Logics/Propositional/Metalogic/ClassicalConjImpCompleteness.lean` (NEW, ~320 lines)
- `Cslib.lean` (barrel updated by `mk_all`)
