# Task 343 — Implementation Summary (COMPLETE)

**Status:** Implemented (all 3 phases executed; CI-green for the affected propositional subtree).

## What Landed

### Phase 1 — Core predicate + defeq `AlgTValid` (CI-green)

File: `Cslib/Logics/Propositional/Defs.lean`
- Added generic single-formula predicate `Satisfies {β} [Top β] (eval : Proposition Atom → β) (A) : Prop := eval A = ⊤`.
- Added generic theory predicate `SatisfiesTheory {β} [Top β] (eval : Proposition Atom → β) (T : Theory Atom) : Prop := ∀ A ∈ T, eval A = ⊤`.
- Added scoped notation `eval ⊨ A` (single formula) and `eval ⊨ T` (theory), disambiguated by
  the expected type of the right operand. The notation-overloading gate passed empirically.

File: `Cslib/Logics/Propositional/Semantics/Algebra.lean`
- Redefined `AlgTValid T v bot_val := SatisfiesTheory (AlgEvaluate v bot_val) T` (definitionally
  equal to the old body).
- Kept `v ⊨[bot_val] T` bracket notation as the documented legacy alias.

### Phase 2 — GHAValid/HAValid/BAValid rewiring (BLOCKED — invariant preserved)

The plan called for rewriting `GHAValid`/`HAValid`/`BAValid` bodies to factor through `Satisfies`.
This is defeq at the type level but NOT at the tactic level: it would require updating 9+
`simp only [AlgEvaluate]` sites in `Algebra/Soundness.lean` (a task-341 file), violating the
hard "341 untouched (defeq)" invariant. Decision: leave `GHAValid`/`HAValid`/`BAValid` with
their original `AlgEvaluate … = ⊤` bodies (already trivially `Satisfies`-shaped by defeq). No
edits to `Soundness.lean`.

### Phase 3 — Prop-valued entailments (Option A) applied (CI-green)

File: `Cslib/Logics/Propositional/Semantics/SemanticConsequence.lean`
- Inspected `SemanticEntails`, `ISemanticEntails`, `MSemanticEntails`.
- Confirmed these use raw-Prop forcing (`Evaluate v ψ` or `IForces val ... w ψ`), which cannot
  factor through `SatisfiesTheory` (that requires `eval A = ⊤`; connecting `Prop` forcing to
  `= True` requires propext, which is not definitional).
- Option A applied: added docstring convention notes to all three predicates explaining the
  Prop-forcing vs `= ⊤` split and recording full unification as a deferred roadmap item. No
  behavior change; no code change to definition bodies.

## Verification

- `lake build Cslib.Logics.Propositional.Semantics.SemanticConsequence` — success.
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertCompleteness` — success.
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertAlgCompleteness` — success.
- Task-341 proofs (`Soundness.lean`, `HilbertLindenbaum.lean`, `HilbertCompleteness.lean`) compile **unchanged** — invariant held.
- `lake exe lint-style` — no warnings for changed files.
- `lake shake --add-public --keep-implied --keep-prefix` — no warnings for changed files.
- `lake lint` — no warnings for changed files.
- Zero `sorry`, zero new axioms.
- `git diff` confined to `Defs.lean`, `Algebra.lean`, `SemanticConsequence.lean`.

### Pre-existing build failures (NOT caused by task 343)

`lake build` and `lake test` report failures in `Bimodal`, `Modal/Tableau`, `Temporal`, and
`Propositional/Tableau` modules. These failures exist on the baseline branch (confirmed by
stashing all task-343 changes and re-running `lake build CslibTests` — same failures). They are
pre-existing open tasks, not regressions introduced here.

`lake exe checkInitImports` also fails for the same reason (requires all modules to be built).
The Init import is satisfied transitively in all three changed files:
- `Defs.lean`: direct `import Cslib.Init`.
- `Algebra.lean`: direct `import Cslib.Init`.
- `SemanticConsequence.lean`: transitively via `Bool.lean` → `Defs.lean` → `Cslib.Init`.

## Roadmap Item

The following item should be captured in ROADMAP.md:

> **Full Prop/valued entailment unification**: Unify `SemanticEntails`/`ISemanticEntails`/
> `MSemanticEntails` premise notation with the algebraic `SatisfiesTheory` convention. Currently
> blocked by the need for `propext` (Prop forcing ≠ `= True` definitionally). Requires either
> (a) a propext-based bridge theorem and notation aliasing, or (b) redefining the Prop-valued
> entailments to use `= True` as the forcing condition (breaking change to existing consumers).

## Plan Deviations

| Phase | Deviation |
|-------|-----------|
| 2 | GHAValid/HAValid/BAValid NOT rewired. Type-level defeq but tactic-level opaque to existing simp proofs in Soundness.lean (task-341). Invariant takes precedence. Accepted per user direction. |
| 3 | No code change to definition bodies. Docstring convention notes added instead. Premise rewiring via `⊨` notation not defeq-safe (requires propext). Option A = docstring-only. |
| 3 CI | `lake test` and `lake exe checkInitImports` blocked by pre-existing Bimodal/Modal/Temporal failures; propositional subtree CI-green. |
