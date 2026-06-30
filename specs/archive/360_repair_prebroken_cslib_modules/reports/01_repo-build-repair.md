# Research Report: Restore Green Repo-Wide `lake build` (Task 360)

- **Task**: 360 — repair pre-broken CSLib modules
- **Session**: sess_1782522754_5f0817_360
- **Toolchain**: Lean v4.31.0 (pinned), experimental `module` system in use
- **Build captured**: `lake build` (full) + per-module `lake build <Module>` on 2026-06-26
- **Status**: Researched. All 11 originally-listed failures diagnosed; 2 drift deltas found.

## Executive Summary

The repo-wide build fails at the very end (3130/3132) plus several mid-tree modules. The
failures fall into **four root-cause clusters**, not eleven independent bugs:

- **Cluster A (6 modules) — task-340 `neg`/`top` typeclass-delegate migration.** The dominant
  cause. `Formula.neg`/`Formula.top` (Temporal + Bimodal) and `Proposition.neg`/`Proposition.top`
  (Modal) were changed to delegate to `PropositionalConnectives.neg`/`.top`. The migration commit
  updated `simp` sets *inside* the `Syntax`/`Basic` files but left downstream `simp only [...]`
  proof sites unaware of the new `PropositionalConnectives.*` unfolding step. Mechanical fix.
- **Cluster B (1 module) — module-system declaration clash.** `Cslib.Logics.Propositional.SequentCalculus`
  (the aggregator) fails because LK and LJ cut-elimination modules emit a colliding auxiliary
  declaration `Cslib.Logic.PL.cutAdmissibility._unary._proof_1` when co-imported.
- **Cluster C (1 module) — dependency signature drift.** `Tableau.Minimal.Soundness` calls
  `intExpandBranches_closed_unsat` with the old arity after `Tableau.Intuitionistic.Soundness`
  changed. Targeted call-site fix.
- **Cluster D (3 modules) — genuinely incomplete WIP.** `Modal.Tableau.Soundness` and
  `Propositional.Tableau.Classical.Completeness` were left mid-refactor by the vague
  `df974743 "update"` commit (renamed/removed hypotheses, non-existent Mathlib lemmas).
  `Semantics.Algebra.HilbertLindenbaumRel` (task 344 territory) has an API mismatch. These need
  intent-bearing fixes or `[BLOCKED]`, not mechanical repair.

`lake exe checkInitImports` and `lake shake` fail only downstream of the missing oleans; they
should clear automatically once the build is green.

### Drift since the /vet snapshot (files moved)

- `Cslib.Logics.Temporal.ConservativeExtension` — listed in the task as failing (lines 54/59/69
  ambiguous term); **now builds clean**. Drop from scope.
- `Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaumRel` — **newly broken** (was not
  in the task list). Add to scope (Cluster D).

## Per-Module Diagnosis

### Cluster A — `neg`/`top` typeclass-delegate migration (task 340)

**Root cause.** Commit `c520724e` ("task 340 phase 3: migrate Temporal and LTL neg/top to
typeclass delegates") and its Bimodal/Modal siblings changed:

```lean
-- before
abbrev Formula.neg (φ : Formula Atom) : Formula Atom := .imp φ .bot
abbrev Formula.top : Formula Atom := .imp .bot .bot
-- after
abbrev Formula.neg (φ : Formula Atom) : Formula Atom := PropositionalConnectives.neg φ
abbrev Formula.top : Formula Atom := PropositionalConnectives.top
```

(Identical pattern in `Cslib/Logics/Bimodal/Syntax/Formula.lean:63,68` and
`Cslib/Logics/Modal/Basic.lean:94,100`.) Because the head symbol after elaboration is now
`PropositionalConnectives.neg`/`.top`, any `simp only [..., Formula.neg/top, ...]` set that does
not *also* list `PropositionalConnectives.neg` / `PropositionalConnectives.top` cannot reduce to
the underlying `.imp _ .bot`, producing either **"`simp` made no progress"** (when the set only
mentioned the old name / a now-non-matching `*_def` lemma) or **"unsolved goals"** (when the set
unfolds `Formula.top` to `PropositionalConnectives.top` but then stops). The migration commit
demonstrably applied exactly this fix in-file (e.g. Formula.lean swapTemporal proofs now read
`simp only [Formula.neg, PropositionalConnectives.neg, ...]`); the downstream files were missed.

**Fix recipe (per site): append `PropositionalConnectives.neg` and/or `PropositionalConnectives.top`**
(and the relevant `Formula.allPast/somePast/someFuture/allFuture` abbrev unfoldings) to the
existing `simp only [...]` list. Verify each with `lake build <Module>` — note the lean-lsp
`multi_attempt` REPL environment diverged from the build environment during research, so trust
`lake build`, not the REPL, for the final check.

| Module | Error sites | Diagnosis | Fix |
|--------|-------------|-----------|-----|
| `Cslib.Logics.Modal.Denotation` | `60:2 simp made no progress` | `simp [Proposition.neg_def, Proposition.denotation]`; `(¬φ)` now elaborates with head `PropositionalConnectives.neg`, so `Proposition.neg_def` (LHS `Proposition.neg φ`) no longer matches | Replace with `simp [Proposition.neg, PropositionalConnectives.neg, Proposition.denotation]` (**verified closes the goal**) |
| `Cslib.Logics.Bimodal.Syntax.SubformulaClosure.NestingDepth` | `47,60,64,87,100,104,126,130` unsolved goals | simp sets list `Formula.top` but omit `PropositionalConnectives.top` (and some omit `PropositionalConnectives.neg`), leaving the final `.imp .bot .bot` reduction undone | Add `PropositionalConnectives.top` (and `PropositionalConnectives.neg` where `neg` appears) to each flagged `simp only` |
| `Cslib.Logics.Bimodal.Metalogic.Separation.Defs` | 22 sites (`73,85,118,134,149,154,227,231,235,239,257,263,284,288,301,305,323,329,382,387,512,518`) | `int_truth_*` lemmas use `simp only [intTruth]` on goals headed by derived ops (`Formula.allPast`, `allFuture`, `somePast`, `someFuture`), which now route through the typeclass delegates | Extend each to `simp only [Formula.allPast, Formula.somePast, Formula.allFuture, Formula.someFuture, Formula.neg, PropositionalConnectives.neg, Formula.top, PropositionalConnectives.top, intTruth]` (prune to the ops each lemma actually mentions) |
| `Cslib.Logics.Bimodal.ProofSystem.Substitution` | `91,106,112,118,124,131,455` unsolved goals | same delegate-unfold gap in substitution simp sets | Add `PropositionalConnectives.neg`/`.top` to the flagged `simp only` sets |
| `Cslib.Logics.Bimodal.Theorems.Perpetuity.Principles` | `84,164` type mismatch; `176` simp no progress | `simp only [Bimodal.Formula.swapTemporal, swapTemporal_involution]` leaves a residual `PropositionalConnectives.neg/top` term, so the subsequent `exact`'s type no longer matches | Add `PropositionalConnectives.neg, PropositionalConnectives.top` to the swapTemporal simp sets feeding the `exact`s at 84/164/176 |
| `Cslib.Logics.Temporal.Metalogic.DenseCompleteness` | `166:78` unsolved goals | `h_eq_form : nub.swapTemporal.allFuture.swapTemporal = nub.allPast` — swapTemporal/involution simp set misses the delegate unfolds | Add `Formula.neg, PropositionalConnectives.neg, Formula.top, PropositionalConnectives.top` to the simp set at line 166 |

**Durability note.** Because every site uses `simp only`, a global `@[simp]` reduction lemma will
not be picked up automatically. If the maintainers want a one-shot durable fix instead of ~35
edits, introduce explicit reduction lemmas (e.g. `PropositionalConnectives.neg_eq_imp_bot` /
`top_eq_imp` for each Formula/Proposition type, `@[simp]`-tagged and `rfl`-proved) and *also*
list them in the affected `simp only` sets. Recommended approach for the plan: do the mechanical
per-site edits (low risk, fully local) rather than re-architecting the connective layer.

### Cluster B — module-system declaration clash (SequentCalculus)

**Module**: `Cslib.Logics.Propositional.SequentCalculus` (aggregator,
`SequentCalculus.lean:7` imports LK then LJ).

**Error**:
```
import ...SequentCalculus.LJ.CutElimination failed, environment already contains
'Cslib.Logic.PL.cutAdmissibility._unary._proof_1' from ...SequentCalculus.LK.CutElimination
```

**Diagnosis.** `cutAdmissibility` is defined only in
`SequentCalculus/LK/CutElimination.lean:825` (`noncomputable def cutAdmissibility ... termination_by
sizeOf C`). LJ uses the distinct name `ljCutAdmissibility`
(`LJ/CutElimination.lean:655`), and the LJ import tree never imports LK (verified: no `import
.LK` anywhere under `SequentCalculus/LJ/`). Both `LK.lean` and `LJ.lean` (and hence the
`SequentCalculus` aggregator) `public import` their respective `CutElimination`. Both
cut-admissibility defs live in the **same namespace `Cslib.Logic.PL`** and are compiled by
well-founded recursion, which emits a `._unary._proof_1` auxiliary. Under the experimental
`module` system these auxiliaries become module-level declarations; co-importing LK and LJ
surfaces a duplicate `Cslib.Logic.PL.cutAdmissibility._unary._proof_1`, which the loader rejects.
(LK and LJ each build fine in isolation — the clash only appears at the aggregator.)

**Fix (recommended, robust regardless of exact name-derivation mechanism):**
1. Move LK's cut-elimination development into a dedicated sub-namespace
   `namespace Cslib.Logic.PL.LK` (and LJ's into `Cslib.Logic.PL.LJ`), so no internal auxiliary
   name can collide. This also matches ORGANISATION conventions for parallel calculi.
2. And/or mark `cutAdmissibility` (LK) and `ljCutAdmissibility` (LJ) `private`, which keeps their
   `._unary._proof_1` auxiliaries out of the public module interface.

**Discriminating test before editing** (cheap): rename LK's `cutAdmissibility` →
`lkCutAdmissibility`. If the clash name changes to `lkCutAdmissibility._unary._proof_1` (i.e. the
error disappears), the collision is confirmed to be a same-base-name auxiliary clash and option
(1)/(2) is the right fix. Implementer should run `lake build Cslib.Logics.Propositional.SequentCalculus`
to confirm.

### Cluster C — dependency signature drift (Minimal.Soundness)

**Module**: `Cslib.Logics.Propositional.Tableau.Minimal.Soundness`.

**Errors**: `131:30 Application type mismatch` (argument to `intExpandBranches_closed_unsat`),
`132:5 invalid ⟨...⟩` (cascade), `131:25 rfl failed`, `132:23 simp made no progress` (cascade).

**Diagnosis.** `Tableau/Intuitionistic/Soundness.lean` (modified recently — appears in the
working tree as `M`) changed the signature of `intExpandBranches_closed_unsat`; the call site in
`Minimal/Soundness.lean:128-135` passes the old argument shape. Root error is the type mismatch;
the rest cascade.

**Fix.** Re-read the current signature of `intExpandBranches_closed_unsat` in
`Intuitionistic/Soundness.lean` and update the application at `Minimal/Soundness.lean:128-135` to
match.

**Zero-debt note.** This file documents (lines 41-44, 116) that it *inherits a pre-existing
`sorry`* from `intExpandBranches_closed_unsat`. That sorry is committed, pre-existing debt and is
**out of scope** for this build-repair task (sorries are warnings, not build failures). The repair
must only fix the type mismatch; it must **not** add new sorries. Flag the inherited sorry to the
user as belonging to a separate Intuitionistic-soundness completion task.

### Cluster D — genuinely incomplete WIP (intent required)

These three are not mechanical fixes. Recommend dedicated fix tasks (or `[BLOCKED]` for user
review) rather than folding them into the mechanical sweep. Per zero-debt policy: do **not** paper
over with `sorry`/axioms — either complete or mark `[BLOCKED]`.

| Module | Errors | Diagnosis | Recommendation |
|--------|--------|-----------|----------------|
| `Cslib.Logics.Modal.Tableau.Soundness` | `303/335/362/402/649/705/729 Unknown identifier hnewBs`; `746 Duplicate alternative name imp`; `275/624 cases nested error`; multiple app mismatches & unsolved goals | Left mid-refactor by `df974743 "update"` (touched only this file + Classical.Completeness). A hypothesis `hnewBs` was renamed/removed but ~20 references remain; a `cases`/`rcases` alternative list has a duplicate `imp` arm | Dedicated fix task referencing task 299 (`299_modal_k_tableau`) plan + the handoff updated by df974743. `[BLOCKED]` if the intended `hnewBs` replacement is unclear |
| `Cslib.Logics.Propositional.Tableau.Classical.Completeness` | `117 Unknown constant List.findSome?_of_mem`; `147 List.find?_of_mem`; many `Function expected`, `rewrite failed`, unsolved goals; 1 `sorry` | `df974743` added 178 WIP lines citing non-existent Mathlib lemmas and partially-applied terms. Mid-development | Dedicated fix task; reference the theory report `reports/01_theory-parametric-completeness.md` added by df974743 and find the correct Mathlib list lemmas (e.g. `List.find?_some`, `List.findSome?_eq_some_iff`) via leansearch. `[BLOCKED]` if scope is large |
| `Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaumRel` | `827:4 Function expected at`; `829:8 introN failed` (no binders to intro) | task 344 phase 2 territory (`relCanonicalV_satisfiesΓ`). `SatisfiesTheory (AlgEvaluate (relCanonicalV ...) ...)` is applied as a function but the head isn't applicable — `AlgEvaluate`/`relCanonicalV` API mismatch after a recent change. **Newly broken (drift)** | Targeted fix in task-344 territory: re-check `AlgEvaluate` and `relCanonicalV` signatures, adjust `relCanonicalV_satisfiesΓ` |

## Recommended Fix Ordering

Prioritize modules with no dependents and the lowest risk first.

1. **Cluster A — mechanical simp-set updates (6 modules).** Independent, low-risk, unblocks the
   Modal/Bimodal/Temporal subtrees. Suggested order (all leaf-ish; order is not load-bearing):
   `Modal.Denotation` → `Bimodal.Syntax.SubformulaClosure.NestingDepth` →
   `Bimodal.Metalogic.Separation.Defs` → `Bimodal.ProofSystem.Substitution` →
   `Bimodal.Theorems.Perpetuity.Principles` → `Temporal.Metalogic.DenseCompleteness`.
   Verify each with `lake build <Module>`.
2. **Cluster B — SequentCalculus namespace isolation (1 change).** Independent of A; unblocks the
   final aggregator (the last build step).
3. **Cluster C — Minimal.Soundness call-site fix (1 change).** Quick; depends on reading the
   current `intExpandBranches_closed_unsat` signature.
4. **Cluster D — WIP (3 modules), do last / split out.** Order by tractability:
   `HilbertLindenbaumRel` (smallest, API mismatch) → `Modal.Tableau.Soundness` (identifier
   rename) → `Classical.Completeness` (largest, missing lemmas). Recommend separate fix tasks;
   `[BLOCKED]` any whose author intent cannot be recovered.
5. **Final gate.** `lake build` (full) green, then re-run `lake exe checkInitImports` and
   `lake shake --add-public --keep-implied --keep-prefix` — both expected to pass once oleans
   exist.

## Reuse Check (CSLib reuse-first)

No new abstractions are recommended. All Cluster A fixes reuse the existing
`PropositionalConnectives` typeclass delegates introduced by task 340 — the correct, already-present
abstraction; the repair simply threads them through the downstream `simp` sets. Cluster B reuses
standard namespace/`private` scoping. No new definitions, notation, or axioms are needed.

## Verification Commands

```bash
# per-cluster
lake build Cslib.Logics.Modal.Denotation
lake build Cslib.Logics.Bimodal.Syntax.SubformulaClosure.NestingDepth
lake build Cslib.Logics.Bimodal.Metalogic.Separation.Defs
lake build Cslib.Logics.Bimodal.ProofSystem.Substitution
lake build Cslib.Logics.Bimodal.Theorems.Perpetuity.Principles
lake build Cslib.Logics.Temporal.Metalogic.DenseCompleteness
lake build Cslib.Logics.Propositional.SequentCalculus
lake build Cslib.Logics.Propositional.Tableau.Minimal.Soundness
# WIP
lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaumRel
lake build Cslib.Logics.Modal.Tableau.Soundness
lake build Cslib.Logics.Propositional.Tableau.Classical.Completeness
# final
lake build && lake exe checkInitImports && lake shake --add-public --keep-implied --keep-prefix
```
