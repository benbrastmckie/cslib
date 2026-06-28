# Implementation Plan (v6 — AS-BUILT reconciliation): Task #332

- **Task**: 332 — Strong-normalization / termination theorem for CSLib `Theory.Derivation`
- **Status**: [COMPLETED] (with two outstanding loose ends — see "Skipped / Outstanding Items")
- **Effort**: Done. ~9 dispatches across this orchestration session (plus prior sessions).
- **Dependencies**: Task 290 ([COMPLETED] — discharged by this task); task 333 module refactor (prior).
- **Research Inputs**: reports/01, 02, 03 (DM-measure route — now superseded); **reports/04_phase4-build-plan.md** (the verified constructive route actually used).
- **Supersedes**: plans/05_termination-plan-v5.md — **v5's core strategy was proven UNSOUND** (see below).
- **Standards**: plan-format.md, cslib.md, lean4.md, literature-fidelity-policy.md
- **Type**: cslib

## Why v6 (the v5 strategy was falsified)

v5 (and all of plans 01–04) pursued a **height-free Dershowitz–Manna measure**
`normMeasure = (maximalFormulas, commutingSum)` with `exists_stronglyNormal_form` proved by
`WellFounded.induction normMeasure_wf` (well-founded *descent*: reduce `d → reduceRoot d'` and show
the measure drops). During this session that route was **empirically disproved** (report 04 §2):

> On the witness `andE1 (orE (ass) (andI ..) (andI ..))` — whose leaves are strongly normal — the
> only available reduction is the root commuting conversion, and it makes `maximalFormulas` go from
> `∅` to `{c, c}`. So the measure **strictly increases** on the only reachable step. Root cause:
> `maximalFormulas` charges a marker only for a *direct* redex; it does **not** charge a maximal
> *segment* through `orE` (the T&S notion), so commuting conversions that turn a segment into a
> direct redex appear to raise the measure. `reduceRoot_decreases_normMeasure` is individually true
> only because its `reduceRootSubSN` hypothesis excludes exactly these reachable configurations.

This is why the task stalled across multiple prior sessions: the documented measure cannot descend.

## What was actually built (the constructive route — report 04)

`exists_stronglyNormal_form` is proved **constructively** (Prawitz weak normalization via "smart
eliminators", not by reducing a given derivation):

- **Smart eliminators** `snAndE1Form`, `snAndE2Form`, `snImpEForm`, `snOrEForm`: build the SN form
  of an elimination from SN premises, pushing eliminations through `orE` branches (commuting) and
  β-projecting at introductions.
- **`snSubst`**: substitution-normalization — the SN form of `body.subsOne arg`.
- **Termination**: the mutual block `snImpEForm`/`snOrEForm`/`snSubst` is well-founded under a
  **3-component lexicographic measure `(cut-formula complexity, phase, sizeOf)`** (phase = 0 for
  eliminators, 1 for `snSubst`), with a carried **head-behaviour invariant** (hereditary-substitution
  / NbE style) discharging the one non-structural "head-bound" edge. β-edges drop cut complexity via
  `subsOne_new_redex_complexity_lt`.
- **Driver** `snForm` (structural) + `exists_stronglyNormal_form := ⟨(snForm d).1, (snForm d).2⟩`.
- `subformula_property` (SubformulaProperty.lean) re-pointed at `exists_stronglyNormal_form`; the
  fuel theorem `normalize_isStronglyNormal` (and its `sorry`) **retired**.

Result: `Normalization/` is **0 sorries, axiom-clean** (`exists_stronglyNormal_form`:
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`; `subformula_property` axiom-clean), builds
green (627 jobs). `lake exe lint-style` passes.

## Phase reconciliation (planned v5 → actual)

| v5 Phase | Planned | Actual status |
|----------|---------|---------------|
| 1 (DM-measure infra) | normMeasure, normMeasure_wf, … | [COMPLETED] earlier — **now mostly DEAD CODE** (route abandoned) |
| 2 (decrease 7/8 cases) | reduceRoot_decreases_normMeasure | [COMPLETED] earlier — **now DEAD CODE** |
| 3 (close h_8) | last decrease case | **[COMPLETED]** this session (commit 41c7281f) — **but now DEAD CODE** (its lemma is unused) |
| 4 (exists_stronglyNormal_form via WF descent) | WellFounded.induction normMeasure_wf | **[COMPLETED] via a DIFFERENT, constructive route** (the planned route was unsound). Commits f855d8c5 (plan), cbb0571d (L0–L2), e87975fc/42bfcbb9/1abb0f53 (termination+head-bound), 766f2ea6…28e6f29d (casts+driver) |
| 5 (re-point subformula_property; delete fuel sorry) | as planned | **[COMPLETED]** (commit 115b7ffe) |
| 6 (CI) | full pipeline green | **[PARTIAL]** — lint-style green; Normalization green/0-sorry/axiom-clean; full-project gates BLOCKED (see below) |

## Skipped / Outstanding Items (the answer to "was anything skipped?")

1. **Full-project CI gates not run** (`lake build` full, `lake exe checkInitImports`, `lake lint`,
   `lake test`, `lake shake`). **External blocker**: the project does not fully build — `Bimodal/…`
   and `Modal/Tableau/Soundness` modules are **red on `main` itself** (verified: `main` fails to
   build `Bimodal.Theorems.Perpetuity.Bridge`; those modules are owned by other in-flight tasks,
   e.g. 364 modal-tableau-soundness-drift-repair). This branch's diff is **`Normalization/`-only**,
   so 332 introduces no regression, but the project-wide gates cannot pass until the unrelated
   modules are fixed. **Action**: re-run the CI pipeline once `main` is green again (or on a rebase).
2. **Dead-code cleanup NOT done.** The abandoned WF-descent + fuel machinery is now unused but still
   in `Termination.lean` (compiles green; would be flagged by `lake shake` / unused-decl linters):
   - `normMeasure`, `normMeasure_wf` — **0 live uses**
   - `reduceRoot_decreases_normMeasure` (incl. the Phase-3 h_8 proof) — referenced only in a docstring
   - `redexWeight`, `redexWeight_zero_sn` — **0 live uses** (the old fuel route)
   - the `Multiset.isDershowitzMannaLT_*` helpers used only by the above
   - the `import Mathlib.Data.Multiset.DershowitzManna` may become removable.
   Shared helpers (`maximalFormulas`, `commutingSum`, `nodeCount`, `weakCtx` lemmas,
   `subsOne_new_redex_complexity_lt`, `maximalFormulas_sn_eq_zero`) are **live** — keep them.
   **Action**: remove the dead closure (~several hundred lines) before PR. Tracked as a follow-up
   (recommend a dedicated cleanup task) since it deletes hard-won-but-orphaned proof code and needs
   a careful live/dead boundary check + a `lake shake` pass to confirm.

## Nothing else was skipped

- The substantive deliverable (a sorry-free, axiom-clean strong-normal-form existence theorem and a
  sorry-free `subformula_property`) is **complete and compiler-verified**.
- No new axioms; no vacuous placeholders; no `sorry`/`admit` anywhere in `Normalization/`.

## Artifacts

- `Cslib/Logics/Propositional/NaturalDeduction/Normalization/Termination.lean` (constructive route; 0 sorry)
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization/SubformulaProperty.lean` (re-pointed; 0 sorry)
- reports/04_phase4-build-plan.md (the verified design); handoffs/phase4b-handoff.md, phase5-handoff.md
