# Implementation Plan: Task #426 — Temporal Tableau Time-Ordering Redesign

- **Task**: 426 - Redesign the temporal tableau time-ordering scheme so ordering invariants hold, then prove the corrected `ordConstraints` lemma sorry-free
- **Status**: [NOT STARTED]
- **Effort**: 7.5 hours
- **Dependencies**: None (independent of tasks 424, 425; decomposed from task 301 blocker A)
- **Research Inputs**: specs/426_temporal_tableau_ordconstraints_redesign/reports/01_ordconstraints-redesign.md
- **Artifacts**: plans/01_ordering-instant-redesign.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

The lemma `ordConstraints_strict` (currently commented out at `Completeness.lean` 254–262) is
**genuinely false**: `addPast t tNew` records the pair `(tNew, t)` while `tNew = branchNextTime b`
is numerically `> t`, so `(tNew, t) ∈ constraints` with `tNew > t` is a direct counterexample to
`∀ (a,b) ∈ constraints, a < b`. This plan adopts the research report's **recommended Option B**:
augment `TimeOrdering` with a relative integer **instant** assigned at creation
(`addFuture`: `instant tNew = instant t + 1`; `addPast`: `instant tNew = instant t - 1`), take the
time domain `D = ℤ` and order-preserving map `f = instant`, and replace the false lemma with the
**immutable edge-by-edge invariant**
`InstantStrict ord : ∀ a b, (a,b) ∈ ord.constraints → ord.instant a < ord.instant b`.
This invariant is maintained from `TimeOrdering.empty` through every constraint-adding operation by
local induction — **no acyclicity / topological-sort / Mathlib order-extension machinery is needed**.

The deliverable is: the corrected ordering invariant proved **sorry-free**, `extractModel` re-keyed
through `f` (`extractModelℤ`) with its atom lemmas re-proved, the false `ordConstraints_strict`
comment block removed/replaced, and a **green `lake build` + `lake test`**. Start from green commit
`7f052834` (verified present: "task 301: add extractModel_atomPos_sat, document ordConstraints
design issue").

**Scope boundary** (from research §5): Task 426 delivers exactly the order-preservation component
(`InstantStrict` + the `D=ℤ / f=instant` choice) and the re-keyed atom properties. It does **NOT**
include the FMP-blocked Until/Since fulfilment lemmas (`temporalTruthLemma_untl/snce`) nor the full
`temporalTruthLemma`; the full `openBranch_branchSat` and `temporalTableau_complete` therefore
**remain BLOCKED on FMP** and are out of scope. Zero-debt: if a threading obstacle would force a
`sorry`, mark the affected phase **[BLOCKED]** for user review instead of introducing any
`sorry`/axiom/vacuous definition.

### Research Integration

- Root cause confirmed (report §1): `addPast` is the offender; `branchNextTime_gt` (Rules.lean:73)
  guarantees `tNew > t` numerically, so the Nat label order cannot coincide with semantic "before".
- Real requirement (report §2): `branchSat` (Soundness.lean 79–87) existentially quantifies over
  `D` and `f`; it needs only *some* order-preserving `f`, not `f = id` / `D = Nat`.
- Chosen design (report §3–4, Option B): integer instants; `D = ℤ` already supplies `LinearOrder` +
  `Nontrivial` via `inferInstance` (precedent at `ConservativeExtension.lean:67`).
- Re-key caveat (report §5): `extractModel`'s valuation is keyed on the Nat label and must be
  re-keyed through `f`. Non-injectivity of `instant` only affects the Until/Since truth lemma, which
  is out of scope.
- Reusable lemmas (report §6): `branchNextTime_gt` (Rules.lean:73), `mem_futureOf_iff` /
  `mem_pastOf_iff` (TimeOrdering.lean:133/149), `freshTime_gt` (TimeOrdering.lean:204) as a
  proof-shape template, `Function.update` (Mathlib), `omega`.
- Documented fallback (report §3 Option A): Mathlib `LinearExtension` / `toLinearExtension`
  (`Mathlib.Order.Extension.Linear`) via an acyclicity argument — heavier; only if Option B
  threading proves too invasive.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (no `roadmap_path` provided; `roadmap_flag` not set).

## Goals & Non-Goals

**Goals**:
- Augment `TimeOrdering` (TimeOrdering.lean) with an `instant : Nat → ℤ` scheme: `empty`,
  `addFuture`, `addPast` set instants consistently with each edge's semantic direction.
- Define `InstantStrict` and prove the edge-by-edge preservation lemmas
  (`InstantStrict.empty`, `InstantStrict.addFuture`, `InstantStrict.addPast`) **sorry-free**.
- Prove the run-level corrected lemma replacing `ordConstraints_strict`:
  `temporalTableau φ = .openBranch b ord → InstantStrict ord`, **sorry-free** (high-risk;
  see Risks + Phase 3 fallback).
- Re-key `extractModel → extractModelℤ` (`TemporalModel ℤ Atom`) and re-prove the atom-level
  model properties sorry-free.
- Remove/replace the false `ordConstraints_strict` comment block and wire the order-preservation
  component of `branchSat` (`D = ℤ`, `f = ord.instant`) as far as the FMP boundary allows.
- Keep the whole project green: `lake build`, `lake test`, plus `lake exe checkInitImports`.

**Non-Goals**:
- Proving `temporalTruthLemma_untl` / `temporalTruthLemma_snce` (FMP-blocked — out of scope).
- Completing the full `openBranch_branchSat` / `temporalTableau_complete` / `instDecidableValid`
  (depend on the FMP truth lemma — remain BLOCKED).
- Adopting Option A (Mathlib `LinearExtension`) unless Option B threading is infeasible.
- Any `sorry`, new axiom, or vacuous definition (`def X := True` etc.) anywhere.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Run-level threading of `InstantStrict` through `temporalExpandBranches`/`processNext` (recursive worklist + fuel induction) is heavy and may not close in one run | H | M | Phase 3 isolates this. Needs the coupling invariant "every time in `ord.allTimes` is a label on `b`" so `tNew = branchNextTime b` is fresh w.r.t. `ord`. Fallback: deliver the edge-by-edge preservation lemmas (Phase 2) as the sorry-free corrected lemma and mark the run-level threading **[BLOCKED]** for user review — never introduce `sorry`. |
| `tNew` freshness w.r.t. `ord` cannot be discharged because `ord` could mention non-branch labels | H | L | Establish/strengthen the coupling invariant (ord endpoints ⊆ branch labels) maintained alongside the branch in the saturation loop; both endpoints of every added edge land on `newB = newForms ++ b`, and `ord`/`b` grow monotonically. |
| `Function.update` rewriting noise in preservation proofs (need `a ≠ tNew`, `b ≠ tNew`) | M | M | Discharge `≠` side-conditions from `branchNextTime_gt` + `mem_futureOf_iff`/`mem_pastOf_iff`; close numeric goals with `omega`. Use `lean_multi_attempt` before editing. |
| Changing the `TimeOrdering` structure breaks existing membership lemmas / Saturation threading | M | M | Structure change is additive (new field with default); existing `constraints`-only lemmas should be unaffected. Phase 1 re-builds `TimeOrdering.lean` and downstream modules incrementally (`lake build Module.Name`). |
| `extractModelℤ` non-injective instants break atom lemmas | M | L | Report §5: atom lemmas survive with `f sf.label` substituted; non-injectivity only bites the out-of-scope Until/Since lemma. Re-prove only the atom properties. |
| Default-value field (`instant := fun _ => 0`) interacts badly with `@[expose] public section` / structure eta | L | M | Mirror existing `empty`/structure style; verify with a scoped `lake build` immediately after the structure edit before proceeding. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 4 | 1 |
| 3 | 3 | 2 |
| 4 | 5 | 3, 4 |

Phases within the same wave can execute in parallel.

### Phase 1: Augment `TimeOrdering` with the instant scheme [NOT STARTED]

**Goal**: Add an integer `instant` field to `TimeOrdering` and thread it through
`empty`/`addFuture`/`addPast` per Option B, keeping `TimeOrdering.lean` and its immediate
dependents compiling.

**Tasks**:
- [ ] Edit `Cslib/Logics/Temporal/Tableau/TimeOrdering.lean`: add field
      `instant : Nat → ℤ := fun _ => 0` to `structure TimeOrdering` (Encoding 1, report §4).
- [ ] Update `empty` to `{ constraints := [], instant := fun _ => 0 }`.
- [ ] Update `addFuture` to set `instant := Function.update ord.instant tNew (ord.instant t + 1)`
      and keep `constraints := (t, tNew) :: ord.constraints`.
- [ ] Update `addPast` to set `instant := Function.update ord.instant tNew (ord.instant t - 1)`
      and keep `constraints := (tNew, t) :: ord.constraints`.
- [ ] Confirm existing `constraints`-only lemmas (`addFuture_hasConstraint`, `mem_futureOf_iff`,
      `mem_pastOf_iff`, the `*_mono` lemmas, etc.) still compile; adjust any `simp [addFuture]` /
      `simp [addPast]` calls only if the new field disturbs them.
- [ ] Confirm `Function.update` is in scope (import `Mathlib.Logic.Function.Basic` if not already
      transitively available via `Cslib.Init`).

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/TimeOrdering.lean` — structure + `empty`/`addFuture`/`addPast`.

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.TimeOrdering` is green (no errors, no `sorry`).
- `lake build Cslib.Logics.Temporal.Tableau.Saturation` is green (threading through
  `temporalTableau` still type-checks; the `addFuture`/`addPast` call sites in `Rules.lean`
  take the same `(t, tNew)` arguments, so signatures are unchanged).

---

### Phase 2: Define `InstantStrict` and prove edge-by-edge preservation lemmas [NOT STARTED]

**Goal**: State `InstantStrict` and prove it is preserved from `empty` through every
`addFuture`/`addPast`, **sorry-free**. These are the corrected replacement for the false
`ordConstraints_strict`, at the operation level.

**Tasks**:
- [ ] Add `def InstantStrict (ord : TimeOrdering) : Prop := ∀ a b, (a,b) ∈ ord.constraints →
      ord.instant a < ord.instant b` in `TimeOrdering.lean`.
- [ ] Prove `InstantStrict.empty : InstantStrict .empty` (constraints empty → vacuous).
- [ ] Prove `InstantStrict.addFuture` with the freshness hypothesis that `tNew` is not an endpoint
      of any existing constraint (i.e. `tNew ∉ ord.allTimes`, expressed via
      `mem_futureOf_iff`/`mem_pastOf_iff` or a direct `∉ allTimes`): new edge `(t, tNew)` closed by
      `Function.update` at `tNew` + `omega` (`instant t < instant t + 1`); old edges unchanged
      because both endpoints `≠ tNew`.
- [ ] Prove `InstantStrict.addPast` symmetrically (`instant tNew = instant t - 1 < instant t`).
- [ ] Use `lean_multi_attempt` to settle the `Function.update` / `≠ tNew` rewrites before editing.

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/TimeOrdering.lean` — `InstantStrict` + three preservation lemmas.

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.TimeOrdering` is green.
- `lean_verify` on `InstantStrict.empty`, `InstantStrict.addFuture`, `InstantStrict.addPast`
  reports no `sorry` and no new axioms.

---

### Phase 3: Thread the invariant through the tableau run (corrected `ordConstraints` lemma) [NOT STARTED]

**Goal**: Prove the run-level corrected lemma that replaces `ordConstraints_strict`:
`temporalTableau φ = .openBranch b ord → InstantStrict ord`, **sorry-free**. This is the core
deliverable and the highest-risk phase.

**Tasks**:
- [ ] Establish the coupling invariant needed for freshness: every time mentioned in
      `ord.allTimes` is a label appearing on the branch `b` (so `tNew = branchNextTime b` is fresh
      w.r.t. `ord`). State it as a helper predicate and prove it is preserved by
      `temporalStepBranch` (both endpoints of each added edge land on `newB = newForms ++ b`).
- [ ] Prove the run-level lemma (place it in `Completeness.lean`, mirroring the location of the old
      false lemma), by induction over `temporalExpandBranches` / its inner `processNext` worklist
      and fuel, carrying `InstantStrict ord` (and the coupling invariant) as a loop invariant from
      the initial `[TimeOrdering.empty]`.
- [ ] Name it descriptively, e.g. `ordConstraints_instantStrict` (or `temporalTableau_instantStrict`),
      with statement `∀ a b, (a,b) ∈ ord.constraints → ord.instant a < ord.instant b`.
- [ ] Discharge each `addFuture`/`addPast` step using the Phase 2 preservation lemmas + the coupling
      invariant for freshness; close numeric goals with `omega`.

**Fallback (zero-debt)**: If the recursive-loop induction cannot be closed within this run, do NOT
introduce `sorry`. Instead (a) keep the Phase 2 edge-by-edge preservation lemmas as the delivered
sorry-free corrected invariant, (b) mark this phase **[BLOCKED]** in the plan with the exact goal
state reached and what is needed (e.g. a `processNext` invariant lemma), and (c) return
`status: "partial"` with `requires_user_review: true`. The documented Option A (`LinearExtension`)
is the heavier alternative if the user chooses to pursue full threading differently.

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — run-level corrected lemma.
- `Cslib/Logics/Temporal/Tableau/Saturation.lean` — (only if a coupling-invariant helper is best
  placed next to `temporalExpandBranches`).

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.Completeness` is green.
- `lean_verify` on the run-level lemma reports no `sorry` / no new axioms (if completed).
- If fallback taken: phase marked `[BLOCKED]`, no `sorry` anywhere, build still green.

---

### Phase 4: Re-key `extractModel` through `f` (`extractModelℤ`) and re-prove atom lemmas [NOT STARTED]

**Goal**: Provide `extractModelℤ : TemporalModel ℤ Atom` keyed on `ord.instant` and re-prove the
atom-level model properties sorry-free. Independent of the Phase 3 threading (depends only on the
Phase 1 structure), so it can run in parallel with Phase 2/3.

**Tasks**:
- [ ] Add `def extractModelℤ (b : TBranch Atom) (ord : TimeOrdering) : TemporalModel ℤ Atom` with
      `valuation z p := b.any fun sf => sf.sign == .pos && ord.instant sf.label == z &&
      sf.formula == .atom p` (report §5).
- [ ] Re-prove the atom-level lemmas in the ℤ-keyed setting, substituting `f sf.label`
      (`ord.instant sf.label`) for the bare Nat label: analogues of `extractModel_atom_sat_iff`,
      `extractModel_atomPos_sat`, `extractModel_bot_false`, and `extractModel_atom_neg_notSat`.
- [ ] Decide (and document inline) whether to keep the original `extractModel`/atom lemmas alongside
      the ℤ versions or replace them; preserve any still-referenced names to avoid breaking other
      modules (grep for `extractModel` consumers first).

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — `extractModelℤ` + re-keyed atom lemmas.

**Verification**:
- `lake build Cslib.Logics.Temporal.Tableau.Completeness` is green.
- `lean_verify` on the new atom lemmas reports no `sorry` / no new axioms.

---

### Phase 5: Remove the false lemma, wire order-preservation, final sorry-free verification [NOT STARTED]

**Goal**: Remove/replace the false `ordConstraints_strict` comment block, wire the
order-preservation component of `branchSat` (`D = ℤ`, `f = ord.instant`, `hf` from Phase 3) as far
as the FMP boundary allows, and confirm the whole project is green and sorry-free.

**Tasks**:
- [ ] Delete the `ordConstraints_strict` BLOCKED comment block (Completeness.lean 232–262) and
      replace its docstring with a pointer to the corrected `InstantStrict` lemma + the `D=ℤ/f=instant`
      design note (explain *why* the Nat-label order is not the semantic order).
- [ ] Update the blocked `openBranch_branchSat` sketch (Completeness.lean 327–339) to use
      `⟨ℤ, inferInstance, inferInstance, extractModelℤ b ord, ord.instant, hInst, …⟩`, where the
      order-preservation argument `hInst` comes from the Phase 3 lemma. The remaining truth-lemma
      argument stays FMP-BLOCKED — keep that obligation documented as a comment, not a `sorry`
      (i.e. the full `openBranch_branchSat` stays BLOCKED; only the order-preservation component is
      discharged and recorded).
- [ ] Confirm no other module referenced the removed lemma (grep `ordConstraints_strict`).
- [ ] Run the full CSLib verification chain and confirm zero `sorry` in the touched files via
      `lean_verify` / `grep`.

**Timing**: 1 hour

**Depends on**: 3, 4

**Files to modify**:
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` — remove false block, wire order-preservation.

**Verification**:
- `lake build` (full project) is green.
- `lake test` passes (CslibTests suite).
- `lake exe checkInitImports` passes.
- `grep -rn "sorry" Cslib/Logics/Temporal/Tableau/` returns no live `sorry` in modified files
  (only the documented FMP-BLOCKED obligations remain, as comments).

## Testing & Validation

- [ ] `lake build Cslib.Logics.Temporal.Tableau.TimeOrdering` green after Phases 1–2.
- [ ] `lake build Cslib.Logics.Temporal.Tableau.Completeness` green after Phases 3–5.
- [ ] `lake build` (full project) green after Phase 5.
- [ ] `lake test` passes.
- [ ] `lake exe checkInitImports` passes.
- [ ] **Acceptance criterion (sorry-free corrected lemma)**: the `InstantStrict` invariant — at
      minimum the edge-by-edge preservation lemmas (Phase 2), and ideally the run-level
      `temporalTableau φ = .openBranch b ord → InstantStrict ord` (Phase 3) — compiles with **no
      `sorry`, no new axioms, no vacuous definitions**, verified by `lean_verify`.
- [ ] The false `ordConstraints_strict` is removed; no module references it.
- [ ] No `sorry`/axiom introduced anywhere; FMP-blocked Until/Since obligations remain documented
      comments only.

## Artifacts & Outputs

- `specs/426_temporal_tableau_ordconstraints_redesign/plans/01_ordering-instant-redesign.md` (this plan)
- Modified `Cslib/Logics/Temporal/Tableau/TimeOrdering.lean` (instant scheme + `InstantStrict` + preservation lemmas)
- Modified `Cslib/Logics/Temporal/Tableau/Completeness.lean` (corrected run-level lemma, `extractModelℤ` + atom lemmas, false block removed, order-preservation wired)
- Possibly modified `Cslib/Logics/Temporal/Tableau/Saturation.lean` (coupling-invariant helper, if needed)
- `specs/426_temporal_tableau_ordconstraints_redesign/summaries/01_ordering-instant-redesign-summary.md` (on implementation)

## Rollback/Contingency

- All work starts from green commit `7f052834`; each phase ends at a green scoped build, enabling
  `git revert`/`git checkout` of individual phase commits.
- If Phase 1's structural change destabilizes downstream modules beyond the Tableau directory,
  revert to the additive-field-with-default form and re-verify before proceeding.
- If Phase 3 run-level threading is infeasible in scope, fall back to the Phase 2 edge-by-edge
  lemmas as the delivered sorry-free corrected invariant and mark Phase 3 `[BLOCKED]` for user
  review (zero-debt; no `sorry`). Option A (`LinearExtension`, `Mathlib.Order.Extension.Linear`)
  is the documented heavier alternative.
- No `sorry`/axiom/vacuous-definition is ever an acceptable rollback state; prefer `[BLOCKED]`.
