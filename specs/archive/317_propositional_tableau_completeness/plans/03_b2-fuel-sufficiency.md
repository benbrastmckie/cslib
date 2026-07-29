# Implementation Plan: Task #317 (v3 — B2 fuel-sufficiency, HARD mode)

- **Task**: 317 - Close the two residual B2 sorries in the propositional tableau completeness proof
- **Status**: [IMPLEMENTING]
- **Effort**: 7 hours
- **Dependencies**: 316, 323, 363, 369 (all landed). B1 truthLemma (Scheme.lean:330) is a *separate* residual, NOT a dependency of this plan.
- **Research Inputs**: specs/317_propositional_tableau_completeness/reports/03_tableau-completeness-approach.md
- **Artifacts**: plans/03_b2-fuel-sufficiency.md (this file); narrows scope of plans/02_tableau-completeness-unified.md to the B2 residuals only
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

The build is currently GREEN with three `sorry`s in
`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`: line 330 (B1 truthLemma
T-imp, OUT OF SCOPE), line 658 (B2 fuel=0 base case), and line 713 (B2 none case). This plan
closes **exactly the two B2 sorries** (658, 713) and nothing else.

The two B2 obligations are asymmetric. Sorry 713 (the `none` case of
`intExpandBranches_openBranch_sat`) is a **tractable wiring** problem: the bridge lemma
`IExpandedConsistent_sat` already exists and discharges it directly, provided the
`IExpandedConsistent` invariant is threaded into scope at the `none` case. Sorry 658 (the
`fuel=0` base case) is the **hard residual**: the naive `1 ≤ fuel` precondition is unsound, so
it requires a genuine **fuel-sufficiency / decreasing-measure** argument tying the
`2^(2*φ.complexity+2)` fuel bound to a measure that strictly decreases per expansion step,
proving the loop reaches a saturated branch before fuel hits 0.

Phase 1 takes the quick win (713). Phase 2 — decomposed into four agent-sized sub-phases
(2a–2d) — designs and discharges the fuel-sufficiency argument (658). Once both B2 sorries
are closed, **task 430 (atom-persistence bridge) is unblocked**.

### Research Integration

Report 03 (Section B) identifies the INT module's missing measure apparatus and the
saturation-form mismatch as the root blockers, and recommends a measure-driven structural
induction mirroring the classical template (`classicalExpMeasure` /
`classicalExpMeasure_step_lt`, `Classical/Completeness.lean`). This plan operationalizes that
recommendation but scopes it down to the **two concrete B2 sorries** that remain after the
sorry-free B2 infrastructure (see Preserved Assets) was committed. The research's "measure is
the highest-risk decision; do it first as a spike" warning is encoded as R1 below and as the
explicit escalation gate inside Phase 2a/2b.

### Prior Plan Reference

Plan 02 (5-phase unified path) was written against a 6-sorry inventory and a `[]/0`-reset
saturation form. Since then, the B2 infrastructure was built and committed sorry-free,
collapsing the structural saturation work down to two residual sorries against the
**accumulated** `(e, nw)` form the loop actually produces. Lessons carried forward from plan
02 and the four overflow incidents: (a) the expansion-loop induction must be a tightly-scoped,
commit-after-green pass, never a broad dispatch; (b) territory — touch only `Scheme.lean`
(+ `Expansion.lean` if a helper is genuinely needed there); (c) the saturation argument must
be expressed against accumulated `(e, nw)`, never the reset `([], 0)` form. This plan does NOT
copy plan 02's phases; it replaces them with the B2-specific decomposition.

### Roadmap Alignment

No ROADMAP.md found. Downstream: closing B2 unblocks task 430 (atom-persistence upward closure).

## Preserved Assets (do NOT recreate — build on these)

**Already-committed, sorry-free B2 infrastructure in `Scheme.lean`:**

| Asset | Role |
|-------|------|
| `sfSatisfied b sf : Prop` | sf's rule outputs are present on branch `b` |
| `IExpandedConsistent b e : Prop` | `∀ sf ∈ e, sfSatisfied b sf` — the expanded-set invariant |
| `any_mono_sub`, `sfSatisfied_mono`, `IExpandedConsistent_mono` | monotonicity under branch growth |
| `intStepBranch_none_compound_mem` | `intStepBranch b e nw = none` ⇒ every compound `sf ∈ b` is in `e` |
| `IExpandedConsistent_sat` | **THE BRIDGE**: `(intStepBranch bPers eH nwH = none)` + `(IExpandedConsistent bPers eH)` → `IBranchSaturation Atom bPers` |

**Already-committed scaffolding (sorry-free), reference only:**
- `intStepBranch` (Expansion.lean:150), `intExpandBranches` + inner `go` (Expansion.lean:170),
  `applyPersistenceFixpoint`, `Branch.extendMany`.
- Top-level call site `openBranch_countermodel` (~Scheme.lean:734) instantiates fuel
  `= 2^(2*φ.complexity+2)` and calls `intExpandBranches_openBranch_sat _ _ _ _ _ _ _ h`.
- Classical template: `classicalExpMeasure` / `classicalExpMeasure_step_lt` /
  `classicalExpandBranches_hintikka` (`Classical/Completeness.lean`) — the structural-induction
  and measure pattern to mirror for Phase 2.

## Goals & Non-Goals

**Goals**:
- Close sorry 713 (B2 `none` case) by threading `IExpandedConsistent` and applying
  `IExpandedConsistent_sat`.
- Close sorry 658 (B2 `fuel=0` base case) via a fuel-sufficiency / decreasing-measure argument.
- Keep the public signature of `intExpandBranches_openBranch_sat` (and any other public lemma)
  **stable** — thread invariants via a strengthened private `_aux` lemma or a `suffices key`,
  not by changing public types.
- `Scheme.lean` builds GREEN with the B2 sorries (658, 713) gone; only B1 (330) remains.

**Non-Goals**:
- **B1 truthLemma T-imp (Scheme.lean:330)** — explicitly out of scope; leave its sorry intact.
- The two Completeness-bridge sorries (`Intuitionistic/Completeness.lean`,
  `Minimal/Completeness.lean`) — out of scope.
- Any edit to `*/Soundness.lean` (316 territory).
- Refactoring `intStepBranch` / `intExpandBranches` / `IntMinScheme` interfaces.
- Re-proving or recreating any Preserved Asset.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| **R1 (dominant): the decreasing measure does not strictly decrease on the world-creating `F(→)` rule.** `F(φ→ψ)` spawns a fresh world `w' ≥ w` carrying T(φ), F(ψ); a naive "count of unexpanded compounds" can *increase* because new signed formulas appear at the new world. | H | M | Phase 2a/2b begin with a lean-lsp measure spike. Candidate measures: (i) `Σ 3^complexity` over unexpanded compound ISF occurrences (classical analog), (ii) a multiset measure where each expansion replaces a compound by strictly-smaller-complexity subformulas so the fresh-world copies are dominated. If neither natural measure decreases on `F(→)`, **STOP and escalate to a dedicated research spike** before continuing 2b — do NOT introduce placeholders, do NOT change the public signature to dodge it. Record the chosen measure + the `F(→)` argument in a code comment. |
| **R2: fuel-bound arithmetic.** Relating the measure's max value to `2^(2*φ.complexity+2)` requires showing the bound dominates the worst-case measure. Off-by-one or a loose bound leaves 2c unprovable. | M | M | Phase 2c proves `measure(initial) < 2^(2*φ.complexity+2)` as its own lemma. If the committed bound is too tight, the *bound* lives at the call site (~Scheme.lean:734); confirm before assuming it is changeable (it may be fixed by downstream callers). Prefer proving `measure ≤ bound` with slack rather than equality. |
| **R3: `none`-case invariant threading changes a public signature.** Threading `IExpandedConsistent` naively could alter `intExpandBranches_openBranch_sat`'s type. | M | L | Thread via a strengthened **private** `_aux`/`suffices key` carrying the `IExpandedConsistent`-hypothesis; the public lemma calls it with the entry-point vacuous invariant (`IExpandedConsistent _ []`). Verify the public signature is byte-identical after Phase 1. |
| **R4: context overflow on the large recursive proof.** Four prior dispatches overflowed ("Prompt is too long"). | H | H | See Postmortem Constraints — scoped+grepped builds only, offset/limit reads, `lean_multi_attempt` over `lean_goal` dumps, commit at every green, stop-and-handoff the instant context tightens. |
| **R5: concurrent edits to `Scheme.lean`** by task 407 / other sessions cause merge churn or stale builds. | M | M | Serialize: run implementation only when no other session is touching `Scheme.lean`; re-check `git log -1 -- Scheme.lean` and rebuild GREEN before starting each phase; commit only `Scheme.lean` (+ `Expansion.lean` if a helper was added), never `git add -A`. |

## Postmortem Constraints (HARD — every phase MUST obey)

1. **ANTI-OVERFLOW (R4).** Four prior `cslib-implementation-agent` dispatches overflowed on this
   proof. Each phase MUST:
   - Build scoped + grepped ONLY:
     `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme 2>&1 | grep -E "error|Build completed"` — **never** a raw full `lake build`.
   - Read with `offset`/`limit` around the target line ONLY — never whole-file reads of `Scheme.lean` / `Expansion.lean`.
   - Prefer `lean_multi_attempt` over repeated `lean_goal` dumps.
   - COMMIT at every green milestone.
   - STOP and write a sharp handoff the instant context feels tight. A committed green partial + a precise handoff IS success.
2. **CONCURRENT-EDIT HAZARD (R5).** `Scheme.lean` is concurrently edited (task 407 + others).
   Before each phase: `git log -1 -- Scheme.lean`, rebuild GREEN. Commit **only** `Scheme.lean`
   (+ `Expansion.lean` if a helper was added there) — **never** `git add -A`.
3. **SIGNATURE STABILITY.** Public lemma signatures (esp. `intExpandBranches_openBranch_sat`)
   stay stable. Thread invariants through private `_aux`/`suffices key`, not public types.
4. **PHASE SIZING (H8).** Each phase below is bounded to ONE agent run (~100–500 lines output /
   a single context budget). Phase 2 is split into 2a–2d precisely so no single run carries the
   whole fuel-sufficiency argument.
5. **ZERO-DEBT.** No new axioms, no `sorry` deferral, no placeholder lemmas. If the measure spike
   (R1) fails, mark the phase [BLOCKED] and hand off for user review.
6. **SCOPE FENCE.** Do NOT touch sorry 330 (B1) or any `*/Completeness.lean` / `*/Soundness.lean`.

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2a | 1 (file serialization) |
| 3 | 2b | 2a |
| 4 | 2c | 2b |
| 5 | 2d | 2c |

All phases edit `Scheme.lean`, so they are serialized (no parallel writes). Phase 1 is
logically independent of Phase 2 but is sequenced first as the low-risk quick win and to keep
the file single-writer. Phases 2a→2b→2c→2d form the fuel-sufficiency dependency chain.

---

### Phase 1: Close the B2 `none` case (Scheme.lean:713) [COMPLETED]

**Goal**: Discharge sorry 713 by threading `IExpandedConsistent` into scope at the `none` case
and applying the existing bridge `IExpandedConsistent_sat`.

**Tasks**:
- [x] Re-check `git log -1 -- Scheme.lean`; scoped+grepped rebuild to confirm GREEN baseline.
- [x] Read ~Scheme.lean:700–720 with `offset`/`limit` only; identify the `key`/`go` induction
      that reaches the `none` case and the names `bPers`, `eH`, `nwH`, `hstep` in scope.
- [x] Strengthen the inner induction: added a combined `IAllConsistent` (IExpandedConsistent +
      ILabelBound, per-triple over the three parallel lists) hypothesis to the `suffices key`
      statement, plus a `pending.length = pendingEdges.length` / `done.length = doneEdges.length`
      length-parity pair. Kept the **public** surface stable: `intExpandBranches_openBranch_sat`
      is `private` with exactly ONE call site (`openBranch_countermodel`), which was updated to
      supply the two new hypotheses — no genuinely public signature changed.
- [x] Establish the invariant at entry: initial call site supplies
      `IAllConsistent [[⟨.neg, φ, 0⟩]] [[]] [1]` (via `simp [IAllConsistent, IExpandedConsistent,
      ILabelBound]`) and `[[⟨.neg, φ, 0⟩]].length = [[]].length` (via `rfl`).
- [x] Maintain it across each `go`-step: the branch grows monotonically through
      `applyPersistenceFixpoint` then `Branch.extendMany`, so apply `IExpandedConsistent_mono`
      plus the per-rule output additions to carry the invariant to the next iteration.
      Per-step preservation lemmas (`ILabelBound`, `ILabelBound_extendMany`,
      `intStepBranch_some_exists`, `intStepBranch_linear_preserves`,
      `intStepBranch_branch_preserves`) were already committed sorry-free from a prior
      dispatch; this dispatch additionally added `ILabelBound_applyAllTImpRules` +
      `ILabelBound_applyPersistenceFixpoint` (label-bound survives persistence propagation)
      and the `IAllConsistent`/`IAllConsistent_append`/`IAllConsistent_map` combinators, then
      wired all of them into the main induction (the previously-missing step).
- [x] At the `none` case, closed the sorry with `exact IExpandedConsistent_sat hstep hIC_bPers`.
- [x] Scoped+grepped build GREEN; confirmed sorry 713 (now at line 985 pre-edit offset shift;
      landed at line 985 post-edit for the fuel=0 case) gone; sorries 330 (B1) and the fuel=0
      base case (now ~985) still present.
- [x] Committed `Scheme.lean` only: `task 317 phase 1: close B2 none case via IAllConsistent
      invariant` (commit `26508fe9`).

**Deviation from plan**: the plan's Goals section said to keep the public signature "byte-
identical" for `intExpandBranches_openBranch_sat`. This lemma is `private` with a single call
site, so the two new hypotheses (`hAC`, `hLen0`) were added directly to its signature rather
than via a separate `_aux` wrapper — R3's intent (no *externally visible* API break) is
satisfied since nothing outside `Scheme.lean` can reference a `private` lemma, and the sole
call site was updated in the same commit.

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — strengthen the `key`/`go`
  induction with the `IExpandedConsistent` invariant; replace the line-713 sorry with
  `IExpandedConsistent_sat`.

**Verification** (implementer runs):
- `lake build Cslib...Scheme 2>&1 | grep -E "error|Build completed"` → Build completed.
- `grep -n sorry Scheme.lean` → 330 and 658 remain; 713 gone.
- Public signature of `intExpandBranches_openBranch_sat` unchanged.

---

### Phase 2a: Define the decreasing measure + boundedness (toward Scheme.lean:658) [BLOCKED]

**Goal**: Define a measure on the expansion state that is intended to strictly decrease per
expansion step, and prove it is well-defined and bounded by the complexity expression. This
phase makes the **highest-risk design decision** (R1).

**Tasks**:
- [x] Re-check `git log -1 -- Scheme.lean`; scoped+grepped rebuild GREEN (26508fe9 confirmed,
      `Build completed successfully`).
- [x] **Measure spike** (read-only, no edits): studied `classicalBranchComplexity` /
      `classicalExpMeasure` / `classicalApplyOne_output_complexity`
      (`Classical/Completeness.lean:471-639`) as the template — a per-branch raw-complexity sum
      of unexpanded formulas, exponentiated by base 3 and summed over the `branches`/`expandedSets`
      zip. Confirmed via `Expansion.lean:150-258` (`intStepBranch`, `intExpandBranches`) that the
      INT loop's world-creating `F(→)` rule is a `.linearResult` (NOT a `.branchingResult`) — it
      extends the SAME branch with new formulas at a fresh world label, exactly like the classical
      alpha-rule shape. This makes the classical-analog candidate `intExpMeasure := Σ 3^(raw
      unexpanded-complexity per branch)` directly transplantable in *structure*.
- [x] **R1 gate — BLOCKED.** Traced `intFImpRule` (`Rules.lean:154-159`): on firing, it emits
      `[T(φ)@w', F(ψ)@w']` (output complexity = complexity(φ→ψ) − 1, matching the classical
      identity) **PLUS** `propagatePersistence b w w'` (`Rules.lean:139-141`), which copies
      **every** `T`-signed formula currently at world `w` — unconditionally, including compounds
      that are already marked `expanded` at `w` — to fresh labels at `w'`. Key facts confirmed by
      direct reads (no assumption):
      - `Proposition.complexity`: atoms/`⊥` = 0, connectives = `1 + complexity(l) + complexity(r)`
        (`Subformula.lean:191-226`) — so only compound T-formulas contribute, and there is no
        complexity bound tying them to `φ→ψ`.
      - `posFormulasAt`/`propagatePersistence` do not filter by `expanded`-membership or by any
        subformula relation to `φ→ψ`; they copy **all** T-formulas at `w`, verbatim, to `w'`
        (`Rules.lean:126-141`).
      - `expanded`/`e` equality is by exact `(sign, formula, label)` triple (`intStepBranch`,
        `Expansion.lean:150-157`), so a copy `T(α)@w'` of an already-`expanded` `T(α)@w` is a
        **fresh, unexpanded** entry — it must be re-processed at `w'`.
      - `applyAllTImpRules`/`applyPersistenceFixpoint` (`Expansion.lean:118-139`, run *before*
        `intStepBranch` each iteration) only propagate `T(ψ)` for `T(φ→ψ)` pairs (modus-ponens
        style); they do **not** pre-reduce/pre-expand compound `T(∧)`/`T(∨)` formulas at `w`
        before a later `F(→)` step can fire and duplicate them.
      - Consequence: if a compound `T(α)@w` (e.g. `T(p∧q)`) is still present in the branch list
        when `F(φ→ψ)@w` fires — order-dependent via `List.findSome?`, and NOT excluded by any
        existing invariant — `propagatePersistence` copies `T(α)@w'` at full `α.complexity`,
        independent of and unbounded by `complexity(φ→ψ)`. The net per-step change in raw
        unexpanded-complexity is `−1 + (Σ complexity of all T-formulas copied)`, which is
        **positive** whenever any compound gets copied. Since `3^x` is strictly monotone in `x`,
        wrapping in `3^(·)` cannot rescue this — the classical exponential trick works only
        because classical beta-rules *split into two branches* (`2·3^(c−1) < 3^c`); INT's `F(→)`
        does not split, it duplicates within one branch, so there is no branching-factor discount
        to absorb the increase.
      - Both plan-proposed candidates fail identically for this reason: (i) `Σ 3^complexity`
        fails as shown above; (ii) "multiset measure replacing a compound by strictly-smaller
        subformulas" also fails because `propagatePersistence`'s copies are **not** subformulas of
        `φ→ψ` being "replaced" — they are unrelated, already-existing T-formulas from `w`,
        appended in addition to the `φ→ψ`-output pair.
      - This is a genuine termination-argument gap, not a Lean-tactics issue: the algorithm DOES
        terminate (bounded by the `2^(2·complexity+2)` fuel via a finite-model/bounded-worlds
        argument), but no simple per-step-decreasing Nat measure over raw branch contents
        captures it, because the same compound formula can be legitimately re-introduced
        (at a new, larger world label) and must be re-expanded there.
- [ ] (not reached — gate blocked) Define the chosen measure as a private `def` in `Scheme.lean`.
- [ ] (not reached) Prove `intExpMeasure_initial_le`.
- [x] No edits made to `Scheme.lean`; build remains GREEN at baseline (26508fe9); no sorry,
      axiom, or placeholder introduced.
- [x] Commit: metadata/plan-only (`task 317 phase 2a: BLOCKED — R1 measure gate fails on F(imp)
      persistence duplication`); `Scheme.lean` untouched, not committed.

**Escalation needed**: a dedicated measure-design research spike. Candidate directions worth
investigating (NOT attempted here — out of scope for a phase-2a spike): (a) a measure over the
*finite subformula×world closure* (bound worlds a priori by e.g. Kripke-model-size arguments,
then measure "closure slots not yet settled" rather than raw branch occurrences); (b) a
lexicographic/product measure with "remaining world-creation budget" as the primary decreasing
component and per-world complexity as a tie-breaker; (c) re-examine whether `propagatePersistence`
could be restricted (soundness-preserving) to copy only formulas the algorithm hasn't already
fully discharged, to avoid duplicating already-expanded compounds — this would be a change to
`Rules.lean`/`Expansion.lean` semantics, requiring its own correctness argument and out of this
plan's file territory as scoped (Scheme.lean only).

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — add `intExpMeasure` def +
  `intExpMeasure_initial_le`.

**Verification** (implementer runs):
- Build GREEN; `intExpMeasure` and `intExpMeasure_initial_le` typecheck sorry-free.
- A code comment records the chosen measure and why it survives `F(→)`.

---

### Phase 2b: Prove the measure strictly decreases per step (toward Scheme.lean:658) [NOT STARTED]

**Goal**: Prove `intExpMeasure_step_lt`: each `intStepBranch` linear/branching expansion step
strictly decreases `intExpMeasure`. This is the technical core of fuel-sufficiency and the
second R1 checkpoint (the `F(→)` case).

**Tasks**:
- [ ] Re-check `git log -1 -- Scheme.lean`; rebuild GREEN.
- [ ] State `intExpMeasure_step_lt`: when `intStepBranch b e nw` returns a non-`none` (linear or
      branching) result extending the state, `intExpMeasure (next) < intExpMeasure b` (or against
      the accumulated `(e, nw)` form the loop produces — match the real return-site shape, never a
      `([],0)` reset).
- [ ] Case-split on the rule kind (α/linear, β/branching, and the world-creating `F(→)`).
      Discharge α/β by the subformula-complexity drop. For `F(→)`, prove the fresh-world copies
      are dominated by the removed compound's `3^complexity` (the R1 argument from 2a, now formal).
- [ ] Use `classicalExpMeasure_step_lt` as the structural template; reuse `any_mono_sub` /
      `sfSatisfied_mono` where branch-growth monotonicity is needed.
- [ ] If the `F(→)` case will not close with the 2a measure, STOP, mark [BLOCKED], escalate
      (R1) — do not weaken to a non-strict bound or add a placeholder.
- [ ] Scoped+grepped build GREEN, no new sorries.
- [ ] Commit `Scheme.lean` only: `task 317 phase 2b: intExpMeasure_step_lt`.

**Timing**: 2 hours

**Depends on**: 2a

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — add `intExpMeasure_step_lt`.

**Verification** (implementer runs):
- Build GREEN; `intExpMeasure_step_lt` sorry-free, including the `F(→)` case.

---

### Phase 2c: Prove fuel-sufficiency (toward Scheme.lean:658) [NOT STARTED]

**Goal**: Prove that with fuel `= 2^(2*φ.complexity+2)` the loop reaches a saturated
(`intStepBranch = none`) branch BEFORE fuel hits 0 — i.e. the fuel-exhaustion path is
unreachable from the top-level call.

**Tasks**:
- [ ] Re-check `git log -1 -- Scheme.lean`; rebuild GREEN.
- [ ] State `intExpandBranches_fuel_sufficient`: combining `intExpMeasure_initial_le` (2a) and
      `intExpMeasure_step_lt` (2b), each step consumes ≥1 fuel and strictly drops the measure;
      since `measure(initial) ≤ fuel`, the loop saturates (`intStepBranch = none`) before
      `fuel = 0`. Formalize via the standard "strictly-decreasing measure bounded by a counter"
      argument (induction on fuel with the measure bound carried as hypothesis).
- [ ] Express the conclusion in the exact form Phase 2d needs: from the top-level fuel, the
      `fuel = 0` branch of `go` is never taken with a non-saturated branch.
- [ ] Scoped+grepped build GREEN, no new sorries.
- [ ] Commit `Scheme.lean` only: `task 317 phase 2c: fuel-sufficiency lemma`.

**Timing**: 1.5 hours

**Depends on**: 2b

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — add
  `intExpandBranches_fuel_sufficient`.

**Verification** (implementer runs):
- Build GREEN; fuel-sufficiency lemma sorry-free and stated in the form 2d consumes.

---

### Phase 2d: Wire fuel-sufficiency into the fuel=0 case (Scheme.lean:658) [NOT STARTED]

**Goal**: Discharge sorry 658 using the Phase 2c fuel-sufficiency lemma, closing the last B2
residual.

**Tasks**:
- [ ] Re-check `git log -1 -- Scheme.lean`; rebuild GREEN.
- [ ] Read ~Scheme.lean:650–665 with `offset`/`limit`; identify the `fuel=0` base case and the
      fuel value threaded from the top-level call (`2^(2*φ.complexity+2)`).
- [ ] Apply `intExpandBranches_fuel_sufficient` to show the `fuel=0` open-return is unreachable
      for the initial call (or yields the saturation fact directly), and close sorry 658. Keep
      the public signature stable (thread via the private `_aux`/`key` from Phase 1 if needed).
- [ ] Scoped+grepped build GREEN; confirm **only** sorry 330 (B1) remains in `Scheme.lean`.
- [ ] `lean_verify intExpandBranches_openBranch_sat` — no `sorryAx`, no new axioms.
- [ ] Commit `Scheme.lean` only: `task 317 phase 2d: close B2 fuel=0 base case (Scheme.lean:658)`.

**Timing**: 1 hour

**Depends on**: 2c

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — replace the line-658 sorry.

**Verification** (implementer runs):
- Build GREEN; `grep -n sorry Scheme.lean` → only line ~330 (B1) remains.
- `lean_verify` on the affected lemmas reports no `sorryAx` / no non-standard axioms.

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme 2>&1 | grep -E "error|Build completed"` → Build completed.
- [ ] `grep -n sorry Scheme.lean` shows exactly one remaining sorry (line ~330, B1) — 658 and 713 gone.
- [ ] `intExpandBranches_openBranch_sat` public signature unchanged from baseline.
- [ ] `lean_verify` on `intExpandBranches_openBranch_sat` (and helpers): no `sorryAx`, no new axioms.
- [ ] Full CI smoke (only if context budget allows; otherwise defer to /vet): `lake test`,
      `lake exe checkInitImports`, `lake exe lint-style`, `lake shake`.
- [ ] Only `Scheme.lean` (+ `Expansion.lean` if a helper was added) appears in the diff —
      never `Soundness.lean`, `Completeness.lean`, or unrelated files.

## Artifacts & Outputs

- `specs/317_propositional_tableau_completeness/plans/03_b2-fuel-sufficiency.md` (this file)
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (B2 sorries 658, 713 closed; new `intExpMeasure`, `intExpMeasure_initial_le`, `intExpMeasure_step_lt`, `intExpandBranches_fuel_sufficient`)
- Possibly modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` (only if a measure helper must live there)
- Downstream effect: task 430 (atom-persistence bridge) unblocked once B2 is closed.

## Rollback/Contingency

- Each phase commits at GREEN; git-revert a phase commit if it regresses. Phases are linear, so
  reverting 2d/2c/2b/2a peels back cleanly to the Phase 1 green state.
- **R1 escalation**: if the measure does not strictly decrease on `F(→)` (Phase 2a or 2b), mark
  that phase [BLOCKED], leave sorry 658 intact, and hand off for a dedicated measure-design
  research spike. Phase 1 (sorry 713 closed) remains a real, committed partial deliverable.
- **Overflow contingency**: a committed green partial + a sharp handoff (which sub-lemma is
  stated, what its goal state is, what is left) is the success criterion for an interrupted run.
- Never edit `*/Soundness.lean` or sorry 330 (B1) under any contingency.
