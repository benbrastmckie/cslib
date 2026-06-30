# Implementation Plan (v2, streamlined): Task #426 — Phase 3 run-level `InstantStrict` threading

- **Task**: 426 - Redesign temporal tableau time-ordering; prove corrected ordering invariant
- **Status**: [IN PROGRESS] — phases 1, 2, 4, 5 DONE green; only phase 3 remains (was [BLOCKED])
- **Effort**: 2-4 hours (one refactor + one threading proof)
- **Dependencies**: None. **Territory**: shares `Completeness.lean` with task 427 — serialize, never parallelize (see `.memory/10-Memories/temporal-tableau-426-427-file-territory.md`).
- **Research Inputs**: reports/01_ordconstraints-redesign.md (Option B instant scheme)
- **Supersedes**: plans/01_ordering-instant-redesign.md (phases 1, 2, 4, 5 complete)
- **Type**: cslib · **Lean Intent**: true

## Already DONE (committed green, sorry-free — do NOT redo)

- **Phase 1**: `instant : Nat → ℤ` field on `TimeOrdering`; `empty` → all 0; `addFuture` → `instant tNew = instant t + 1`; `addPast` → `instant tNew = instant t - 1` (`TimeOrdering.lean`).
- **Phase 2**: `InstantStrict` def + edge-by-edge preservation lemmas for `empty`/`addFuture`/`addPast`. This is the correct sorry-free replacement for the false `ordConstraints_strict`.
- **Phase 4**: `extractModelℤ : TemporalModel ℤ Atom` keyed on `ord.instant`, with four re-proved atom lemmas.
- **Phase 5**: false `ordConstraints_strict` comment block removed; `openBranch_branchSat` sketch documents `D=ℤ/f=instant`.

`lake build` + `lake test` (9152/9152) + `lake exe checkInitImports` all green. Zero new sorries.

## The remaining blocker (Phase 3) and its root cause

**Goal**: thread the `InstantStrict` invariant through the *run-level* saturation loop so the
final extracted model is well-founded — i.e. prove that the `TimeOrdering` produced by
`temporalExpandBranches` always satisfies `InstantStrict`.

**Why it's blocked**: `processNext` is defined as a `let rec` inside a `do`-style `match` in
`Saturation.lean`. Lean 4 does **not** generate a standalone equation/recursion principle for a
`let rec` binding, so `Nat.strongInduction` / fuel induction over the worklist cannot be applied
to it. The edge-by-edge lemmas from Phase 2 are ready to be the inductive step, but there is no
induction principle to hang them on.

## Phase 3 — streamlined steps (each ends green + committed)

#### Step 3.1: Extract `processNext` to a top-level `def` [NOT STARTED]
- [ ] In `Cslib/Logics/Temporal/Tableau/Saturation.lean`, lift the inline `let rec processNext`
  out of `temporalExpandBranches` into a top-level `def processNext (…) : … := …` with the same
  body, taking the worklist/fuel and accumulators as explicit parameters.
- [ ] Rewrite `temporalExpandBranches` to call the top-level `processNext`.
- [ ] Confirm definitional equality is preserved: `lake build Cslib.Logics.Temporal.Tableau.Saturation 2>&1 | grep -E 'error|completed'` green, and any existing lemmas that unfold `temporalExpandBranches` still build.
- [ ] Commit `task 426 phase 3.1: lift processNext to top-level def (green)`.

#### Step 3.2: Carry the coupling invariant [NOT STARTED]
- [ ] State the loop invariant pairing the branch and ordering: every endpoint of every edge in
  `ord.constraints` is a label on `b`, and `tNew = branchNextTime b` is fresh w.r.t. `ord`
  (so `Function.update` side-conditions `a ≠ tNew`, `b ≠ tNew` discharge from `branchNextTime_gt`
  + `mem_futureOf_iff`/`mem_pastOf_iff`; numeric goals via `omega`).
- [ ] Prove `processNext` preserves `InstantStrict` by strong induction on its fuel/worklist
  (now possible — it has a recursion principle), using the Phase 2 edge-by-edge lemmas as the step.
- [ ] `lean_multi_attempt` before editing each tricky step; build after the lemma closes.
- [ ] Commit `task 426 phase 3.2: InstantStrict preserved through run (green, sorry-free)`.

#### Step 3.3: Wire and finalize [NOT STARTED]
- [ ] Use the run-level `InstantStrict` to discharge the order-preservation component of
  `branchSat` for the extracted `D=ℤ/f=instant` model, as far as the FMP boundary allows
  (Until/Since remain FMP-blocked — out of scope, leave documented, NO sorry).
- [ ] `lake build` full + `lake test 2>&1 | tail -5` green; `lake exe checkInitImports` pass;
  no active `sorry` introduced by 426 (427's pre-existing imp-case sorry is the only allowed one).
- [ ] Update state → completed; update summary; commit `task 426: complete (phase 3 threaded)`.

## Hard constraints
- The `processNext` lift is a refactor of core saturation code — keep it behaviour-preserving;
  build after the lift (3.1) BEFORE attempting any proof, to catch ripple in dependent lemmas early.
- If 3.2 cannot be closed after the lift, the zero-debt fallback still applies: keep 3.1's green
  refactor, mark 3.2 `[BLOCKED]`, document the exact remaining goal — never introduce `sorry` or a vacuous def.
- NEVER call `lean_diagnostic_messages`. Prefer scoped `lake build Module.Name`, piped through `grep`.
