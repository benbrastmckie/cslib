# Handoff: Task 553, Phase 7 complete, Phase 8 not started

## State

Phases 1-7 of `plans/01_s4-settled-context-scheduling.md` are complete, committed, and verified
green. Phase 7 defined the ordered driver and entry point as structural copies of the unordered
pair, substituting `modalStepBranchS4KeyedOrdered` at the single `processNext` call site. Lean's
termination checker accepted the copied `fuel'` recursion with no `termination_by`/`decreasing_by`
workaround, confirming Phase 5's termination measure lemma alone suffices for the ordered driver.

**Landed in Phase 7** (both in `Cslib/Logics/Modal/Tableau/LoopChecking.lean`):
- `modalExpandBranchesS4KeyedOrdered` (def, line 6872)
- `modalTableauS4KeyedOrdered` (def, line 6933) -- seeds `keys := [(0, ∅)]` per the Phase 11
  correction, NOT `keys := []`

Full CI pipeline green after Phase 7's commit: whole-project `lake build` (3256/3256, confirms
`FrameSoundness.lean`/`FrameCompleteness.lean` still build), `lake exe checkInitImports` (clean),
`lake exe lint-style` (clean), `lake lint` (one pre-existing, out-of-scope error in
`Temporal/Tableau/Saturation.lean`; zero issues in `LoopChecking.lean`), `lake shake` (zero import
changes needed for `LoopChecking.lean`), `lake test` (9250/9250, including
`CslibTests.S4LoopGuardRegression`). Repo-wide `sorry` count unchanged at 5. `axiom` count
unchanged at 26. `modalStepBranchS4Keyed`/`modalExpandBranchesS4Keyed`/`modalTableauS4Keyed` and
everything from Phases 1-6 remain byte-for-byte unchanged.

**ESCALATION STATUS**: still live, not yet triggered. The task's standing prediction is that
narrowing the guard may break TERMINATION rather than merely completeness. Phase 7's
`lake build` succeeding on the copied `processNext` recursion (accepted verbatim, no workaround)
is evidence AGAINST a termination gap at the driver-wiring level, but this is not yet the
empirical test — Phase 8 below is the first point where the reordering's actual PROOF-SEARCH
behavior (not just its type-checking) is exercised against the known countermodel and a broad
formula sweep. If Phase 8 finds a verdict regression (anything OPEN-to-CLOSED, i.e. a
completeness loss, or `cex` still closing, i.e. the soundness fix failing), STOP and report it as
a machine-checked finding — do not weaken the test to make it pass.

## Phase 8 scope: Empirical Gate — Counterexample Must Not Close

Per the plan (`plans/01_s4-settled-context-scheduling.md`, Phase 8 section, lines 433-465):

1. **Add regression rows** to `CslibTests/S4LoopGuardRegression.lean` for
   `modalExpandBranchesS4KeyedOrdered` on `cex` (defined at line 104; initial branch
   `cexInitBranch` line 107, initial keys `cexInitKeys` line 112) at fuel 400, asserting `OPEN`
   (i.e. `s4Verdict (...) = "OPEN"`, mirroring the existing `#eval`/`/-- info: ... -/` pattern at
   lines 121-134). This is the primary empirical claim: the ordered driver does NOT close the
   known unsound countermodel that the unordered driver (line 123's `KNOWN-UNSOUND` row) does
   close.
2. **Flip the `KNOWN-UNSOUND` documentation**: the file docstring (lines 59-63, 115-119) currently
   frames the old driver's `CLOSED` verdict on `cex` as a temporary, documented defect. Since
   `modalStepBranchS4Keyed`/`modalExpandBranchesS4Keyed` themselves are NOT touched or retired
   until Phase 15, KEEP the existing `KNOWN-UNSOUND` row as-is (it still correctly documents the
   old driver's behavior), but update the docstring prose so it's clear the inversion/defect no
   longer applies to the new ordered driver -- i.e. add a note that
   `modalExpandBranchesS4KeyedOrdered` is the fixed, sound-on-this-example successor.
3. **B/T/K/4-axiom controls**: add ordered-driver rows for `bAxiom` (line 144, expect `OPEN` --
   not S4-valid) and `tAxiom` (line 147, expect `CLOSED` -- S4-valid), mirroring the existing
   unordered-driver control rows at lines 149-156. The plan also names K- and 4-axiom controls;
   grep the file for any existing K/4 rows beyond B/T before assuming only two controls exist (the
   file may have grown since this handoff was written). All controls must produce the SAME
   verdict under the ordered driver as under the unordered driver -- reordering must not change
   completeness on valid/invalid axiom schemas.
4. **Exhaustive sweep**: `specs/553_s4_loop_guard_soundness_reachability_restriction/artifacts/
   s4probe.lean` already exists (confirmed present) -- read it first to understand its current
   shape (likely built against `modalExpandBranchesS4Keyed`/size-<=6 formula enumeration). Adapt
   it to call `modalExpandBranchesS4KeyedOrdered` instead, re-run, and record the verdict-change
   census against the plan's stated pre-change baseline: **8532 formulas: 1650 closed, 6882 open,
   0 fuel-exhausted**. Compare old-driver vs. new-driver verdict per formula. Every verdict change
   must be closed-to-open (a soundness fix). A single open-to-closed change is a COMPLETENESS
   REGRESSION and blocks the phase -- do not weaken this criterion; report it as a finding if it
   occurs, per the Escalation Protocol (mark phase `[BLOCKED]`, document what was tried, do not
   use `sorry` or vacuous placeholders to route around it).
5. **Record the sweep numbers** in the phase's completion note (same style as Phase 6/7's
   completion notes already in the plan file) once done.

Also NOTE (from the Phase 7 handoff, still relevant): `modalStepBranchS4KeyedBody`/
`modalStepBranchS4KeyedOrdered`/their driver call `modalApplyOneS4Keyed` directly (concrete
call site), so any proof or `#eval` context that destructures returned pair/tuple values follows
direct pattern-match/projection semantics as normal -- this note from Phase 7 was about PROOF
`let`-destructuring idioms, not `#eval` usage, so it is unlikely to matter for Phase 8's
`#eval`-based regression rows, but keep it in mind if Phase 8 needs any new lemma (it shouldn't,
per the plan -- this phase is empirical/test-only, no new theorem obligations).

## Verification checklist for Phase 8 before committing

- `lake test` passes with the new ordered-driver rows (this is the phase's stated verification
  criterion). `CslibTests/S4LoopGuardRegression.lean` specifically: `lake build
  CslibTests.S4LoopGuardRegression` or the relevant `lake test` invocation.
- `git grep -c '^\s*sorry\s*$' -- 'Cslib'` still reads exactly 5 (this phase adds no Lean proofs,
  only `#eval`-driven test rows and a probe script update, so this should be trivially unchanged
  -- confirm anyway).
- Sweep census recorded in the plan file's Phase 8 section, with exact counts.
- If ANY verdict regression (open-to-closed) is found: STOP, mark `[BLOCKED]`, do not proceed to
  Phase 9, and report the finding explicitly -- this is the task's central risk and a genuine
  refutation here is a valid, valuable deliverable.
- If the sweep is clean (only closed-to-open changes, `cex` opens under the ordered driver, all
  axiom controls agree): mark `### Phase 8: ...` `[COMPLETED]` in the plan file, commit as
  `task 553 phase 8: empirical gate`.

## Remaining phases after 8 (for context, not this dispatch's scope)

Phases 9-13 re-derive soundness/completeness against the ordered driver via settled-context
scheduling (propagation-adequacy invariant, redirect-inertness, step preservation/soundness
theorem, Hintikka invariant, top-loop Hintikka induction). Phase 14 adds (not replaces)
`modalTableauS4KeyedOrdered_complete`. Phase 15 is the sole destructive phase, deleting the
unordered stepper/driver/entry-point trio once every ordered replacement is proved.
