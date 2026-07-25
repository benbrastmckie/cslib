# Handoff: Task 553, Phase 8 complete, Phase 9 not started

## State

Phases 1-8 of `plans/01_s4-settled-context-scheduling.md` are complete, committed, and verified
green. Phase 8 is the empirical proof-search gate: it exercises the ordered driver's actual
proof-search behavior against the known countermodel and a broad formula sweep, as opposed to
Phase 7's mere type-checking of the copied recursion.

**Phase 8 result, stated plainly (this is the task's central empirical finding to date):**

1. **`cex` (the primary claim):** the ordered driver `modalExpandBranchesS4KeyedOrdered` does
   **NOT** close `cex`, whereas the shipped (unordered) driver `modalExpandBranchesS4Keyed`
   **does** close it. Both verdicts are machine-checked via `#guard_msgs`-checked `#eval` rows in
   `CslibTests/S4LoopGuardRegression.lean`, and independently reproduced via `lake env lean` on
   `specs/553_.../artifacts/s4probe.lean`: `KEYED (unordered) closes cex = (some true)`,
   `KEYED (ordered) closes cex = (some false)`. This is the soundness fix working, on the exact
   example that motivated this task.
2. **B/T-axiom controls:** ordered driver agrees with unordered on both -- B axiom `(some
   false)` (open, correctly not S4-valid), T axiom `(some true)` (closed, correctly S4-valid),
   under both drivers. No completeness regression on these two schemas. (Only B/T controls exist
   in the file for either driver -- no K/4 rows exist at Phase 1's baseline, so none were added
   for the ordered driver either; this mirrors the existing pattern rather than inventing new
   scope.)
3. **Exhaustive size-<=6, 2-atom sweep** (`allUpTo 2 6`, fuel 100, 8532 formulas): the
   unordered-driver leg reproduces the Phase 1 baseline exactly (1650 closed, 6882 open, 0
   fuel-exhausted). The ordered-driver leg over the SAME 8532 formulas is **verdict-for-verdict
   identical**: 1650 closed, 6882 open, 0 fuel-exhausted. `closedToOpen = 0`,
   `openToClosed = 0`. **Read this precisely**: within this sweep's size class, the reordering
   changes NOTHING -- the stale-birth-content interaction that unsoundly closes `cex` simply does
   not arise for any formula this small (`cex` itself is larger than size 6). This is an honest
   negative result at this scope, not independent confirmation of the fix -- the fix is
   confirmed by item 1 above, directly.
4. **STOP-condition check, both halves clear**: `openToClosed = 0` (no completeness regression),
   `fuelInvolved = 0` with `newFuel(0) == oldFuel(0)` (no termination regression observed at this
   sweep's scope). **The task's standing central prediction -- that narrowing the guard may break
   TERMINATION rather than merely completeness -- is NOT corroborated by this phase's evidence.**
   This does not retire the prediction: the sweep only reaches size 6, and Phases 9-14's
   soundness/completeness re-derivation (specifically whether key-distinctness survives under
   the ordered driver at the PROOF level, not just empirically) is the real test. No empirical
   counter-evidence has appeared yet, and Phase 7's termination checker already accepted the
   copied recursion unchanged.

**No regression found. Phase 8 gate PASSES. Proceed to Phase 9.**

**Landed in Phase 8**:
- `CslibTests/S4LoopGuardRegression.lean`: new ordered-driver rows for `cex` (`OPEN`), `bAxiom`
  (`OPEN`), `tAxiom` (`CLOSED`); file docstring updated so the `KNOWN-UNSOUND` inversion note no
  longer applies to the ordered driver (the unordered row itself is unchanged and still correct,
  since `modalStepBranchS4Keyed`/`modalExpandBranchesS4Keyed` are untouched until Phase 15).
- `specs/553_s4_loop_guard_soundness_reachability_restriction/artifacts/s4probe.lean`: rewritten
  to add the ordered-driver analogues (`dfsOrdered`/`tabClosesOrdered`) alongside the existing
  unordered/live drivers, plus a combined sweep (`sweepRows`) that computes both drivers' verdicts
  per formula in one pass and censuses closed-to-open / open-to-closed / fuel-involved counts.
  Task-artifact scratch file, not a repository surface.
- No `Cslib/` source files were touched this phase -- `git diff` on
  `Cslib/Logics/Modal/Tableau/LoopChecking.lean` is empty for Phase 8. Phases 1-7's declarations
  (`modalStepBranchS4Keyed`/`modalExpandBranchesS4Keyed`/`modalTableauS4Keyed` and everything
  ordered-successor) remain byte-for-byte unchanged.

Full CI pipeline green after Phase 8's commit: `lake build CslibTests.S4LoopGuardRegression`
(848 jobs, clean), `lake exe checkInitImports` (clean), `lake exe lint-style` (clean), `lake
lint` (same one pre-existing, out-of-scope error in `Temporal/Tableau/Saturation.lean`; zero new
issues), `lake shake --add-public --keep-implied --keep-prefix` (zero import changes needed for
the test file), `lake exe mk_all --module` (no update necessary -- no new files), `lake test`
(exit 0, no errors, full repo replay including the new ordered-driver rows). Repo-wide `axiom`
count unchanged at 26 (verified: `grep -rn '^axiom ' Cslib/ | wc -l`). This phase adds no Lean
proofs (only `#eval`-driven test rows and a probe-script rewrite), so the `sorry` inventory is
unaffected by this phase's own changes.

## Phase 9 scope: Propagation-Adequacy Invariant

Per the plan (`plans/01_s4-settled-context-scheduling.md`, Phase 9 section, starting line 471),
read that section directly for the exact goal, tasks, and verification criteria -- this handoff
does not restate it in full since Phase 9 is real, sized proof work, not empirical testing.

Context that carries forward from Phase 8 relevant to Phase 9's proof work:
- The escalation concern (narrowing the guard may break termination via loss of
  key-distinctness) remains formally live. Phase 6 already machine-checked that
  `modalStepBranchS4KeyedOrdered_preserves_keysDistinct` PASSES with the unordered
  `keysUpdate_preserves_keysDistinct`/`blockingWorldS4Keyed_none_fresh` consumed at their exact
  original signatures -- no weakening. Phase 8 adds empirical (not proof-level) support: no fuel
  exhaustion appeared anywhere in the size-<=6 sweep. Phases 9-14 are where this gets a real
  proof-level test via the soundness/completeness re-derivation.
- Phase 9 (propagation-adequacy invariant) is the first of the soundness re-derivation phases
  (9-14) that this Phase 8 gate was explicitly a precondition for (plan risk table, line 87:
  "Phase 8 re-runs the size-<=6 sweep ... and requires every verdict change to be closed-to-open").
  That condition is now satisfied, so Phase 9 is unblocked to proceed.

## Verification checklist for Phase 9 before committing

Follow the plan's own Phase 9 section verification criteria directly. General reminders that
apply to every remaining phase (9-15) per the escalation and phase-checkpoint protocols:
- `lean_verify` (or `#print axioms`) on every new declaration: axiom-clean
  (`propext`/`Classical.choice`/`Quot.sound` only), no `sorryAx`.
- No `sorry`, no vacuous placeholder definitions, ever -- if blocked, mark `[BLOCKED]` and report
  per the Escalation Protocol rather than routing around the obstruction.
- `modalStepBranchS4Keyed`/`modalExpandBranchesS4Keyed`/`modalTableauS4Keyed` and all of Phases
  1-8's committed declarations must remain byte-for-byte unchanged (Phase 15 is the sole
  destructive phase).
- Full CI pipeline (build, checkInitImports, lint-style, lint, shake, mk_all, test) before
  marking the phase `[COMPLETED]` and committing as `task 553 phase 9: {name}`.

## Remaining phases after 9 (for context, not this dispatch's scope)

Phases 10-13 continue the soundness re-derivation (redirect-inertness, step
preservation/soundness theorem, Hintikka invariant, top-loop Hintikka induction). Phase 14 adds
(not replaces) `modalTableauS4KeyedOrdered_complete`. Phase 15 is the sole destructive phase,
deleting the unordered stepper/driver/entry-point trio once every ordered replacement is proved.
