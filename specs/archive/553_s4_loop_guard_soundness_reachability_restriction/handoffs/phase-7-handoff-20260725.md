# Handoff: Task 553, Phase 6 complete, Phase 7 not started

## State

Phases 1-6 of `plans/01_s4-settled-context-scheduling.md` are complete, committed, and verified
green. Phase 6 (`S4LoopInv` preservation and the fuel-sufficiency chain against the ordered
stepper) required ordered analogues of TEN separate per-field sub-lemmas, TWO proof-internal
auxiliaries, and TWO additional prerequisite auxiliaries not named in the plan text, landed
across thirteen individually-committed dispatches (`task 553 phase 6: {name}` commits). The
escalation-trigger sub-lemma (`keysDistinct`, attempted first) PASSED with no weakening of
`keysUpdate_preserves_keysDistinct` -- the plan's central claim (reordering only changes timing,
never producing a duplicate key) is now machine-checked, not merely assumed.

**Landed in Phase 6** (all in `Cslib/Logics/Modal/Tableau/LoopChecking.lean`):
- `modalStepBranchS4KeyedOrdered_branch_superset` / `_keys_subset` (two prerequisite auxiliaries)
- `modalStepBranchS4KeyedOrdered_preserves_{keysDistinct, keyLowerBd, keysInUniverse, keysTotal,
  eNodup, keysWorldsKnown, outDegEq, accFresh, accKnown, worldsContiguousS4, eClosure,
  bClosure}` (ten field sub-lemmas plus two proof-internal auxiliaries)
- `modalStepBranchS4KeyedOrdered_preserves_S4LoopInv` (the final wrapper)

Full CI pipeline green after Phase 6's final commit: whole-project `lake build` (3256/3256),
`lake exe checkInitImports`, `lake exe lint-style`, `lake lint` (one pre-existing, out-of-scope
error in `Temporal/Tableau/Saturation.lean`; zero issues in `LoopChecking.lean`), `lake shake`
(zero import changes needed), `lake test` (9250/9250, including
`CslibTests.S4LoopGuardRegression`). Repo-wide `sorry` count unchanged at 5. `axiom` count
unchanged at 26 (`grep -rn '^axiom ' Cslib/`). `modalStepBranchS4Keyed` and everything from
Phases 1-5 remain byte-for-byte unchanged.

**Line numbers have shifted substantially again** from Phase 6's own additions (~1500 lines).
Re-grep before editing; current locations of Phase 7's targets as of this commit:
- `modalExpandBranchesS4Keyed` (def): line 6780
- `modalTableauS4Keyed` (def): line 6844 -- its docstring explains the Phase 11 `keys := [(0,
  ∅)]` correction (an empty `keys` list violates `S4LoopInv.keysTotal`); Phase 7's entry point
  must seed `keys` the same way, not `keys := []`
- `modalExpMeasure_entry_le_fuelS4`: line 7530 (confirmed in Phase 6 to apply verbatim to the
  ordered driver -- it is stated purely over `modalUniverseS4 φ₀`/`modalFuelS4 φ₀`, independent
  of traversal)
- `modalStepBranchS4KeyedOrdered` (def): line 1107
- `modalStepBranchS4KeyedOrdered_preserves_S4LoopInv`: search for this name directly; located
  immediately before the `/-! ## Keyed S4 Driver (Bespoke, Path (b)) -/` section header that
  `modalExpandBranchesS4Keyed`/`modalTableauS4Keyed` themselves sit under

## Two Lean elaboration lessons from Phases 4-6 (read before writing Phase 7 code)

1. **`rcases`/`cases h : e with ...` auto-substitutes occurrences of `e` in the GOAL, but NEVER
   in other hypotheses.** If a hypothesis's type needs updating too, `rw [h] at hyp` explicitly.
2. **A `let (a,b) := f x; body` pattern-match compiles to direct `.1`/`.2` PROJECTIONS when `f`
   is an ABSTRACT parameter, but to a full `match` when `f` is CONCRETE at the definition site.**
   `modalStepBranchS4KeyedBody`/`modalStepBranchS4KeyedOrdered` call `modalApplyOneS4Keyed`
   directly (concrete), so any proof about them that destructures a `let (result, newAcc) := ...`
   needs the `rcases hpair : f x with ⟨a, b⟩; rw [hpair] at hyp` idiom, not `.1`-based
   projections. This is unlikely to matter for Phase 7 itself (which defines NEW declarations
   rather than proving new lemmas about existing ones), but will matter again for Phase 8's
   empirical gate and Phases 9-13's soundness/completeness re-derivation.

## Phase 7 scope: Ordered Driver and Entry Point

Per the plan (`plans/01_s4-settled-context-scheduling.md`, Phase 7 section), this phase is
comparatively small (plan estimate: 2 hours) relative to Phase 6:

1. **`modalExpandBranchesS4KeyedOrdered`**: structural copy of `modalExpandBranchesS4Keyed`
   (line 6780) -- same `processNext` worklist shape, same `keys` threading via `keyss` -- with
   `modalStepBranchS4KeyedOrdered` substituted for `modalStepBranchS4Keyed` at the single call
   site inside `processNext`'s expanded-branch arm. Termination is Phase 5's own concern
   (`modalExpMeasure_step_lt_S4KeyedOrdered`), not a new obligation Phase 7 needs to re-derive --
   the `processNext` recursion structure (recursing on `fuel'` via the outer `match fuel with |
   fuel' + 1 => ...`) is identical to the existing driver's, so Lean's own termination checker
   should accept the copy exactly as it accepts the original.
2. **`modalTableauS4KeyedOrdered φ`**: entry point mirroring `modalTableauS4Keyed` (line 6844)
   exactly -- SAME `keys := [(0, ∅)]` seeding (do NOT use `keys := []`; see the Phase 11
   correction note at that definition, still directly relevant here), SAME initial branch
   `[F(φ)@0]`, SAME fuel `modalFuelS4 φ`.
3. **Docstrings**: both should name `modalExpandBranchesS4Keyed`/`modalTableauS4Keyed` as their
   predecessors and flag Phase 15 as the eventual retirement point for the unordered pair (per
   this task's own plan -- Phase 15 deletes `modalStepBranchS4Keyed`,
   `modalExpandBranchesS4Keyed`, `modalTableauS4Keyed`, `modalTableauS4Keyed_complete` and their
   stepper-specific support lemmas, each with a proved ordered replacement by then).

This phase does NOT touch `modalStepBranchS4Keyed`, `modalExpandBranchesS4Keyed`, or
`modalTableauS4Keyed` themselves (all remain byte-for-byte unchanged pending Phase 15's
destructive retirement). It also does not require any NEW proof obligations about `S4LoopInv`
or the termination measure -- both are already fully closed by Phases 5-6 for
`modalStepBranchS4KeyedOrdered`'s single-step behavior; Phase 7 only needs Lean's own
structural/well-founded recursion checker to accept the copied `processNext` loop, which it
should since the recursion shape is unchanged from the original.

## Verification checklist for Phase 7 before committing

- `lake build Cslib.Logics.Modal.Tableau.LoopChecking` succeeds, including the termination
  obligation for the new fuel loop (this is the phase's own stated verification criterion --
  if the termination checker rejects the copied `processNext` recursion for any reason, that is
  worth flagging explicitly rather than working around with `termination_by`/`decreasing_by`
  hacks not present in the original).
- `lean_verify` on both new declarations: only `propext`/`Classical.choice`/`Quot.sound` in the
  axiom list (these are `def`s, not `theorem`s, so this mainly guards against accidentally
  introducing a `sorry`-backed placeholder rather than checking a proof).
- `git grep -c '^\s*sorry\s*$' -- 'Cslib'` still reads exactly 5.
- Confirm `modalStepBranchS4Keyed`/`modalExpandBranchesS4Keyed`/`modalTableauS4Keyed` and
  everything from Phases 1-6 still compile unchanged (a full `lake build
  Cslib.Logics.Modal.Tableau.LoopChecking` covers this).
- Mark `### Phase 7: ...` `[COMPLETED]` in the plan file, commit as
  `task 553 phase 7: ordered driver and entry point`.

## Remaining phases after 7 (for context, not this dispatch's scope)

Phase 8 is an "Empirical Gate" (counterexample must not close) -- worth reading before Phase 9,
since it likely exercises `modalTableauS4KeyedOrdered` against
`CslibTests/S4LoopGuardRegression.lean`'s corpus directly. Phases 9-13 re-derive
soundness/completeness against the ordered driver via settled-context scheduling. Phase 14 adds
(not replaces) `modalTableauS4KeyedOrdered_complete`. Phase 15 is the sole destructive phase,
deleting the unordered stepper/driver/entry-point trio once every ordered replacement is proved.
