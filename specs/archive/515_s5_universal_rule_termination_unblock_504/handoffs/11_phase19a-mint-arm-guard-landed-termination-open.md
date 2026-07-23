# Handoff 11: Phase 19a mint-arm guard landed; termination re-derivation still open

**Task**: 515 - s5_universal_rule_termination_unblock_504
**Plan**: plans/07_s5-termination-machinery.md (v6)
**Phase**: 19a (`Guarded mint arm + termination bound re-derivation`)
**Commit landed this dispatch**: `56a84d07` (`task 515 phase 19a.1: land root-aware mint-arm guard
in modalApplyOneFive`)

## What landed

The Route (a) root-aware mint-arm guard (`reports/08_mint-arm-reuse-route-decision.md`) is now
installed in `Cslib/Logics/Modal/Tableau/FiveSimplification.lean`:

- New `witnessWorldFive` (a Five-local refinement of `witnessWorldS5`) excludes root world `0` from
  witness candidacy in its search.
- `modalApplyOneFive`'s two mint arms (`T(◇φ)@w`, `F(□φ)@w`) additionally check `sf.label == 0`:
  when the trigger is root, mint FRESH unconditionally (never consult the witness search); otherwise
  consult `witnessWorldFive` as before. Both branches fall through to `modalApplyOneFiveProp` on a
  miss -- **never** to `.notApplicable`.
- Two new case-split helper lemmas, `modalApplyOneFive_diaPos_eq_or_reuse` /
  `_boxNeg_eq_or_reuse`, replace the old `cases hw : witnessWorldS5 .. with | none | some w'`
  pattern used throughout the file. Every downstream consumer of that old pattern
  (`modalApplyOneFive_fresh_local`, `_branchingLength`, `_persistentFresh`,
  `_outputsSubsetUniverse`, `_diaPosWitness'`/`_boxNegWitness'`, `_agree_or_reuse`) was rewritten
  against the two new helpers and re-verified.
- `modalApplyOneFive_specCore` re-verified unconditionally (it is a `where`-record built from the
  above sub-lemmas; it typechecks once they do -- confirmed by the full project build).

This closes both unsound sub-cases from `handoffs/10_phase19-mint-arm-reuse-soundness-gap.md`
(root-as-witness, root-as-trigger) at the **rule definition and its structural corollaries** level.

**Verification performed** (all green, this dispatch, re-run directly since the dispatching agent
stalled mid-verification on an infra timeout, not a logic failure):
- `lake build` (full project, 777/777 jobs) -- green.
- `lake exe checkInitImports` -- exit 0.
- `lake exe lint-style Cslib.Logics.Modal.Tableau.FiveSimplification` -- clean, no output.
- `lake lint --builtin-lint Cslib.Logics.Modal.Tableau.FiveSimplification` -- triggers a full-repo
  scan; zero new warnings attributable to this file beyond one **pre-existing, untouched**
  `flexible`-tactic info at line 510 (inside `modalApplyOneFiveProp_snd_eq`, outside every diff
  hunk); the only *error* in the whole scan is the known `PrimeExclusion.lean` baseline
  (non-regression per plan guardrails).
- `lake shake --add-public --keep-implied --keep-prefix` -- no import-removal suggestion for
  `FiveSimplification.lean` (the import swap from `S5Simplification` to `GenericDriver` +
  `Mathlib.Data.Prod.Basic` + `Mathlib.Data.Nat.Basic` is exactly what the file now needs).
- `lake test` -- exit 0, full `CslibTests/` suite green.
- Axiom check via `lake env lean` + `#print axioms` on `witnessWorldFive`, `witnessWorldFive_mem`,
  `modalApplyOneFive_diaPos_eq_or_reuse`, `modalApplyOneFive_boxNeg_eq_or_reuse`,
  `modalApplyOneFive`, `modalApplyOneFive_specCore`: all report only
  `[propext, Classical.choice, Quot.sound]` (or a subset) -- **no `sorryAx`, no new axiom**.
- `grep -n "sorry\|admit"` on the file: zero hits.

## What is still open (Phase 19a, second task)

**The termination-bound re-derivation was NOT attempted this dispatch.** The plan's own Phase 19a
description explicitly sanctions this split: "if the guarded mint-arm rule ALONE lands green and
sorry-free (task 1) but the termination re-derivation (task 2) cannot be closed this dispatch, that
is a legitimate, valuable partial." The KILL budget for this dispatch was consumed re-verifying the
guard's downstream consumers carefully (a genuine multi-lemma rewrite, not a one-line patch).

**Important scoping correction discovered while re-verifying**: `modalApplyOneFive_specCore`'s
`outputsSubsetUniverse` field takes the world-bound fact as a raw hypothesis parameter
(`hW : modalMaxWorld b < modalWorldBound φ0`) supplied by the caller -- it does **not** itself
derive `hW` from `S5wWorldInv`/`modalMaxWorld_lt_worldBound_of_S5w`, and no site in
`FiveSimplification.lean` currently discharges `hW` via that chain. So the specCore
re-verification landed this dispatch is **unconditional** on the termination re-derivation; the
re-derivation remains necessary work, but for whatever call site eventually maintains `S5wWorldInv`
(or its source-split analogue) across the fuel induction in Phase 19b, not for anything already
landed.

**Next step (Phase 19a, remaining task)**: state and prove a source-split family of lemmas,
additive in `FiveSimplification.lean`, that do NOT edit any of the shared `S5Simplification.lean`
declarations (`mintTags`, `usedTags`, `usedTags_mono`, `S5wTagInv`, `S5wWorldInv`,
`modalMaxWorld_lt_worldBound_of_S5w` -- the S5 chain still consumes these verbatim):

1. A Five-local analogue of `witnessWorldS5_none_not_mem_usedTags` against `witnessWorldFive`,
   accounting for the new root-trigger-always-fresh branch (when `sf.label = 0`, the mint always
   fires regardless of `witnessWorldFive`'s result, so the "no witness -> tag unused" argument needs
   an extra case for "root trigger, tag possibly already used by a *non-root* mint, minting again
   under the root source-class").
2. A source-split version of `usedTags`/`S5wTagInv` distinguishing root-class mints from non-root
   mints (e.g. two `Finset (Sign × Proposition Atom)` trackers, or a single `Finset ((Sign ×
   Proposition Atom) × Bool)` keyed by source-class), each individually bounded by `mintTags φ₀`.
3. A source-split `S5wWorldInv`/`modalMaxWorld_lt_worldBound_of_S5w` analogue chaining to
   `modalMaxWorld b ≤ 2 * (mintTags φ₀).card ≤ 2 * modalOps φ₀` (or tighter), i.e. linear as the
   plan requires.

**No `lean_goal` state exists to record** -- no proof attempt was made on this sub-task; the
starting point is a blank declaration, not a stuck tactic.

**Do not** re-attempt the mint-arm guard (landed, `56a84d07`) or any of the five Route-1
building-block lemmas (`modalApplyOneFiveProp_knownWorlds_step`, `modalApplyOneFive_agree_or_reuse`,
`modalStepBranchFive_preserves_accReachableInv`, `FiveSoundInv`, `modalFiveBoxAll_soundIn`,
`modalFiveDiaNegAll_soundIn`) -- all still valid, landed, green, and reusable.

## Orchestration note

The agent originally dispatched for this phase stalled at the infra level (stream watchdog: "no
progress for 600s") while mid-way through its own CI re-verification loop, immediately after
writing `Full project builds cleanly with the minimized import` and proposing to re-run
`lake shake`/`checkInitImports`/`lint-style`. Its uncommitted edit to `FiveSimplification.lean` was
inspected directly, confirmed sorry-free and green by an independent re-run of the full CI
pipeline (see above), and committed as `56a84d07`. This was an infrastructure failure, not a logic
or soundness failure -- the guard design and its downstream rewrites were correct on inspection.

## Resume point for the next dispatch

1. Read this handoff, `reports/08_mint-arm-reuse-route-decision.md`, and plan v6's Phase 19a
   section (the "RE-DERIVE the tag-injection termination chain" checklist item, now annotated
   `[ ]` with a BLOCKER note) before writing any code.
2. Work in `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` only, additive lemmas, sub-milestone
   commits (`task 515 phase 19a.2: ...`, `.3`, etc.), each independently `lake build`-verified and
   sorry-free before committing.
3. Do not touch `S5Simplification.lean`'s shared S5w declarations. If truly unavoidable, stop and
   escalate rather than edit them.
4. Once the source-split bound lands, Phase 19a is `[COMPLETED]` and Phase 19b (`modalTableauFive_sound`
   bespoke assembly) can begin.
