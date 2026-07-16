# Phase 8 Handoff: R1 Scratch Probe -- GO

**Status**: Phase 8 COMPLETED. Verdict: **GO**. No production Lean touched (by design -- Phase 8
is a sanctioned gate/probe phase).

## What was probed

The plan's top risk R1: whether `modalTableauS5_sound`'s re-proof against the witness-reuse rule
`modalApplyOneS5w` is feasible within ~400 lines. The new case introduced by witness reuse is the
"reuse edge" `w → w'` to an *existing* world `w'` already carrying `⟨s, φ, w'⟩`, as opposed to
the old rule's unconditional mint of a fresh world.

## Evidence

`lean_run_code` against the real project imports (`Cslib.Logics.Modal.Tableau.S5Simplification`,
`Cslib.Logics.Modal.Tableau.FrameSoundness`) -- full transcript and target lemma saved at
`specs/515_s5_universal_rule_termination_unblock_504/probes/phase8-r1-reuse-soundness.lean`:

- The reuse case's obligation splits into `sfSat m f ⟨.pos, φ, w'⟩` (one line, replay of the
  branch's existing satisfaction witness `hb`) and `m.r (f lbl) (f w')` (one line,
  `accReachableInv_related_s5 hFC hacc hreach hlblknown hw'known`). **Both close sorry-free**,
  using only already-landed lemmas.
- The obligation is stated purely in terms of the *original* `f` (no extended `f'`), confirming
  structurally that the world-assignment is not extended in the reuse case.
- `lean_references` on `modalApplyOneS5_snd_eq` (`S5Simplification.lean:358`, not `:340-351` as
  the plan cited -- that range is the *preceding* lemma) returned 8 real consumers. None matched
  the plan's cited line numbers, which are stale (predate Phases 4-7's ~1,500 new lines in this
  file). The taxonomy and count still match exactly: `FrameSoundness.lean:1326` (the reusable
  `fresh_local` lemma) plus 7 sites split across `modalApplyOneS5_snd_eq_acc_of_not_mint_shape`,
  `modalApplyOneS5_fresh_local_local`, and three `modalStepBranchS5g_preserves_*` lemmas (all
  `S5g`-prefixed, all already scheduled for Phase 14 retirement). No blocker; only a citation
  correction for future artifacts.

## Line estimate: ~150-250 new lines (kill threshold: ~400)

Grounded in measured comparables:
- `modalStepBranchS5_preserves_satIn` (`FrameSoundness.lean:1708-2221`, ~514 lines): ~394 lines
  are the "port every shape verbatim from K" branch, untouched by the witness-reuse change.
- The two mint-shape bodies that change (diaPos ~118 lines at 1901-2019, boxNeg ~122 lines at
  2090-2212): each splits into a `none` arm (existing proof reused verbatim, ~5-10 wiring lines)
  and a `some w'` arm (new, ~30-40 lines once `RuleResultSat`/`branchSatisfiableIn` packaging is
  included, matching `modalS5BoxAll_soundIn`'s ~47-line packaging pattern). Net new: ~40-50 lines
  per case, ~80-100 lines total.
- A new `accReachableInv`-preservation lemma for `modalStepBranchGen modalApplyOneS5w` (the S5w
  analogue of the landed `modalStepBranchS5_preserves_accReachableInv`,
  `FrameSoundness.lean:1508`): ~50-100 lines, comparable to Phase 7's own preservation lemmas.
- `modalTableauS5w_sound` itself: near-zero new content, structurally identical to
  `modalTableauS5_sound` (`FrameSoundness.lean:2379-2404`, ~26 lines).

## Recommended next dispatch

Phase 9 (spec split + the one-token weakening). No pivot to fallback 2 needed.

## Files touched this dispatch

- `specs/515_s5_universal_rule_termination_unblock_504/plans/05_s5-termination-machinery.md`
  (Phase 8 heading -> `[COMPLETED]`, checklist checked off, completion note added)
- `specs/515_s5_universal_rule_termination_unblock_504/probes/phase8-r1-reuse-soundness.lean`
  (new -- probe evidence artifact)
- `specs/515_s5_universal_rule_termination_unblock_504/summaries/05_s5-termination-machinery-summary.md`
  (Phase 8 section appended)
- `specs/515_s5_universal_rule_termination_unblock_504/handoffs/08_phase8-r1-gate-go.md` (this file)
- `specs/515_s5_universal_rule_termination_unblock_504/.orchestrator-handoff.json` (updated)

No `Cslib/**` file was read-write touched beyond the `Read`/`Grep`/`lean_references` calls used to
gather evidence; no `.lean` file under `Cslib/` was edited.
