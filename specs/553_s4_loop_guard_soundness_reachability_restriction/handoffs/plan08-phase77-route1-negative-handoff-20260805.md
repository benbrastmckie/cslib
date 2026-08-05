# Continuation Handoff: Plan 08, Phase 7.7 route-1 search — NEGATIVE RESULT (BLOCKED)

- **Plan**: `plans/08_reformulated-s4-redirect-sound-inv.md`
- **Date**: 2026-08-05
- **Dispatch scope**: route 1 ONLY — search for an already-existing invariant that bounds
  `outDeg` at a recorded-successor world, or otherwise rules out `outDeg acc w' ≠ 0` for a
  successor reached via a later 4-rule propagation. Weakening conjunct (d) (route 2) was
  explicitly out of scope.
- **Outcome**: route 1 does NOT close. No Lean was written. Phase 7.7 is marked `[BLOCKED]` in
  the plan file. The full search record (seven invariants/mechanisms examined, what each says,
  why each fails to apply) is in the plan's `#### Phase 7.7 Progress Record (second dispatch —
  route 1 search, NEGATIVE RESULT)` subsection — read that in full; it is the authoritative
  record, not repeated verbatim here.

## What was searched and why each failed

1. `S4LoopInv.outDegEq` — purely numerical (`outDeg = count of minting-shaped e-members`), no
   saturation content for box-positive/diamond-negative formulas.
2. `S4LoopInv.accKnown` / `accTargetsKnown` — a freshness/membership fact, not an outDeg bound.
3. `modalNonMintCandidates` / settled-context scheduling — provably unavailable AT a
   primary-scan firing step: the firing formula is itself drawn from `modalNonMintCandidates`,
   so the list is non-empty by construction at the moment this rule fires. This is not merely
   the phase's own docstring caveat; it follows directly from `modalNonMintCandidates`'s
   definition (`LoopChecking.lean:1205`) and `modalStepBranchS4KeyedOrdered`'s traversal order
   (`:1439`).
4. `successorBirthContent` (`LoopChecking.lean:525`) — a MINT-TIME SNAPSHOT of the parent's
   box-positive content, never updated afterward. This is the structural reason no snapshot-based
   invariant can close this gap: new box-positive content arriving at a parent after a child was
   minted is exactly the scenario the 4-rule step under discussion handles, and nothing
   constrains the child's `outDeg` at that later point.
5. `modalS4Saturated` — whole-branch saturation, same unavailability argument as item 3.
6. Reachability-restriction machinery — the only reachability-restriction content in
   `LoopChecking.lean` is the Phase 9-11 prerequisite (not yet landed); `S4RedirectSoundInv`
   itself is documented as having "No reachability restriction" (`LoopChecking.lean:640`).
7. `S4KeyedHintikkaInv` — `hintikkaInv` is vacuous at box/diamond shapes; the witness fields
   concern the opposite sign/shape pair (mint-shaped, not box-positive/diamond-negative).

A targeted grep for a per-world settledness notion distinct from the whole-branch
`modalNonMintCandidates` notion (`worldSettled`, `perWorldSettled`, "settled at") returned zero
hits.

## What is needed to unblock (recorded as a user decision, not made here)

- **Option (i)**: design and prove a genuinely new per-world invariant tracking box-positive/
  diamond-negative saturation at successor worlds under the driver's actual processing order.
  Substantial new semantic content; not attempted in this dispatch (out of scope).
- **Option (ii)**: weaken conjunct (d) of `S4RedirectSoundInv` for non-mint-shaped formulas at
  already-minted successor worlds. This is route 2, explicitly prohibited for this dispatch; it
  requires re-verification against every already-landed arm (Phases 7.2, 7.3, 7.5, 7.6) and is a
  user design decision per the task's standing kill-criteria discipline.

## Verification performed this dispatch

- No Lean files were modified — only the plan file (`plans/08_reformulated-s4-redirect-sound-
  inv.md`) was edited (Phase 7.7 heading marker + new Progress Record subsection).
- Sorry census (repo's canonical two-grep code-position form, restricted to `Modal/Tableau/`)
  confirmed unchanged at exactly 1 (`FrameSoundness.lean:1251`).
- No build was needed since no `.lean` file changed; this is consistent with the task's own
  discipline that a read-only investigation dispatch does not require a fresh `lake build`.

## Next continuation step

1. Read the plan's `#### Phase 7.7 Progress Record (second dispatch — route 1 search, NEGATIVE
   RESULT)` subsection in full.
2. This is a legitimate stopping point for autonomous orchestration: Phase 7.7 needs a **user
   design decision** between options (i) and (ii) above before any further Lean can be written
   for it. Do not attempt route 2 (weakening conjunct (d)) autonomously.
3. Phase 7.8 (the dispatcher) remains blocked until Phase 7.7 closes.
