# Phase 3 Summary: DECISION GATE B — the Redirect Forward-Cone Transfer (BLOCKED)

- **Task**: 553 - s4_loop_guard_soundness_reachability_restriction
- **Plan**: `plans/04_subtractive-blocking-red-channel.md` (v4), Phase 3
- **Phase status**: `[BLOCKED]`
- **Verdict**: **FAIL** — route (3) does not survive Decision Gate B

## What was done

1. **Landed the two free transfers** (the certain part), as near-transcriptions of
   `modalStepBranchS4Keyed_blocked_witness_mem`'s proof (`LoopChecking.lean:9055` at dispatch
   start):
   - `blockedRedirect_unwrapped_boxPos_mem` (`LoopChecking.lean:9060-9090`): from
     `hkL : keyLowerBd`-shaped and `hblock : blockingWorldS4Keyed φ₀ b keys s φ src = some
     wBlock`, for every `χ` with `(pos, χ) ∈ signedSubfmls φ₀` and `⟨.pos, .box χ, src⟩ ∈ b`,
     concludes the **unwrapped** `⟨.pos, χ, wBlock⟩ ∈ b`. Condition (c), measured 0/24,314.
   - `blockedRedirect_unwrapped_diaNeg_mem`: the dual, condition (e), 0/24,314.
   - Both sorry-free, `lean_verify` reports only `{propext, Classical.choice, Quot.sound}`,
     scoped `lake build Cslib.Logics.Modal.Tableau.LoopChecking` clean. Committed at
     `task 553 phase 3.1`.
2. **Attempted the cone extension** as a standalone, driver-independent lemma over abstract
   `(b, acc, red, keys)` hypotheses, generalizing the induction to carry the *wrapped*
   `⟨.pos, .box χ, w⟩ ∈ b` fact forward (so it could feed the existing `hintikkaS4_box_pos_step`
   bridge across further `acc`-edges), and granting the most generous plausible additional
   hypothesis, `hredValid` (every `red` entry reflects a genuine guard decision). The induction
   got stuck immediately past the first further hop: `ih` demands the wrapped fact at the new
   point, but the free transfer (even re-invoked under `hredValid`) only ever produces the
   *unwrapped* fact. `exact`/`assumption`/`aesop` all fail on the resulting goal — confirmed via
   `lean_multi_attempt`, not merely asserted. This is a genuine mathematical dead end (asserting
   an unwrapped-to-wrapped bridge would be unsound in S4), not a proof-search gap.
3. **Reverted the probe attempt** before commit — no `sorry` was ever committed to the tree, per
   the gate exception in the dispatch contract.
4. Recorded the full verdict, including the exact `lean_goal` state, under
   `#### Phase 3 Verdict` in the plan file, and marked the Phase 3 heading `[BLOCKED]`.

## Why outcome (iii), not (ii)

`keyLowerBd` is definitionally incapable of ever producing a *wrapped* branch fact — it only
recovers `Finset (Sign × Proposition Atom)` membership, i.e. unwrapped signed-formula
membership, from `successorBirthContent`'s box-context-transfer branch. No invariant expressible
purely over `(keys, red)` bookkeeping can close this gap without either (a) adding the redirect
edge to `acc` — the single defect shared by all three prior failed routes, forbidden by the
Postmortem Constraints — or (b) inventing a wholly new persistence mechanism with no basis in
the current guard/key/red apparatus. Neither is a "nameable additional invariant on recorded
redirects" in the sense outcome (ii) contemplates.

## Consequence

Per the Overview's kill table and Phase 3's kill/branch criterion, **route (3) is dead as
planned.** Phases 4-12 are not dispatched (the plan explicitly states they are "not scaffolded
on a positive verdict"). Escalating to the user.

## Plan Deviations

None beyond what the plan itself anticipated (the abstract-lemma attempt and its revert are
exactly the "attempt the proof, record explicitly" task as specified; the `hredValid` hypothesis
was an ad hoc strengthening tried during the attempt, not committed to the tree).

## Files touched

- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — two new sorry-free lemmas
  (`blockedRedirect_unwrapped_boxPos_mem`, `blockedRedirect_unwrapped_diaNeg_mem`); no other
  change (the cone-extension probe was written and then removed in the same dispatch, leaving no
  diff against the phase-3.1 commit).
- `specs/553_s4_loop_guard_soundness_reachability_restriction/plans/04_subtractive-blocking-red-channel.md`
  — Phase 3 checklist checked off, heading → `[BLOCKED]`, `#### Phase 3 Verdict` added.
- This summary.

## Sorry inventory

Unchanged from Phase 2: exactly one, `FrameSoundness.lean:1244`, pre-existing, untouched.
