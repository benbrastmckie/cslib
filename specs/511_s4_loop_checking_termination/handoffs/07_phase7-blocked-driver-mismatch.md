# Task 511 Phase 7 — Dispatch 8 Handoff: [BLOCKED] with a Sharpened Goal State

## Summary

Phase 7 (the final phase) was attempted. Task 1 of the plan's checklist (the independent
Hintikka-alignment `rfl` bridge, `modalHintikkaSetS4_eq`) was already landed by a prior
dispatch; this dispatch re-verified it builds green and `lean_verify`-clean. A genuine, concrete
attempt at Task 2/3 (9-B: wire `modalStepBranchS4_worldBound` into fuel sufficiency for
`Decidable (s4Valid φ)`) surfaced a structural gap not previously documented in the plan or
prior handoffs, and Phase 7 is marked `[BLOCKED]` with that finding.

## The Finding: a driver/shadow-invariant mismatch

`s4Valid`'s `Decidable` instance must run the REAL computational driver:

```
def modalTableauS4 (φ : Proposition Atom) : ModalTableauResult Atom :=
  modalTableauGen (modalApplyOneS4 φ) φ
```

`modalApplyOneS4`'s minting guard is `blockingWorldS4` — it compares a prospective successor's
birth content against the **CURRENT LIVE** `relevantSetFinset` of every existing known world.

`S4LoopInv` and `modalStepBranchS4_worldBound` (task 511 Phases 4-6) are proven **only** for the
keyed SHADOW stepper `modalStepBranchS4Keyed`, whose guard `blockingWorldS4Keyed` compares
against the **stable, birth-frozen `keys` list** instead. This is directly visible in the step
hypothesis of the assembly theorem:

```
theorem modalStepBranchS4_preserves_S4LoopInv ...
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) : ...
```

— not `modalStepBranchS4`. The two guards are not interchangeable: `S4LoopInv.keyLowerBd` gives
only `keys ⊆ relevantSetFinset` (a subset, not equality), so a live-set freshness guarantee
(`blockingWorldS4_none_fresh`) does not imply a keys-freshness guarantee. This is exactly the
class of gap that forced Phase 5 to introduce a *second* guard (`blockingWorldS4Keyed`) in the
first place — re-encountered here from the Decidable-instance side, where it means the
world-bound guarantee is proven about a driver `modalTableauS4` does not actually run.

## A promising lead that turned out insufficient alone

While investigating, this dispatch discovered that task 515 (a concurrent/later task) already
landed a more general, rank-free top-loop lemma in `CompletenessLoop.lean`:
`modalExpandBranchesHintikka`, parametrized over an abstract `Aux : List SF → List SF →
Accessibility → Prop` (`AuxStepPreserved`/`AuxBounds`/`ModalLoopInvHintikka`), built to support
S5's decidability (`ModalLoopAuxS5w`). This postdates task 511's own research report (which only
evaluated the older, rank/`geomCap`-requiring `modalExpandBranchesGen_hintikka`) and is real,
useful groundwork for the 9-A option.

It does **not**, however, close S4 by itself: wrapping `keys` inside an existential
`Aux(b,e,acc) := ∃ keys, S4LoopInv-fields` does not avoid the mismatch above, because
`AuxStepPreserved` would still need to re-derive `keysDistinct` preservation using the REAL
(live-set) guard's contract — the same insufficient argument. The generic interface's `apply :
RuleApply Atom` is a single fixed function per call; it has no mechanism for extra per-branch
threaded state (like `keys`) to evolve across steps, only for a `Prop`-valued `Aux` to be
re-derived from `(b, e, acc)` at each point.

## What Would Close Phase 7

Either:

**(a) 9-B, sharpened**: build a bespoke S4-specific top-level driver
(`modalExpandBranchesS4Keyed`/`modalTableauS4Keyed`) directly around `modalStepBranchS4Keyed`,
with its own full `processNext`-style fuel induction (mirroring the ~700-line
`modalExpandBranchesHintikka`/`modalExpandBranchesGen_hintikka` precedent), plus
re-verification that soundness (`modalTableauS4_sound`, task 506) and the truth lemma
(`modalTruthLemmaS4`) reconnect against the keyed guard's Hintikka witnesses. This looks
plausible in principle — the keyed and unkeyed guards' non-minting arms are byte-identical, and
both guards' "blocked target already has the required content" contracts hold by construction
(`successorBirthContent`/`keyLowerBd` monotonicity) — but is unverified and is comparable in
scope to Phase 5's ~13-hour, 6-dispatch crux.

**(b) 9-A, extended**: generalize the driver framework itself (`RuleApply`/`Accessibility`, or a
new wrapper type) to support extra opaque per-branch threaded state generically, not just a
`Prop`-valued `Aux`. This is a materially larger 9-A than the plan originally scoped (which only
anticipated replacing `ModalLoopInvGen`'s rank/`geomCap` machinery, not adding threaded state),
but is the more reusable fix, and task 515's `Aux`-parametrized machinery is a partial head
start.

Either path also requires `modalTableauS4` to be repointed (or a new `modalTableauS4Keyed`
substituted and `s4Valid`'s `Decidable` instance redefined against it) — the currently-shipped
`modalTableauS4` runs the live-set-guarded `modalApplyOneS4`, not the keyed guard the
termination proof is about.

## Zero-Debt Discipline

No `sorry`, `axiom`, or vacuous placeholder was introduced at any point while investigating this.
No code was written that could not close cleanly — the entire dispatch consisted of reading
existing definitions/theorem signatures, tracing the mismatch precisely, and documenting it; no
Lean source files were edited. `lake build` green on both files in scope; `lean_verify` clean
(`propext`/`Classical.choice`/`Quot.sound` only, no `sorryAx`) on every lemma re-checked.

## Verification

- `lake build Cslib.Logics.Modal.Tableau.LoopChecking` — green, 847 jobs, no errors.
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` — green, 880 jobs, no errors.
- `grep -c '\bsorry\b'` both files: zero actual `sorry` uses (only doc-comment prose mentions).
- `lean_verify Cslib.Logic.Modal.Tableau.modalHintikkaSetS4_eq`: clean.
- `lean_verify Cslib.Logic.Modal.Tableau.modalStepBranchS4_worldBound`: clean.

## Files Modified

- `specs/511_s4_loop_checking_termination/plans/01_s4-termination-bound-decidability.md` (Phase 7
  heading `[IN PROGRESS]` → `[BLOCKED]`, checklist updated, continuation note added)
- `specs/511_s4_loop_checking_termination/summaries/01_s4-termination-bound-decidability-summary.md`
  (rewritten to reflect the final Phases 1-6 landed / Phase 7 blocked state)
- `specs/511_s4_loop_checking_termination/.orchestrator-handoff.json`

No `Cslib/` Lean source files were modified this dispatch (Phases 1-6 and the Phase 7 `rfl`
bridge were already landed sorry-free by prior dispatches).

## Recommendation

Spawn: **"abstract termination-measure interface for S4/B loop lemma (task 511 Phase 7
follow-on)"**, scoped to `CompletenessLoop.lean`/`GenericDriver.lean` (and, as the S4-consuming
side, `LoopChecking.lean`), shared with tasks 505 (B-system) and 513. Brief it with this exact
finding — survey task 515's `Aux`-parametrized `modalExpandBranchesHintikka` first, but plan for
extending it (or building the bespoke S4-local driver) to close the guard mismatch above. Do NOT
run `/spawn` from within this dispatch (out of scope per dispatch instructions); this is a
recommendation for the orchestrator/user.

Phases 1-6 of task 511 (the original task 506 Phase 8 world-bound deliverable) remain a valid,
self-contained, fully sorry-free artifact regardless of Phase 7's outcome.
