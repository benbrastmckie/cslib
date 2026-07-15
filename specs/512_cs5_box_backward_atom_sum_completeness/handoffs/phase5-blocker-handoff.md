# Phase 5 Handoff: `cs5Incest` Fails on the Canonical Model (Blocker)

## Status

Phase 5 marked `[BLOCKED]` in `plans/02_birelational-pivot.md`. Task 512's implementation
STOPS here per dispatch instructions — Phase 6 was not started.

## What happened

Phase 5's literal goal — prove `cs5Incest (@cs5CanonMreach Atom)` (the canonical model
satisfies the ≤-mediated incestuality condition) — is **mathematically false** for the
`CS5CanonSegment`/`cs5CanonMreach` world type landed in Phase 3. This was confirmed by
mechanizing a complete, sorry-free, axiom-clean counterexample rather than forcing the
(false) theorem through or leaving a `sorry`.

## Why

`boxInv` is monotone under `⊆`. `cs5Incest`'s witness `u′ ≥ u` (i.e. `u.head ⊆ u′.head`)
can never help satisfy `boxInv u′.head ⊆ w.head` if `boxInv u.head ⊄ w.head` already —
any `□C ∈ u.head` persists into `u′.head`, and `w.head` is untouched by the choice of
`u′`. So the goal collapses to plain (unmediated) symmetry of `cs5CanonMreach`, which
fails concretely: the exploding world `Ω` (head `= Set.univ`) is reachable from every
canonical world `P`, but cannot route back to any non-exploding `P` (its head is already
maximal, so the only candidate witness is itself).

## What was landed instead (in `CS5Canonical.lean`, all sorry-free, axiom-clean)

- `cs5CanonMreach_to_univ` — the exploding world is universally reachable.
- `cs5Incest_cs5CanonMreach_forces_univ` — if `cs5Incest` held, every canonical world
  would be exploding.
- `cs5_consistent_incest` — `CS5` is consistent (bot underivable), via a one-point model
  reusing Phase 4's `cs5_soundness_derivable_incest`/`cs5FCIncest` unchanged.
- `cs5Incest_cs5CanonMreach_false` — the outright contradiction.

## What is needed to unblock (two options, either needs a new planning round)

1. Restrict `CS5CanonSegment` with a hereditary invariant excluding the degenerate case
   (precedent: `CS4Segment`'s `excl`/`excl_head`, task 508).
2. Weaken `cs5Incest` to an existential/disjunctive clause handling the exploding case
   specially (precedent: `cs4FC'`'s existential weakening of blanket transitivity, task
   508).

Both require explicit human authorization (Phase 4's landed `cs5FCIncest` should not be
reworked without approval per this dispatch's hard constraints) and are themselves
~100-250 line efforts, not a Phase-5 in-flight expansion.

## Files touched

- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` (only file touched)
- `specs/512_cs5_box_backward_atom_sum_completeness/plans/02_birelational-pivot.md`
  (Phase 5 marked `[BLOCKED]` with full documentation)

## Verified untouched

- `cs5FC''` (task 509, `CKExtension.lean`) — not referenced anywhere in this dispatch.
- `cs5FCIncest`/`cs5_axiom_sound_incest`/`cs5_soundness_derivable_incest` (Phase 4) —
  reused unchanged (grep-confirmed), not redefined.
