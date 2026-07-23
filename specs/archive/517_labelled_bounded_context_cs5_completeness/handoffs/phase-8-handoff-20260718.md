# Handoff: Task 517 Phase 8 complete — Canonical Model + Truth Lemma

## State

Phase 8 (Canonical model + truth lemma, Simpson 5.3.2/8.2.6) is **fully complete** in one
dispatch (plan estimated 2-3, explicitly allowed a partial landing). New mainline file:
`Cslib/Logics/Modal/Metalogic/Constructive/Labelled/CanonicalModel.lean`. Full CSLib CI pipeline
green; `canon_truth_lemma` sorry-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

See `summaries/18_phase8-canonical-model-truth-lemma-summary.md` for the full writeup.

## Next: Phase 9 — Frame-class match

**Goal**: discharge the frame-class conditions `cs5FC''`/`cs5FCIncest` need from
`TPrime.clModel : ClassicalModelOn TS5 H.G.X H.G.R`.

**What's already landed and ready to consume**:
- `equivalence_of_classicalModelOn_TS5` (`Context.lean`): `ClassicalModelOn TS5 D R →
  EquivalenceOn D R` — already proves the domain-relative reflexivity/symmetry/transitivity from
  clause 0. This is likely the bulk of Phase 9's first task.
- `cs5Incest`/`cs5FCIncest` live at `CS5Canonical.lean:234,255`.
- `canon_truth_lemma`/`CanonWorld` (this phase): the world type and truth lemma Phase 9's
  frame-class match needs to line up against.

**Tasks per the plan** (plans/12, Phase 9):
1. Derive the domain-relative `EquivalenceOn` on `H.G.X` (should be near-immediate given
   `equivalence_of_classicalModelOn_TS5` already exists).
2. Match the `cs5FCIncest` conjuncts against `CanonWorld`'s `≤`/`r` (need to work out precisely
   how `CanonWorld.r`'s same-context relation and `CanonWorld.le`'s persistence order interact
   with `cs5FCIncest`'s `≤`-composed clauses — this is new design work, not yet scoped in detail).
3. State non-trip of `cs5Incest_forces_symm` and `cs5TwoSidedR_iff_cs5Tail` at the point of use
   (both already landed guardrail theorems, cited in the plan's Preserved Assets table).

**Caution**: `CanonWorld`'s `≤` (`CanonWorld.le`) is NOT literally `cs5FCIncest`'s `≤` — Phase 9
needs to determine whether `CanonWorld` itself instantiates `cs5FCIncest`'s frame-condition
signature directly, or whether a further world-type adjustment (e.g. restricting to a single
fixed maximal `H` obtained via `primeLemma`, since `cs5_completeness`'s assembly in Phase 10 only
ever needs ONE canonical model, not the full class `W^𝒯` of all `TPrime` contexts) is the right
move. This was intentionally left open by Phase 8 — the `CanonWorld` type as built is general
(ranges over ALL `TPrime` contexts), matching Simpson's own `𝒦^𝒯`, but Phase 10's assembly
(`primeLemma` applied once at the top level to refute a fixed underivable `φ`) may only need the
model restricted to contexts `≥` that one base point. Flag this explicitly in Phase 9's own
`--lit` step if the frame-class match doesn't go through cleanly on the general `CanonWorld` type.

## Preserved Assets (unchanged, do not re-litigate)

- Phases 1-7 (FLO apparatus in `probes/`, `primeLemma` in mainline `PrimeLemma.lean`): unchanged.
- Phase 8 (this dispatch): `CanonicalModel.lean`, unchanged, do not redo.
