# Handoff: Task 454 — Phase 0 + Phase 1 complete, Phase 2 ready to start

## Status: [PARTIAL] — 2 of 7 phases complete (0, 1), CI green, zero new sorries/axioms

## What is DONE (committed, verified)

1. **Phase 0** (commit `3cfb2569`): Created
   `Cslib/Foundations/Logic/Metalogic/Chronicle/SinceSeedConsistency.lean` with the
   `SinceSeedInterface (F : Type*)` structure (~45 fields: formula operators, an abstract
   `Deriv : List F → F → Type*` family, derivation combinators, and the Burgess/MCS
   apparatus lemmas as statements-only), plus purely-definitional derived notions
   (`SetConsistent`, `SetMaximalConsistent`, `ClosedUnderDerivation`, `deductiveClosure`,
   `burgessR`/`burgessRSet`/`burgessRSince`/`burgessRSetSince`/`burgessR3`/
   `BurgessR3Maximal`, `gContent`, `hContent`). Verified by fully instantiating the
   interface against BOTH logics' real lemmas in throwaway scratch files (since deleted).

2. **Phase 1** (commit `d375df73`): Relocated the small `lemma27SinceSeed`/`l27s*`
   formula-operator helpers into the shared module as generic defs/theorems. **Went
   further than the plan required**: also built the FULL, verified
   `temporalSinceInterface : SinceSeedInterface (Formula Atom)` (Temporal,
   `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion/Since.lean`, right after the
   `/-! ## Phase 4: Since-Direction Mirrors -/` heading) and
   `bimodalSinceInterface (fc : FrameClass) : SinceSeedInterface (Formula Atom)`
   (Bimodal, `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion/Since.lean`,
   same location) — every field populated and building. Both `Since.lean` files' local
   `lemma27SinceSeed`/`l27sC5EventList`/`l27s_c5_event_list_mem`/`l27sB5GuardList`/
   `l27s_b5_guard_list_mem`/`l27s_c5_γ_mem`/`l27s_b5_β_mem` are now thin aliases
   delegating to the shared module (Bimodal's use `bimodalSinceInterface FrameClass.Base`
   internally since these particular helpers don't depend on `fc` at all — original
   no-`fc` call signatures preserved verbatim, zero call-site churn elsewhere in the
   file).

   Two fields NOT anticipated in the Phase-0 research sketch were added:
   `untlInjective`/`andInjective` (needed by `l27s_c5_γ_mem`/`l27s_b5_β_mem`, which rely
   on injectivity of the concrete `Formula.untl`/`Formula.and` constructors — not
   recoverable generically over an abstract `F`). Both trivially supplied by each logic.

**Full verification passed**: `lake build` (3189/3189 jobs), `lake test`,
`lake exe checkInitImports`, `lake exe lint-style`, `lake shake --add-public
--keep-implied --keep-prefix` (import list already minimized per shake's own
suggestion — dropped `Mathlib.Order.Zorn`/`Cslib.Foundations.Logic.Connectives`, added
`Mathlib.Tactic.SetLike`/`Mathlib.Data.Set.Basic`/`Aesop`), `lake lint` (zero findings
attributable to touched files), `lake exe mk_all --module` (barrel updated). Zero
sorries/axioms in any touched file (grep-verified). Both logics' downstream
`CounterexampleElimination` consumers build unchanged (Bimodal `Interface.lean`;
Temporal `RecursiveWalks.lean`/`MainElimination.lean`/`Elimination.lean`).

## What is NOT done (Phases 2-6)

The big `lemma_2_7_since_seed_consistent`/`lemma_2_8_since_seed_consistent` private
theorem bodies, and the `lemma_2_7_since`/`lemma_2_8_since` public wrapper bodies, are
**still local to each logic's `Since.lean`** — completely untouched by this dispatch.
This is the bulk of the remaining work (plan Phases 2-5, ~8 hours of the original
12-hour estimate).

## Continuation: resume at Phase 2

**Key acceleration for the next dispatch**: the hardest infrastructural piece — building
and verifying `temporalSinceInterface`/`bimodalSinceInterface fc` against real per-logic
lemmas — is ALREADY DONE. Phase 2/3 no longer need to "define the Temporal/Bimodal
instance"; they only need to port the proof BODY into a generic theorem and wire a
one-line delegation. This should make Phase 2 meaningfully faster than the plan's
2-hour estimate.

**Read first**:
- `specs/454_consolidate_chronicle_pointinsertion_bimodal_temporal/plans/01_consolidate-since-seed-interface.md`
  Phase 2 section (already annotated with this groundwork note).
- `Cslib/Foundations/Logic/Metalogic/Chronicle/SinceSeedConsistency.lean` — the full
  field list (read the whole file; ~410 lines).
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion/Since.lean` lines ~145-415 —
  the CURRENT (still-local) `lemma_2_7_since_seed_consistent` + `lemma_2_7_since` bodies
  to port (simplest reading, `fc := .Base`, used as the source of truth for the generic
  proof — Bimodal's version differs only by `fc`-threading, confirmed via full-body
  `diff` in the research report §1.3).

**Concrete next steps**:
1. In `SinceSeedConsistency.lean`, add (after the Phase-1 `l27s*` section, before
   `end Cslib.Logic.Metalogic.Chronicle`) a generic
   `theorem lemma_2_7_since_seed_consistent (I : SinceSeedInterface F) {A B C : Set F}
   (h_mcs_A : SetMaximalConsistent I A) (h_mcs_C : SetMaximalConsistent I C)
   (h_r3m : BurgessR3Maximal I A B C) (h_B_dcs : ClosedUnderDerivation I B)
   (_h_gc : gContent I A ⊆ C) (xi eta : F) (h_since : I.snce xi eta ∈ C)
   (h_xi_not_B : xi ∉ B) : SetConsistent I (lemma27SinceSeed I A B C xi eta)`, transcribing
   Temporal's body verbatim with `Formula.foo` → `I.foo` and bare lemma names → `I.fieldName`.
2. Also port the `lemma_2_7_since` WRAPPER body (not just the seed-consistency theorem)
   as a second generic theorem — it diverges 100% mechanically too (confirmed in the
   research), so per the Definition-of-Done ("both logics reduced to thin
   instantiations") it should collapse into the shared module as well, not stay an
   ~80-line per-logic body. Its remaining apparatus calls (`xu_lemma_3_2_1_until/since`,
   `burgessR_implies_burgessRSince`, `burgessRSince_implies_burgessR`, `burgessR_conj`,
   `burgessRSince_conj`, `dc_delta_B_burgessR3`, `burgessR3Maximal_extension_exists`,
   `subset_deductiveClosure`, `deductiveClosure_closed_under_derivation`,
   `cud_contains_theorems`, `set_lindenbaum_fc`/`temporal_lindenbaum`) ARE already
   interface fields (all present in `SinceSeedInterface` per Phase 0) — `set_lindenbaum_fc`
   /`temporal_lindenbaum` (Lindenbaum's lemma) is the ONE apparatus call in the wrapper
   NOT yet in the interface; check whether it needs to be added as a field before porting
   (`lindenbaum : ∀ {S}, SetConsistent I S → ∃ M, S ⊆ M ∧ SetMaximalConsistent I M`).
3. Build the shared module in isolation after adding the generic theorem(s)
   (`lake build Cslib.Foundations.Logic.Metalogic.Chronicle.SinceSeedConsistency`) —
   use `lean_goal`/`lean_multi_attempt` iteratively; this is the highest-effort step.
4. Wire Temporal's public `lemma_2_7_since` as
   `theorem lemma_2_7_since {A B C} ... := <generic theorem> temporalSinceInterface ...`
   (verify signature is byte-identical to before — external consumers depend on it).
5. Re-grep `lemma_2_7_since_seed_consistent` in Temporal's file to confirm zero
   consumers, delete the local private body (keep the public `lemma_2_7_since` name).
6. `lake build` Temporal `Since.lean` +
   `Cslib.Logics.Temporal.Metalogic.Chronicle.CounterexampleElimination.{RecursiveWalks,MainElimination,Elimination}`.
7. Mark Phase 2 `[COMPLETED]` in the plan file, commit, then proceed to Phase 3 (Bimodal
   wiring — should be fast: define `bimodalSinceInterface`-based wrapper, same pattern).

**Escalation reminder**: if the generic proof body cannot be closed without a NEW proof
obligation (would require a `sorry`), STOP, restore the local body, mark Phase 2
`[BLOCKED]` with the exact goal state, and return `status: "partial"` — do NOT introduce
a `sorry`. The local bodies in both `Since.lean` files remain fully intact and correct as
a rollback point; nothing about Phase 0/1 depends on Phase 2 succeeding.

## Files touched so far (absolute paths)

- `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Metalogic/Chronicle/SinceSeedConsistency.lean` (new)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion/Since.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion/Since.lean`
- `/home/benjamin/Projects/cslib/Cslib.lean` (barrel entry added)
- `/home/benjamin/Projects/cslib/specs/454_consolidate_chronicle_pointinsertion_bimodal_temporal/plans/01_consolidate-since-seed-interface.md`

## Commits

- `3cfb2569` task 454 phase 0
- `d375df73` task 454 phase 1

## Coordination note

Tasks 449-451 were `not_started` at research/plan time and are still not in flight in
this dispatch's git history (no `TemporalConservativity`/Chronicle churn observed).
