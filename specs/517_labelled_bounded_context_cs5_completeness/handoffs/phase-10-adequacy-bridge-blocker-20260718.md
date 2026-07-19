# Task 517 — Phase 10 BLOCKED: the missing Hilbert↔labelled "Adequacy" bridge

**Session context**: autonomous orchestrator dispatch, resuming from the Phase 9 handoff
(`phases_completed=9, phases_total=11, next_phase=10`). This dispatch attempted Phase 10
(`cs5_completeness` assembly) and Phase 11 (bookkeeping) per
`plans/12_wellfounded-zorn-oldlabel-reconstruction.md`.

## Outcome

**Phase 10 is [BLOCKED]. No Lean files were edited this dispatch** — the blocker was identified
during scoping/research, before any `Cslib/` edit, so there is no partial/half-applied proof to
roll back. Phase 11 was not attempted (it `Depends on: 10` per the plan's own dependency table).

**Zero-debt status unaffected**: no `sorry`, no new `axiom`, no vacuous definition was introduced.
`Cslib/` is exactly as it was at the end of Phase 9 (commit `5909c893`), plus this dispatch's plan
file annotation (Phase 10 heading `[BLOCKED]` + inline blocker writeup) and this handoff.

## The blocker, in one paragraph

Phase 10's task list treats `cs5_completeness`'s proof as "compose Phases 7-9." It is not. The
theorem's target is `CKValidFC cs5FCIncest φ → Derivable CS5ModalAxiom φ`, where `Derivable` is
the **Hilbert-style** axiomatic system (`DerivationTree`/`Derivable`,
`Cslib/Logics/Modal/Metalogic/DerivationTree.lean:134,201`). Phases 7-9 are entirely internal to
the **labelled** system (`NIK`/`Deriv`, `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/
Deduction.lean:240`) or purely semantic (`CKForces`/`CKValidFC`). To run the standard
contrapositive completeness argument — assume `¬ Derivable CS5ModalAxiom φ`, build a countermodel
via `primeLemma` — the dispatch needs to seed `primeLemma` with `¬ Deriv 𝒯_S5 G₀.G Γ₀ (x₀ ∶ φ)` for
some base labelled context, which requires the **converse** direction: `NIKTheorem 𝒯_S5 φ →
Derivable CS5ModalAxiom φ` (used contrapositively). This is a genuinely new theorem — a
translation from graph-labelled, multi-world natural-deduction proofs into single-formula
Hilbert-style proofs — not a corollary of anything landed so far.

## Why this is not a same-dispatch gap-fill

This exact theorem is Simpson's **Chapter 6 Adequacy Theorem**. It has independent history *within
this same task*, under an earlier plan decomposition:

- `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/{Syntax,Deduction,Context}.lean`'s own
  module docstrings all explicitly carve it out as future work: *"the adequacy gate's
  prerequisite -- `Adequacy.lean` (the adequacy bridge, developed separately)."* That file does
  not exist yet.
- `specs/517_labelled_bounded_context_cs5_completeness/handoffs/00_RESUME-HERE.md` (an earlier
  plan iteration, `plans/02_decomposed-track-a-b-c.md`'s "Track C") identifies this same bridge as
  **"THE TRUE CRUX, HIGH risk"**. Four sub-phases landed sorry-free in `probes/
  lemma612-scaffold.lean` / `probes/track-c-c1-tele-conj.lean` (C1: `Tele`/`Conj`; C2: formula
  6.7; C3: formula 6.8; C4: `LTree`/`star`/`prune`/`fullSubtree` + the unfolding identity). **C5
  (`pathSpine` + its commutation with `addChild`) was never started**, and C6-C8 (the truth-lemma
  cases consuming C5) were never reached.
- `specs/state.json`'s task-517 entry records the same finding from the team-research round:
  *"Named blocking obligation: CS5 |- FS (entailed by the target, ~25% target false). **Do NOT
  dispatch C5.**"* — i.e. a prior orchestration cycle deliberately deferred C5 pending resolution
  of a decision gate (`CS5 ⊢ FS`, since resolved TRUE as `cs5_fs` in `probes/
  fs-derivation-gate.lean`, per `00_RESUME-HERE.md`'s "Phase 19" note — but `cs5_fs` itself is
  *not yet transcribed into `Cslib/`*, and resolving the decision gate does not by itself supply
  C5-C8).

Plan 12 (v5) superseded that Track A/B/C decomposition with the FLO/well-founded reconstruction
(Phases 1-6) and "carried over" Phases 7-11 from plan 11 (v4) "largely unchanged." Neither v4 nor
v5's Phase 10 text re-derives whether the Ch.6 Adequacy bridge is still required for the final
assembly — it is, and nothing in Phases 1-9 built it (Phase 7 transcribes `primeLemma`, Phase 8
builds the labelled canonical model + truth lemma, Phase 9 matches the frame class; none of the
three touches `DerivationTree`/`Derivable`).

## What was checked and ruled out (not shortcuts)

1. **Full source search** for any existing `NIK ↔ DerivationTree`/`Derivable` bridge anywhere
   under `Cslib/Logics/Modal/` — none exists.
2. **The Segment/MCS canonical-model route** (`SegmentLindenbaum.lean`, which supplies
   `CKValidFC`-completeness for `CK`/`CT`/`CS4` without any labelled system) cannot substitute:
   its own module docstring states *"This is false for `CS5`"* — task 517's labelled framework
   exists specifically because that route hits the box-backward wall
   (`cs5_symmetric_tail_box_gap`/`cs5Incest_forces_symm`/`cs5TwoSidedR_iff_cs5Tail`, tasks
   509/512). Task 512's own parallel attempt at a birelational canonical model
   (`CS5Canonical.lean`'s `cs5CanonSeg`/`CS5CanonSegment`) is also incomplete for the same
   structural reason and is listed `abandoned` in plan 12's Dependencies.
3. **This task's own "cofinite-from-one" toolkit** (`NIK.relabelFresh`/`NIK.oldLabelTransport`,
   which closed Phase 8's box-backward case and Phase 5/6's "old label" sorries without the Ch.6
   apparatus) does not generalize here: that trick transports *one NIK-derivation across labels,
   staying entirely inside `NIK`*. The missing step for Phase 10 is a different problem in kind —
   translating a graph-labelled, multi-world derivation into a *single unlabelled Hilbert
   formula* — and even a `Γ = []`-seeded `NIKTheorem` derivation recurses into non-empty,
   multi-label sub-contexts via `boxI`/`diaE`, so the general internalization problem is
   unavoidable.

## What is needed to unblock

A dedicated follow-up plan (new phases on this task, or a new spawned task) to build
`Adequacy.lean`:

1. Resume `probes/lemma612-scaffold.lean`'s Track C at **C5**: `pathSpine` (the whole-path
   recursion with pruning built in) and its commutation lemma with `Context.addChild`/graph
   extension. Reuse `prune`/`fullSubtree`/`star_unfold_imp1`/`star_unfold_imp2` from the already
   sorry-free C4.
2. **C6-C8**: the truth-lemma-shaped induction cases that consume `pathSpine` to complete the
   general translation `NIK 𝒯 G Γ (x ∶ A) → Derivable-relative-to-internalized-Γ A` (see the plan
   file's Track C table, `plans/02_decomposed-track-a-b-c.md`, for the exact C1-C8 breakdown and
   risk ratings — that breakdown remains the right shape for this sub-project even though plan 12
   supersedes plans 01/02's overall route).
3. Specialize the general result to `NIKTheorem 𝒯_S5 φ → Derivable CS5ModalAxiom φ` (the `Γ = []`,
   trivial-graph instance Phase 10 actually needs) and re-attempt the contrapositive assembly.
4. This is HIGH-risk, multi-dispatch work by this task's own prior estimate (four dispatches
   reached only C1-C4; C5 was explicitly deferred, not merely unstarted by chance).

## Explicitly NOT done, and why that is correct here

- **No `sorry`/`axiom`/vacuous placeholder was introduced** for `cs5_completeness` or any
  supporting lemma — prohibited unconditionally by `lean4.md`/`cslib.md`/the plan's own zero-debt
  invariant, and specifically flagged in the plan's Postmortem Constraints.
- **`cs5_completeness`'s target was not weakened** (e.g. to `NIKTheorem 𝒯_S5 φ →` instead of
  `Derivable CS5ModalAxiom φ →`) without user sign-off — that would silently narrow the task's own
  "Definition of done" and is exactly the kind of scope substitution `plan-compliance.md`
  prohibits on `.lean` files without first raising a blocker (this document is that blocker).
- **Phase 11 was not attempted.** Its tasks (transcribe `cs5_fs`, fix `fischer-servi-probe.lean`'s
  stale docstring, rewrite `state.json`'s `blockers` field, record the literature-briefing
  resolution note) are largely independent of Phase 10's Lean content, but the plan states
  `Depends on: 10`; per plan-compliance.md this dispatch did not silently reorder the plan's
  sequence. A future dispatch or the user may choose to run Phase 11's bookkeeping items
  independently — flagging this as an option, not doing it unilaterally.

## Landed-asset accounting (unchanged this dispatch)

Everything in the plan's "Preserved Assets" table plus Phases 7-9's mainline files
(`PrimeLemma.lean`, `CanonicalModel.lean`, `FrameClass.lean`) remains exactly as landed at the end
of Phase 9 — commit `5909c893`. This dispatch touched only:
- `specs/517_labelled_bounded_context_cs5_completeness/plans/12_wellfounded-zorn-oldlabel-reconstruction.md`
  (Phase 10 heading → `[BLOCKED]`, inline blocker writeup, deviation annotations)
- `specs/517_labelled_bounded_context_cs5_completeness/handoffs/phase-10-adequacy-bridge-blocker-20260718.md`
  (this file)
- `specs/517_labelled_bounded_context_cs5_completeness/.orchestrator-handoff.json`
- `specs/517_labelled_bounded_context_cs5_completeness/.return-meta.json`

## Recommendation to the orchestrator / user

Do not re-dispatch `/implement 517` expecting Phase 10 to close in one more standard dispatch.
Either:
(a) spawn/plan a dedicated Adequacy-bridge sub-effort (Track C, C5-C8) as its own bounded work
    item before returning to Phase 10, or
(b) get explicit user direction on whether `cs5_completeness`'s target may be restated in a way
    that avoids the Hilbert bridge (a real scope change to the task's "Definition of done," not a
    decision this agent may make unilaterally).
