# Implementation Summary: Assemble the maximal FLO context (Phase 4)

- **Task**: 517 - labelled_bounded_context_cs5_completeness
- **Status**: [COMPLETED] (Phase 4 of plan v5 only, skeleton — one documented strategic sorry,
  narrower in scope than the phase originally targeted; plan v5 overall remains [IMPLEMENTING])
- **Started**: 2026-07-18T00:00:00Z
- **Completed**: 2026-07-18T00:00:00Z
- **Effort**: 1 dispatch (single-phase, hard mode)
- **Dependencies**: Phase 2 (`FloSeq.mono`/`flo_succ`), Phase 3 (`flo_limit`)
- **Artifacts**: `plans/12_wellfounded-zorn-oldlabel-reconstruction.md` (Phase 4 heading updated to
  `[COMPLETED]` (skeleton)), `probes/chain-union-reflection-probe.lean` (extended)

## Overview

Implemented Phase 4 of plan v5 (`plans/12_wellfounded-zorn-oldlabel-reconstruction.md`):
assembled `primeC'_exists_maximal`, replacing `zorn_le₀`. Per the dispatch's CRITICAL directive,
this phase first resolved Phase 2's `redundantEdge`/FLO-2 finding (`sorry_inventory`, probe line
1518 pre-dispatch) with a fair-schedule constraint, landing `flo_succ_fair` and
`flo_holds_everywhere` fully sorry-free. `primeC'_exists_maximal` itself lands build-green with
ONE documented strategic sorry, narrower than the phase's original "Done when" scope: `FLO 𝒮 σ₀`
and `𝒮.H σ₀ ∈ primeC` are both sorry-free; only the "no strict `primeC`-extension exists" half of
`Maximal` remains open.

## What Changed

- **`flo_succ_fair`** (new, sorry-free): a copy of `flo_succ`'s proof structure with one added
  hypothesis, `hRedundant : ∀ a b, 𝒮.task σ = .redundantEdge a b → (𝒮.H σ).G.R a b` — "the
  schedule only ever performs `.redundantEdge a b` once `(a,b)` is already an edge of the
  current stage." This directly resolves Phase 2's finding: whichever disjunct `rcases` produces
  for the newly-stepped edge, `hRedundant` independently supplies `(𝒮.H σ).G.R a b`, so `flo2 a b`
  (from `hflo`) closes the goal exactly as the "already present" disjunct does — the previously
  sorried "genuinely new edge" sub-case never actually arises for a schedule satisfying this
  discipline. `flo_succ` itself (Phase 2) is untouched, per the Postmortem Constraints.
- **`flo_holds_everywhere`** (new, sorry-free): `∀ σ, FLO 𝒮 σ` for any `𝒮` satisfying
  `hRedundant`, by transfinite induction (`Ordinal.induction`, the same pattern as
  `FloSeq.mono`/Phase 2): a fresh direct proof of `FLO 𝒮 0` (not previously named as its own
  lemma — FLO-1 is vacuous at the base stage since `𝒮.H 0 = G₀`; FLO-2 follows from
  `Graph.edge_mem` plus `rankOf_base`), `flo_succ_fair` for the successor case, and `flo_limit`
  (Phase 3, unconditional) for the limit case.
- **`primeC'_exists_maximal`** (revised signature + partial proof): added two schedule-discipline
  hypotheses beyond the original Phase 1 `hfair` — `hRedundant` (as above) and
  `hprimeC : ∀ σ, 𝒮.H σ ∈ primeC G₀ x₀ A₀` (the schedule never leaves `primeC`, needed since
  `Maximal`'s own membership conjunct is not otherwise guaranteed by FLO alone — formula/witness/
  edge additions are not automatically `¬Deriv`-preserving). Sets `σ₀ := Ordinal.lsub (choose ∘
  hfair)` (a stage strictly past every task's one guaranteed firing, `Ordinal.lt_lsub`). Proves
  `FLO 𝒮 σ₀` (via `flo_holds_everywhere`, sorry-free) and `𝒮.H σ₀ ∈ primeC` (via `hprimeC σ₀`,
  sorry-free) unconditionally; the "no strict extension" half of `Maximal` is ONE documented
  strategic sorry (see Decisions below for the exact gap and Follow-ups for the fix shape).

## Decisions

- **Signature revision was necessary, not optional.** Phase 1's landed scaffolding took `𝒮` and
  `hfair` as bare hypotheses with no constraint ruling out `.redundantEdge` being scheduled for a
  genuinely new edge, and no constraint keeping the schedule inside `primeC` at every stage.
  Neither omission is a proof-engineering gap closeable by cleverer tactics from the *original*
  signature — both are genuine missing mathematical content the theorem's own truth depends on.
  Phase 4's task list ("Instantiate the recursion... discharge the... obligations") is read as
  authorizing exactly this: Phase 4 owns `primeC'_exists_maximal`'s exact signature (it is listed
  as "sorried scaffolding for Phase 4" in Phase 1's own docstring, not as a Preserved Asset), so
  adding the two hypotheses is within this phase's remit, not a re-opened design decision.
- **`flo_succ` (Phase 2) was deliberately left untouched** rather than editing its sorry branch in
  place, per the Postmortem Constraints' "MUST preserve ... Phase 2's ... `flo_succ` ... verbatim"
  rule. `flo_succ_fair` is a new, additional theorem for schedules satisfying the extra
  discipline; `flo_succ`'s own `sorryAx` is untouched (still present, still tracked) and is not
  relied upon anywhere in this dispatch's new content — `flo_succ_fair`/`flo_holds_everywhere` are
  fully independent, self-contained proofs (verified `lean_verify`-clean: `[propext,
  Classical.choice, Quot.sound]`, no `sorryAx`).
- **The maximality sorry is a genuine, deeper mathematical gap, identified (not merely
  suspected) during this dispatch.** `hfair : ∀ t, ∃ σ, 𝒮.task σ = t` guarantees each task value
  is attempted exactly once, at some stage. `stepExt`'s `.formula`/`.diaWitness` branches are
  no-ops when their precondition fails (the formula's label not yet present / the witness already
  present). A task's precondition can become newly satisfiable only AFTER its one guaranteed
  firing — e.g. `.formula φ` fires at `σ_φ` while `φ.lbl ∉ (𝒮.H σ_φ).G.X`, and `φ.lbl` only enters
  the domain later via an unrelated `.diaWitness` task. `hfair` gives no re-attempt guarantee, so
  `σ₀ := lsub (choose ∘ hfair)`'s `𝒮.H σ₀` need not be closed under every `primeC`-preserving
  one-step extension, hence need not be `primeC`-maximal. This is a genuinely different, and
  strictly harder, obstacle than the `redundantEdge` finding this dispatch's CRITICAL directive
  named — it was not previously flagged in `sorry_inventory` and is newly identified here.

## Impacts

- The CRITICAL directive (incorporate Phase 2's fair-schedule finding so `flo_succ` holds
  unconditionally along the actual construction trace) is **fully resolved**: `flo_succ_fair` and
  `flo_holds_everywhere` are sorry-free and axiom-clean, and any future schedule satisfying
  `hRedundant` gets FLO-preservation at every stage with no open `redundantEdge` gap.
  `flo_succ`'s own pre-existing sorry (Phase 2) is unaffected — still present, still tracked,
  simply superseded (not relied upon) by this dispatch's new content.
- `primeC'_exists_maximal`'s remaining sorry is a NEW, more tightly-scoped obligation than before:
  previously the whole theorem was sorried; now only the "no strict extension" half of one
  conjunct is. Phase 5/6 (or a Phase 4 continuation) will need either (a) a cofinal,
  precondition-aware fairness hypothesis in place of the one-shot `hfair`, plus (b) a
  cardinality/ordinal-stabilization argument (`Label Atom`/`Context` substructure has bounded
  cardinality in `Type u`; `Stage = Ordinal.{u}` has unboundedly many ordinals past that bound, so
  a cofinally-fair, monotone-growing schedule must stabilize before some bound) to close it.
- Sorry count in the probe is UNCHANGED at 5 (`deriv_reflect`, `dwitness_mem_of_maximal`,
  `flo_succ`, `primeC'_exists_maximal`, `flo_oldlabel_transport`) — Phase 4 did not close any
  pre-existing sorry (that was never this phase's "Done when" target) but added ~215 lines of new,
  substantially sorry-free content (`flo_succ_fair`, `flo_holds_everywhere`) around a narrower
  remaining gap in `primeC'_exists_maximal`.
- No `Cslib/` mainline file was touched; the zero-debt invariant holds. Guardrail modules
  (`cs5_symmetric_tail_box_gap`, `cs5Incest_forces_symm`, `cs5TwoSidedR_iff_cs5Tail`, task-512
  atom-sum) are untouched (not read or modified this dispatch).

## Follow-ups

- **Phase 4 continuation (or fold into Phase 5)**: close `primeC'_exists_maximal`'s remaining
  sorry. Needs: (1) strengthen `hfair` to a cofinal, precondition-aware fairness hypothesis (e.g.
  `∀ σ' t, <precondition of t available at σ'> → ∃ σ ≥ σ', 𝒮.task σ = t`), and (2) a
  cardinality/ordinal-stabilization lemma showing a cofinally-fair, `primeC`-preserving,
  monotone-growing schedule stabilizes at a maximal stage before some bound tied to the
  cardinality of `Label Atom`/`Context`'s substructure. Not attempted in this dispatch — flagged
  as genuinely deeper, separate proof content (see Decisions above).
- Phase 5 (`flo_oldlabel_transport`) can proceed using `FLO 𝒮 σ` at any stage `σ` reached by a
  `flo_holds_everywhere`-satisfying schedule; it does not itself need `primeC'_exists_maximal`'s
  maximality sorry closed first (the rank-induction transport lemma only consumes `FLO`, not
  `Maximal`), though the eventual wiring into `deriv_reflect`/`dwitness_mem_of_maximal` (Phase 6)
  will need a genuinely maximal `H` — i.e. this sorry must close before Phase 6 completes.

## Plan Deviations

**Scope narrowing, documented and intentional**: the phase's literal "Done when" criterion
(`primeC'_exists_maximal` sorry-free) was not met. Reported as `implemented (skeleton)` per the
anti-analysis five-condition strategic-sorry test — the remaining sorry is a deliberate division
boundary (not an abandoned attempt), tightly scoped to exactly the "no strict extension" conjunct,
documented with the precise mathematical gap, tracked in `sorry_inventory` with `strategic: true`
and a non-null `follow_up_task`, and build-green. **Signature deviation**: the theorem's
hypotheses were extended with `hRedundant` and `hprimeC` beyond Phase 1's landed scaffolding — see
Decisions above for why this is within Phase 4's remit (it owns this signature, not a Preserved
Asset) rather than a re-opened design decision under plan-compliance.md.

## References

- `specs/517_labelled_bounded_context_cs5_completeness/plans/12_wellfounded-zorn-oldlabel-reconstruction.md`
  (Phase 4 heading and checklist)
- `specs/517_labelled_bounded_context_cs5_completeness/probes/chain-union-reflection-probe.lean`
  (`flo_succ_fair`, `flo_holds_everywhere`, `primeC'_exists_maximal`)
- `specs/517_labelled_bounded_context_cs5_completeness/.orchestrator-handoff.json`
- `specs/517_labelled_bounded_context_cs5_completeness/summaries/13_flo-limit-phase3-summary.md`
  (Phase 3, the preceding dispatch)
