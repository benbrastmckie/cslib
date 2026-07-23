# Phase 4 Summary — Bounded Prime Lemma (Simpson 5.3.1) — Zorn over whole contexts

- **Task**: 517 — labelled_bounded_context_cs5_completeness
- **Phase**: 4 of 9 (`[PARTIAL]`)
- **Plan**: `plans/11_tprime-repair-cs5-completeness.md`

## What was accomplished

Simpson's Prime Lemma 5.3.1 — the Zorn maximalisation over whole labelled bounded contexts that
produces an inhabitant of the repaired `TPrime` — was mechanized end to end in
`probes/chain-union-reflection-probe.lean` (extended in place from Phase 3), landing as
`primeLemma`. This is the plan's own stated Phase 4 objective, verbatim.

Of `TPrime`'s five defining clauses (clause 0 `clModel` plus the four numbered clauses):

- **Clause 0 (`clModel`), consistency, and disjunction are fully proven, sorry-free.**
- **Deductive closure and diamond** have their outer maximality-argument structure fully proven,
  each routing through exactly ONE new, well-scoped, documented strategic sorry for a genuinely
  new sub-lemma this dispatch discovered was needed (cut/substitution admissibility for
  deductive closure; a cofinite-range "old label" case for diamond).

The zero-debt invariant holds throughout: no `Cslib/` file was touched this phase; all work lives
in `probes/`. Three total `sorry`s remain in the probe file (2 new, 1 inherited from Phase 3),
each meeting the anti-analysis five-condition strategic-sorry test.

## Research finding: unbounded vs. bounded route resolved

The plan flagged an open risk about whether Simpson's *bounded* prime lemma (Ch 7-8, Lemma 8.2.6)
or the *unbounded* Chapter 5 form (5.3.1) is needed. `--lit` research against Simpson
`chunk_0165.md`/`chunk_0166.md` resolved this: the bounded route's Lemma 8.2.5 shows that
bounded-context primeness does *not* entail raw classical-modelhood — that only holds of a
separately-constructed completion `T-Comp(H)`, built *after* primeness. Since the already-landed
`TPrime` (`Context.lean`) requires **raw** `clModel`, the **unbounded** Ch 5 form is the one that
matches it, and is what Phase 4 transcribes. This finding likely makes Phase 5 ("T-Comp graph
completion — symmetry") unneeded for a `TPrime`-typed target; the plan's Phase 5 section has been
annotated with this finding (not unilaterally skipped — flagged for orchestrator/user decision).

## Clause 0 without an existential witness search

Simpson's own clause-0 proof is written for the general geometric-sequent case (existential
witnesses), which `GeomAxiom`'s Horn-only axioms (`T`, `B`, `Four`, `Five`) don't instantiate.
This dispatch reconstructed a specialized "redundant edge" maximality argument from Simpson's
*stated property* instead: since `NIK`'s only graph-reading rules consume `TClosure 𝒯 G.R` (not
the raw relation), and `T`/`B`/`Four` are exactly the constructors `TClosure` already closes
under, any raw edge that's already `𝒯`-closure-derivable adds no new derivation power when
adjoined — letting the SAME Lindenbaum-style maximality pattern used for the other clauses
discharge clause 0. New lemma chain: `TClosure.mono'` → `NIK.weaken_tclosure` (a strict
generalization of the mainline `NIK.weaken`) → `TClosure.addEdge_redundant` →
`NIK.drop_redundant_edge` → `raw_edge_of_tclosure` → `clModel_of_maximal`. Fully sorry-free.

## A recurring structural gap, confirmed (not a one-off)

Phase 3 left `ChainCtx.deriv_reflect` with one strategic sorry: the cofinite quantifier in
`NIK`'s `boxI`/`diaE` ranges over *every* label outside a finite exclusion set, but the
freshness-transport technique available (`NIK.freshWitness_transport`, and now Phase 4's own
`NIK.diaWitness_transport`) only handles labels fresh w.r.t. the relevant graph domain — "old"
labels already present in that domain are not covered. Phase 4's diamond clause hit the
**identical** obstacle independently (in `dwitness_mem_of_maximal`), confirming this is a
structural property of the cofinite-quantification encoding versus `Context.G.X`'s potentially-
infinite domain, not specific to either theorem. Investigated whether Phase 4's concrete Zorn
construction (via Mathlib's `zorn_le₀`) would supply the invariant Phase 3's docstring named as
route (a) ("the construction only ever extends by fresh labels at each step") — it does not:
`zorn_le₀` is a non-constructive existence result with no exposed step-indexed extension
sequence. Left both sorries as-is; recorded together in `sorry_inventory` with a shared
`follow_up_task` recommending a joint dispatch.

## Plan Deviations

- **Phase 3's `deriv_reflect` sorry was NOT discharged** (the dispatch's secondary objective),
  per the explicit permission in the dispatch instructions ("if it does not fall out cleanly,
  leave Phase 3's sorry as-is"). Investigated and ruled out the route Phase 3's docstring
  proposed; documented why in the plan and this summary.
- **Two new strategic sorries were introduced** (`NIK.subst` for deductive closure,
  `dwitness_mem_of_maximal`'s "old label" case for diamond) rather than fully discharging all
  five `TPrime` clauses as the plan's Phase 4 task list implies. Both are for genuinely new
  sub-lemmas not named in the plan's own task breakdown (the plan's task list only anticipated
  "maximality" as the mechanism, not that deductive closure specifically needs an additional
  cut-admissibility lemma, or that diamond's freshness-transport would hit the same gap as
  Phase 3). Both meet the anti-analysis five-condition strategic-sorry test and are tracked.
- **Phase 5 was not executed or skipped** — flagged in the plan as likely unneeded given Phase
  4's research finding, left `[NOT STARTED]` pending explicit confirmation, since redefining
  phase scope is outside a single phase dispatch's authority.

## Verification

- `lake env lean specs/517_labelled_bounded_context_cs5_completeness/probes/chain-union-reflection-probe.lean`:
  green, exactly 3 `sorry` warnings (documented, strategic).
- `git status --short` confirms zero changes to any `Cslib/` file this phase.
- Scoped `lake build` of `Labelled.Context`/`Labelled.Deduction` (the guardrail-adjacent modules):
  green, unaffected.
- `grep -rn '\bsorry\b' Cslib/` (excluding docstring false positives like "sorry-free"): 0 actual
  `sorry` tactic usages under `Cslib/`.

## Artifacts

- `probes/chain-union-reflection-probe.lean` (extended, ~1035 lines total, ~700 new this phase)
- `plans/11_tprime-repair-cs5-completeness.md` (Phase 4 marked `[PARTIAL]` with detailed notes;
  Phase 5 flagged)
- `progress/phase-4-progress.json`
- `handoffs/phase-4-handoff-20260718.md`
- `.orchestrator-handoff.json`
