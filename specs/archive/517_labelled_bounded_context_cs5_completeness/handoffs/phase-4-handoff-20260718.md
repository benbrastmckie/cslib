# Phase 4 handoff — Bounded Prime Lemma (Simpson 5.3.1) — Zorn over whole contexts

## Immediate Next Action

Two independent follow-ups, either can be dispatched first:

1. **`NIK.subst` (cut/substitution admissibility)** — `probes/chain-union-reflection-probe.lean`,
   the theorem just above `deductiveClosure_of_maximal`. Read its docstring for the exact induction
   shape needed (generalize over an accumulating prefix `Δ`, re-weaken the substituting derivation
   at each level). This is the ONLY gap in `TPrime`'s clause 1 (deductive closure) — everything
   else in that clause is proven.
2. **The diamond "old label" cofinite-range sub-case** — `dwitness_mem_of_maximal`'s `sorry`. Read
   its inline docstring comment for the exact diagnosis: `NIK.diaWitness_transport` (built this
   dispatch) only handles TARGET labels fresh w.r.t. `H.G.X`; labels already in `H.G.X` need a
   different argument. **This is the SAME obstacle as Phase 3's `ChainCtx.deriv_reflect` sorry**
   (see below) — a joint dispatch investigating both together is likely more efficient than two
   separate ones.

Once both are closed, re-run `lake env lean` on the probe (should show ZERO sorry warnings other
than Phase 3's `deriv_reflect`), then decide whether to transcribe `primeLemma` and its
dependencies into `Cslib/` mainline (a new file under `Constructive/Labelled/` or `Constructive/`)
as Phase 4's final deliverable, or continue accumulating probe-level proof mass and transcribe once
Phase 3's sorry is ALSO resolved (transcription is mechanical once everything is sorry-free; the
plan does not mandate transcribing per-phase).

## Current State

- `specs/517_labelled_bounded_context_cs5_completeness/probes/chain-union-reflection-probe.lean`
  (EXTENDED in place from Phase 3, now ~1035 lines): Phase 3's content (lines 1-340) is UNCHANGED.
  Phase 4's additions (lines ~341 onward):
  - `TClosure.mono'`, `NIK.weaken_tclosure`, `TClosure.addEdge_redundant`,
    `NIK.drop_redundant_edge` — the closure-invariance machinery behind clause 0. **Proven,
    sorry-free.**
  - `ChainCtx.unionContext`, `ChainCtx.le_unionContext` — packages Phase 3's `unionG`/`unionΓ`
    into a genuine `Context 𝒯 Atom`. **Proven, sorry-free.**
  - `primeC`, `primeC_mem_base`, `primeC_chain_bddAbove`, `primeC_exists_maximal` — Simpson's
    poset `C` and the Zorn maximalisation (via Mathlib's `zorn_le₀`). **Proven, sorry-free.**
  - `Graph.addEdge_X_eq_of_mem`, `Context.addRedundantEdge`/`_le`, `raw_edge_of_tclosure`,
    `clModel_of_maximal` — clause 0. **Proven, sorry-free.**
  - `consistency_of_maximal` — clause 2. **Proven, sorry-free.**
  - `LabelledFormula.ctxLabels_finite`, `Context.addFormula`/`_le`, `mem_of_maximal_addFormula`,
    `Deriv.orE`, `disjunction_of_maximal` — clause 3. **Proven, sorry-free.**
  - `NIK.diaWitness_transport`, `Context.addDiaWitness`/`_le`, `dwitness_mem_of_maximal`,
    `diamond_of_maximal` — clause 4. **Outer wiring and fresh-label transport proven, sorry-free.
    ONE documented strategic sorry** for the "old label" cofinite-range sub-case (same root cause
    as Phase 3's `deriv_reflect`).
  - `NIK.subst`, `Deriv.subst`, `deductiveClosure_of_maximal` — clause 1. **`Deriv.subst` and
    `deductiveClosure_of_maximal` are sorry-free modulo `NIK.subst` itself, which carries ONE
    documented strategic sorry** (cut admissibility, a genuinely new lemma this dispatch
    discovered is needed).
  - `primeLemma` — Simpson's Prime Lemma 5.3.1, assembled from the five clause theorems.
    **Proven, sorry-free** (as a wrapper; the clause theorems it calls carry the sorries above).
- **No `Cslib/` files were touched.** `Labelled/Context.lean`, `Labelled/Deduction.lean`,
  `CS5Canonical.lean`, `CKExtension.lean` are all unchanged from Phase 3's landed state. Confirmed
  via `git status --short` and a scoped `lake build` of `Labelled.Context`/`Labelled.Deduction`
  (green, no changes).
- Build verified via `lake env lean specs/.../probes/chain-union-reflection-probe.lean` after
  EVERY addition (7 incremental green commits, each individually build-checked): exits clean with
  exactly 3 `declaration uses 'sorry'` warnings (Phase 3's `deriv_reflect` at line 327-328, the new
  `dwitness_mem_of_maximal` at ~875, the new `NIK.subst` at ~985).

## Key Decisions Made

1. **Unbounded (Ch 5) route, not bounded (Ch 7-8)**, for the concrete construction — resolves the
   plan's own flagged risk. See the module docstring's "`--lit` research resolution" section
   (chain-union-reflection-probe.lean, right after `primeC_exists_maximal`... actually right
   before it, in the Phase 4 section header docstring) for the full argument from Simpson
   `chunk_0165.md`/`chunk_0166.md`. **This likely makes Phase 5 unneeded** — flagged in the plan,
   not acted on.
2. **Clause 0 (`clModel`) mechanized via a "redundant edge" maximality argument**, NOT Simpson's
   literal general-geometric-axiom witness-search proof (which is written for existential
   geometric sequents that `GeomAxiom` doesn't represent). This is a reconstruction from Simpson's
   *stated property*, per the plan's transcription discipline — see `raw_edge_of_tclosure`'s
   docstring.
3. **`primeC`'s reserve `V'` is fixed as `G₀.coinfinite.choose`** (Classical.choice-extracted from
   the base context's own clause-1 witness), matching Simpson's "let `V'` be some coinfinite
   subset such that the underlying set of `G` is contained in `W(V')`."
4. **Extended Phase 3's file in place** rather than creating a new probe file, to directly reuse
   `NIK.swap_relabel`/`NIK.freshWitness_transport`/`ChainCtx` without any cross-probe import
   (probes are standalone-compiled via `lake env lean`, not part of the Lake module graph, so
   cross-file imports between probes are not viable — confirmed by grepping every existing probe's
   import list, none cross-import another probe).

## What NOT to Try

- **Do NOT re-attempt discharging Phase 3's `deriv_reflect` sorry via "the concrete Zorn
  construction's extension-step invariant"** (Phase 3's docstring's route (a)) using Mathlib's
  `zorn_le₀` as the mechanism. `zorn_le₀` is a non-constructive existence result — it does not
  expose the step-by-step extension sequence route (a) needs. A genuinely different, more
  hands-on Zorn construction (e.g. ordinal-indexed recursion) would be needed to make route (a)
  available, which is a much larger undertaking than this or the prior dispatch attempted.
- **Do NOT try to prove clause 0 via Simpson's literal witness-search argument** (the general
  geometric-sequent case with existential witnesses) — `GeomAxiom` has no existential-conclusion
  constructor, so that argument's machinery has no target to transcribe. The "redundant edge"
  reconstruction already landed sorry-free is the right approach; do not revert to attempting a
  literal transcription of the general case.
- **Do NOT assume `x₀ ≠ Label.dwitness y B`** when attacking the diamond "old label" sorry — this
  specific collision (the excluded target's own label happening to coincide with a diamond-witness
  label constructed during the argument) is part of WHY the naive freshness-transport approach
  breaks down in general; a full fix needs to either rule this out via an additional invariant or
  handle it as a genuine case split.

## Remaining Goals (verbatim from plan)

Phase 4's plan text (as updated): "Discharge the four clauses with the repaired rules" — 3 of 4
clauses (plus clause 0) are sorry-free; deductive closure and diamond each carry one sorry as
described above. Phase 4's stated objective — "prove `Γ ⊬_G x:A ⟹ ∃ 𝒯-prime (H,Δ) ⊇ (G,Γ) with
`Δ ⊬_H x:A`` — producing an inhabitant of the repaired `TPrime`" — IS assembled (`primeLemma`), but
its truth currently depends on the 2 new + 1 inherited sorries via the clause theorems it calls.

## References

- Plan: `specs/517_labelled_bounded_context_cs5_completeness/plans/11_tprime-repair-cs5-completeness.md`
  (Phase 4 section, updated `[PARTIAL]`; Phase 5 flagged).
- Progress: `specs/517_labelled_bounded_context_cs5_completeness/progress/phase-4-progress.json`
- Probe (all Phase 4 work): `specs/517_labelled_bounded_context_cs5_completeness/probes/chain-union-reflection-probe.lean`
- Literature consulted: `chunk_0102.md`, `chunk_0103.md` (5.3.1), `chunk_0165.md`, `chunk_0166.md`
  (8.2.5/8.2.6), all in `/home/benjamin/Projects/Literature/simpson_1994_intuitionisticmodallogic/`.
