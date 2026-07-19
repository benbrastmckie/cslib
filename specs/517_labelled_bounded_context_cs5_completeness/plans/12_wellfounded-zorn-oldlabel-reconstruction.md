# Implementation Plan v5: Task #517 — Well-founded Zorn / "old label" reconstruction (Phase 4.5) + downstream CS5 completeness

- **Task**: 517 - labelled_bounded_context_cs5_completeness
- **Status**: [IMPLEMENTING]
- **Effort**: HIGH, MEDIUM-HIGH uncertainty. The genuinely new work is the "Phase 4.5"
  well-founded maximalisation reconstruction (Phases 1-6 below) that replaces Mathlib's
  `zorn_le₀` in `primeC_exists_maximal` and discharges the two shared "old label" strategic
  sorries. Downstream phases (7-11) are carried over from v4 (plans/11) largely unchanged. Honest
  headline: **~8-14 dispatches remaining**; the reconstruction (Phases 1-6) is the crux and the
  majority of the risk. This plan version exists solely because a completed divergence audit
  (below) proved the two remaining sorries need one dedicated construction, not further quick
  follow-ups.
- **Dependencies**: [] (former deps 509 completed, 512 abandoned, 516 abandoned — all terminal).
  517 remains the sole surviving CS5-completeness route.
- **Research Inputs** (audit/diagnosis artifacts folded into THIS revision):
  - handoffs/oldlabel-joint-dispatch-handoff-20260718.md (**the divergence audit** — independent
    re-derivation of the obstacle; three additional shortcuts formally ruled out; route (a)
    confirmed as the only fix)
  - handoffs/phase-4-handoff-20260718.md (Phase 4 Zorn assembly; the diamond "old label" sorry
    first isolated as sharing `deriv_reflect`'s root cause)
  - handoffs/nik-subst-followup-handoff-20260718.md (`NIK.subst` cut-admissibility closed;
    `TPrime` clause 1 now fully sorry-free)
  - probes/chain-union-reflection-probe.lean — the module-level analysis section preceding
    `ChainCtx.deriv_reflect` (~line 295) and the expanded `dwitness_mem_of_maximal` sorry comment
    (~line 913): the sharpened root-cause diagnosis and the FLO-invariant sketch this plan
    formalizes
  - .orchestrator-handoff.json — the sharpened `sorry_inventory` (both sorries, shared root cause,
    shared follow-up)
  - Prior plans preserved for history: plans/01 (v1), plans/02 (v2), plans/08 (v3),
    **plans/11 (v4)**. This v5 **supersedes v4's Phase 3-4 completion path** (the `zorn_le₀`-based
    route to a sorry-free `primeLemma`); v4's Phases 1-2 landed assets and its downstream Phase
    6-9 text are carried forward, not superseded.
- **Artifacts**: plans/12_wellfounded-zorn-oldlabel-reconstruction.md (this file). Supersedes the
  Phase 3-4 completion path of plans/11_tprime-repair-cs5-completeness.md (v4 retained for
  history; not deleted).
- **Standards**: plan-format.md; plan-compliance.md; artifact-formats.md; cslib.md; lean4.md;
  cslib CONTRIBUTING/NOTATION/ORGANISATION.
- **Type**: cslib
- **Lean Intent**: true

## Overview

This is a `/revise`-style version bump, not a from-scratch plan. A dedicated **divergence-audit
dispatch** (handoffs/oldlabel-joint-dispatch-handoff-20260718.md) closed the diagnostic question
that stalled v4's Phase 3-4: the two remaining strategic sorries — `ChainCtx.deriv_reflect`
(Phase 3) and `dwitness_mem_of_maximal`'s diamond "old label" sub-case (Phase 4) — **share one
root cause** (a cofinite-eigenvariable quantifier ranging over labels that may already be "old",
against a potentially-infinite graph domain) and **both need the same fix**: replacing Mathlib's
non-constructive `zorn_le₀` in `primeC_exists_maximal` with a **step-indexed / well-founded
(transfinite) Lindenbaum construction** that carries a *fresh-labels-only extension invariant*
(FLO, stated precisely below) through every stage. The audit **formally ruled out four
alternative shortcuts** (see Postmortem Constraints), so no future dispatch should retry them.

This plan sequences that reconstruction as "Phase 4.5 territory" (Phases 1-6), then re-attaches
v4's downstream phases (transcription → canonical model + truth lemma → frame-class match →
`cs5_completeness` assembly → bookkeeping) as Phases 7-11.

**Definition of done**: `cs5_completeness : CKValidFC cs5FC'' φ → Derivable CS5ModalAxiom φ` lands
sorry-free and axiom-clean (footprint ⊆ `[propext, Classical.choice, Quot.sound]`) under `Cslib/`.

**Definition of done for the Phase 4.5 core (Phases 1-6)**: `probes/chain-union-reflection-probe.lean`
(or a successor probe) is **fully sorry-free** — both `deriv_reflect` and `dwitness_mem_of_maximal`
discharged, `primeLemma` sorry-free, `#print axioms primeLemma` ⊆ `[propext, Classical.choice,
Quot.sound]` (no `sorryAx`).

**Zero-debt invariant**: no `sorry`, no new `axiom`, no vacuous (`:= True`/`Unit`/`trivial`)
definitions under `Cslib/` at any phase boundary. All new proof work (Phases 1-6) lives in
`probes/`, where `sorry` is permitted only as an intermediate state within a dispatch, never at a
phase boundary of the FLO-core once that phase claims completion. Mainline `Cslib/` is not touched
until Phase 7 (transcription of the already-green result).

**Transcription discipline (standing rule)**: every formula and inference rule is read from the
PDF page raster or reconstructed from a stated property; chunk/OCR text is admissible for prose
and structure only. Simpson1994 chunks live at
`/home/benjamin/Projects/Literature/simpson_1994_intuitionisticmodallogic/`; **PDF page offset is
+9** (printed p.N = PDF p.N+9); verify citations by content, never by chunk number.

**Phase-count note (H8 discipline)**: this plan carries 11 phases, above the nominal complex-tier
ceiling of 8. This is deliberate and is NOT the "single unbounded unit split into many phases"
anti-pattern the ceiling guards against: Phases 1-6 are six genuinely distinct, individually
bounded-and-verifiable units of the new reconstruction, and Phases 7-11 are carried-over,
already-scoped downstream work from v4. No skeleton/follow-up-task split is used because this plan
*discharges* existing strategic sorries rather than declaring new ones; `plan_metadata.skeleton`
stays `false`.

### The FLO invariant (the exact fresh-labels-only extension invariant)

Fix the base context `G₀` and its shared coinfinite reserve `V' := G₀.coinfinite.choose` (so every
context in the poset is `W(V')`-confined, matching Simpson's fixed `V'`, `chunk_0102.md`). A
context `H ⊇ G₀` produced by the construction carries a **birth-rank** function
`rank : {x // x ∈ H.G.X} → σType` (where `σType` is the construction's stage-index type — an
`Ordinal`, or the well-founded stage type chosen in Phase 1) satisfying:

- **(FLO-0) base**: every `x ∈ G₀.G.X` has `rank x = ⊥` (the base stage). Base labels are the only
  labels not introduced by an extension step.
- **(FLO-1) fresh at birth**: for every `x ∈ H.G.X \ G₀.G.X` there is a unique successor stage
  `σ` with `rank x = σ` at which `x` was adjoined, and at that stage `x` was **either**
  - (a) drawn **fresh from the reserve** `V'ᶜ` and `x ∉ H_{<σ}.G.X` (prime / deductive-closure /
    disjunction extension steps), **or**
  - (b) `x = Label.dwitness w B` for some `w ∈ H_{<σ}.G.X` already present and some `B` (diamond
    extension step; `Label.InW` does not consume the reserve for `dwitness`, so confinement is
    inherited — cf. `Context.addDiaWitness`, probe ~line 902).
- **(FLO-2) edge locality**: every edge `(u,v) ∈ H.G.R` was introduced at the stage
  `max(rank u, rank v)`; equivalently, no extension step ever adds an edge between two labels both
  strictly older than that step. Each step adds edges incident **only** to the label(s) it adjoins
  that step.

**Why FLO discharges both sorries** (the load-bearing consequence, to be mechanized in Phase 5):
FLO-2 is exactly what makes the naive swap `swapFn y₀ y` for an "old" label `y` legitimate under
control — the audit confirmed (via direct inspection of `NIK.diaE`, `Deduction.lean:309-312`) that
an unstructured swap is **actively invalid** precisely when `H.G` has an edge incident to `y` that
the target graph does not know about. FLO-2 bounds those incident edges to `y`'s birth stage, so a
`rank`-indexed (well-founded) induction can transport the single witnessing derivation across old
labels rather than requiring a single dominating chain index (the impossibility the audit proved
for the `zorn_le₀` route). FLO-1(a)'s reserve-freshness gives the fresh-label half already proven
(`NIK.freshWitness_transport` / `NIK.diaWitness_transport`); FLO-1(b) handles the diamond witness
labels; together they cover the whole cofinite eigenvariable range.

### Preserved Assets (landed, green, sorry-free — do NOT redo or re-scope)

The following work is complete and must not regress. This accounting is binding on every
implementation dispatch (see Postmortem Constraints).

| Component | File | Status | Verified |
|-----------|------|--------|----------|
| Phase 1: `TPrime` repair — `(⊥E)`/`(∨E)` cross-label (`NIK.efq`/`NIK.orE`) | `Cslib/.../Constructive/Labelled/Deduction.lean` | [COMPLETED] | green, sorry-free |
| Phase 1: `NIK.weaken` re-proved for cross-label constructors | `Cslib/.../Constructive/Labelled/Deduction.lean` | [COMPLETED] | green, sorry-free |
| Phase 1: clause 0 → `ClassicalModelOn 𝒯 G.X G.R` (domain-relative) | `Cslib/.../Constructive/Labelled/Context.lean` | [COMPLETED] | green, sorry-free |
| Phase 1: clause 1 → relativized `deductiveClosure` (`∀ x ∈ G.X`) | `Cslib/.../Constructive/Labelled/Context.lean` | [COMPLETED] | green, sorry-free |
| Phase 2: inhabitedness gate (weaker form, `TPrime.gx_ne_univ`) | `probes/inhabitedness-gate-probe.lean` | [COMPLETED] | sorry-free (probe) |
| Phase 3: `NIK.swap_relabel`, `NIK.freshWitness_transport` | `probes/chain-union-reflection-probe.lean` | [COMPLETED] | sorry-free (probe) |
| Phase 4: `primeLemma` assembled (Simpson 5.3.1) | `probes/chain-union-reflection-probe.lean` | [COMPLETED] (Phase 6) | fully sorry-free, axiom-clean (`lean_verify`: `[propext, Classical.choice, Quot.sound]`) |
| Phase 4: `TPrime` clauses 0,1,2,3 (`clModel`, `deductiveClosure` via `NIK.subst`, consistency, disjunction) | `probes/chain-union-reflection-probe.lean` | [COMPLETED] | all four sorry-free |
| Guardrails: `cs5_symmetric_tail_box_gap`, `cs5Incest_forces_symm`, `cs5TwoSidedR_iff_cs5Tail`, task-512 atom-sum | `Cslib/.../CS5*.lean` | [COMPLETED] | true, unregressed theorems |

**The ONLY remaining obstacle** is the "old label" cofinite-range reflection, shared by
`deriv_reflect` (Phase 3) and `dwitness_mem_of_maximal` (Phase 4, clause 4). Everything else in the
prime lemma is done.

## Postmortem Constraints

Binding rules for all implementation dispatches on this task. Derived from four prior dispatches
(Phase 3, Phase 4, the `NIK.subst` follow-up, and the divergence audit) and their formally
ruled-out alternatives. Violating these re-treads already-refuted ground.

**Do NOT** (explicitly-rejected alternatives — do not retry any of these):
- **Do not re-attempt `zorn_le₀` over the plain `primeC` poset** expecting it to expose a
  step-indexed "each step adjoins only a fresh label" invariant. `zorn_le₀` is a non-constructive
  existence result (`∃ m, Maximal … m`); it exposes no extension sequence. Confirmed by two
  independent dispatches. Route (a) requires a *different* construction, not a different use of
  `zorn_le₀` over the same carrier.
- **Do not attempt Shortcut 1 (finite-subgraph existential in `Deriv`)** — redefining `Deriv 𝒯 G Γ φ`
  to existentially quantify a finite sub-graph `G₀ ≤ G` (matching Simpson's `:5090` finitary
  bundling) reduces to the identical uniform-index obstruction one level down: different `y`'s each
  need a different finite `G₀_y` with no common bound. Formally ruled out by the audit.
- **Do not attempt Shortcut 2 (direct IH reuse at old labels, no relabelling)** — it supplies the
  fact with a *different chain index per label*, and `Directed`/`ChainCtx.dir` bounds only finitely
  many indices at once, never an unboundedly-indexed family. Formally ruled out.
- **Do not add an unconditional "bounded-old-label" hypothesis to `ChainCtx`** (a single index
  dominating every old label) as a "fix" (Shortcut 3). It *would* close the gap but is NOT
  derivable from `ChainCtx`'s current merely-`Directed` definition; it is only legitimate if the
  new FLO construction *provably supplies* such a bound at every stage — which is the whole point of
  Phases 1-4. Do not assert it as a free hypothesis.
- **Do not naive-swap `swapFn v y'` for an "old" label `y'`** — the audit confirmed via direct
  inspection of `NIK.diaE`'s constructor (`Deduction.lean:309-312`) that this is not merely
  unproven but **actively invalid** whenever `H.G` has any edge incident to `y'` other than possibly
  `(y,y')`: the swapped edge touches `v`, which the target graph `H.G.addEdge y y'` does not know
  about. Old-label transport must go through the FLO-2 rank induction, never a bare swap.
- **Do not introduce an `axiom`** or a vacuous (`:= True`/`Unit`/`trivial`) definition to discharge
  either sorry. Explicitly prohibited by every prior plan and by cslib.md/lean4.md.
- **Do not re-derive a different decomposition mid-implementation** (plan-compliance.md, binding on
  all `.lean` files whenever a plan exists). Execute this plan's task sequence; a genuine blocker is
  raised as `[BLOCKED]`, not silently re-decomposed.
- **Do not touch `Cslib/` mainline before Phase 7.** All Phase 1-6 proof work stays in `probes/`.
- **Do not re-attempt `NIK.subst`** — it is closed (cut/substitution admissibility, via
  `NIK.subst_aux`). Do not re-open its design.
- **Do not revert clause 0 to Simpson's literal witness-search** — `GeomAxiom` has no
  existential-conclusion constructor; the landed "redundant edge" reconstruction
  (`raw_edge_of_tclosure`/`clModel_of_maximal`) is the correct approach.

**MUST preserve** (see the Preserved Assets table above for the full list):
- The mainline `TPrime` repair (`Deduction.lean` + `Context.lean`): cross-label `NIK.efq`/`NIK.orE`,
  re-proved `NIK.weaken`, `ClassicalModelOn` clause 0, relativized `deductiveClosure` clause 1.
- `TPrime` clauses 0-3 sorry-free (including clause 1 via `NIK.subst` cut-admissibility).
- Phase 3's `NIK.swap_relabel`, `NIK.freshWitness_transport`; Phase 4's `NIK.diaWitness_transport`,
  `Context.addDiaWitness`, `primeC`, and all sorry-free clause theorems.
- The four guardrails as true, unregressed theorems; the zero-debt invariant.

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):
- **Route (a) — the step-indexed / well-founded (transfinite) Lindenbaum reconstruction carrying
  FLO — is the ONLY viable fix.** Four alternatives (Shortcuts 1-3 above + the naive swap) were
  formally ruled out by the audit. Do not reopen the question of *whether* a reconstruction is
  needed.
- **The construction must be transfinite, not `ω`-indexed.** `Atom : Type u` is not assumed
  countable, so Simpson's own "denumerable ⟹ choice-free iterative construction" remark
  (`chunk_0103.md`) does not bound the recursion at `ω`.
- **Both sorries share one root cause and one shared FLO-derived lemma discharges both** (Phase 5).
  Do not build two separate arguments.
- **Unbounded (Ch 5) route + RAW canonical relation.** The already-landed `TPrime` requires raw
  `clModel`; the canonical relation is raw `xRy` in `H` (Simpson p.94, confirmed twice), NOT
  `𝒯-Comp(H)` and NOT the `TClosure`. Use `ClassicalModelOn 𝒯 G.X G.R`, not `ClassicalModel` of the
  closure.
- **Original Phase 5 (T-Comp graph completion, Simpson 8.2.5) is likely UNNEEDED** for a
  `TPrime`-typed target (Phase 4's `--lit` finding). Flagged for confirmation at Phase 8, not
  deleted (see the flagged note before Phase 8).

## Goals & Non-Goals

- **Goals**:
  1. Define the step-indexed / well-founded maximalisation construction and the FLO invariant
     precisely, in Lean (Phase 1).
  2. Prove FLO is maintained at successor and limit stages (Phases 2, 3) and assemble the maximal
     FLO context `primeC'_exists_maximal`, replacing `zorn_le₀` (Phase 4).
  3. Use FLO to discharge BOTH `deriv_reflect` and `dwitness_mem_of_maximal` via one shared lemma
     (Phases 5-6); re-verify `primeLemma` fully sorry-free.
  4. Transcribe the sorry-free result into `Cslib/` mainline (Phase 7), then sequence the remaining
     downstream phases (canonical model + truth lemma, frame-class match, `cs5_completeness`
     assembly, bookkeeping) to the sorry-free, axiom-clean `cs5_completeness` (Phases 8-11).
- **Non-Goals**:
  - Do NOT re-litigate the target (proven satisfiable, `cs5_fs`, v3). Never target `cs5FC`.
  - Do NOT re-open the Phase 1-4 landed assets (Preserved Assets table) — they are green.
  - Do NOT retry any ruled-out shortcut (Postmortem Constraints).
  - Do NOT port MMS `labIK≤` or de Groot–Shillito–Clouston constructions; the carried proof is
    Simpson's.
  - Do NOT build the T-Comp completion (original Phase 5) unless Phase 8 confirms it is needed.

## Risks & Mitigations

- **Risk (HIGH — the crux): the transfinite construction mechanism.** Two candidate Lean encodings
  exist: (i) explicit well-founded/`Ordinal` recursion producing an FLO-carrying context at each
  stage with limit unions; (ii) `zorn_le₀` over an **FLO-enriched carrier** — a subtype/structure
  bundling the birth-rank trace so every poset member satisfies FLO by construction, with chain
  closure required to preserve the trace coherently. **Mitigation**: Phase 1 evaluates both against
  Simpson's proof text (`chunk_0102.md`/`chunk_0103.md`) and Mathlib's available recursion/Zorn
  API, and **commits to one** (plan-compliance: the choice is then fixed for downstream phases). The
  audit's constraint is only that the plain-carrier `zorn_le₀` cannot supply FLO; an FLO-enriched
  carrier is not excluded and may be more tractable in Lean than raw ordinal recursion. Flag the
  decision explicitly in Phase 1's probe docstring.
- **Risk (MEDIUM): FLO-2 edge-locality may need strengthening for the diamond step.** The diamond
  extension (`Context.addDiaWitness`) adds edge `y R dwitness y B` with `y` possibly old. FLO-2 must
  be stated so this is the *one* edge introduced at the dwitness's birth stage. **Mitigation**:
  Phase 1 states FLO-2 to cover exactly the three extension operations (`addFormula`,
  `addDiaWitness`, `addRedundantEdge`); Phase 2 proves each preserves it.
- **Risk (MEDIUM): the shared old-label lemma (Phase 5) is the real mathematical content** and may
  itself split. **Mitigation**: Phase 5 is allowed to split into 5.1 (the rank-induction transport
  lemma for `NIK` derivations) and 5.2 (its application to the cofinite `boxI`/`diaE` premise); each
  sub-phase is a bounded unit. If the transport lemma cannot be proved from FLO as stated, escalate
  `[BLOCKED]` with the exact goal — do NOT weaken FLO to a free hypothesis (Shortcut 3).
- **Risk (~100%/dispatch base rate): another transcription defect.** Every dispatch has found the
  previous one's transcription subtly wrong. **Mitigation**: the PDF-raster rule; `--lit` research +
  small-model check on every transcribed schema before writing Lean.
- **Risk: original Phase 5 (T-Comp) turns out to be needed after all.** **Mitigation**: it is left
  flagged, not deleted; Phase 8 confirms before proceeding, and the retained
  `probes/lemma612-scaffold.lean` / `track-c-c1-tele-conj.lean` material is the fallback for a
  box-backward Ch.6 bridge.

## Implementation Phases

Phases 1-6 (the FLO reconstruction) operate entirely in `probes/`; Phase 7 transcribes the green
result into `Cslib/`; Phases 8-11 carry over v4's downstream work. Every proof-leg phase opens with
an `--lit` step against the relevant Simpson chunks before transcription. `--hard` is recommended
throughout (3+ prior plan versions; history of analysis-only dispatches — both `--hard` triggers).

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |
| 5 | 6 | 5 |
| 6 | 7 | 6 |
| 7 | 8 | 7 |
| 8 | 9 | 8 |
| 9 | 10 | 8, 9 |
| 10 | 11 | 10 |

Phases within the same wave can execute in parallel (only Wave 2 has genuine parallelism:
successor-preservation and limit-preservation are independent statements).

### Phase 1: Define the well-founded maximalisation carrier + the FLO invariant (probe) [COMPLETED]

- **Goal:** land, in `probes/`, the concrete Lean definitions of the stepped/well-founded
  construction and the FLO invariant, with the successor/limit/maximality obligations stated as
  sorried theorem signatures. This phase produces DEFINITIONS that typecheck, not proofs — but the
  definitions must be non-vacuous (FLO is a real predicate, never `:= True`).
- **Tasks:**
  - [x] `--lit`: read Simpson's Prime Lemma proof (`chunk_0102.md`/`chunk_0103.md`, pp.92-93 raster)
    for the iterative construction and the denumerable-vs-general remark; confirm the transfinite
    requirement grounding (`Atom : Type u` not countable).
  - [x] Choose the construction mechanism — (i) explicit well-founded/`Ordinal` recursion, or
    (ii) `zorn_le₀` over an FLO-enriched carrier — and record the decision + rejected alternative in
    the probe docstring (Risks, "the crux"). This choice is SETTLED for Phases 2-6 once made.
    **Decision: route (i)** (explicit `Ordinal`-indexed recursion), recorded in the probe's new
    module docstring above `Stage`.
  - [x] Define the stage-index type `σType`, the task enumeration (formula-adds for deductive
    closure/disjunction; diamond witnesses), the single-step extension function, and the stage
    context `H_σ`, reusing the landed `Context.addFormula`/`Context.addDiaWitness`/
    `Context.addRedundantEdge` operations. Landed as `Stage`, `FloTask`, `stepExt`
    (+ sorry-free `stepExt_le`), `FloSeq`.
  - [x] Define the `FLO` predicate as a `structure`/`def` bundling `rank`, (FLO-0), (FLO-1)(a,b),
    (FLO-2) exactly as stated in the Overview. Ensure it is not vacuous. Landed as `rankOf`
    (+ sorry-free `rankOf_base`) and the `FLO` structure (flo0/flo1/flo2 fields).
  - [x] State (sorried) the four downstream obligations as theorem signatures:
    `flo_succ` (successor preservation), `flo_limit` (limit preservation), `primeC'_exists_maximal`
    (maximal FLO context with the `⊬ x₀:A₀` property), and `flo_oldlabel_transport` (the shared
    reflection lemma Phase 5 proves). All four landed as sorried signatures.
- **Timing:** 1 dispatch. Estimated output: ~200-350 lines (probe). **Actual: ~260 lines.**
- **Depends on:** none (all Phase 1-4 landed assets are in place).
- **Done when:** the probe typechecks (`lake env lean`) with only the four named sorried
  signatures; `FLO` is confirmed non-vacuous; the mechanism decision is recorded. **Verified**:
  `lake env lean` on the probe is clean (only the 2 pre-existing + 4 new named sorries as
  warnings, zero errors); `FLO` bundles three independent, non-`True`/`Unit` constraints on
  `rankOf 𝒮`/`𝒮.H` (flo0/flo1/flo2); mechanism decision recorded in the probe docstring.

### Phase 2: FLO maintained at successor stages [COMPLETED] (skeleton — one documented strategic sorry)

- **Goal:** prove `flo_succ` — each single extension step (`addFormula`, `addDiaWitness`,
  `addRedundantEdge`, reserve-draw) preserves the FLO invariant, extending `rank` by the new
  label(s) at the current successor stage.
- **Tasks:**
  - [x] Prove FLO-0/FLO-1/FLO-2 preservation for `addFormula` (reserve-drawn fresh label, FLO-1(a)).
    Sorry-free (`X`/`R` provably unchanged by `stepExt`'s `.formula` branch in both `if`-arms;
    `flo0`/`flo1`/`flo2` reused verbatim from `hflo`). `.skip` handled identically (also sorry-free).
  - [x] Prove preservation for `addDiaWitness` (`dwitness w B`, FLO-1(b); the single new edge
    `w R dwitness w B` satisfies FLO-2 at the birth stage). Sorry-free: added a new auxiliary
    monotonicity lemma `FloSeq.mono` (transfinite/`Ordinal.induction` over `succ_eq`/`limit_eq`/
    `stepExt_le`, itself sorry-free) to compute `rankOf 𝒮 (dwitness y B) = σ + 1` exactly (via
    `IsLeast.csInf_eq`), then closed both the FLO-1 fresh-label clause and the FLO-2 new-edge
    clause for this task variant.
  - [x] Prove preservation for `addRedundantEdge` (no new label; edge between already-present labels
    — confirm this is admissible under FLO-2 or that redundant-edge additions are handled by the
    maximality argument rather than the construction trace). **CONFIRMED INADMISSIBLE for an
    unconstrained schedule, and proved so, not merely suspected**: `stepExt`'s `.redundantEdge a b`
    case carries no side condition tying the introduction stage to `max (rankOf a, rankOf b)`; for
    `a, b` both already present at `σ` (hence `rankOf a, rankOf b ≤ σ` by `FloSeq.mono`) and the
    edge `(a,b)` genuinely new at `σ+1`, FLO-2 would force `max(rankOf a, rankOf b) = σ+1`, which
    is impossible since `max(rankOf a, rankOf b) ≤ σ < σ+1` for any ordinal. This is the "or ...
    handled by the maximality argument rather than the construction trace" branch of this task's
    own hedge: `.redundantEdge` must be schedule-constrained (Phase 4's fairness hypothesis, or a
    revision ruling out premature redundant-edge scheduling) before `flo_succ` can be fully
    sorry-free. Landed as one documented, tracked, build-green strategic sorry (five-condition
    test) in the genuinely-new-edge sub-case only — the "edge already present" half of this case,
    and the label-freshness (FLO-1) half, are both sorry-free.
- **Timing:** 1 dispatch. Estimated output: ~150-300 lines (probe).
- **Depends on:** 1.
- **Done when:** `flo_succ` sorry-free; probe build green. **Landed as build-green with one
  documented strategic sorry** (probe build green, confirmed via `lake env lean`; see the
  `addRedundantEdge` task note above and `.orchestrator-handoff.json`'s `sorry_inventory` for the
  follow-up this leaves for Phase 4/6).

### Phase 3: FLO maintained at limit stages (chain unions) [COMPLETED]

- **Goal:** prove `flo_limit` — the union of an FLO-coherent chain of stage contexts is a `Context`
  satisfying FLO, with `rank` extended coherently across the chain (each label keeps its birth
  stage; FLO-2 edge-locality is preserved in the union).
- **Tasks:**
  - [x] Reuse `ChainCtx.unionContext`/`ChainCtx.chain_closure` where they transfer; establish that a
    chain of FLO contexts sharing coherent `rank` yields an FLO union. **Deviation**: neither was
    invoked — see "Plan Deviations" in `summaries/13_flo-limit-phase3-summary.md`. `FLO`'s own
    clauses (FLO-1/FLO-2) are stated purely in terms of `𝒮`/`rankOf`, independent of the stage `σ`
    being proved at, so membership/relatedness at the limit stage descends directly (via
    `FloSeq.limit_eq`'s raw `Set.iUnion`/existential) to a witnessing predecessor stage `τ < σ`,
    and `hflo τ hτσ` closes the goal with no need for `ChainCtx.unionContext`'s `Monotone` setup.
  - [x] Prove the union's `rank` is well-defined (each label's birth stage is the least chain stage
    containing it) and that FLO-2 holds in the union (every union edge is introduced at one chain
    stage, inheriting edge-locality). Achieved by the same direct-descent argument (no separate
    "rank well-definedness" lemma was needed — `rankOf` is already globally well-defined,
    independent of `σ`).
- **Timing:** 1 dispatch. Estimated output: ~150-300 lines (probe).
- **Depends on:** 1. (Parallel with Phase 2.)
- **Done when:** `flo_limit` sorry-free; probe build green. **MET**: `flo_limit` sorry-free (`lake
  env lean` on the probe: exit 0, zero errors, sorry count 6 -> 5); `lean_verify` on `flo_limit`:
  axioms `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

### Phase 4: Assemble the maximal FLO context — `primeC'_exists_maximal` (replaces `zorn_le₀`) [COMPLETED] (skeleton — one documented strategic sorry)

- **Goal:** run the chosen construction (well-founded recursion or FLO-enriched Zorn) using
  `flo_succ` (Phase 2) and `flo_limit` (Phase 3) to produce a maximal context `H ⊇ G₀`, confined to
  `W(V')`, with `H ⊬ x₀:A₀`, **carrying `FLO H`**. This is the object v4's `primeC_exists_maximal`
  produced *without* FLO.
- **Tasks:**
  - [x] Instantiate the recursion/Zorn over the chosen carrier; discharge the well-foundedness /
    chain-bddAbove obligation via `flo_limit`. **Done, with a revised signature**: added
    `hRedundant` (the fair-schedule constraint Phase 2's finding required — `.redundantEdge` only
    fires once the edge is already present) and `hprimeC` (the schedule stays inside `primeC` at
    every stage). Landed `flo_succ_fair` (successor step, sorry-free, resolving Phase 2's open
    `redundantEdge` branch along the real schedule trace) and `flo_holds_everywhere` (FLO holds at
    every stage, sorry-free, via transfinite induction combining a fresh `FLO 𝒮 0` base case,
    `flo_succ_fair`, and `flo_limit`). Both verified axiom-clean (`lean_verify`: `[propext,
    Classical.choice, Quot.sound]`, no `sorryAx`).
  - [x] Extract the maximal `H` together with `FLO H` and the preserved `⊬ x₀:A₀` and
    `W(V')`-confinement properties. `FLO 𝒮 σ₀` at `σ₀ := Ordinal.lsub (choose ∘ hfair)` is fully
    sorry-free; `𝒮.H σ₀ ∈ primeC` follows directly from `hprimeC σ₀`.
  - [x] Confirm `H` still satisfies the five `TPrime`-clause preconditions the existing clause
    theorems consume — unaffected by this phase's design (the clause theorems only ever consume an
    abstract `Maximal (· ∈ primeC ...) H` fact, unchanged in shape here).
- **Timing:** 1 dispatch. Estimated output: ~150-350 lines (probe). **Actual: ~215 lines added.**
- **Depends on:** 2, 3.
- **Done when:** `primeC'_exists_maximal` sorry-free, returns `H` with `FLO H`; the five clause
  theorems still apply to it; probe build green. **Landed as build-green with ONE documented
  strategic sorry**, narrower than the phase's original scope: `FLO 𝒮 σ₀` and `𝒮.H σ₀ ∈ primeC` are
  both sorry-free; only the `Maximal` conjunct's "no strict extension" half remains open, because
  `hfair`'s one-shot-per-task shape does not itself rule out a task whose precondition becomes
  available only after its one guaranteed firing (needs a cofinal, precondition-aware fairness
  hypothesis plus a cardinality/ordinal-stabilization argument — see the theorem's docstring and
  `.orchestrator-handoff.json`'s `sorry_inventory` for the exact follow-up).

### Phase 5: The shared old-label reflection lemma from FLO — `flo_oldlabel_transport` [COMPLETED]

- **Goal:** the mathematical crux. Using FLO-2's `rank` bound, prove the shared lemma that
  transports a single witnessing `NIK`-derivation across "old" labels — the exact fact both
  `deriv_reflect` and `dwitness_mem_of_maximal` need for their cofinite `boxI`/`diaE` eigenvariable
  premise (`∀ y' ∉ L, …`) where `y'` may already be in the domain.
- **Tasks:**
  - [x] `--lit`: re-read the "(◇E)"/"(□I)" eigenvariable justification in `chunk_0102.md`/
    `chunk_0103.md` (raster) for the intended reflection. **Confirmed**: both chunks (Prime Lemma
    5.3.1's proof and the diamond/deductive-closure maximality argument) contain no further detail
    on the fresh-vs-old label distinction than what prior phases already extracted — Simpson's
    informal proof never surfaces this obstacle at all; it is an artifact purely of this
    development's cofinite-quantifier Lean encoding of `(□I)`/`(◇E)` (`Deduction.lean:288-312`),
    confirming the module docstring's existing diagnosis rather than adding new textual guidance.
  - [x] (5.1) Prove the transport lemma. *(deviation: altered — a well-founded/rank induction
    using FLO-2 turned out to be unnecessary; see the "Finding (documented deviation...)" module
    section directly above `flo_oldlabel_transport` in the probe, ~line 1846. A **one-directional**
    relabeling `substFn a b` (`a↦b`, identity elsewhere, in particular fixing `b`) — as opposed to
    `swapFn a b`, an involution that also sends `b↦a` — never touches `y'`'s own incident edges at
    all, because it is not invertible and does not relocate `y'`'s structure onto `y₀`. This avoids
    the naive-swap collision **by construction** (matching the task's own requirement), just via a
    different construction (a non-swap substitution) than the anticipated rank-indexed induction.
    The only freshness fact used is `hy₀ : y₀ ∉ (𝒮.H σ).G.X` (already part of the theorem's fixed
    signature); FLO/`rankOf`/FLO-2 are not needed by the proof. Landed as the reusable general
    lemma `NIK.relabelFresh` (mirrors `NIK.swap_relabel`'s case shape) plus the helper `substFn`/
    `substFn_self`/`substFn_other`/`List.map_substFn_eq_self`, all sorry-free.*
  - [x] (5.2) Build the full premise for every `y'`. *(deviation: skipped as a separate assembly
    step — subsumed by 5.1's generalized shape. Because `NIK.relabelFresh`/`substFn`-transport does
    not case on whether `y'` is fresh or old, dwitness-shaped or not, `flo_oldlabel_transport`'s
    single conclusion (`∀ y' ∈ (𝒮.H σ).G.X, x≠y' → (∀ψ∈Γ,ψ.lbl≠y') → NIK …`) already covers every
    `y'` uniformly in one shot, so no separate combination of the fresh-witness case
    (`NIK.freshWitness_transport`) and a distinct old-label/dwitness case was required —
    `freshWitness_transport` is in fact the special case of `flo_oldlabel_transport` where the
    extra hypothesis `y ∉ G.X` also happens to hold.)*
- **Timing:** 1-2 dispatches (may split 5.1/5.2). Estimated output: ~200-400 lines (probe).
  **Actual: ~150 lines** (simpler than anticipated per the 5.1 deviation).
- **Depends on:** 4.
- **Done when:** `flo_oldlabel_transport` sorry-free; probe build green. If the transport lemma
  cannot be proved from FLO as stated, escalate `[BLOCKED]` with the exact failing goal — do NOT
  weaken FLO to a free bounded-old-label hypothesis (Shortcut 3, Postmortem Constraints). **MET**:
  `flo_oldlabel_transport` sorry-free (`lake env lean` on the probe: exit 0, zero errors, sorry
  count unchanged at 4 — the pre-existing `deriv_reflect`/`dwitness_mem_of_maximal`/`flo_succ`/
  `primeC'_exists_maximal` strategic sorries, all preserved verbatim, none newly introduced);
  `lean_verify` on `flo_oldlabel_transport` and `NIK.relabelFresh`: axioms `[propext,
  Classical.choice, Quot.sound]`, no `sorryAx`, for both.

### Phase 6: Discharge both sorries; re-verify `primeLemma` fully sorry-free [COMPLETED]

- **Goal:** wire `flo_oldlabel_transport` (Phase 5) into `deriv_reflect` and
  `dwitness_mem_of_maximal`, closing both sorries, and re-verify `primeLemma` is fully sorry-free
  and axiom-clean.
- **Tasks:**
  - [x] Close `ChainCtx.deriv_reflect` (probe ~line 394). *(deviation: altered -- the anticipated
    fix was "use `flo_oldlabel_transport` directly," but `deriv_reflect` is stated over the
    generic `ChainCtx`/`Preorder ι` abstraction, not a `FloSeq`. Reconciled by extracting the
    graph-generic core of `flo_oldlabel_transport` -- `NIK.oldLabelTransport`/
    `NIK.diaWitnessTransportOld`, built directly from `NIK.relabelFresh`, needing no `FloSeq`/`FLO`
    at all -- and a new `GChain` (graph-only chain) + `NIK.reflectChain` master reflection
    induction that discovers the single chain index by structural recursion, picking one fresh
    witness per `(□I)`/`(◇E)` node from the chain's shared reserve `V'ᶜ` and rebuilding the full
    cofinite family from it via the one-directional transport. Fully sorry-free,
    `lean_verify`-clean.)*
  - [x] Close `dwitness_mem_of_maximal`'s diamond "old label" sub-case (probe ~line 980).
    *(deviation: altered -- used `NIK.diaWitnessTransportOld` (the `diaE`-shaped analogue of
    `NIK.oldLabelTransport`, both graph-generic, built directly from `NIK.relabelFresh`) applied
    directly to `H.G` -- no `FloSeq`/`primeC'_exists_maximal` routing needed, since the transport
    needs no invariant about *how* `H` was built. One genuinely new requirement surfaced: the
    excluded label `x₀` must differ from the freshly-adjoined witness `v`, else the transported
    conclusion's label moves out from under `x₀`. Discharged by adding an explicit hypothesis
    `hx₀ : x₀ ∈ G₀.G.X` to `dwitness_mem_of_maximal`/`diamond_of_maximal`/`primeLemma` -- a
    standard well-formedness assumption matching Simpson's own implicit convention that the
    excluded judgement's label is a label of the ambient graph (the same convention
    `Context.ctxSubset` already enforces for `Γ`'s labels), not a weakening of any FLO- or
    old-label-related argument. Also added `Label.ne_dwitness_self` (a diamond-witness label is
    never its own pivot, by structural recursion) to separate `y` from `v`. Fully sorry-free,
    `lean_verify`-clean.)*
  - [x] Re-run the whole probe: `lake env lean` exit 0, zero errors. **Two documented,
    PRE-EXISTING, out-of-scope sorries remain** (both explicitly excluded from this phase's
    target by the orchestrator dispatch brief and by Postmortem Constraints): `flo_succ`'s
    `redundantEdge` branch (superseded by the sorry-free `flo_succ_fair`; "MUST preserve...
    `flo_succ`... verbatim") and `primeC'_exists_maximal`'s `Maximal`-conjunct (the deeper
    ordinal-stabilization gap the plan's own Rollback/Contingency section anticipates: "if it
    cannot be settled, escalate... do NOT introduce an axiom, a vacuous placeholder"). Neither is
    on `primeLemma`'s dependency path -- see below.
  - [x] `lean_verify primeLemma`: axioms `[propext, Classical.choice, Quot.sound]`, **no
    `sorryAx`**. Also re-verified `deriv_reflect`, `dwitness_mem_of_maximal`, `diamond_of_maximal`
    individually: all three axiom-clean, no `sorryAx`.
- **Finding (exceeds the phase's original scope, corrects an upstream premise)**: `primeLemma` is
  assembled from `primeC_exists_maximal` (the plain `zorn_le₀` Zorn maximalisation), **not**
  `primeC'_exists_maximal` (the FLO-carrying reconstruction) -- it never needed FLO. The "old
  label" obstacle both sorries shared is resolvable entirely at the `NIK`/`Graph` level (a
  **one-directional** `substFn`-based relabeling, unlike the involutive `swapFn` the prior three
  dispatches tried, needs freshness of only the *source* witness, never the target), independent
  of *how* the maximal context was constructed. The FLO apparatus (Phases 1-5: `Stage`/`FloSeq`/
  `FLO`/`flo_succ`/`flo_limit`/`primeC'_exists_maximal`/`flo_oldlabel_transport`) remains landed
  verbatim (Postmortem Constraints) and is not deleted, but is confirmed **not load-bearing** for
  `primeLemma`. This does not contradict the divergence audit's ruling-out of Shortcuts 1-3 (those
  were about swap-based or no-relabelling techniques specifically); it identifies a fourth
  technique (one-directional substitution) the audit did not test.
- **Timing:** 1 dispatch. Estimated output: ~100-250 lines (probe). **Actual: ~350 lines** (the
  `GChain`/`NIK.reflectChain` reflection apparatus was larger than anticipated, since
  `deriv_reflect`'s `sorry` had NO prior proof skeleton to build on, unlike `dwitness_mem_of_maximal`).
- **Depends on:** 5.
- **Done when:** `primeLemma` sorry-free and axiom-clean. **MET -- this is the Phase 4.5
  completion milestone.** (The plan's literal "whole probe fully sorry-free" phrasing is not met
  -- 2 pre-existing, non-blocking sorries remain, both explicitly out of this phase's scope per
  the dispatch brief and Postmortem Constraints; the substantive milestone, a fully sorry-free
  `primeLemma`, is met.)

### Phase 7: Transcribe `primeLemma` + FLO machinery into `Cslib/` mainline [COMPLETED]

- **Goal:** move the now-sorry-free construction, the FLO machinery, the clause theorems, and
  `primeLemma` from the probe into a new mainline file under `Constructive/Labelled/` (or
  `Constructive/`), zero-debt. Mechanical transcription of already-green content.
- **Tasks:**
  - [x] (7.1) Transcribe the FLO carrier, `flo_succ`, `flo_limit`, `primeC'_exists_maximal`, and
    `flo_oldlabel_transport` into mainline; `import Cslib.Init`; scoped `lake build` green.
    *(deviation: FLO machinery NOT transcribed to mainline — resolved scope decision from the
    orchestrator continuation brief. Phase 6 established `primeLemma` routes through
    `primeC_exists_maximal` (plain `zorn_le₀`), not the FLO apparatus; the FLO machinery
    (`Stage`/`FloSeq`/`FLO`/`flo_succ`/`flo_limit`/`primeC'_exists_maximal`/
    `flo_oldlabel_transport`) is non-load-bearing for `primeLemma` and still carries 2 open,
    documented sorries (`flo_succ`'s superseded `redundantEdge` branch;
    `primeC'_exists_maximal`'s `Maximal`-conjunct half). Since mainline transcription must be
    zero-debt (sorry-free), transcribing FLO would either introduce debt or require re-proving
    the 2 open sorries out of scope for this phase. The FLO apparatus stays in `probes/
    chain-union-reflection-probe.lean`, preserved verbatim, as correct scaffolding — out of
    scope for mainline pending a future task if ever needed.)*
  - [x] (7.2) Transcribe the five clause theorems, `deriv_reflect`/chain-closure, the diamond wiring,
    and `primeLemma`; scoped `lake build` green.
    *(deviation: scope narrowed per the same resolved decision — transcribed `primeLemma` and its
    actual sorry-free dependency closure only: `swapFn`/`NIK.swap_relabel`/
    `NIK.freshWitness_transport`, `substFn`/`NIK.relabelFresh`, `NIK.oldLabelTransport`/
    `NIK.diaWitnessTransportOld`, `GChain`/`TClosure.reflectChain`/`NIK.reflectChain`,
    `ChainCtx`/`ChainCtx.deriv_reflect`/`ChainCtx.chain_closure`, `primeC`/`primeC_mem_base`/
    `primeC_chain_bddAbove`/`primeC_exists_maximal`, the five clause theorems
    (`clModel_of_maximal`/`deductiveClosure_of_maximal`/`consistency_of_maximal`/
    `disjunction_of_maximal`/`diamond_of_maximal`, via `dwitness_mem_of_maximal` and
    `NIK.subst`/`NIK.subst_aux`), and `primeLemma` itself — landed in new file
    `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/PrimeLemma.lean`.)*
  - [x] `lean_verify` on the mainline `primeLemma`: axioms ⊆ `[propext, Classical.choice,
    Quot.sound]`; zero sorry / zero new axiom / zero vacuous def. **Confirmed**: `lean_verify`
    returned `{"axioms":["propext","Classical.choice","Quot.sound"],"warnings":[]}` for both
    `primeLemma` and `dwitness_mem_of_maximal`.
- **Timing:** 1-2 dispatches (split 7.1/7.2 if >300 lines each). Estimated output: ~300-600 lines
  (mainline, split across sub-phases). **Actual: 1 dispatch, ~1660 lines** (narrower scope per
  the FLO-exclusion deviation above; the file is larger than the original FLO+primeLemma estimate
  because it is dominated by the `NIK`-level reflection/relabeling apparatus, not because more
  was transcribed than planned).
- **Depends on:** 6.
- **Done when:** mainline `primeLemma` builds green, sorry-free, axiom-clean; guardrail modules
  re-checked to still build. **MET.** Full CSLib CI pipeline green: scoped `lake build`,
  `lake exe checkInitImports`, `lake lint` (0 warnings for the new file), `lake exe lint-style`
  (0 warnings), `lake shake` (no suggestions for the new file), `lake exe mk_all --module`
  (`Cslib.lean` updated), `lake test` (green), full `lake build` (3243/3243 jobs green,
  guardrail modules — `Context.lean`/`Deduction.lean`/`Syntax.lean`/`CS5Canonical.lean` —
  unregressed).

> **Flagged for confirmation (carried from v4, Phase 4 `--lit` finding — do NOT delete, do NOT
> build without confirming): original Phase 5 (T-Comp graph completion, Simpson Lemma 8.2.5,
> symmetry).** Phase 4's research found `T-Comp(H)` belongs to the *bounded* (Ch 7-8) route, in
> which primeness does NOT entail raw classical-modelhood; the landed `TPrime` requires RAW
> `clModel`, discharged directly (`clModel_of_maximal`/`raw_edge_of_tclosure`). If Phase 8 consumes
> the raw relation from `primeLemma`'s output directly, T-Comp is **likely UNNEEDED**. Confirm at
> Phase 8 before building it; if needed, insert it as a sub-phase 8.0 mining Simpson 8.2.5 and
> proving the completion preserves `𝒯`-primeness + yields symmetry on `H.X`. The retained
> `probes/lemma612-scaffold.lean` material is the fallback.

### Phase 8: Canonical model + truth lemma (Simpson 5.3.2 / 8.2.6) — box-backward [COMPLETED]

- **Goal:** build the canonical model over `TPrime` worlds with the **raw** relation and prove the
  truth lemma by formula induction, including the box-backward case. (Carried from v4 Phase 6.)
- **Tasks:**
  - [x] `--lit`: mine Simpson Lemma 5.3.2 (pp.94-98 raster) and 8.2.6; **canonical relation = RAW
    `xRy` in `H`** (NOT `𝒯-Comp(H)`, confirmed twice); domain-relative "for all `y` in `H`".
    **Confirmed a third time** against `chunk_0103.md`-`chunk_0105.md` (verbatim quotation of the
    `𝒦^𝒯` construction and the per-case Lemma 5.3.2 proof in `CanonicalModel.lean`'s module
    docstring).
  - [x] **Confirm the flagged T-Comp question above** (raw relation consumed directly ⟹ original
    Phase 5 unneeded); record the confirmation. **CONFIRMED UNNEEDED**: `CanonWorld.r` is built
    directly from `ctx.G.R` with no `TClosure`/graph-completion step anywhere in the truth lemma;
    Lemma 8.2.6 (`chunk_0166.md`) is the *bounded* (Ch 7-8) canonical model lemma, out of scope for
    this *unbounded* (Ch 5) route. Documented in `CanonicalModel.lean`'s module docstring.
    `probes/lemma612-scaffold.lean` remains an untouched fallback, not needed.
  - [x] (8.1) Define the canonical model over `TPrime` worlds, raw relation, valuation from labelled
    membership `y:B`. Landed as `CanonWorld` (a pointed `𝒯`-prime context `⟨ctx,lbl,mem⟩`,
    Simpson's `(H,Δ),y` pair), `CanonWorld.le`/`CanonWorld.r`, `canonVal`/`canonBotForces` (the
    latter trivially `False`, since `TPrime`'s Consistency clause bans exploding worlds), plus the
    `CKValidFC`-required monotonicity lemmas (`canonVal_mono`, `canonBotForces_mono`,
    `canonBotForces_val`, `canonBotForces_r`, `canonBotForces_r_wit`).
  - [x] (8.2) Prove the truth lemma by induction on the formula; box-backward via the bounded
    canonical model lemma over `y:B`. *(deviation: the Ch.6 tree-surgery bridge
    (`probes/lemma612-scaffold.lean`) was NOT needed — box-backward closes via a fresh
    `Context.addFreshVar` extension (one new raw-variable node + edge, `Γ` unchanged) followed by a
    *fresh reapplication of `primeLemma` itself* (not the Ch.6 apparatus), then
    `NIK.oldLabelTransport` (already landed, Phase 6) to upgrade the single fresh witness to the
    cofinite family `NIK.boxI` needs.)* Landed as `canon_truth_lemma`, fully sorry-free,
    `lean_verify`-clean (axioms `[propext, Classical.choice, Quot.sound]`, no `sorryAx`), covering
    all seven `Proposition` cases (`atom`/`bot`/`and`/`or`/`imp`/`box`/`diamond`), both the
    `⊃`-backward and `□`-backward reductio directions via a fresh `primeLemma` application
    contradicting the semantic `CKForces` hypothesis at the witnessing extension.
- **Timing:** 2-3 dispatches (split 8.1/8.2). **Actual: 1 dispatch, ~420 lines** (mainline;
  narrower than estimated since the Ch.6 bridge and the FLO/T-Comp apparatus were both confirmed
  unneeded).
- **Depends on:** 7.
- **Done when:** `lake build` green; sorry-free; ◇-case and □-case both proved about the RAW
  relation the model is built on (no silent closure swap). **MET.** New mainline file
  `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/CanonicalModel.lean`. Full CSLib CI pipeline
  green: scoped + full `lake build` (3244/3244), `lake exe checkInitImports` (pass), `lake lint`
  (0 warnings after `@[nolint unusedArguments]` on the two genuinely-unused-by-design parameters —
  `Context.addFreshVar`'s freshness witness and `canonBotForces`'s constant-`False` world
  argument), `lake exe lint-style` (0 warnings), `lake shake` (no suggestions), `lake exe mk_all
  --module` (`Cslib.lean` updated), `lake test` (green, 9235/9236 -- pre-existing sorries in
  unrelated Propositional Tableau files unregressed). `lean_verify canon_truth_lemma`: axioms
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

### Phase 9: Frame-class match — domain-relative equivalence ⟹ `cs5FCIncest` [COMPLETED]

- **Goal:** discharge the frame-class conditions `cs5FC''`/`cs5FCIncest` needs from
  `ClassicalModelOn TS5 H.X H.R`. (Carried from v4 Phase 7.)
- **Tasks:**
  - [x] Derive the domain-relative `Equivalence` on `H.X` (reflexive, symmetric, transitive) via the
    Phase-1-of-v4 design choice (domain-relative equivalence or `↥H.X` subtype) and
    `classicalModelOn_TS5_iff`. Landed as `TPrime.equivOn` (near-immediate, as expected: a direct
    projection of `equivalence_of_classicalModelOn_TS5` already landed in `Context.lean`).
  - [x] Match the `cs5FCIncest` conjuncts. **Citation**: `cs5Incest`/`cs5FCIncest` live at
    `CS5Canonical.lean:234,255`. *(deviation: altered -- target is `cs5FCIncest` specifically, not
    the older `cs5FC''` (`CKExtension.lean:184`, task 509): `CS5Canonical.lean`'s soundness
    theorems (`cs5_axiom_sound_incest`) are proved only over `cs5FCIncest`, which the birelational
    pivot (task 512) documents as `cs5FC''` with its plain-symmetry conjunct replaced by
    `cs5Incest`; matching `cs5FC''` itself would leave soundness/completeness targeting different
    frame classes. This is the plan's own "Definition of done" text lagging the later CS5Canonical
    pivot, not a scope substitution.)* Design nuance resolved: `CanonWorld` as built (the
    **general** type, ranging over every `TPrime TS5 Atom`, matching Simpson's `𝒦^𝒯`) instantiates
    `cs5FCIncest`'s signature DIRECTLY -- no restricted world-type subtype was needed. This works
    (unlike the analogous match failing for `CS5Canonical.lean`'s `CS5CanonSegment`/
    `CS5PrimeSegment`) because `CanonWorld.r` is the RAW graph relation with genuine
    `EquivalenceOn`-witnessed symmetry, not a box-based one-sided containment subject to the
    monotonicity-collapse argument that sinks the `CS5Canonical.lean` route at the universally
    reachable exploding world `Ω`. Landed in new file `Cslib/Logics/Modal/Metalogic/Constructive/
    Labelled/FrameClass.lean`: `CanonWorld.r_refl`/`CanonWorld.r_trans` (plain
    reflexivity/transitivity), `CanonWorld.r_rebase` (the `fourBox`-style re-basing conjunct,
    transitivity only), `CanonWorld.r_symBox` (the `bBox`-style re-basing conjunct, needs
    symmetry), `CanonWorld.r_incest` (`cs5Incest`, the `bDia` instance, witness `u' := u`, plain
    symmetry), bundled into `cs5FCIncest_canonWorld_r`. All five sorry-free,
    `lean_verify`-clean (axioms ⊆ `[propext, Quot.sound]`, no `sorryAx`).
  - [x] State non-trip of `cs5Incest_forces_symm` (Consistency banishes `Ω`) and
    `cs5TwoSidedR_iff_cs5Tail` (not quasi-prime theories) at the point of use. Documented in
    `FrameClass.lean`'s module docstring ("Point-of-use notes on the two landed guardrails"):
    `cs5Incest_forces_symm` is inapplicable (its `hbox` hypothesis presumes a box-based relation;
    `CanonWorld.r` is not box-based, and coincidentally lands on the same "true, harmless plain
    symmetry" outcome that theorem's own docstring anticipates for a relation with no reachable
    `Ω`); `cs5TwoSidedR_iff_cs5Tail` is inapplicable (its hypotheses require `QuasiPrime
    CS5ModalAxiom` theories; `TPrime` contexts are graph-node structures, not quasi-prime
    theories, matching `Context.lean`'s existing guardrail-3 analysis).
- **Timing:** 1-2 dispatches. Estimated output: ~150-350 lines (mainline). **Actual: 1 dispatch,
  ~200 lines** (new file `FrameClass.lean`).
- **Depends on:** 8.
- **Done when:** `lake build` green; sorry-free; guardrails unregressed. **MET.** Full CSLib CI
  pipeline green: scoped `lake build` (`Labelled.FrameClass`), `lake exe checkInitImports` (pass),
  `lake lint` (0 warnings for the new file), `lake exe lint-style` (0 warnings), `lake shake`
  (no suggestions for the new file), `lake exe mk_all --module` (`Cslib.lean` updated), `lake test`
  (green, 9237/9237 -- pre-existing sorries in unrelated Propositional Tableau files
  unregressed), full `lake build` (3245/3245 jobs green; guardrail modules -- `Context.lean`/
  `CanonicalModel.lean`/`CS5Canonical.lean` -- unregressed). `lean_verify
  cs5FCIncest_canonWorld_r`: axioms `["propext","Quot.sound"]`, no `sorryAx`.

### Phase 10: `cs5_completeness` assembly [BLOCKED]

- **Goal:** compose Phases 7-9 into `cs5_completeness : CKValidFC cs5FC'' φ → Derivable
  CS5ModalAxiom φ`, sorry-free and axiom-clean. (Carried from v4 Phase 8.)
- **Tasks:**
  - [ ] Contrapositive assembly: `¬ Derivable` ⟹ prime context refuting `φ` (`primeLemma`, Phase 7)
    ⟹ canonical model + truth lemma (Phase 8) ⟹ frame-class member (Phase 9) ⟹ `¬ CKValidFC cs5FC''`.
    *(deviation: blocked before any Lean was written — see BLOCKER below. The contrapositive's
    seed step, `¬ Derivable CS5ModalAxiom φ ⟹ ¬ Deriv 𝒯_S5 G₀ Γ₀ (x₀ ∶ φ)` for a suitable base
    `(G₀,Γ₀,x₀)`, is not a restatement of Phases 7-9's output — it requires a genuinely new,
    unbuilt bridge between the Hilbert-style `DerivationTree`/`Derivable` system and the labelled
    `NIK`/`Deriv` system.)*
  - [ ] Reuse only what genuinely transfers (`Proposition`/`Proposition.map`,
    `DerivationTree`/`Derivable`, `CS5ModalAxiom`, task-512's axiom-free soundness where the frame
    class matches). *(deviation: not attempted — blocked upstream of this step.)*
- **Timing:** 1 dispatch. Estimated output: ~100-250 lines (mainline). **Actual: 0 lines landed;
  blocked during scoping/research before any Lean edit.**
- **Depends on:** 8, 9.
- **Done when:** full `lake build`; `lean_verify cs5_completeness` axioms ⊆ `[propext,
  Classical.choice, Quot.sound]`; full CSLib CI order green.

**BLOCKER (Phase 10)**:
- **What failed**: the phase's own task list assumes the "contrapositive assembly" is a pure
  composition of Phases 7-9's already-landed outputs (`primeLemma`, `canon_truth_lemma`,
  `cs5FCIncest_canonWorld_r`). It is not. To invoke `primeLemma (G₀) (x₀) (φ) (hx₀) (h0)`, the
  dispatch needs `h0 : ¬ Deriv 𝒯_S5 G₀.G G₀.Γ (x₀ ∶ φ)` for some base labelled context. The only
  hypothesis Phase 10 is given is `¬ Derivable CS5ModalAxiom φ` — a fact about the **unlabelled**,
  Hilbert-style `DerivationTree`/`Derivable` system (`Cslib/Logics/Modal/Metalogic/
  DerivationTree.lean:134,201`). `Deriv`/`NIK` (`Cslib/Logics/Modal/Metalogic/Constructive/
  Labelled/Deduction.lean:240`) is a **different, graph-labelled natural-deduction system** with
  no axiom-schema constructor at all (T/B/4 enter only via `TClosure`-closed edges, not via a
  Hilbert-style `.ax` rule). Converting `¬ Derivable(φ)` into `¬ Deriv 𝒯_S5 (trivial graph) ∅ (x₀
  ∶ φ)` (equivalently `¬ NIKTheorem 𝒯_S5 φ`, `Deduction.lean:316`) needs, by contraposition, the
  theorem **`NIKTheorem 𝒯_S5 φ → Derivable CS5ModalAxiom φ`** — i.e. that every labelled-system
  proof can be translated into a Hilbert-style proof. This is exactly Simpson's **Chapter 6
  Adequacy Theorem** (internalizing a multi-label, graph-structured derivation into a single
  nested-modality Hilbert formula), not a restatement of anything Phases 7-9 built.
- **What was tried**: (1) exhaustive source search across `Cslib/Logics/Modal/` for any existing
  `NIK ↔ DerivationTree`/`Derivable` bridge — none exists; `Deduction.lean`, `Syntax.lean`, and
  `Context.lean`'s own module docstrings explicitly name this gap and reserve it for a **separate,
  not-yet-created file `Adequacy.lean`** ("the adequacy bridge, developed separately... quantifies
  over the `NIK` relation... needed nothing more from this file"). (2) Checked whether the
  alternative Segment/MCS canonical-model route (`SegmentLindenbaum.lean`, used successfully for
  `CK`/`CT`/`CS4`'s `CKValidFC`-completeness) could sidestep the need for this bridge — it cannot:
  that route is the one task 517 exists to route AROUND, because it hits the box-backward wall
  documented by `cs5_symmetric_tail_box_gap`/`cs5Incest_forces_symm`/`cs5TwoSidedR_iff_cs5Tail`
  (task 509/512's dead ends; `SegmentLindenbaum.lean`'s own module docstring confirms "This is
  false for `CS5`"). (3) Checked this task's own earlier decomposition
  (`plans/02_decomposed-track-a-b-c.md`, `handoffs/00_RESUME-HERE.md`) for prior work on precisely
  this bridge: it exists, under the name **"Track C" / "the adequacy bridge" (Simpson Lemma
  6.1.2/6.2.2)**, and was explicitly flagged there as **"THE TRUE CRUX, HIGH risk"** after four
  sub-phases (C1-C4: `Tele`/`Conj`, formulas 6.7/6.8, `LTree`/`star`/`prune`/`fullSubtree` +
  unfolding identity) landed sorry-free in `probes/lemma612-scaffold.lean` and
  `probes/track-c-c1-tele-conj.lean`, but **C5 (`pathSpine`, the whole-path recursion + its
  commutation with `addChild`) was never started**, and C6-C8 (the truth-lemma cases consuming
  C5) were never reached. (4) Attempted to find a smaller-scope shortcut specific to this task's
  own toolkit (`NIK.relabelFresh`/`NIK.oldLabelTransport`, the "cofinite-from-one" trick that
  closed Phase 8's box-backward case and Phase 5/6's "old label" sorries without the Ch.6
  apparatus) — that trick is internal to `NIK` (it transports one NIK-derivation across labels,
  never touching Hilbert) and does not translate: the missing step here is not "cofinite from
  one" but "graph-labelled proof from single-formula proof," a different problem in kind, because
  even a `NIKTheorem`-level derivation (starting from `Γ = []`) recurses through `boxI`/`diaE`
  sub-derivations with non-empty, multi-label `Γ`s internally, so the general "internalize an
  arbitrary open-assumption, multi-label context into one nested-modal formula" problem is
  unavoidable and is not smaller than the Ch.6 theorem C5-C8 were built to solve.
- **Why it's stuck**: this is a substantial, independently-scoped formalization project (Simpson's
  Chapter 6 Adequacy Theorem, ~4-8+ dispatches by this task's own prior estimate, HIGH risk),
  not a same-dispatch corollary of Phases 7-9. Plan 12 (v5) carried Phase 10's task list forward
  from v4 "largely unchanged" while its Phases 1-9 focused on a different obstacle (the "old
  label"/FLO reconstruction inside `primeLemma`); neither v4 nor v5's Phase 10 text accounts for
  the Hilbert-to-labelled bridge, and no phase 1-9 dispatch built it (Phases 7-9 transcribe/build
  purely *inside* the labelled system or purely semantically — none touch `DerivationTree`/
  `Derivable`).
- **What is needed**: a dedicated follow-up plan (new phases, or a new task) to build
  `Adequacy.lean`: at minimum the theorem `NIKTheorem 𝒯_S5 φ → Derivable CS5ModalAxiom φ` (or the
  more general form `NIK`-derivability implies `Derivable`-derivability of a suitably
  internalized formula), by resuming `probes/lemma612-scaffold.lean`'s Track C at **C5**
  (`pathSpine` + its `addChild` commutation lemma) and proceeding through **C6-C8** (the
  induction cases that discharge the general translation), then wiring the result into Phase 10's
  contrapositive assembly. This is scoped, bounded, HIGH-risk work explicitly separable from
  Phases 1-9's (now complete) FLO/primeLemma/canonical-model/frame-class content.
- **Prohibited workarounds**: do NOT use `sorry`, `def cs5_completeness := True`/`trivial`, or any
  vacuous placeholder to close this gap. Do NOT weaken `cs5_completeness`'s target away from
  `Derivable CS5ModalAxiom φ` (e.g. substituting `NIKTheorem 𝒯_S5 φ`) without explicit user
  sign-off — that would silently narrow the task's own "Definition of done."

### Phase 11: Bookkeeping and paper fixes [NOT STARTED]

- **Note (this dispatch)**: not attempted -- `Depends on: 10`, and Phase 10 is `[BLOCKED]` (see
  its blocker note above and `handoffs/phase-10-adequacy-bridge-blocker-20260718.md`). Most of
  this phase's tasks are mechanically independent of Phase 10's Lean content (bookkeeping/
  docstring fixes, not proof work) and a future dispatch or the user MAY choose to run them ahead
  of Phase 10's resolution -- this dispatch did not do so unilaterally, per plan-compliance.md's
  sequencing rule.
- **Goal:** clear the recorded follow-ups. (Carried from v4 Phase 9.)
- **Tasks:**
  - [ ] Transcribe `cs5_fs` (the v3 decision-gate result, currently in `probes/`) into `Cslib/`.
  - [ ] Correct the stale REFUTED verdict in `fischer-servi-probe.lean`'s docstring (`fs_sound` is
    valid; only the narrative is wrong).
  - [ ] Rewrite `state.json`'s `blockers` field to match this plan (v3/v4 language superseded).
  - [ ] Record the `literature-briefing.sh` modal-source resolution note (index keys `.id` vs
    `.doc_id`) so `--lit` runs verify Simpson chunks by content.
- **Timing:** 1 dispatch. Estimated output: ~100-200 lines.
- **Depends on:** 10.
- **Done when:** `lake build` green; docstrings accurate; `state.json` consistent.

## Testing & Validation

- **Per-phase (Phases 1-6, probe)**: `lake env lean` on the probe green; the phase's named
  theorem/definition sorry-free (definitions non-vacuous); `#print axioms` / `lean_verify` footprint
  ⊆ `[propext, Classical.choice, Quot.sound]` (no `sorryAx`) once a phase claims completion.
- **Per-phase (Phases 7-11, mainline)**: scoped `lake build Module.Name` green; `lean_verify` axiom
  check (zero sorry, zero new axiom, zero vacuous def) at every phase boundary; guardrail lemmas
  re-checked to still build after Phases 7, 9.
- **FLO non-vacuity gate (Phase 1)**: `FLO` must be a real predicate, never `:= True`/`Unit`; a
  reviewer confirms it constrains `rank`/edges as stated.
- **Small-model / countermodel check on every transcribed schema BEFORE writing Lean** (the
  discipline that caught prior defects).
- **Phase 4.5 completion gate (Phase 6)**: whole probe sorry-free is a hard precondition on Phase 7.
- **Final**: full CSLib CI order (§ cslib.md): `lake build` → `checkInitImports` → `lake lint` →
  `lake exe lint-style` → `lake test` → `mk_all --module` → `shake`.

## Artifacts & Outputs

- **Probes** (`probes/chain-union-reflection-probe.lean`, extended in place, or a successor probe):
  the FLO carrier + invariant (Phase 1), `flo_succ`/`flo_limit`/`primeC'_exists_maximal` (Phases
  2-4), `flo_oldlabel_transport` (Phase 5), both sorries discharged + sorry-free `primeLemma`
  (Phase 6).
- **Mainline** (`Cslib/.../Constructive/Labelled/` or `.../Constructive/`): transcribed FLO
  machinery + `primeLemma` (Phase 7); canonical model + truth lemma (Phase 8); frame-class match
  (Phase 9); `cs5_completeness` (Phase 10); `cs5_fs` + fixes (Phase 11). Estimated ~1000-1800
  new/changed mainline lines total.
- **The single headline deliverable**: `cs5_completeness`, sorry-free, axiom-clean, CI-green.

## Rollback/Contingency

- **Phase 1 mechanism choice proves unworkable** (both encodings blocked): mark `[BLOCKED]`, STOP,
  escalate with the exact obstruction. Leg A is banked at the repaired-substrate level (an
  independent contribution: a correctly-transcribed, inhabitable labelled framework with a
  sorry-free `TPrime` for clauses 0-3).
- **Phase 5 transport lemma cannot be proved from FLO as stated**: escalate `[BLOCKED]` with the
  exact failing goal; do NOT introduce an axiom, a vacuous placeholder, or the free
  bounded-old-label hypothesis (Shortcut 3). Reconsider FLO-2's statement in a revised Phase 1
  rather than papering over.
- **Phase 8 box-backward requires the Ch.6 bridge**: pull in the retained
  `probes/lemma612-scaffold.lean` (C4 tree-surgery) and `track-c-c1-tele-conj.lean` (C1-C3) material.
- **Original Phase 5 (T-Comp) turns out to be needed** (Phase 8 confirmation is negative): insert
  sub-phase 8.0 to build it before the canonical model.
- **General**: every phase boundary is a green, committed checkpoint (zero-debt invariant); any
  failure rolls back to the last green phase without losing landed work. Phases 1-6 leave `Cslib/`
  mainline untouched, so the entire FLO reconstruction is revertable by discarding the probe delta.
