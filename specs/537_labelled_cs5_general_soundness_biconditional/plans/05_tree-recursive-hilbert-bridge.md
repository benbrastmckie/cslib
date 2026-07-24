# Implementation Plan: General Labelled CS5 Soundness via the FAITHFUL Tree-Recursive Hilbert Adequacy Bridge (nik_TS5_soundness)

- **Task**: 537 - Prove the general labelled soundness direction, completing Simpson 1994 Thm 8.1.4's biconditional
- **Status**: IMPLEMENTING
- **Effort**: 12-20 hours remaining (Phases 1-7 + PD.1 landed; the concentrated remaining work is Simpson's full tree-recursive Ch.6 adequacy bridge, decomposed into four agent-run-sized steps 8.1-8.4)
- **Dependencies**: 517 (delivered completeness + anti-vacuity + landed Hilbert-side soundness `cs5_soundness_derivable_incest`)
- **Research Inputs**: reports/04_crosslabel-motive-audit.md (Tier 1, H4-verified; AUTHORITATIVE — selects the route, rates the P3 Hilbert bridge ~70% "known-shape" and the PD `efq` residual genuinely open), reports/03_tree-shape-invariant-audit.md, reports/02_direct-route-from-sources.md
- **Artifacts**: plans/05_tree-recursive-hilbert-bridge.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/plan-format-enforcement.md
  - .claude/context/formats/plan-format.md
  - .claude/context/contracts/wrap-up.md
  - .claude/context/contracts/reference-grounding.md
- **Type**: cslib
- **Plan version**: 5 (supersedes plans/04_hilbert-adequacy-bridge.md; commits to the FAITHFUL tree-recursive bridge after the v4 dispatches established that the two flattened shortcut translations fail and the direct PD `efq` residual is genuinely open)

## Overview

Prove `nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ` in the single file
`Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`, closing the soundness
direction (2⟹1) of Simpson Thm 8.1.4 for CSLib constructive CS5/IS5, by transcribing **Simpson's
faithful Ch. 6 labelled↔Hilbert adequacy construction** (Lemma 6.1.2, extended to `Ax(𝒯)` by
Thm 6.2.1 / Lemma 6.2.3) and composing it with the already-landed Hilbert-side soundness
`cs5_soundness_derivable_incest`.

### The decision this version resolves (route (a) over route (b))

Two dispatches under plan v4 seriously investigated both sanctioned routes and left the task
`[BLOCKED]` on each. The v4 recommendation (summaries/10) posed a binary replan fork:

- **(a)** Commit the budget to the Hilbert bridge's **full tree-recursive construction** (Phase 8;
  report 04 rates ~70% closable, ~300-600+ lines, **never actually attempted in Lean** — only two
  flattened shortcut variants were tried and refuted).
- **(b)** Accept Path PD's `efq` gap as **genuinely open**, requiring dedicated cut-admissibility /
  normalization research before further implementation, and terminate the task blocked-pending-research.

**This plan chooses (a).** The decisive reason, weighed critically against the phase-8.1
obstruction findings (commit `0172b639`):

> The Phase-8 obstructions documented in v4 are obstructions to two **flattened** translations
> (the "split-by-label flat" and "fully-boxed flat" variants) that deliberately collapsed
> Simpson's tree-depth indexing by exploiting `IKTB4`'s `□A ↔ □□A` box-collapse. They both broke
> at `orE`/`efq` for a reason intrinsic to the collapse (re-boxing a `T`-unboxed hypothesis;
> needing the non-theorem `□(A∨B) → □A ∨ □B`). They are **NOT** obstructions to Simpson's
> **faithful** Fig. 6-1/6-2 tree-recursive translation, which nests one `⊃□(...)` per tree level
> precisely so that each label carries its own box-depth and no cross-depth re-boxing is ever
> required. Simpson's Lemma 6.1.2 is a **complete, published theorem**; its entire purpose
> (§8.1.2, chunk 0158) is to route labelled derivations through Hilbert **so as to avoid the
> non-tree excursion** that dooms the direct semantic route (Path PD's `efq` residual). Therefore
> report 04's ~70% "known-shape, not open" rating for the full bridge **survives** the 8.1
> findings — the 8.1 findings only refute the shortcuts, which this plan does not retry — whereas
> Path PD's `efq` gap remains genuinely open. Route (a) is the only concrete, implementable route.

This plan **supersedes** `plans/04_hilbert-adequacy-bridge.md`. It preserves every landed asset:
the Phase 1-7 lemmas AND the PD.1 `bot_*` lemmas (commit `0172b639`, now given a purpose on the
critical path — they discharge the bridge's `efq` translation case) AND the corrected PD.2 motive
design writeup (retained as a documented asset for the route-(b) research task, should the bridge
itself overrun). All remain sorry-free, axiom-clean, and unregressed.

### Why the faithful construction, and what it costs

The v4 Phase-8 source pass (Simpson Ch. 6,
`~/Projects/Literature/simpson_1994_intuitionisticmodallogic/...reflowed.md:943-1073`) already
identified the exact target: this bridge is Simpson's Lemma 6.1.2 (`Γ ⊢_G x:A ⟹ (Γ⊢_G x:A)^T` a
theorem of `IK`, via the recursive tree-translation of Fig. 6-1/6-2), plus Theorem 6.2.1 /
Lemma 6.2.3's extension to `Ax(𝒯)` for `𝒯 = {χ_T, χ_B, χ_4}` (= `TS5` / `CS5ModalAxiom` = `IKTB4`).
The translation indexes by a label's **tree-depth from the root**, nesting one `⊃□(...)` per level.
This infrastructure does not yet exist anywhere in the codebase and is a genuinely large
transcription (v4 estimate: 300-600+ new lines: a tree/subtree accessor, a recursive translation
function, and the 12-constructor main adequacy lemma). This plan sizes it as **four sequential
agent-run-sized steps** (8.1-8.4) so no single dispatch is asked to produce the whole thing, and
each step lands a green, independently-committable Preserved Asset for the next.

### Definition of Done

`nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ` lands sorry-free and axiom-clean
in `Soundness.lean`; full `lake build` green; `lean_verify` on `nik_TS5_soundness` reports no
`sorryAx` and no new axioms; `lake lint` / `lint-style` / `shake` / `checkInitImports` / `test`
unregressed against the task-517 green baseline; the stale module-docstring `INTRACTABLE` /
`GATE-C` / "What remains" / "Fifth dispatch" notes retired.

**Sanctioned terminal alternative (intellectual-honesty clause).** Route (a) is a commitment, not
a certainty (report 04: ~70%). If the faithful tree-recursive construction ALSO genuinely overruns
budget across dispatches — a concrete, machine-checked obstruction in the translation function or a
constructor case, NOT a hand-waved "wall" — then the sanctioned terminal is a documented `[BLOCKED]`
handoff scoped to the precise overrun, with the landed assets (Phases 1-7 + PD.1 + any green 8.x
step) intact, build green, zero debt, and a **route-(b) research task recommended** (dedicated
cut-admissibility / `⊥`-locality research for `N_IK(𝒯)`; see Phase 11). **Never a `sorry`, never a
new axiom, never a return to the refuted connectivity-lemma / clique / exact-symmetry
decompositions, and never a retry of the two refuted flat-translation shortcuts.**

### Research Integration

This revision integrates no NEW research report (none was produced since plan v4); it re-weighs the
existing report 04 against the v4 Phase-8 and Phase-11 dispatch findings and commits to route (a).

- reports/04_crosslabel-motive-audit.md — AUTHORITATIVE, integrated since plan_version 4. Supplies:
  the verdict `nik_TS5_soundness` is true/provable; the H4 refutation of the connectivity-lemma fix;
  the diagnosis that `efq` is the direct-route residual and it is Simpson's "non-tree excursion";
  the ranked two-path recommendation (P3 Hilbert bridge ~70% LOW-risk primary, PD existential
  teleport ~35% HIGH-risk fallback); the concrete Phase-8 sequences; and the Tier-1
  source-to-implementation mapping (Simpson chunks 0151-0158, MMS Def 5.1). **This plan acts on
  report 04's primary recommendation (P3), now with the faithful construction rather than a
  shortcut.**
- v4 Phase-8 dispatch finding (plans/04 §Phase 8; commit `0172b639`) — establishes that the two
  flat-translation shortcuts fail at `orE`/`efq` and that the faithful tree-recursive translation
  (the route this plan takes) was not attempted. Integrated here as the evidence that route (a)'s
  residual risk is transcription-scale, not open-problem-scale.
- summaries/10_phase11-blocked-motive-redesign-summary.md — establishes that Path PD's `efq`
  residual is genuinely open (independently re-derived), justifying deprioritizing PD to the
  route-(b) research recommendation rather than the implementation fallback it was under v4.
- reports/03, reports/02 — LANDED outputs (Phases 1-7) carried forward as Preserved Assets.

### Preserved Assets

Complete, landed sorry-free / axiom-clean, MUST NOT regress. Namespace of the landed lemmas is
`Cslib.Logic.Modal.Labelled` (singular `Logic`; the file path uses `Logics`). Under the faithful
bridge, the forest/tree machinery (Phases 6-7) and PD.1's `bot_*` lemmas are **back on the critical
path**: the tree-depth index reuses the forest/height machinery, and PD.1 discharges the bridge's
`efq` translation case.

| Component | File:Line | Status | Verified |
|-----------|-----------|--------|----------|
| `cs5_completeness` | Completeness.lean:132 | [COMPLETED] | task 517 (2026-07-19) |
| `nik_TS5_consistent` (anti-vacuity) | Soundness.lean:848 | [COMPLETED] | task 517 / this task (2026-07-19) |
| `nik_soundness_onePoint` (12-constructor skeleton) | Soundness.lean:774 | [COMPLETED] | task 517 (2026-07-19) |
| `cs5FCIncest_lift` (= confluence direction F1) | Soundness.lean:322 | [COMPLETED] | task 517 (2026-07-19) |
| `ckforces_persistence` (upward closure) | Forcing.lean:122 | [COMPLETED] | task 517 (2026-07-19) |
| **`cs5_soundness_derivable_incest` (Hilbert soundness — bridge CRITICAL PATH)** | CS5Canonical.lean:359 | [COMPLETED] | task 517 (2026-07-19) |
| `box_iff_base` (Phase 1) | Soundness.lean:374 | [COMPLETED] | this task (2026-07-19) |
| `dia_iff_base` (Phase 1) | Soundness.lean:392 | [COMPLETED] | this task (2026-07-19) |
| `box_iff_TClosure` (Phase 2) | Soundness.lean:422 | [COMPLETED] | this task (2026-07-19) |
| `dia_iff_TClosure` (Phase 2) | Soundness.lean:437 | [COMPLETED] | this task (2026-07-19) |
| `cs5FCIncest_raise` (= confluence direction F2, Phase 3) | Soundness.lean:337 | [COMPLETED] | this task (2026-07-19) |
| `box_gives_here` (Phase 3) | Soundness.lean:349 | [COMPLETED] | this task (2026-07-19) |
| `boxI_raise_step` (Phase 4) | Soundness.lean:472 | [COMPLETED] | this task (2026-07-19) |
| `boxI_lift_star` (Phase 5) | Soundness.lean:604 | [COMPLETED] | this task (2026-07-19) |
| `IsDerivationForest` + `forest_trivial` + `forest_addEdge_fresh` (Phase 6) | Soundness.lean:713 | [COMPLETED] | this task (2026-07-19) |
| `ht_le_of_reflTransGen` / `raise_subtree` / `siblings_disjoint` / `boxI_lift_ancestor` / `boxI_lift` (Phase 7) | Soundness.lean | [COMPLETED] | this task (2026-07-19) |
| **`bot_backward` / `bot_iff_edge` / `bot_iff_TClosure` (PD.1)** | Soundness.lean | [COMPLETED] | this task (2026-07-24, commit `0172b639`) |

### Source-to-Implementation Mapping (H3, Tier 1)

BibKeys VERIFIED in `references.bib`: `Simpson1994` (`@phdthesis`),
`MarinMoralesStrassburger2021` (`@article`). Grounding from report 04 + the v4 Phase-8 source pass.

| Source | Prop / Location (chunk / reflowed line) | Lean Identifier | Role | Status |
|--------|-------------------------|-----------------|------|--------|
| Simpson1994 | Fig. 6-1/6-2 tree-depth-indexed translation `(·)^T` (reflowed 943-1073) | `nikTr` (translation function) | **the translation — Phase 8.1 (to land)** | to land |
| Simpson1994 | Lemma 6.1.2: `Γ ⊢_G x:A ⟹ (Γ⊢_G x:A)^T ∈ IK` (reflowed 943-1073) | `nik_adequacy` (main induction) | **the bridge core — Phases 8.2/8.3 (to land)** | to land |
| Simpson1994 | Thm 6.2.1 / Lemma 6.2.3: extension to `Ax(𝒯)`, `𝒯 = {χ_T,χ_B,χ_4}` = `IKTB4` | (axiom-set instantiation inside `nik_adequacy`) | matches `CS5ModalAxiom` | to land |
| Simpson1994 | §8.1.2 direct `N(𝒯)` has "unavoidable non-tree excursions"; route via Hilbert (0158) | (route selection) | motivates the bridge over the direct induction | ROUTE SELECTION |
| Simpson1994 | Thm 8.1.4, tree case (0151) | `nik_TS5_soundness` (goal) | `NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ` | **Phase 9 (to land)** |
| MarinMoralesStrassburger2021 | Thm 7.1 klmn-incestuality / Thm 7.2 direct birelational soundness | `cs5_soundness_derivable_incest` (CS5Canonical.lean:359) | Hilbert-side soundness, already `CKValidFC cs5FCIncest`-valued | LANDED (task 517) |

## Goals & Non-Goals

- **Goals**:
  - Transcribe Simpson's faithful tree-depth-indexed translation `(·)^T` (Fig. 6-1/6-2) as a Lean
    function `nikTr` over the landed forest/tree machinery (Phase 8.1).
  - Prove the main adequacy induction `nik_adequacy : NIK TS5 G Γ (x ∶ A) → Derivable CS5ModalAxiom
    (nikTr …)` across all 12 `NIK` constructors, split into the propositional+cross-label cases
    (Phase 8.2) and the modal cases (Phase 8.3).
  - Specialise to `nik_TS5_to_hilbert : NIKTheorem TS5 φ → Derivable CS5ModalAxiom φ` over
    `Graph.trivial` (Phase 8.4).
  - Assemble `nik_TS5_soundness` as the ~3-line corollary composing the bridge with
    `cs5_soundness_derivable_incest`; retire the stale docstring notes (Phase 9).
  - Keep every intermediate state green and committed (H9 wrap-up discipline; commit-per-green-substep).
  - Preserve all 17 landed asset rows above (no regression).
- **Non-Goals**:
  - Any change to the `Graph` structure, `cs5FCIncest`, `NIK`, the completeness direction, or the
    anti-vacuity certificate.
  - Re-planning any of the landed Phases 1-7 or PD.1.
  - Reviving the refuted connectivity-lemma / clique / exact-`r`-symmetry decompositions.
  - **Retrying either flat-translation shortcut** (split-by-label flat; fully-boxed flat) — both are
    machine-refuted at `orE`/`efq` (v4 Phase-8 finding). The faithful tree-depth-indexed translation
    is the ONLY sanctioned bridge shape.
  - Introducing a new `L_m` modified sequent system (the bridge targets the existing `Derivable
    CS5ModalAxiom` Hilbert system, not a new sequent calculus).
  - Implementing the direct PD existential-teleport induction (its `efq` residual is genuinely open;
    it is deferred to the route-(b) research recommendation in Phase 11).

## Postmortem Constraints

Binding rules for all implementation dispatches. Derived from the six prior blocked/partial
dispatches, the v4 Phase-8 and Phase-11 `[BLOCKED]` findings, report 04's audit, and the zero-debt
task constraints.

**Do NOT**:
- Do NOT retry either **flat-translation shortcut**. The "split-by-label flat" (`Cx` unboxed /
  `C¬x` single-boxed) fails at `orE`/`efq` by requiring re-boxing of a `T`-unboxed hypothesis; the
  "fully-boxed flat" (`□(BigConj Γ) → □A`) fails at `orE` by requiring the non-theorem
  `□(A∨B) → □A ∨ □B` (machine-refuted, v4 Phase-8, commit `0172b639`). Only Simpson's faithful
  tree-depth-indexed translation is sanctioned.
- Do NOT re-attempt the plan v3 direct `∀ρ` induction motive, NOR the PD existential-teleport
  motive, for the main theorem on THIS route. PD's `efq` residual is genuinely open (summaries/10,
  independently re-derived) and is deferred to the Phase 11 route-(b) research recommendation.
- Do NOT attempt to strengthen `IsDerivationForest` to a connectivity invariant (report 04 Finding 2,
  H4-refuted). The forest machinery is reused ONLY for its tree-depth / height / unique-parent
  content, which IS preserved.
- Do NOT weaken `NIK.efq`/`NIK.orE` to require `y ∈ G.X` (completeness needs the cross-label
  disconnected form; Deduction.lean:245-253 docstring; `PrimeLemma.consistency_of_maximal`).
- Do NOT introduce `sorry` anywhere under `Cslib/` — not "temporary", not "strategic" (a `sorry`
  scaffold used transiently inside `lean_multi_attempt`/a scratch buffer is fine ONLY if it is never
  written to the committed file). A genuinely blocked sub-goal routes to a `[BLOCKED]` handoff.
- Do NOT add any new `axiom` under `Cslib/`.
- Do NOT weaken `cs5FCIncest` (do not drop or relax any of its five conjuncts) or modify the `Graph`
  structure.
- Do NOT edit or re-derive the 17 landed asset rows; their proofs must not regress.
- Do NOT expand file scope beyond `Soundness.lean`. No new file is introduced. (The bridge's Hilbert
  target `cs5_soundness_derivable_incest` already lives in the imported `CS5Canonical.lean` and is
  consumed, not modified.)
- Do NOT hand-analyze a "wall" and escalate without first machine-checking the blocking sub-goal
  with `lean_run_code` / `lean_multi_attempt` / `lean_goal`.

**MUST preserve**:
- All 17 landed asset rows above (sorry-free, axiom-clean, unregressed).
- Existing full-project green state: `lake build`, `lake lint`, `lint-style`, `shake`,
  `checkInitImports`, `lake test`. Pre-existing unrelated sorries in Propositional Tableau files are
  the known baseline — do not "fix" or count them.

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):
- `nik_TS5_soundness` is TRUE and provable (report 04 verdict, H4-verified).
- The selected route is the **faithful tree-recursive Hilbert adequacy bridge** (route (a)). The
  direct PD induction's `efq` residual is genuinely open and is NOT on this critical path.
- `cs5_soundness_derivable_incest` (CS5Canonical.lean:359) is landed, sorry-free, and already
  `CKValidFC cs5FCIncest`-valued: only the labelled→Hilbert bridge is missing.
- The forest/lifting machinery (Phases 6-7) and PD.1's `bot_*` lemmas are ON the critical path of
  this route (tree-depth index; `efq` translation) — reused, not deleted.

## Risks & Mitigations

- **Risk (primary, concentrated)**: The faithful tree-recursive translation + main adequacy lemma is
  substantial NEW proof-theory infrastructure (~300-600+ lines) that task 517 deferred as "THE TRUE
  CRUX" and that has never been attempted in Lean. Report 04 rates it ~70% closable — "known-shape"
  (a complete published theorem, Simpson Lemma 6.1.2 + Thm 6.2.1) rather than open, but non-trivial.
  **Mitigation**: decomposed into four sequential agent-run-sized steps (8.1 translation function;
  8.2 propositional+cross-label cases; 8.3 modal cases; 8.4 specialisation), each with its own green
  criterion and commit-per-green-substep. Phase 8.1 begins with a focused re-read of Simpson Ch. 6
  (Fig. 6-1/6-2) before Lean work. If a step overruns across dispatches, land the green portion and
  either continue the next dispatch or, if a concrete machine-checked obstruction emerges, route to
  the Phase 11 sanctioned `[BLOCKED]` terminal + route-(b) research task, NEVER a `sorry`.
- **Risk (translation-definitional)**: getting the tree-depth-indexed `⊃□(...)` nesting subtly wrong
  so that a later constructor case is unprovable not because the math is hard but because the
  definition is off. **Mitigation**: Phase 8.1's green criterion includes `example`/`#eval` sanity
  checks pinning `nikTr` on `Graph.trivial` (must reduce to `φ` at depth 0) and on a one-edge graph
  (must add exactly one `⊃□` level) before ANY constructor case is attempted; if 8.2/8.3 reveals the
  definition is wrong, fix 8.1 (re-commit) rather than papering over it in a case.
- **Risk (the `orE`/`efq` cases still bite)**: these are exactly where the shortcuts died.
  **Mitigation**: the faithful nesting gives each label its own box-depth, so `efq`/`orE` translate
  without cross-depth re-boxing; PD.1's `bot_*` lemmas (landed) supply the `⊥`-handling. These two
  cases are isolated in Phase 8.2 and machine-checked (`lean_goal`/`lean_multi_attempt`) case-by-case;
  if EITHER genuinely resists the faithful translation, that is a concrete obstruction → Phase 11
  terminal (it would mean route (a) is also blocked, the honest outcome the task lead asked for).
- **Risk (fallback route (b) is not implementable now)**: Path PD's `efq` residual needs a genuinely
  novel `⊥`-locality / cut-admissibility lemma (report 04 ~35%; summaries/10 re-confirmed open).
  **Mitigation**: it is NOT an implementation contingency under this plan — it is a recommended
  **research task** (Phase 11). The corrected PD.2 motive design (11/12 constructors) is preserved as
  a documented asset so that research can resume from it, not from scratch.
- **Risk**: a phase silently touches a Preserved Asset and regresses it. **Mitigation**: every phase's
  Zero-Debt Contract re-verifies the assets build sorry-free before commit; `lean_verify` on each
  completing lemma.
- **Risk**: file-territory contention — all phases write the single file `Soundness.lean`.
  **Mitigation**: phases (and sub-steps 8.1-8.4) execute strictly sequentially; no parallel dispatch
  onto `Soundness.lean`.

## Implementation Phases

**Dependency Analysis**:

All phases write the single file `Soundness.lean` (H7 territory: one owner), so they execute
**strictly sequentially** — no two phases (or 8.x sub-steps) may be dispatched in parallel. Phases
1-7 and PD.1 are LANDED (historical). Execution order for the remaining work is
8.1 → 8.2 → 8.3 → 8.4 → 9 → 10, with Phase 11 as a documented terminal / research recommendation,
NOT an implementation step on this route.

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1-7 (landed) | 1, 2, 3, 4, 5, 6, 7 | -- (historical; all [COMPLETED]) |
| PD.1 (landed) | 11 §PD.1 | -- (historical; [COMPLETED], commit `0172b639`) |
| 8.1 | 8.1 | -- (reuses landed forest/tree machinery + PD.1; sequential by file territory) |
| 8.2 | 8.2 | 8.1 |
| 8.3 | 8.3 | 8.1 (uses `nikTr`), 8.2 (same `induction` block) |
| 8.4 | 8.4 | 8.2, 8.3 (needs the completed `nik_adequacy`) |
| 9 | 9 | 8.4 |
| 10 | 10 | 9 |
| (research recommendation) | 11 | not on this route's critical path |

The orchestrator heading-scan picks the first non-`[COMPLETED]` phase: **Phase 8** (starting at
sub-step 8.1).

### Phase 1: Base forcing-equivalence lemmas box_iff_base, dia_iff_base [COMPLETED]

- **Landed**: `box_iff_base` (Soundness.lean:374), `dia_iff_base` (Soundness.lean:392). Sorry-free,
  axiom-clean. **Do NOT re-plan or re-derive.** Preserved Asset.

### Phase 2: TClosure-class extension box_iff_TClosure, dia_iff_TClosure [COMPLETED]

- **Landed**: `box_iff_TClosure` (Soundness.lean:422), `dia_iff_TClosure` (Soundness.lean:437).
  Sorry-free, axiom-clean. **Do NOT re-plan or re-derive.** Preserved Asset.

### Phase 3: F2 target-raise + reflexive here-extraction helpers [COMPLETED]

- **Landed**: `cs5FCIncest_raise` (Soundness.lean:337); `box_gives_here` (Soundness.lean:349).
  Sorry-free, axiom-clean. **Do NOT re-plan or re-derive.** Preserved Asset.

### Phase 4: Single-node interpretation-raise step boxI_raise_step [COMPLETED]

- **Landed**: `boxI_raise_step` (Soundness.lean:472). Sorry-free, axiom-clean. **Do NOT re-plan or
  re-derive.** Preserved Asset.

### Phase 5: Star-lifting over all direct raw-neighbours boxI_lift_star [COMPLETED]

- **Landed**: `boxI_lift_star` (Soundness.lean:604). Sorry-free, axiom-clean. **Do NOT re-plan or
  re-derive.** Preserved Asset.

### Phase 6: Derivation-forest invariant IsDerivationForest + preservation lemmas [COMPLETED]

- **Landed**: `IsDerivationForest` (Soundness.lean:713), `forest_trivial`, `forest_addEdge_fresh`.
  Sorry-free, axiom-clean. **Do NOT re-plan or re-derive.** Preserved Asset. **Back on the critical
  path**: its graded-rank / unique-parent content supplies the tree-depth index for `nikTr`
  (Phase 8.1).

### Phase 7: Tree-cascade lifting lemma boxI_lift [COMPLETED]

- **Landed**: `ht_le_of_reflTransGen`, `raise_subtree`, `siblings_disjoint`, `boxI_lift_ancestor`,
  `boxI_lift`. Sorry-free, axiom-clean. **Do NOT re-plan or re-derive.** Preserved Asset. **Back on
  the critical path**: `ht_le_of_reflTransGen` / tree-height content feeds `nikTr`'s depth index;
  `boxI_lift` is reused by the `boxI` case (Phase 8.3).

### Phase 8: Faithful tree-recursive labelled→Hilbert adequacy bridge nik_TS5_to_hilbert [IN PROGRESS]

The sole concentrated-risk phase of the selected route (report 04: ~70% closable; the full Simpson
Ch. 6 construction, ~300-600+ lines, NEVER attempted in Lean — only the two refuted flat shortcuts
were). Decomposed into four sequential agent-run-sized sub-steps. **Do NOT retry the flat
shortcuts.** Each sub-step lands a green, independently-committable Preserved Asset.

- **Goal (phase):** Land `nik_TS5_to_hilbert : NIKTheorem TS5 φ → Derivable CS5ModalAxiom φ`
  (Simpson Ch. 6 Lemma 6.1.2 + Thm 6.2.1, specialised to theoremhood over `Graph.trivial`).
  `NIKTheorem TS5 φ` is `NIKDerivable` over `Graph.trivial`/empty-context (Deduction.lean:316);
  `Derivable CS5ModalAxiom` is the landed Hilbert system consumed by `cs5_soundness_derivable_incest`.

#### Sub-step 8.1 — Tree-depth-indexed translation function `nikTr` + subtree/depth accessors

- **Tasks:**
  - [x] **Source pass first (H3):** re-read Simpson Ch. 6 Fig. 6-1/6-2
        (`~/Projects/Literature/simpson_1994_intuitionisticmodallogic/...reflowed.md:943-1073`) to
        fix the exact recursive translation `(Γ ⊢_G x:A)^T` and its per-level `⊃□(...)` nesting.
        Record the definitional shape (base at the root; one `⊃□` added per descent) before Lean.
        *(deviation: the reflowed OCR of chunks 943-975 is severely corrupted at the formula level
        -- box/diamond glyphs conflated with digits, sub/superscripts scrambled, and the one worked
        example in the source could not be reproduced consistently from the OCR'd formula alone.
        The definitional shape (the `Γ@U` subtree recursion + spine-threading via iterated `⊃□`)
        was reconstructed from the surrounding PROSE, which is legible and internally consistent,
        and is flagged in `Soundness.lean`'s new section docstring per the literature-fidelity
        policy rather than silently guessed.)*
  - [x] Define the label tree-depth accessor over the landed forest machinery (reuse
        `IsDerivationForest`'s graded-rank / `ht_le_of_reflTransGen` height content, Phases 6-7),
        and the recursive translation function `nikTr` (name to taste) mapping a labelled context +
        goal over a forest-shaped `G` to a `CS5ModalAxiom` `Formula`. *(deviation: altered -- the
        landed `nikTr`/`sigAt` use a fuel-bounded structural recursion (fuel = `G.X`'s finite
        cardinality, safely dominating any node's descent depth in a finite graded-rank forest)
        rather than directly indexing by `IsDerivationForest`'s `ht`/`ht_le_of_reflTransGen`; this
        sidesteps needing a well-founded-recursion `def` over the `ncard`-based measure `raise_subtree`
        uses, since a global fuel bound is simpler to define correctly for a computational `def`
        (as opposed to the existential-witness `theorem`s Phases 6-7 are). `IsDerivationForest`
        itself is untouched and remains available for Phase 8.2/8.3's `boxI`/`boxE` cases.)*
  - [x] Pin the definition with sanity `example`s: `nikTr` on `Graph.trivial` reduces to the bare
        `φ.prop` (depth 0, no nesting); `nikTr` on a single `addEdge`-extended graph adds exactly one
        `⊃□` level. These are the green anchor for the definition. *(deviation: altered -- the first
        sanity `example` reduces to a `⊤`-padded identity `(sigAt Γ_trivial x ⊃ A)`, not literally
        bare `A`, since `bigAndL`'s empty-conjunction base case is a `⊤`-surrogate tautology rather
        than a genuinely absent conjunct (a documented, sound, `CS5ModalAxiom`-equivalent Lean-
        encoding choice, not a mathematical change). The second sanity `example` is stated as an
        existential (`∃ n q antecedent, nikTr … = nikTrFuel … n q (antecedent ⊃ □(sigAt … ⊃ A))`)
        rather than a fully-reduced closed-form equality, since full reduction routes through
        `Classical.choose`/`Set.Finite.toFinset`, which are not kernel-reducible via `rfl`; the
        existential form still confirms exactly one `⊃□` level was added, which is the intended
        cross-check.)*
- **Green criterion / Done when:** `nikTr` and the depth accessor type-check and reduce; the two
  sanity `example`s compile; `Soundness.lean` builds green; `lean_verify` on `nikTr` axiom-clean
  (no `sorryAx`, no new axiom). Commit as a green sub-step. **[MET]** -- scoped
  `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness` green; no `sorry`, no
  new `axiom` in the file (`grep` confirmed); `lake exe checkInitImports` clean.
- **Estimated output:** ~100-250 lines. **Depends on:** landed Phases 6-7.
- **Reuses:** `IsDerivationForest`, `ht_le_of_reflTransGen` (tree height/depth), forest preservation.
- **Zero-debt contract:** no `sorry` in the committed file, no new axiom, `cs5FCIncest` unweakened,
  `Graph` unmodified, no Preserved Asset touched.

#### Sub-step 8.2 — Adequacy induction: propositional + cross-label (`efq`, `orE`) cases `[IN PROGRESS]`

- **Tasks:**
  - [x] State the main adequacy lemma `nik_adequacy : NIK TS5 G Γ (x ∶ A) → Derivable CS5ModalAxiom
        (nikTr G Γ (x ∶ A))` (adjust to the landed `NIK` spelling, Deduction.lean:316; instantiate
        the axiom set to `{χ_T, χ_B, χ_4}` = `CS5ModalAxiom` per Thm 6.2.1). *(deviation: altered --
        per this sub-step's own green criterion's sanctioned fallback, `nik_adequacy` itself is NOT
        yet stated as a single `induction … with` block (Lean requires all 12 cases at once); instead
        landed as ten standalone "core" helper lemmas (`sigAt_*`, see below) that the actual
        `induction` will consume once 8.3's modal cases are also ready. `nikTr_of_sigAt_imp`
        packages the one-time wrap from a "core" `sigAt`-level fact to the full `nikTr` statement.)*
  - [x] Open the 12-constructor `induction … with` and discharge the **8 label-local propositional
        constructors** (`assumption`, `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `impI`, `impE`)
        using standard `Derivable CS5ModalAxiom` combinators from CS5Canonical and the per-label
        box-depth from `nikTr`. *(deviation: altered -- landed as standalone lemmas `sigAt_assumption`,
        `sigAt_andI`, `sigAt_andE1`, `sigAt_andE2`, `sigAt_orI1`, `sigAt_orI2`, `sigAt_impE`,
        `sigAt_impI`, each proving the "core" `sigAt`-level fact rather than being a case inside a
        completed `induction` block, per the reason above. All 8 landed sorry-free and axiom-clean,
        supported by a new reusable propositional-combinator toolkit (`cs5_deriv_imp_trans`/`_and`/
        `_andE1`/`_andE2`/`_orI1`/`_orI2`/`_mp`/`_of_derivable`/`_self`/`_trans_under`,
        `cs5_deriv_curry`/`_uncurry`), `bigAndL_mem`/`_mono`/`_cons`, `factsAt_cons_ne`/`_self`, the
        rank-based context-extension congruence `sigAtFuel_congr_above_rank`, and the ancestor-wrap
        bridge `nikTrFuel_of_derivable`/`nikTr_of_sigAt_imp`. `impI` additionally needed
        `sigAt_cons_self_imp`, the hardest of the eight.)*
  - [ ] Discharge the **two cross-label constructors** `efq` and `orE` — the cases the flat shortcuts
        died on. **NOT machine-attempted yet** (no concrete `efq`/`orE` Lean goal has been opened;
        all work so far is reusable infrastructure the eventual case proofs will need).
        *(deviation: deferred -- across TWO dispatches now, a progressively deeper design analysis
        found:
        (1) [dispatch N] the "core" `sigAt`-only motive used for the 8 cases above is INSUFFICIENT
        for `efq`/`orE`: a bare `sigAt x` fact only packages `x`'s own subtree, with no route to an
        unrelated label `y`, whereas `nikTr`'s full ancestor-wrap threads in off-spine sibling
        subtrees. PD.1's `bot_*` lemmas (originally earmarked for `efq`) are semantic/`CKForces`
        facts from the superseded direct-motive route, NOT reusable for this syntactic bridge.
        (2) [dispatch N+1, this one] closing the gap identified in (1) requires THREE further
        infrastructure layers, of which the first two are now LANDED and machine-verified:
          (a) **Context-monotonicity across the whole ancestor wrap** — `sigAtFuel_mono_context`
              (landed): a Γ-extension `Δ ⊇ Γ` pointwise (not just at descendants of the extended
              label, which the earlier rank-threshold `sigAtFuel_congr_above_rank` could reach, but
              also at SIBLING branches sharing the extended label's own rank) always derivably
              entails the smaller-context translation. Superseding-in-scope, not replacing,
              `sigAtFuel_congr_above_rank` (still valid, just narrower).
          (b) **`nikTrFuel` fuel-sufficiency** — `nikTrFuel_fuel_invariant_step` (landed): the fuel
              amount `nikTr` fixes globally (`card+1`) and the REDUCED fuel exposed one level up
              inside any `sigAt`/`nikTrFuel` unfold need to be reconciled; proved via induction on
              an upper bound for the graded-rank witness `ht`, confirming the ancestor walk halts
              at the true root regardless of leftover fuel. (`sigAtFuel_mono_fuel`/`_le`, an easier
              UNCONDITIONAL fuel-monotonicity fact needing no sufficiency side-condition at all,
              landed alongside as a related but distinct tool.)
          (c) **A root-connectivity invariant — NOT YET DEFINED, the next concrete blocker.**
              Completing the "propagate `⊥` up `x`'s ancestor chain to the tree's root, then back
              down to an arbitrary `y`" argument (the natural proof strategy once (a)/(b) are in
              hand, avoiding an explicit lowest-common-ancestor computation by routing through the
              root instead) needs EVERY label to be reachable from a single distinguished root via
              `Relation.ReflTransGen G.R`. This is TRUE for every actual derivation graph (`G` is
              always built from `Graph.trivial`'s one node via repeated `addEdge` from an EXISTING
              node), but it is **NOT implied by `IsDerivationForest`'s three existing conjuncts**
              (finite + graded rank + unique parent) alone -- those are purely LOCAL constraints
              consistent in principle with several disjoint rank-graded unique-parent components.
              Closing `efq`/`orE` via the root-propagation strategy needs a NEW invariant (e.g.
              `IsRootedForest`, or a fourth conjunct added to `IsDerivationForest`) asserting
              `∃ root, ∀ z ∈ G.X, Relation.ReflTransGen G.R root z`, PLUS preservation lemmas
              mirroring `forest_trivial`/`forest_addEdge_fresh` (expected straightforward:
              `Graph.trivial`'s single node trivially reaches itself; `addEdge x y` for fresh `y`
              preserves reachability-from-root inductively, since the root already reaches `x`).
        This is a genuine, freshly-identified INFRASTRUCTURE GAP, not a machine-checked proof
        obstruction against a concrete goal -- (a) and (b) above are proof this general direction
        is tractable engineering, verified by compiling. But the cumulative remaining scope (root-
        connectivity + its preservation lemmas, the propagate-up-to-root argument, the propagate-
        down-from-root `efq` argument, and `orE`'s own comparable-complexity treatment) is
        substantially larger than originally estimated -- plausibly 400-600+ further lines, i.e.
        multiple further dedicated dispatches, not "one more lemma." Reusable infrastructure landed
        regardless of how the redesign is finished: `cs5_deriv_box_mono`, `cs5_deriv_imp_congr_right`,
        `nikTrFuel_mono`, `bigAndL_imp_of_pointwise`, `sigAtFuel_mono_context`,
        `sigAtFuel_mono_fuel`/`_le`, `nikTrFuel_succ_eq`, `nikTrFuel_no_parent`,
        `nikTrFuel_fuel_invariant_step`.)*
- **Green criterion / Done when:** the 10 constructor cases of `nik_adequacy` compile sorry-free
  (the 4 modal cases may remain open ONLY inside a scratch buffer, never in the committed file —
  land 8.2 by committing the file with the 10 cases proven and the modal cases stubbed via a
  structured `induction` that is completed in 8.3; if Lean's single-`induction` shape forbids a
  partial commit, keep 8.2's green artifact as the standalone helper lemmas the modal cases will
  consume, and defer stating `nik_adequacy` itself to 8.3). `Soundness.lean` builds green; commit.
  **[PARTIAL]** -- 8 of 10 in-scope constructors landed as standalone core lemmas (sorry-free,
  axiom-clean, scoped build green, each individually committed); `efq`/`orE` remain. Substantial
  reusable cross-label infrastructure (context-monotonicity, fuel-sufficiency) landed this
  dispatch; the concrete next blocker is a not-yet-defined root-connectivity invariant (see above).
- **Estimated output:** ~150-350 lines. **Depends on:** 8.1. **Actual so far:** ~690 lines across
  fourteen commits over two dispatches (toolkit + bigAndL_mem, ancestor-wrap bridge, sigAt-core
  infra + `assumption`, the six `P`-generic cases, `sigAtFuel_congr_above_rank`,
  `sigAt_cons_self_imp`, `sigAt_impI`, `nikTrFuel_mono` + motive-design writeup,
  `sigAtFuel_mono_context`, `sigAtFuel_mono_fuel`/`_le`, `nikTrFuel_fuel_invariant_step`) --
  roughly double the top of the estimated range, with the cross-label cases (the hardest part,
  per report 04's own risk rating) still not started. This sub-step needs several more dedicated
  dispatches, exceeding Phase 8's own worst-case 6-run sizing for the phase as a whole; a plan
  revision or a dedicated `/research` pass on the root-connectivity + propagation strategy is
  recommended before the next implementation dispatch, rather than continuing ad hoc.
- **Reuses:** PD.1 `bot_backward`/`bot_iff_edge`/`bot_iff_TClosure`; CS5Canonical Hilbert combinators.
  *(deviation: PD.1's `bot_*` lemmas turned out NOT reusable here -- they are semantic/`CKForces`
  facts for the superseded direct-motive route, not syntactic `Derivable`/`sigAt` facts. The
  cross-label bridge will need new syntactic infrastructure instead; see the `efq`/`orE` deviation
  note above.)*
- **Zero-debt contract:** as 8.1. Verified: no `sorry`, no new `axiom` in the committed file; scoped
  `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness` green after every commit.

#### Sub-step 8.3 — Adequacy induction: modal (`boxI`, `boxE`, `diaI`, `diaE`) cases

- **Tasks:**
  - [ ] Discharge the 4 modal constructor cases of `nik_adequacy`. `boxI` descends one tree level
        (adds a `⊃□`) — reuse the landed `boxI_lift` / `raise_subtree` / `IsDerivationForest` (Phase 7)
        for the subtree structure. `boxE` ascends via `TClosure` — reuse `box_iff_TClosure`
        (Phase 2). `diaI`/`diaE` symmetric via `dia_iff_TClosure` and `le_refl`.
  - [ ] Complete `nik_adequacy` (all 12 cases green). Machine-check each stuck modal sub-goal before
        escalating.
- **Green criterion / Done when:** `nik_adequacy` compiles sorry-free across all 12 constructors;
  `lean_verify` on `nik_adequacy` axiom-clean; `Soundness.lean` builds green; commit.
- **Estimated output:** ~150-300 lines. **Depends on:** 8.1 (`nikTr`), 8.2 (same induction / helpers).
- **Reuses:** Phase 7 `boxI_lift` + helpers, Phase 2 `box_iff_TClosure`/`dia_iff_TClosure`, Phase 6 forest.
- **Zero-debt contract:** as 8.1.

#### Sub-step 8.4 — Specialise to theoremhood over `Graph.trivial`

- **Tasks:**
  - [ ] Derive `nik_TS5_to_hilbert : NIKTheorem TS5 φ → Derivable CS5ModalAxiom φ` by instantiating
        `nik_adequacy` at `G := Graph.trivial`, `Γ := []`, `x := (Graph.trivial).nonempty.choose`,
        and simplifying `nikTr` at the trivial tree (depth 0 ⇒ the nesting collapses to `φ`, matching
        8.1's sanity `example`). Reconcile any implicit `Atom`/`φ` binders and universe variables.
- **Green criterion / Done when:** `nik_TS5_to_hilbert` compiles with the exact stated signature;
  `lean_verify` on it axiom-clean; `Soundness.lean` builds green; commit.
- **Estimated output:** ~30-100 lines. **Depends on:** 8.2, 8.3 (`nik_adequacy` complete).
- **Zero-debt contract:** as 8.1.

- **Phase 8 timing:** four to (worst-case) six agent runs, hard budget cap per sub-step. Land each
  green sub-step's helper(s) first (independently-committable Preserved Assets for the follow-on).
- **Phase 8 contingency sub-gate:** if a sub-step hits a **concrete, machine-checked** obstruction in
  the faithful construction that genuinely overruns budget across dispatches (NOT a hand-waved wall,
  NOT the flat-shortcut obstructions which are out of scope), land the green portion and route to the
  **Phase 11 sanctioned `[BLOCKED]` terminal + route-(b) research recommendation**, never a `sorry`.
- **Phase 8 Verification / Done when:** `nik_TS5_to_hilbert` compiles with the stated signature;
  `lean_verify` axiom-clean on `nikTr`, `nik_adequacy`, and `nik_TS5_to_hilbert`; no NEW tactic
  `sorry` in the committed file.

### Phase 9: Corollary assembly nik_TS5_soundness + docstring cleanup [IN PROGRESS]

- **Goal:** Assemble the goal theorem as the corollary composing the Phase 8 bridge with the landed
  Hilbert soundness, and retire the stale module-docstring notes (report 04 Path P3 §8b).
- **Tasks:**
  - [ ] Land `nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ` as
        `fun h => cs5_soundness_derivable_incest (nik_TS5_to_hilbert h)` (CS5Canonical.lean:359).
        Reconcile universe variables (`cs5_soundness_derivable_incest` is `.{u, v}`-polymorphic) and
        any implicit `Atom`/`φ` binders. ~3-10 lines.
  - [ ] Update the `Soundness.lean` module docstring: mark the general theorem LANDED via the
        Hilbert bridge; **remove the stale `INTRACTABLE` / `GATE-C` / "What remains" / "Fifth
        dispatch" notes**. Keep the accurate historical record of the landed lemmas.
- **Estimated output:** ~10-40 lines (mostly docstring edits). **Timing:** one agent run. **Depends on:** 8.4.
- **Zero-debt contract:** no `sorry`, no new axiom, no weakening, no Preserved Asset regressed.
- **Verification / Done when:** `nik_TS5_soundness` sorry-free; `Soundness.lean` builds green;
  `lean_verify` on `nik_TS5_soundness` axiom-clean (no `sorryAx`, no new axiom).

### Phase 10: Regression gate + full-project verification [IN PROGRESS]

- **Goal:** Confirm the full project is green and unregressed, the Simpson 8.1.4 biconditional is
  complete, and no debt was added anywhere (report 04 Path P3 §8c).
- **Tasks:**
  - [ ] Full `lake build` green.
  - [ ] `lean_verify` on `nik_TS5_soundness` reports no `sorryAx` and no new axioms.
  - [ ] `grep -nE '\bsorry\b'` on `Soundness.lean`: no NEW *tactic* `sorry` (docstring prose
        excepted); `grep -nE '^axiom '`: zero new axioms.
  - [ ] Spot-verify the 17 landed asset rows still build sorry-free (esp. `cs5_completeness`,
        `nik_TS5_consistent`, `cs5_soundness_derivable_incest`, the Phases 1-7 lemmas, and PD.1).
  - [ ] `lake lint`, `lake exe lint-style <file>`, `lake shake`, `lake exe checkInitImports`,
        `lake test` all unregressed against the task-517 baseline.
- **Estimated output:** verification only; docstring touch-ups if any (~0-20 lines). **Timing:** one
  agent run. **Depends on:** 9.
- **Zero-debt contract:** no `sorry`, no new axiom, no weakening, no regression.
- **Verification / Done when:** all checks pass; the Simpson 8.1.4 biconditional is complete.

### Phase 11: Direct route PD — sanctioned terminal + route-(b) research recommendation [BLOCKED]

**Not an implementation step on this route.** This phase records (i) the landed PD.1 asset,
(ii) the corrected PD.2 motive design preserved for future research, and (iii) the sanctioned
`[BLOCKED]` terminal + the recommended route-(b) research task, should the Phase 8 faithful bridge
itself overrun. Under plan v4 this was an implementation "fallback"; two dispatches established that
its `efq` residual is **genuinely open** (independently re-derived, summaries/10), so it is
downgraded here from an implementation contingency to a **research recommendation**.

- **PD.1 — LANDED (Preserved Asset).** `bot_backward` / `bot_iff_edge` / `bot_iff_TClosure`
  (Soundness.lean, commit `0172b639`), sorry-free, axiom-clean. **Now on the critical path**: reused
  by the bridge's `efq` translation case (Phase 8.2). Do NOT re-derive.

- **PD.2 — corrected motive design (preserved, NOT implemented).** The report-04 literal motive
  `M(G,Γ,φ) := ∀ρ, edge-cond → Γ-cond → ∃ρ', (∀z,ρz≤ρ'z) ∧ (agrees on G.X∪ctxLabels Γ) ∧
  CKForces(ρ'φ.lbl)φ.prop` is **unprovable as stated** (the bare `∀z,ρz≤ρ'z` conjunct has no witness
  for `efq`'s adversarial dangling label on a non-directed `Preorder`; `orE` DOES need coordination,
  contra report 04 Finding 4). The corrected design — exact-agreement domain
  `Dom(G,Γ,φ) := G.X ∪ ctxLabels Γ ∪ {φ.lbl}` (no constraint outside `Dom`) plus a caller-supplied
  protect-set `T ⊇ Dom` widened per sibling call — closes **11 of 12** constructors (worked by hand,
  verified structurally against every constructor; summaries/10). It is preserved here as the
  starting point for the route-(b) research, NOT written in Lean (a single closed `induction … with`
  cannot be a buildable sorry-free artifact while the 12th case is open).

- **PD.3 — the `efq` residual: GENUINELY OPEN (the route-(b) research goal).** `efq` with conclusion
  label `y ∈ Dom` (so `ρ'y` is pinned to `ρy`) and the premise's `⊥`-label `x` dangling or
  `r`-disconnected from `y`. This is exactly report 04 Finding 5 / Simpson's "unavoidable non-tree
  excursion" (§8.1.2, chunk 0158), independently re-derived twice. Closing it needs a genuinely new
  normalization / cut-admissibility invariant for `N_IK(𝒯)` ("any `⊥` derivable in a live
  sub-derivation is already reachable from a live, connected assumption") — **research-scale, not a
  transcription task.** report 04 rates it ~35%.

- **Recommended route-(b) research task (only if Phase 8 also overruns):** a dedicated
  `/research`-scale investigation of cut-admissibility / `⊥`-locality for `N_IK(𝒯)`, taking the
  preserved PD.2 corrected motive (11/12 cases) as its starting point and targeting the PD.3 `efq`
  gap. On success, PD.2's 11 tractable cases become a straightforward transcription and PD.4
  (assemble `nik_TS5_soundness` by specialising `M` to `Graph.trivial`/`[]`, then the Phase 10
  regression gate) follows. This research task is the sanctioned successor to a Phase 8 `[BLOCKED]`
  terminal — it is NOT dispatched pre-emptively while the Phase 8 bridge is the live route.

- **Zero-debt contract:** no `sorry`, no new axiom, `cs5FCIncest` unweakened, `Graph` unmodified, no
  Preserved Asset touched. Do NOT attempt the connectivity-lemma path (report 04 Finding 2 refutes
  it), do NOT weaken `efq`/`orE`, do NOT retry the flat-translation shortcuts.
- **Verification / Done when (this phase, as a terminal):** invoked ONLY if the Phase 8 faithful
  bridge overruns — then a `[BLOCKED]` handoff records the concrete Phase-8 obstruction, build green,
  zero debt, PD.1 + PD.2-design preserved, and the route-(b) research task recommended.

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness` green after every
      sub-step / phase that touches `.lean` (H9 green-milestone commit).
- [ ] Full `lake build` green at each phase completion.
- [ ] `lean_verify` axiom-clean on each new definition/lemma as it lands (`nikTr`, `nik_adequacy`,
      `nik_TS5_to_hilbert`, `nik_TS5_soundness`).
- [ ] `nikTr` sanity `example`s (trivial graph ⇒ `φ`; one-edge ⇒ one `⊃□` level) compile (Phase 8.1).
- [ ] `grep -nE '\bsorry\b'` on `Soundness.lean`: no NEW *tactic* `sorry` (docstring prose excepted).
- [ ] `grep -nE '^axiom '` on modified files: zero new axioms.
- [ ] `Graph` structure unmodified; `cs5FCIncest` (CS5Canonical.lean) unweakened.
- [ ] `lake lint`, `lake exe lint-style <file>`, `lake shake`, `lake exe checkInitImports`,
      `lake test`: all unregressed against the task-517 green baseline.
- [ ] Preserved Assets unregressed (spot-verify the 17 listed asset rows build sorry-free).

## Artifacts & Outputs

- plans/05_tree-recursive-hilbert-bridge.md (this file)
- Modified: Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean (Phases 8.1-8.4, 9)
- handoffs/ blocked handoff (contingency, only if the Phase 8 faithful bridge overruns → Phase 11)
- summaries/05_tree-recursive-hilbert-bridge-summary.md (on completion)

## Rollback/Contingency

- Each sub-step / phase commits only its own green result (H9 incremental commit;
  commit-per-green-substep mandate applies to every 8.x helper lemma). If a step fails to reach
  green, leave the prior committed state intact; fix forward — never destructive git on a dirty tree
  (see `.claude/rules/git-workflow.md`, "No Destructive Git on Uncommitted Work").
- The route (a) faithful bridge is the committed line. Its ONLY sanctioned terminal, if it genuinely
  overruns across dispatches with a concrete machine-checked obstruction, is the Phase 11 `[BLOCKED]`
  handoff + route-(b) research recommendation (dedicated `⊥`-locality / cut-admissibility research) —
  scoped to the concrete Phase-8 gap, PD.1 + PD.2-design preserved, zero debt, build green — **never a
  `sorry`, never a new axiom, never a return to the refuted connectivity-lemma / clique / exact-symmetry
  decompositions, and never a retry of the two refuted flat-translation shortcuts.**
