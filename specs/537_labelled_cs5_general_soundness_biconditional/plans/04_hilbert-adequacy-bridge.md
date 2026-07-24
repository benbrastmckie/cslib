# Implementation Plan: General Labelled CS5 Soundness via Hilbert-Labelled Adequacy Bridge (nik_TS5_soundness)

- **Task**: 537 - Prove the general labelled soundness direction, completing Simpson 1994 Thm 8.1.4's biconditional
- **Status**: IMPLEMENTING
- **Effort**: 6-12 hours remaining (Phases 1-7 landed; residual risk concentrated in the Phase 8 adequacy bridge)
- **Dependencies**: 517 (delivered completeness + anti-vacuity + landed Hilbert-side soundness `cs5_soundness_derivable_incest`)
- **Research Inputs**: reports/04_crosslabel-motive-audit.md (Tier 1, H4-verified; AUTHORITATIVE — refutes the connectivity-lemma fix, selects the route), reports/03_tree-shape-invariant-audit.md, reports/02_direct-route-from-sources.md
- **Artifacts**: plans/04_hilbert-adequacy-bridge.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/plan-format-enforcement.md
  - .claude/context/formats/plan-format.md
  - .claude/context/contracts/wrap-up.md
  - .claude/context/contracts/reference-grounding.md
- **Type**: cslib
- **Plan version**: 4 (supersedes plans/03_direct-route-forest.md; folds the cross-label motive audit, report 04)

## Overview

Prove `nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ` in the single file
`Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`, closing the soundness
direction (2⟹1) of Simpson Thm 8.1.4 for CSLib constructive CS5/IS5. **This is a pivot in proof
architecture, not in the theorem.** Plan v3 attempted a *direct* structural induction over `NIK`
derivations threading a derivation-forest invariant; its Phase 8 hit a genuine `[BLOCKED]`: the
naive `∀ρ` induction motive is machine-refuted for the **cross-label** `NIK.efq`/`NIK.orE`
constructors (a 2-point disconnected `cs5FCIncest`+`CKValidFC` countermodel, `handoffs/08`,
commit c3684a4c). The divergence audit (report 04, adversarially verified, Tier 1) confirms:

- **`nik_TS5_soundness` IS true and provable** — the countermodel refutes only the naive local
  motive, never the theorem (which holds because `⊥` is never derivable from the empty root
  context, `nik_TS5_consistent`, landed).
- **The connectivity-lemma fix contemplated by plan v3's Phase 8 is REFUTED (H4).** Connectivity is
  *not* a derivation-graph invariant: `NIK.boxI`/`NIK.diaE` (Deduction.lean:297,309) carry no
  `x ∈ G.X` side-condition, so firing at a dangling `efq`/`orE` label creates a `G.R`-disconnected
  component. `IsDerivationForest` correctly omits connectivity; it cannot be strengthened to it.
- **The recommended route is Strategy 3 — the Hilbert-labelled adequacy bridge**, obtaining
  `nik_TS5_soundness` as a corollary of the **already-landed, sorry-free**
  `cs5_soundness_derivable_incest` (CS5Canonical.lean:359). This sidesteps the induction and its
  `efq` "non-tree excursion" entirely, and is endorsed by Simpson §8.1.2 itself (chunk 0158: the
  direct `N(𝒯)` route has "unavoidable non-tree excursions", routed around via `L_m`/Hilbert).

This plan **supersedes** `plans/03_direct-route-forest.md`. It preserves all landed work: the 14
Preserved Assets from task 517 and this task's Phases 1-5, plus Phase 6 (`IsDerivationForest` +
preservation lemmas) and Phase 7 (`boxI_lift` and its helpers). Those assets remain sorry-free,
axiom-clean, and unregressed. **On the P3 critical path they are no longer required** (the bridge
does not consume the forest/lifting machinery), but they stay valid and reusable — in particular
they are the foundation of the fallback route PD (Phase 11) should the bridge prove intractable.

### Definition of Done

`nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ` lands sorry-free and axiom-clean
in `Soundness.lean`; full `lake build` green; `lean_verify` on `nik_TS5_soundness` reports no
`sorryAx` and no new axioms; `lake lint` / `lint-style` / `shake` / `checkInitImports` / `test`
unregressed against the task-517 green baseline; the stale module-docstring `INTRACTABLE` /
`GATE-C` / "What remains" / "Fifth dispatch" notes retired. Sanctioned terminal alternative: if
BOTH the primary bridge (Phase 8) AND the fallback route PD's novel `⊥`-locality lemma (Phase 11,
report 04 rates ~35% closable) genuinely overrun budget across dispatches, a documented `[BLOCKED]`
handoff scoped to the remaining gap, build green, zero debt — **never a `sorry`**.

### Research Integration

- reports/04_crosslabel-motive-audit.md — integrated in plan_version 4 (2026-07-24). AUTHORITATIVE.
  Supplies: the verdict that `nik_TS5_soundness` is true/provable; the H4 refutation of the
  connectivity-lemma fix (connectivity is not a graph invariant); the diagnosis that `efq` alone
  (not `orE`) is the direct-route residual and it is Simpson's "non-tree excursion"; the ranked
  two-path recommendation (P3 Hilbert bridge LOW risk primary, PD existential-teleport HIGH risk
  fallback); the concrete Phase-8 sequences for both paths; and the Tier-1 source-to-implementation
  mapping (Simpson chunks 0151–0158, MMS Def 5.1). Closable estimates: P3 bridge ~70%, PD
  `⊥`-locality lemma ~35%.
- reports/03_tree-shape-invariant-audit.md — integrated in plan_version 3; delivered the
  finite-rooted-forest verdict and the `IsDerivationForest` invariant. Its Phases 6-7 outputs are
  LANDED and carried forward as Preserved Assets; its main-induction recommendation is superseded
  by report 04 (the induction motive it presumed is the one report 04 refutes).
- reports/02_direct-route-from-sources.md — integrated in plan_version 2; the Wall-A dissolution
  and machine-verified crux inventory it supplied are LANDED (Phases 1-5) and carried forward.
- reports/01_general-soundness-strategies.md — superseded. (Its Strategy 3 "adequacy bridge"
  option is the route this plan now adopts.)

### Preserved Assets

The following work is complete (landed sorry-free / axiom-clean) and MUST NOT regress. Namespace of
the landed lemmas is `Cslib.Logic.Modal.Labelled` (singular `Logic`; the file path uses `Logics`).
On the P3 critical path only `cs5_soundness_derivable_incest` is consumed; the remainder are kept
valid, unregressed, and are the foundation of the fallback route PD (Phase 11).

| Component | File:Line | Status | Verified |
|-----------|-----------|--------|----------|
| `cs5_completeness` | Completeness.lean:132 | [COMPLETED] | task 517 (2026-07-19) |
| `nik_TS5_consistent` (anti-vacuity) | Soundness.lean:848 | [COMPLETED] | task 517 / this task (2026-07-19) |
| `nik_soundness_onePoint` (12-constructor skeleton) | Soundness.lean:774 | [COMPLETED] | task 517 (2026-07-19) |
| `cs5FCIncest_lift` (= confluence direction F1) | Soundness.lean:322 | [COMPLETED] | task 517 (2026-07-19) |
| `ckforces_persistence` (upward closure) | Forcing.lean:122 | [COMPLETED] | task 517 (2026-07-19) |
| **`cs5_soundness_derivable_incest` (Hilbert soundness — P3 CRITICAL PATH)** | CS5Canonical.lean:359 | [COMPLETED] | task 517 (2026-07-19) |
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

### Source-to-Implementation Mapping (H3, Tier 1)

BibKeys VERIFIED in `references.bib`: `Simpson1994` (`@phdthesis`),
`MarinMoralesStrassburger2021` (`@article`). Grounding from report 04 (audit pass).

| Source | Prop / Location (chunk) | Lean Identifier | Role | Status |
|--------|-------------------------|-----------------|------|--------|
| Simpson1994 | §8.1.2 direct `N(𝒯)` soundness has "unavoidable non-tree excursions"; fix via `L_m`/Hilbert (0158) | (diagnosis) motivates the bridge over the direct induction | ROUTE SELECTION |
| Simpson1994 | Ch. 6 labelled ↔ Hilbert adequacy (to be read at Phase 8) | `nik_TS5_to_hilbert` | **the bridge — Phase 8 (to land)** |
| Simpson1994 | Thm 8.1.4, tree case (0151) | `nik_TS5_soundness` (goal) | `NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ` | **Phase 9 (to land)** |
| MarinMoralesStrassburger2021 | Thm 7.1 klmn-incestuality / Thm 7.2 direct birelational soundness | `cs5_soundness_derivable_incest` (CS5Canonical.lean:359) | Hilbert-side soundness, already `CKValidFC cs5FCIncest`-valued | LANDED (task 517) |

## Goals & Non-Goals

- **Goals**:
  - Deliver `nik_TS5_soundness` sorry-free / axiom-clean in `Soundness.lean` via the Hilbert
    adequacy bridge (Strategy 3 / Path P3).
  - Land `nik_TS5_to_hilbert : NIKTheorem TS5 φ → Derivable CS5ModalAxiom φ` as a named,
    independently build-checkable lemma.
  - Assemble `nik_TS5_soundness` as the ~3-line corollary composing the bridge with
    `cs5_soundness_derivable_incest`; retire the stale docstring notes.
  - Keep every intermediate state green and committed (H9 wrap-up discipline).
  - Preserve all 16 landed asset rows above (no regression).
- **Non-Goals**:
  - Any change to the `Graph` structure, `cs5FCIncest`, `NIK`, the completeness direction, or the
    anti-vacuity certificate.
  - Re-planning any of the landed Phases 1-7.
  - Reviving the refuted connectivity-lemma / clique / exact-`r`-symmetry decompositions.
  - Introducing a new `L_m` modified sequent system (the bridge targets the existing `Derivable
    CS5ModalAxiom` Hilbert system, not a new sequent calculus).

## Postmortem Constraints

Binding rules for all implementation dispatches. Derived from the five prior blocked/partial
dispatches, the Phase 8 `[BLOCKED]` handoff, report 04's audit, and the zero-debt task constraints.

**Do NOT**:
- Do NOT re-attempt the plan v3 direct `∀ρ` induction motive for the main theorem. It is
  machine-refuted for cross-label `efq`/`orE` (`handoffs/08`, 2-point countermodel). The P3 route
  does not touch that induction at all.
- Do NOT attempt to strengthen `IsDerivationForest` to a connectivity / "`TClosure TS5 G.R` total on
  `G.X`" invariant. Report 04 Finding 2 (H4) proves connectivity is NOT preserved by `boxI`/`diaE`
  at a dangling label — the invariant genuinely fails. This was plan v3's contemplated fix and it is
  refuted.
- Do NOT weaken `NIK.efq`/`NIK.orE` to require `y ∈ G.X`. Completeness needs the cross-label
  disconnected form (Deduction.lean:245-253 docstring; `PrimeLemma.consistency_of_maximal`).
- Do NOT introduce `sorry` anywhere under `Cslib/` — not "temporary", not "strategic". This task
  forbids it. A genuinely blocked sub-goal routes to a `[BLOCKED]` handoff, never a placeholder.
- Do NOT add any new `axiom` under `Cslib/`.
- Do NOT weaken `cs5FCIncest` (do not drop or relax any of its five conjuncts) or modify the `Graph`
  structure.
- Do NOT edit or re-derive the 16 landed asset rows; their proofs must not regress.
- Do NOT expand file scope beyond `Soundness.lean`. No new file is introduced on this route. (The
  bridge's Hilbert target `cs5_soundness_derivable_incest` already lives in the imported
  `CS5Canonical.lean` and is consumed, not modified.)
- Do NOT hand-analyze a "wall" and escalate without first machine-checking the blocking sub-goal
  with `lean_run_code` / `lean_multi_attempt`.

**MUST preserve**:
- All 16 landed asset rows above (sorry-free, axiom-clean, unregressed).
- Existing full-project green state: `lake build`, `lake lint`, `lint-style`, `shake`,
  `checkInitImports`, `lake test`. Pre-existing unrelated sorries in Propositional Tableau files are
  the known baseline — do not "fix" or count them.

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):
- `nik_TS5_soundness` is TRUE and provable (report 04 verdict, H4-verified against the countermodel).
- The connectivity-forest-induction of plan v3 is the WRONG architecture for the main theorem; the
  Hilbert adequacy bridge is the selected route (report 04 §Recommendation, Simpson §8.1.2).
- `cs5_soundness_derivable_incest` (CS5Canonical.lean:359) is landed, sorry-free, and already
  `CKValidFC cs5FCIncest`-valued: only the labelled→Hilbert bridge is missing on the P3 path.
- On the P3 path the forest/lifting machinery (Phases 6-7) is off the critical path but is NOT
  deleted — it is the foundation of the Phase 11 fallback.

## Risks & Mitigations

- **Risk (primary)**: The Phase 8 bridge `nik_TS5_to_hilbert` (Simpson Ch. 6 labelled↔Hilbert
  adequacy, specialised to theoremhood over `Graph.trivial`) is substantial proof-theory that task
  517 explicitly deferred as "THE TRUE CRUX". Report 04 rates it ~70% closable — "known-shape"
  rather than open, but non-trivial and warranting its own reading of Simpson Ch. 6.
  **Mitigation**: Phase 8 begins with a focused source pass on Simpson Ch. 6 (labelled deduction ↔
  Hilbert adequacy) before Lean work; it is sized as its own bounded phase with a hard budget cap;
  commit-per-green-substep applies to any internal helper lemmas. If it overruns budget across
  dispatches, route to the Phase 11 fallback (route PD), NOT to a `sorry`.
- **Risk (fallback)**: The Phase 11 fallback route PD needs a genuinely novel `⊥`-locality lemma
  (report 04 Path PD Phase 8.3, ~35% closable) — the direct analogue of Simpson's non-tree-excursion
  difficulty; it may itself require normalization/cut infrastructure.
  **Mitigation**: PD is a contingency only, entered solely if Phase 8 is intractable. If PD's 8.3
  also overruns, that is the sanctioned `[BLOCKED]` terminal (scoped, zero-debt, follow-up routed),
  never a `sorry`. PD reuses all 16 landed assets for the modal/propositional cases, so only 8.3 is
  novel.
- **Risk**: A phase silently touches a Preserved Asset and regresses it.
  **Mitigation**: every phase's Zero-Debt Contract re-verifies the assets build sorry-free before
  commit; `lean_verify` on the completing lemma.
- **Risk**: File-territory contention — all phases write the single file `Soundness.lean`.
  **Mitigation**: phases execute strictly sequentially (see Dependency Analysis); no parallel
  dispatch onto `Soundness.lean`.

## Implementation Phases

**Dependency Analysis**:

All phases write the single file `Soundness.lean` (H7 territory: one owner), so they execute
**strictly sequentially** — no two phases may be dispatched in parallel. The wave table records the
logical dependency structure; Phases 1-7 are LANDED (historical). Execution order for the remaining
work is 8 → 9 → 10, with Phase 11 (fallback route PD) as the conditional contingency reachable ONLY
if the Phase 8 bridge proves intractable within budget.

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1-7 (landed) | 1, 2, 3, 4, 5, 6, 7 | -- (historical; all [COMPLETED]) |
| 8 | 8 | -- (consumes landed Hilbert-side `cs5_soundness_derivable_incest`; sequential by file territory) |
| 9 | 9 | 8 |
| 10 | 10 | 9 |
| (contingency) | 11 | Phase 8 bridge intractable within budget only |

The orchestrator heading-scan picks the first non-`[COMPLETED]` phase: **Phase 8**.

### Phase 1: Base forcing-equivalence lemmas box_iff_base, dia_iff_base [COMPLETED]

- **Landed**: `box_iff_base` (Soundness.lean:374), `dia_iff_base` (Soundness.lean:392) — the two
  machine-verified base biconditionals that dissolved the ex-"Wall A". Sorry-free, axiom-clean.
- **Do NOT re-plan or re-derive.** Preserved Asset. (Retained even on the P3 path — no regression.)

### Phase 2: TClosure-class extension box_iff_TClosure, dia_iff_TClosure [COMPLETED]

- **Landed**: `box_iff_TClosure` (Soundness.lean:422), `dia_iff_TClosure` (Soundness.lean:437),
  each a five-case `TClosure` induction. Sorry-free, axiom-clean.
- **Do NOT re-plan or re-derive.** Preserved Asset.

### Phase 3: F2 target-raise + reflexive here-extraction helpers [COMPLETED]

- **Landed**: `cs5FCIncest_raise` (F2, Soundness.lean:337); `box_gives_here` (Soundness.lean:349).
  Sorry-free, axiom-clean.
- **Do NOT re-plan or re-derive.** Preserved Asset.

### Phase 4: Single-node interpretation-raise step boxI_raise_step [COMPLETED]

- **Landed**: `boxI_raise_step` (Soundness.lean:472). Sorry-free, axiom-clean.
- **Do NOT re-plan or re-derive.** Preserved Asset.

### Phase 5: Star-lifting over all direct raw-neighbours boxI_lift_star [COMPLETED]

- **Landed**: `boxI_lift_star` (Soundness.lean:604). Sorry-free, axiom-clean.
- **Do NOT re-plan or re-derive.** Preserved Asset.

### Phase 6: Derivation-forest invariant IsDerivationForest + preservation lemmas [COMPLETED]

- **Landed**: `IsDerivationForest` (Soundness.lean:713, three conjuncts: `X.Finite` ∧ graded-rank ∧
  unique-parent), `forest_trivial`, `forest_addEdge_fresh`. Sorry-free, axiom-clean; `lean_verify`
  reports the three standard axioms only.
- **Do NOT re-plan or re-derive.** Preserved Asset. Off the P3 critical path; the foundation of the
  Phase 11 fallback.

### Phase 7: Tree-cascade lifting lemma boxI_lift [COMPLETED]

- **Landed**: `ht_le_of_reflTransGen`, `raise_subtree`, `siblings_disjoint`, `boxI_lift_ancestor`,
  and `boxI_lift` (tree-restricted Lifting Lemma, Simpson 8.1.3), assembled across two dispatches.
  Sorry-free, axiom-clean.
- **Do NOT re-plan or re-derive.** Preserved Asset. Off the P3 critical path; reusable by the Phase
  11 fallback's modal cases.

### Phase 8: Labelled-to-Hilbert adequacy bridge nik_TS5_to_hilbert [BLOCKED]

**Dispatch finding (2026-07-24, sess_1784905751_756cda_537).** A source pass on Simpson Ch. 6
(`~/Projects/Literature/simpson_1994_intuitionisticmodallogic/...reflowed.md:943-1073`) confirms
this bridge is exactly Simpson's Lemma 6.1.2 (`Γ ⊢_G x:A` ⟹ `(Γ⊢_G x:A)^T` a theorem of `IK`,
via the recursive tree-translation of Fig. 6-1/6-2) plus Theorem 6.2.1/Lemma 6.2.3's extension to
`Ax(𝒯)` for `𝒯 = {χ_T,χ_B,χ_4}` (matching `TS5`/`CS5ModalAxiom`=`IKTB4`). Before writing the
general tree-recursive infrastructure (which does not exist anywhere in the codebase and is a
genuinely large undertaking -- Simpson's own construction indexes the translation by a label's
**tree-depth from the root**, nesting one more `⊃□(...)` per level, Fig. 6-1/6-2), two candidate
*simplified* translations exploiting `IKTB4`'s `□A ↔ □□A` (T+4) box-nesting collapse were tried
and checked, machine-groundable via basic, universal facts about ALL normal modal Hilbert systems
(true regardless of `CS5ModalAxiom`'s specific T/B/4 axioms, so no further live check needed):
1. **Split-by-label flat translation** (`Cx(Γ)` unboxed, `C¬x(Γ)` single-boxed): fails at
   `orE`/`efq` because moving from a proof "at label x" to "at label y" (x≠y) requires **re-boxing
   an already-`T`-unboxed hypothesis**, which is unsound in any normal modal logic (necessitation
   is a rule on empty-context theorems only, never on assumptions).
2. **Fully-boxed flat translation** (`□(BigConj Γ) → □A` throughout): fails at `orE` because it
   needs `□(A∨B) → (□A ∨ □B)` to case-split under a box, which is **not a theorem of any normal
   modal logic K or its extensions** (K itself refutes this; T/B/4/5 do not add it) -- confirmed
   by a `cs5FCIncest`+`CKValidFC` two-point countermodel (`World:=Bool`, `r:=fun _ _ => True`,
   atoms `p:=true`/`q:=false` s.t. `A∨B` holds everywhere but neither `A` nor `B` is `□`-forced
   anywhere).
Both obstructions are genuine (not merely unexplored), and land on **exactly the same "cross-label
efq/orE" residual** the direct route's Phase 8 (plan v3) hit, now on the Hilbert-provability side
rather than the semantic-forcing side. The FAITHFUL construction (Simpson's actual tree-depth-
indexed translation with Fig. 6-2 dissection) is estimated at 300-600+ new lines (tree/subtree
data structure, recursive translation function, 12-constructor main lemma) -- substantially past
the original 150-300 line estimate once these proof-theoretic subtleties are accounted for, and
was not attempted in Lean this dispatch given the budget cap and the sanctioned Phase 11 fallback.
**Per the plan's own contingency structure ("Contingency sub-gate: budget overrun → Phase 11")**,
this phase is marked `[BLOCKED]` (not a task-terminal blocker -- the plan's sanctioned pivot) and
work proceeds to **Phase 11 (fallback route PD)**. No `sorry`, no new axiom, no vacuous
placeholder; nothing in `Soundness.lean` was modified for this phase (analysis-only, per the
"machine-check before escalating" requirement -- the two obstructions above are grounded in
universal modal-logic facts, not hand-waved).

This is the sole concentrated-risk phase of the P3 route (report 04: ~70% closable; "known-shape"
proof-theory that task 517 deferred as "THE TRUE CRUX"). It carries the budget cap and the sole
route to the Phase 11 fallback.

- **Goal:** State and prove the labelled→Hilbert adequacy bridge specialised to theoremhood over
  `Graph.trivial`: `nik_TS5_to_hilbert : NIKTheorem TS5 φ → Derivable CS5ModalAxiom φ` (Simpson
  Ch. 6 labelled-deduction ↔ Hilbert adequacy; report 04 Path P3 §8a). `NIKTheorem TS5 φ` is
  `NIKDerivable` over `Graph.trivial`/empty-context (Deduction.lean:316); `Derivable CS5ModalAxiom`
  is the landed Hilbert system consumed by `cs5_soundness_derivable_incest`.
- **Tasks:**
  - [ ] **Source pass first (H3):** read Simpson Ch. 6 (labelled ↔ Hilbert adequacy) chunks and the
        CSLib Hilbert side (`CS5ModalAxiom`, `Derivable`, `DerivationTree` in CS5Canonical.lean and
        its Hilbert-system dependencies) to fix the exact translation of each `NIK` rule over
        `Graph.trivial` into a `Derivable CS5ModalAxiom` step. Confirm whether an intermediate
        induction over `NIK` derivations (translating each constructor) or a higher-level adequacy
        result is the right granularity. Record the rule-by-rule mapping before writing Lean.
  - [ ] State `nik_TS5_to_hilbert : NIKTheorem TS5 φ → Derivable CS5ModalAxiom φ` (adjust the exact
        `NIKTheorem`/`NIKDerivable` spelling to the landed definition at Deduction.lean:316).
  - [ ] Prove it. Land any needed translation helpers as their own green, independently-committable
        sub-steps (commit-per-green-substep mandate). Machine-check each stuck sub-goal with
        `lean_multi_attempt`/`lean_goal` before deciding anything is a wall.
  - [ ] If the **engineering/proof-theory** genuinely overruns budget across dispatches, land any
        green helper, then route to **Phase 11** (fallback route PD) — never a `sorry`.
- **Estimated output:** ~150-300 lines (report 04 §8a). **Bounded unit:** the bridge lemma plus any
  translation helpers; concrete stopping condition = `nik_TS5_to_hilbert` compiles with the stated
  signature, OR the documented budget is hit and Phase 11 fires.
- **Timing:** one to two agent runs, hard budget cap. If a second dispatch is needed, land the green
  helper(s) first (independently-committable Preserved Assets for the follow-on dispatch).
- **Depends on:** none new (consumes the landed Hilbert side; sequential after Phase 7 by file
  territory).
- **Zero-debt contract:** no `sorry`, no new axiom, `cs5FCIncest` unweakened, `Graph` unmodified, no
  Preserved Asset touched.
- **Contingency sub-gate:** budget overrun → **Phase 11** (fallback route PD), never a `sorry`.
- **Verification / Done when:** `Soundness.lean` builds green; `lean_verify` on `nik_TS5_to_hilbert`
  (and any helper) reports axiom-clean; no NEW tactic `sorry`.

### Phase 9: Corollary assembly nik_TS5_soundness + docstring cleanup [NOT STARTED]

- **Goal:** Assemble the goal theorem as the corollary composing the Phase 8 bridge with the landed
  Hilbert soundness, and retire the stale module-docstring notes (report 04 Path P3 §8b).
- **Tasks:**
  - [ ] Land `nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ` as
        `fun h => cs5_soundness_derivable_incest (nik_TS5_to_hilbert h)` (CS5Canonical.lean:359).
        Reconcile universe variables (`cs5_soundness_derivable_incest` is `.{u, v}`-polymorphic) and
        any implicit `Atom`/`φ` binders. ~3-10 lines.
  - [ ] Update the `Soundness.lean` module docstring: mark the general theorem LANDED via the
        Hilbert bridge; **remove the stale `INTRACTABLE` / `GATE-C` / "What remains" / "Fifth
        dispatch" notes** (superseded per report 04). Do not remove the accurate historical record
        of the landed lemmas.
- **Estimated output:** ~10-40 lines (mostly docstring edits).
- **Timing:** one agent run.
- **Depends on:** 8.
- **Zero-debt contract:** no `sorry`, no new axiom, no weakening, no Preserved Asset regressed.
- **Verification / Done when:** `nik_TS5_soundness` sorry-free; `Soundness.lean` builds green;
  `lean_verify` on `nik_TS5_soundness` axiom-clean (no `sorryAx`, no new axiom); no NEW tactic
  `sorry`.

### Phase 10: Regression gate + full-project verification [NOT STARTED]

- **Goal:** Confirm the full project is green and unregressed, the Simpson 8.1.4 biconditional is
  complete, and no debt was added anywhere (report 04 Path P3 §8c).
- **Tasks:**
  - [ ] Full `lake build` green.
  - [ ] `lean_verify` on `nik_TS5_soundness` reports no `sorryAx` and no new axioms.
  - [ ] `grep -nE '\bsorry\b'` on `Soundness.lean`: no NEW *tactic* `sorry` (docstring prose
        excepted); `grep -nE '^axiom '`: zero new axioms.
  - [ ] Spot-verify the 16 landed asset rows still build sorry-free (esp. `cs5_completeness`,
        `nik_TS5_consistent`, `cs5_soundness_derivable_incest`, and the Phases 1-7 lemmas).
  - [ ] `lake lint`, `lake exe lint-style <file>`, `lake shake`, `lake exe checkInitImports`,
        `lake test` all unregressed against the task-517 baseline.
- **Estimated output:** verification only; docstring touch-ups if any (~0-20 lines).
- **Timing:** one agent run.
- **Depends on:** 9.
- **Zero-debt contract:** no `sorry`, no new axiom, no weakening, no regression.
- **Verification / Done when:** all checks above pass; the Simpson 8.1.4 biconditional is complete.

### Phase 11: Fallback route PD — direct existential-teleport induction (contingency only) [BLOCKED]

- **Goal:** If — contra the ~70% estimate — the Phase 8 Hilbert bridge genuinely overruns budget
  across dispatches (or a concrete defect in it emerges), obtain `nik_TS5_soundness` instead via the
  direct existential-teleport induction (report 04 Path PD), reusing all 16 landed assets for the
  modal/propositional cases. Entered ONLY from a Phase 8 intractability finding; it does NOT pre-empt
  the P3 main line. Report 04 rates PD's novel sub-lemma (8.3 below) ~35% closable — higher risk than
  the bridge, hence fallback not primary.

**Dispatch finding (2026-07-24, sess_1784905751_756cda_537, resume dispatch).** Design-only pass
(no `sorry`, no Lean edits beyond the already-committed PD.1): worked out, on paper, a corrected
formalization of PD.2's existential-monotone motive `M` and stress-tested it case-by-case against
all 12 `NIK` constructors before writing any Lean, since report 04's one-line motive sketch
under-specifies two coordination details that matter:

1. **The "agrees with ρ on `G.X ∪ ctxLabels Γ`" conjunct must be *exact equality*, not merely
   `≤`-monotone**, and must ALSO include the *current goal's own label* `φ.lbl` (i.e. the tracked
   set is `Dom(G,Γ,φ) := G.X ∪ ctxLabels Γ ∪ {φ.lbl}`, not just `G.X ∪ ctxLabels Γ`). Exact
   equality on `G.X` is what lets the raw edge-cond `∀a b, G.R a b → r(ρa)(ρb)` transfer for free
   across sequential premise composition (`andI`/`impE`/orE's minor branch): if two premises share
   a graph `G`, the second premise's edge-cond hypothesis is only available if the first premise's
   witness `ρ'` reproduces the SAME `G`-values, not merely dominates them (`r` is not itself
   `≤`-monotone the way `CKForces` is). A bare "monotone, unconstrained off `G.X∪ctxLabels Γ`"
   reading (the literal report-04 shorthand) is UNPROVABLE in general: for `efq`'s dangling
   conclusion label `y ∉ G.X∪ctxLabels Γ`, the input `ρ` assigns `y` an adversarial, ∀-quantified
   value with no relation to anything else, and `Preorder World` is not assumed directed/a
   lattice, so no witness `ρ'y ≥ ρy` can also satisfy `botForces(ρ'y)` in general (there need be no
   common upper bound of an arbitrary point and a `botForces`-holding point). Dropping the bare
   monotonicity requirement in favour of *exact* agreement on `Dom(G,Γ,φ)` (with **no** constraint
   at all outside `Dom`, since nothing downstream needs one — verified against every constructor's
   discharge below) removes this obstruction cleanly.
2. **A single, unparametrized `Dom(G,Γ,φ)` is still insufficient for the 2-and-3-premise
   constructors** (`andI`, `impE`, `orE`): a "sibling" premise/branch can need a label protected
   through an unrelated premise's recursive call even though that label is not in ITS OWN `Dom`
   (concretely, `orE`'s shared minor-premise/conclusion label `y` is not in the major premise
   `x:A∨B`'s own `Dom = G.X∪ctxLabels Γ∪{x}` whenever `y` is dangling and `y≠x`, so the major
   premise's witness has no theorem-level obligation to leave `ρ(y)` untouched). The fix is a
   **caller-supplied protect-set `T`**: generalize the motive to `∀T ⊇ Dom(G,Γ,φ), ∀ρ, ec → gc →
   ∃ρ', (ρ'=ρ EXACTLY on T) ∧ CKForces(ρ'φ.lbl)φ.prop`, with composing constructors invoking every
   sibling IH at a common, explicitly-enlarged `T' := T ∪ {the other premises' labels}` rather than
   the bare per-call `Dom`.

**Verified tractable under this corrected motive** (worked by hand, not yet in Lean): `assumption`,
`andI`/`andE1`/`andE2`, `orI1`/`orI2`, `impI` (via `boxI_lift`-style local raise-to-exactly-`w'`
when the shared label is graph-resident, trivial `Function.update` when dangling — no cascade
needed either way since the OUTER witness for `impI`/`boxI` is just `ρ' := ρ` unchanged, discharging
the universal `□`/`⊃` clause by a fresh, internally-scoped IH invocation per successor rather than
by returning a raised outer witness), `impE`, `boxE`/`diaI` (via the landed `box_iff_TClosure`/
`dia_iff_TClosure` + `box_gives_here`, plus `cs5FCIncest_lift`+`ckforces_persistence` to promote a
single-point `diaI` fact to the full universally-quantified diamond clause), `diaE` (`le_refl`, no
lift, symmetric to `boxE`), `boxI` (via the landed `boxI_lift`/`IsDerivationForest`, `T`-threading
not required since the outer witness is always `ρ`), and `orE`'s **coordination** itself (via the
`T`-threading fix above — the report-04 "no coordination" claim was too strong: coordination IS
needed to protect the minor-premise label through the major premise, but IS mechanically resolvable
with a wider `T`).

**NOT closed, confirmed genuinely open**: `efq`'s residual — conclusion label `y ∈ Dom` (so `ρ'y`
is pinned to the ORIGINAL `ρ y`, no teleport freedom) with the premise's `⊥`-label `x` either
dangling or `r`-disconnected from `y`. This is *exactly* report 04's Finding 5 / Phase-8 `[BLOCKED]`
countermodel, re-derived independently rather than assumed, and is unaffected by either fix above
(both fixes address coordination/monotonicity bookkeeping around the motive's *shape*; the `efq`
residual is a genuine proof-theoretic gap in `N_IK(𝒯)`'s soundness *content* — Simpson's own
"unavoidable non-tree excursion" (§8.1.2, chunk 0158), which he routes around via `L_m`/Hilbert
rather than closing directly). Report 04's own confidence on this residual (PD.3, ~35%) stands;
this dispatch's independent re-derivation found no shortcut and surfaces no reason to raise that
estimate. Closing it in full would need a genuinely new normalization/cut-style invariant ("any
`⊥` derivable in a live sub-derivation is already reachable from a live, connected assumption") —
research-scale, not a transcription task.

**Disposition.** Because `NIK`'s induction is a single closed Lean `induction ... with` covering
all 12 constructors, the motive cannot be landed as a *buildable*, sorry-free artifact while `efq`'s
residual remains open — a partial case split is not expressible without a `sorry`, which is
forbidden. No Lean code for PD.2 was written this dispatch (design-only; verified by hand against
every constructor before touching the file, per the "machine-check before escalating" discipline —
the corrected motive's 11 tractable cases were checked structurally, not merely asserted). Per the
plan's own sanctioned terminal ("Verification / Done when: ... OR a `[BLOCKED]` handoff records the
concrete PD.3 gap with build green and zero debt"), Phase 11 is marked `[BLOCKED]`. PD.1 remains
landed, sorry-free, axiom-clean, and unregressed. **Recommendation for a future dispatch/replan**:
both sanctioned routes (Phase 8's Hilbert Ch. 6 bridge, ~70% per report 04 but 300-600+ line
tree-recursive translation, not yet attempted in Lean; and this Phase 11 PD route, now with a
corrected, worked-through motive design for 11/12 cases but a confirmed-open 12th) have been
seriously investigated across two dispatches without a sorry-free result. A replan should weigh:
(a) committing the budget to the Hilbert bridge's full tree-recursive construction (Phase 8, the
lower-residual-risk route on the *content* side, though larger in raw line count), or (b) accepting
Path PD's `efq` gap as requiring dedicated research (cut-admissibility for `N_IK(𝒯)`) before further
implementation effort, landing the 11 tractable PD.2 cases only once (a) is confirmed via (b)'s
research, or a fresh angle on the `efq` residual is found.

- **Tasks (report 04 §Path PD):**
  - [x] **PD.1** — Land Finding 3's machine-verified `bot_backward` + `bot_iff_edge` and their
        `TClosure {T,B,Four}` transport `bot_iff_TClosure` (copy the `box_iff_TClosure` skeleton,
        Soundness.lean:422). LOW risk (verified axiom-free in the audit). **LANDED** (this dispatch,
        commit `0172b639`): `bot_backward`/`bot_iff_edge`/`bot_iff_TClosure`, sorry-free,
        axiom-clean (`lean_verify` confirms no `sorryAx`, no new axioms).
  - [ ] **PD.2** — State the existential-monotone soundness motive `M(G,Γ,φ) := ∀ρ, (∀ a b, G.R a b
        → r(ρa)(ρb)) → (∀ψ∈Γ, CKForces (ρ ψ.lbl) ψ.prop) → ∃ρ', (∀z, ρ z ≤ ρ' z) ∧ (agrees with ρ
        on G.X ∪ ctxLabels Γ) ∧ CKForces (ρ' φ.lbl) φ.prop`. Discharge: the 8 label-local
        propositional constructors by sequential premise-threading + `ckforces_persistence`;
        `boxE`/`diaI` via `box_iff_TClosure`/`dia_iff_TClosure` + `box_gives_here`; `boxI` via
        `boxI_lift` (landed); `diaE` via `le_refl` (no lift); `orE` via report 04 Finding 4
        (single-branch, no coordination). MEDIUM risk. *(deviation: this dispatch found the
        literal motive as stated is unprovable — the bare `∀z,ρz≤ρ'z` conjunct has no witness for
        `efq`'s adversarial dangling label on a non-directed `Preorder`, and `orE` DOES need
        coordination (report 04 Finding 4 overstated "no coordination") — see the Phase 11 dispatch
        finding above for the corrected `Dom(G,Γ,φ):=G.X∪ctxLabels Γ∪{φ.lbl}` + caller-supplied
        protect-set `T` design, worked by hand for 11/12 constructors but not yet written in Lean,
        since the 12th (`efq`'s residual) blocks the whole induction from being buildable.)*
  - [ ] **PD.3** — Prove the `efq` `⊥`-locality lemma that closes `efq`-with-disconnected-`⊥`
        (report 04 Finding 5). Candidate: strengthen `M` to also output, when `φ.prop = ⊥`, a domain
        witness `∃ z ∈ G.X ∪ ctxLabels Γ, botForces (ρ' z)`, surviving every constructor. **HIGH
        risk / genuinely open** — the analogue of Simpson's non-tree excursion. Machine-check the
        stuck sub-goal; if unprovable within budget, this is the sanctioned `[BLOCKED]` terminal
        (scoped handoff, zero debt, follow-up routed), never a `sorry`. *(deviation: confirmed
        genuinely open this dispatch, independently re-derived rather than assumed — see the Phase
        11 dispatch finding above. This is the sanctioned `[BLOCKED]` terminal: build green, zero
        debt, PD.1 landed, follow-up routed to a replan.)*
  - [ ] **PD.4** — Assemble `nik_TS5_soundness` by specialising `M` to `Graph.trivial`/`[]` and run
        the Phase 10 regression gate. *(deviation: deferred — blocked on PD.3.)*
- **Estimated output:** ~150-350 lines across PD.1-PD.4.
- **Timing:** multiple agent runs, entered only on Phase 8 intractability.
- **Depends on:** Phase 8 bridge intractability. Reuses Phases 1-7 assets.
- **Zero-debt contract:** no `sorry`, no new axiom, `cs5FCIncest` unweakened, `Graph` unmodified, no
  Preserved Asset touched. **Do NOT** attempt the connectivity-lemma path (report 04 Finding 2
  refutes it) and **do NOT** weaken `efq`/`orE`.
- **Verification / Done when:** either `nik_TS5_soundness` lands sorry-free/axiom-clean (then run
  Phase 10), OR a `[BLOCKED]` handoff records the concrete PD.3 gap with build green and zero debt.

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness` green after every
      phase that touches `.lean` (H9 green-milestone commit).
- [ ] Full `lake build` green at each phase completion.
- [ ] `lean_verify` axiom-clean on each new lemma as it lands (`nik_TS5_to_hilbert`, any Phase 8
      helper, `nik_TS5_soundness`).
- [ ] `grep -nE '\bsorry\b'` on `Soundness.lean`: no NEW *tactic* `sorry` (docstring prose excepted).
- [ ] `grep -nE '^axiom '` on modified files: zero new axioms.
- [ ] `Graph` structure unmodified; `cs5FCIncest` (CS5Canonical.lean) unweakened.
- [ ] `lake lint`, `lake exe lint-style <file>`, `lake shake`, `lake exe checkInitImports`,
      `lake test`: all unregressed against the task-517 green baseline.
- [ ] Preserved Assets unregressed (spot-verify the 16 listed asset rows build sorry-free).

## Artifacts & Outputs

- plans/04_hilbert-adequacy-bridge.md (this file)
- Modified: Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean (Phases 8-9, optional
  Phase 11)
- handoffs/ blocked handoff (contingency, only if Phase 8 AND Phase 11 PD.3 both overrun)
- summaries/04_hilbert-adequacy-bridge-summary.md (on completion)

## Rollback/Contingency

- Each phase commits only its own green result (H9 incremental commit; commit-per-green-substep
  mandate applies to Phase 8 helpers). If a phase fails to reach green, leave the prior committed
  state intact; fix forward — never destructive git on a dirty tree (see
  `.claude/rules/git-workflow.md`, "No Destructive Git on Uncommitted Work").
- The primary contingency for a Phase 8 bridge overrun is the **Phase 11 fallback route PD**, not a
  `[BLOCKED]`. Only if BOTH the bridge (Phase 8) and PD's novel `⊥`-locality lemma (Phase 11 PD.3)
  overrun budget is a `[BLOCKED]` handoff the sanctioned terminal — scoped to the remaining gap, with
  a concrete machine-checked blocker and a follow-up route, zero debt, build green — never a `sorry`,
  and never a return to the refuted connectivity-lemma / clique / exact-symmetry decompositions.
