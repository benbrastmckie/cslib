# Implementation Plan: Direct-Route General Labelled CS5 Soundness (nik_TS5_soundness)

- **Task**: 537 - Prove the general labelled soundness direction, completing Simpson 1994 Thm 8.1.4's biconditional
- **Status**: [IMPLEMENTING]
- **Effort**: 8-14 hours (mainline; risk concentrated in Phase 4.2)
- **Dependencies**: 517 (delivered completeness + anti-vacuity + landed building blocks)
- **Research Inputs**: reports/02_direct-route-from-sources.md (Tier 1, H4-verified, all cruxes machine-verified axiom-free)
- **Artifacts**: plans/02_direct-route.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/plan-format-enforcement.md
  - .claude/context/formats/plan-format.md
  - .claude/context/contracts/wrap-up.md
  - .claude/context/contracts/reference-grounding.md
- **Type**: cslib
- **Plan version**: 2 (supersedes plans/01_general-soundness.md)

## Overview

Prove **directly** `nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ` in the single
file `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`, closing the soundness
direction (2⟹1) of Simpson Thm 8.1.4 for CSLib constructive CS5/IS5. **No adequacy bridge, no
`L_m` sequent system, no new file.** The completeness direction and anti-vacuity certificate are
already landed sorry-free by parent task 517.

This plan **supersedes** `plans/01_general-soundness.md`, which was built around a now-refuted
"exact-edge symmetry" obstruction (its "Wall A") and a three-outcome `[BLOCKED]` pivot gate.
Report 02 (source-grounded against Simpson Ch.8 and MMS 2021, every mathematical crux
machine-verified via `lean_run_code` + `#print axioms` = "does not depend on any axioms") shows
the prior `[BLOCKED]` rested on proving the **wrong lemma** (`TClosure`-closed edge ⟹ exact
`r`-edge, which needs exact symmetry — false-in-general and unnecessary). The correct central
result is box/diamond **forcing-equivalence across the `TClosure {T,B,Four}` class**, provable
from the raised-witness conjuncts of `cs5FCIncest` alone. The direct route is assessed **~80-85%**
completable, with residual risk concentrated **solely** in the Phase 4.2 `boxI` tree-lifting
recursion.

### Definition of Done

`nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ` lands sorry-free and axiom-clean
in `Soundness.lean`; full `lake build` green; `lean_verify nik_TS5_soundness` reports no `sorryAx`
and no new axioms; `lake lint` / `lint-style` / `shake` / `checkInitImports` / `test` unregressed
against the task-517 green baseline. Sanctioned terminal alternative if (contra the estimate) the
Phase 4.2 recursion genuinely stalls: a documented `[BLOCKED]` handoff routed to a follow-up task,
build still green, zero debt — **never a `sorry`** (Phase 7).

### Research Integration

- reports/02_direct-route-from-sources.md — integrated in plan_version 2 (2026-07-19). Supplies
  the refuted-wall correction, the machine-verified crux inventory (`box_iff_base`, `dia_iff_base`,
  `F1`, `F2`, `box_gives_here`), the H3 source-to-implementation mapping, and the ranked
  de-risking order this plan encodes.
- reports/01_general-soundness-strategies.md — superseded. Its "genuinely open / Wall A"
  conclusion is explicitly refuted by report 02 and is NOT carried forward.

### Preserved Assets

The following work is complete (landed sorry-free / axiom-clean by task 517) and MUST NOT regress.
All line numbers verified against the current tree.

| Component | File | Status | Verified |
|-----------|------|--------|----------|
| `cs5_completeness` | Completeness.lean:132 | [COMPLETED] | task 517 (2026-07-19) |
| `nik_TS5_consistent` (anti-vacuity) | Soundness.lean:419 | [COMPLETED] | task 517 (2026-07-19) |
| `nik_soundness_onePoint` (12-constructor skeleton) | Soundness.lean:345 | [COMPLETED] | task 517 (2026-07-19) |
| `cs5FCIncest_lift` (= confluence direction F1) | Soundness.lean:322 | [COMPLETED] | task 517 (2026-07-19) |
| `ckforces_persistence` (upward closure) | Forcing.lean:122 | [COMPLETED] | task 517 (2026-07-19) |
| `cs5_soundness_derivable_incest` (Hilbert soundness) | CS5Canonical.lean:373 | [COMPLETED] | task 517 (2026-07-19) |

### Source-to-Implementation Mapping (H3, Tier 1)

BibKeys VERIFIED in `references.bib`: `Simpson1994` (`:86`, `@phdthesis`),
`MarinMoralesStrassburger2021` (`:962`, `@article`). Sources read this pass: Simpson chunks
0151-0158; MMS chunks 0026, 0028, 0043, 0044, 0046, 0048 (recipe: `.lit-access.md`; the
`literature-search.sh` wrapper is degraded — use direct `sqlite3` per that file). OCR caveat
honored: every symbol-heavy claim is cross-checked against the live Lean API. `cs5FCIncest`'s five
conjuncts are destructured as `⟨hrefl, htrans, hfour, hsymbox, hincest⟩` (CS5Canonical.lean:255,
:281); the `CKForces .box` clause is `Forcing.lean:75`; `@[simp]` shapes `CKForces_box`/
`CKForces_diamond` at Forcing.lean:106/:112.

| Source | Prop / Location | Lean Identifier | Type Signature | Status |
|--------|-----------------|-----------------|----------------|--------|
| MarinMoralesStrassburger2021 | ⊠gklmn soundness, fresh-witness (chunk 0046) | `box_iff_base` | `r a b → ((∀ w' ≥ a, ∀ u, r w' u → P u) ↔ (∀ w' ≥ b, ∀ u, r w' u → P u))` | pending |
| MarinMoralesStrassburger2021 | 3L / dia case (chunk 0028, 0046) | `dia_iff_base` | `r a b → ((∀ w' ≥ a, ∃ u, r w' u ∧ Q u) ↔ (∀ w' ≥ b, ∃ u, r w' u ∧ Q u))` | pending |
| Simpson1994 + MMS | box-persistence over class (chunks 0028, 0046) | `box_iff_TClosure` / `dia_iff_TClosure` | `TClosure TS5 R a b → (CKForces … (□A) ↔ CKForces … (□A))` (dia dual) | pending |
| MarinMoralesStrassburger2021 | refl/trans/F1/F2 trivial (chunk 0028) | `F2` (target-raise) | `r w u → u ≤ u' → ∃ w', w ≤ w' ∧ r w' u'` | pending |
| Simpson1994 | Lifting Lemma 8.1.3, single-node step (chunks 0153-0155) | `boxI_raise_step` (Phase 4.1) | interpretation-raise preserving raw edge-cond + Γ-cond | pending |
| Simpson1994 | Lifting Lemma 8.1.3 iterated + §8.1.2 (□I) (chunks 0154-0156) | `boxI_lift` (Phase 4.2) | full tree-lifting, closes `boxI` case | pending |
| Simpson1994 | Thm 8.1.1 / 8.1.4, tree case (chunk 0151) | `nik_TS5_soundness` (goal) | `NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ` | pending |
| MarinMoralesStrassburger2021 | Def 5.1 G-interpretation, raw atoms (chunk 0026) | raw edge-cond invariant `∀ a b, G.R a b → r (ρa) (ρb)` | (threaded through Phase 5 induction) | pending |

Confluence direction **F1** = the already-landed `cs5FCIncest_lift` (Soundness.lean:322):
`r w u → w ≤ w' → ∃ u', u ≤ u' ∧ r w' u'`.

## Goals & Non-Goals

- **Goals**:
  - Deliver `nik_TS5_soundness` sorry-free / axiom-clean in `Soundness.lean` via the direct route.
  - Land the reusable box/diamond forcing-equivalence lemmas and the F2 confluence direction as
    named, independently-verified lemmas.
  - Keep every intermediate state green and committed (H9 wrap-up discipline).
- **Non-Goals**:
  - Any adequacy bridge (`Adequacy.lean`, Simpson Ch.6) or `L_m` modified sequent system — report
    02 shows neither is needed and the user declined the bridge.
  - Any change to the completeness direction, the anti-vacuity certificate, or `cs5FCIncest`.
  - Reviving the refuted "exact `r`-symmetry" / clique edge-cond invariant from plan 01.

## Postmortem Constraints

Binding rules for all implementation dispatches. Derived from the four prior blocked dispatches,
report 02's refutation of them, and the zero-debt task constraints.

**Do NOT**:
- Do NOT re-attempt the refuted lemma `TClosure TS5 R a b → r (ρa) (ρb)` (validate each closed
  edge as an **exact** `r`-edge). Its `.symm` case demands exact symmetry, which `cs5FCIncest`
  does not supply and constructively should not (birelational `R` is not symmetric). It is
  **false-in-general and unnecessary** — four dispatches died on it. The correct object is the
  box/diamond forcing-**equivalence** across the `TClosure` class (Phases 1-2).
- Do NOT maintain a **clique** edge-cond invariant (`∀ a b, TClosure TS5 G.R a b → r (ρa)(ρb)`).
  Maintain the **raw** edge-cond invariant (`∀ a b, G.R a b → r (ρa)(ρb)`, MMS Def 5.1, chunk
  0026) and discharge the `TClosure`-closed `boxE`/`diaI` premises via the Phase 2 persistence
  lemmas — never by re-validating the closed edge.
- Do NOT introduce `sorry` anywhere under `Cslib/` — not even "temporary" or "strategic". This
  task forbids it. This plan is NOT a skeleton (`plan_metadata.skeleton: false`) and has NO
  planned strategic sorries. A genuinely blocked sub-goal routes to a `[BLOCKED]` handoff (Phase
  7), never a placeholder.
- Do NOT add any new `axiom` under `Cslib/`.
- Do NOT weaken `cs5FCIncest` (do not drop or relax any of its five conjuncts `hrefl`/`htrans`/
  `hfour`/`hsymbox`/`hincest` to force a proof through).
- Do NOT edit or re-derive the six Preserved Assets; their proofs must not regress.
- Do NOT expand file scope beyond `Soundness.lean`. No new file is introduced on this route.
- Do NOT hand-analyze a "wall" and escalate without first machine-checking the blocking lemma with
  `lean_run_code` / `lean_multi_attempt` — the specific failure mode of the four prior dispatches.

**MUST preserve**:
- All six Preserved Assets above (sorry-free, axiom-clean, unregressed).
- Existing full-project green state: `lake build`, `lake lint`, `lint-style`, `shake`,
  `checkInitImports`, `lake test`. Pre-existing unrelated sorries in Propositional Tableau files
  are the known baseline — do not "fix" or count them.

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):
- The `CKForces .box` clause (Forcing.lean:75) is **identical** to the standard birelational box
  clause (Simpson Ch.3; MMS Def 2) — NOT stronger. The obstruction was architectural (the
  `TClosure`-closed premise on `boxE`/`diaI`), not semantic. Do not re-litigate the forcing clause.
- Wall A dissolves via `box_iff_base` / `dia_iff_base` (both machine-verified axiom-free): the
  ex-"symm" direction is discharged by `hincest` then `hfour` (box) / `hincest`+`hsymbox`+`htrans`
  (dia). No exact symmetry anywhere.
- The biconditionals extend over all of `TClosure {T,B,Four}` by a trivial `Iff` induction: `base`
  = the Phase 1 lemma, `refl` = `Iff.rfl`, `symm` = `Iff.symm`, `trans` = `Iff.trans`, `eucl` =
  vacuous (`Five ∉ TS5`, Deduction.lean:207-208).
- Confluence has BOTH directions from `cs5FCIncest`: F1 = landed `cs5FCIncest_lift`; F2 =
  `hsymbox` then `hincest` (~3 lines). Lifting is needed for `boxI` ONLY; `diaE` uses `le_refl`
  and needs none.
- `NIK` and `cs5FCIncest` stay exactly as landed (no regression, no rule change).

## Risks & Mitigations

- **Risk**: The Phase 4.2 `boxI` tree-lifting recursion is the sole concentrated risk (~80-85%
  overall confidence; F1/F2 verified, the freshness/finite-tree invariant is standard
  Simpson-8.1.3 structure but not reduced to a compiling snippet this pass).
  **Mitigation**: Phase 4 is split into 4.1 (single-node raise step, bounded, machine-checkable in
  isolation) and 4.2 (the iterated recursion). Phase 4.2 carries a hard budget cap and a
  blocked-honesty exit to Phase 7 (`[BLOCKED]` handoff), never a `sorry` and never an undirected
  retry.
- **Risk**: A phase silently touches a Preserved Asset and regresses it.
  **Mitigation**: every phase's Zero-Debt Contract re-verifies the six assets build sorry-free
  before commit; `lean_verify` on the completing phase.
- **Risk**: Reintroducing the refuted clique/exact-symmetry decomposition under time pressure.
  **Mitigation**: the Postmortem Constraints forbid it explicitly; Phases 1-2 provide the correct
  persistence lemmas so the closed-edge premise never needs exact validation.
- **Risk**: File-territory contention — all phases write the single file `Soundness.lean`.
  **Mitigation**: phases execute strictly sequentially (see Dependency Analysis); no parallel
  dispatch onto `Soundness.lean`.

## Implementation Phases

**Dependency Analysis**:

All phases write the single file `Soundness.lean` (H7 territory: one owner), so they execute
**strictly sequentially** — no two phases may be dispatched in parallel. The wave table below
records the logical dependency structure; execution order is 1 → 2 → 3 → 4 → 5 → 6, with Phase 7
as the conditional contingency terminal reachable from a Phase 4.2 stall.

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | -- (logically independent; F1 landed, F2 tiny) |
| 4 | 4 (4.1, 4.2) | 3 |
| 5 | 5 | 2, 4 |
| 6 | 6 | 5 |
| (contingency) | 7 | 4.2 stall (or Phase 5 escalation) |

Phase order is de-risking order (report 02 ranked steps): land the machine-verified cruxes
(Phases 1-3) first, each sorry-free and build-green, before the concentrated-risk Phase 4.2.

### Phase 1: Base forcing-equivalence lemmas box_iff_base, dia_iff_base [COMPLETED]

- **Goal:** Land the two machine-verified base biconditionals that dissolve the ex-"Wall A"
  (report 02 §4(A)). These are the load-bearing cruxes and are already known to compile axiom-free.
- **Tasks:**
  - [x] State and prove `box_iff_base : r a b → ((∀ w' ≥ a, ∀ u, r w' u → P u) ↔ (∀ w' ≥ b, ∀ u,
        r w' u → P u))` with `P` an arbitrary predicate. Forward direction via `hfour`; backward
        (ex-"symm") via `hincest` then `hfour`. Cite `cs5FCIncest` conjuncts (CS5Canonical.lean:255).
  - [x] State and prove `dia_iff_base : r a b → ((∀ w' ≥ a, ∃ u, r w' u ∧ Q u) ↔ (∀ w' ≥ b, ∃ u,
        r w' u ∧ Q u))` with `Q` arbitrary. Forward via `hsymbox`+`htrans`; backward via
        `hincest`+`hsymbox`+`htrans`.
  - [x] Confirm the clause shapes match `CKForces_box` / `CKForces_diamond` (Forcing.lean:106/:112)
        so the lemmas apply to real forcing goals (predicates `P`/`Q` are NOT assumed upward-closed).
- **Estimated output:** ~120-180 lines. **Bounded unit:** two named lemmas, each provable in
  isolation from the `cs5FCIncest` conjuncts; concrete stopping condition = both compile.
- **Timing:** one agent run.
- **Depends on:** none
- **Zero-debt contract:** no `sorry`, no new axiom, `cs5FCIncest` unweakened, no Preserved Asset
  touched. Both lemmas sorry-free before commit.
- **Verification / Done when:** `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness`
  green; `lean_verify` on each new lemma reports axiom-clean; `grep` finds no tactic `sorry`.

### Phase 2: TClosure-class extension box_iff_TClosure, dia_iff_TClosure [COMPLETED]

- **Goal:** Extend the Phase 1 base biconditionals over the entire `TClosure {T,B,Four}` class by
  induction on `TClosure` (report 02 §4(A)), giving the transport lemmas the `boxE`/`diaI` cases need.
- **Tasks:**
  - [x] Prove `box_iff_TClosure : TClosure TS5 R a b → (CKForces … a (□A) ↔ CKForces … b (□A))`
        by induction on the `TClosure` derivation: `base` → `box_iff_base`; `refl` → `Iff.rfl`;
        `symm` → `Iff.symm` of the IH; `trans` → `Iff.trans`; `eucl` → `False.elim` (Five ∉ TS5,
        Deduction.lean:207-208).
  - [x] Prove `dia_iff_TClosure` dually from `dia_iff_base`.
- **Estimated output:** ~90-150 lines. **Bounded unit:** two lemmas, each a five-case `TClosure`
  induction with every case a one-liner; stopping condition = both compile.
- **Timing:** one agent run.
- **Depends on:** 1
- **Zero-debt contract:** no `sorry`, no new axiom, `cs5FCIncest` unweakened, no Preserved Asset
  touched.
- **Verification / Done when:** `Soundness.lean` builds green; both TClosure lemmas sorry-free and
  axiom-clean (`lean_verify`); no tactic `sorry`.

### Phase 3: F2 target-raise + reflexive here-extraction helpers [COMPLETED]

- **Goal:** Land the second confluence direction `F2` and the small "extract A here" helpers that
  the `boxE`/`diaI` closures and the Phase 4 lifting both consume (report 02 §4(A)/(B)).
- **Tasks:**
  - [x] Prove `F2 : r w u → u ≤ u' → ∃ w', w ≤ w' ∧ r w' u'` (report: `hsymbox` then `hincest`,
        ~3 lines). Place it next to the landed `cs5FCIncest_lift` (= F1, Soundness.lean:322).
        Landed as `cs5FCIncest_raise` (Soundness.lean, immediately after `cs5FCIncest_lift`).
  - [x] Prove `box_gives_here : CKForces … w (□A) → CKForces … w A` via the `hrefl` instance
        (`hbox w (le_refl w) w (hrefl w)`, mirroring CS5Canonical.lean:313).
  - [~] Dual diamond here-helper if needed for `diaI` (dia-iff + `hrefl` + `ckforces_persistence`,
        Forcing.lean:122): DEFERRED to Phase 5. Unlike `F2`/`box_gives_here`, the plan gates this
        item conditionally ("if needed") and gives no concrete target signature; Phase 5's `diaI`
        induction case has not been written yet, so its exact required shape is not yet knowable.
        Guessing a shape now risks landing an unused or wrongly-shaped lemma. See Plan Deviations
        in the Phase 3 summary.
- **Estimated output:** ~60-120 lines. **Bounded unit:** F2 + 1-2 here-helpers, each a handful of
  lines from a single conjunct; stopping condition = all compile.
- **Timing:** one agent run.
- **Depends on:** none (logically independent of Phases 1-2; sequenced after them by file territory)
- **Zero-debt contract:** no `sorry`, no new axiom, `cs5FCIncest` unweakened, no Preserved Asset
  touched.
- **Verification / Done when:** `Soundness.lean` builds green; F2 and the here-helpers sorry-free
  and axiom-clean; no tactic `sorry`.

### Phase 4: boxI tree-lifting lemma (Simpson Lifting Lemma 8.1.3 analogue) [NOT STARTED]

This is the sole concentrated-risk phase (report 02 "Uncertain claims", ~80-85%). It is split
into two bounded sub-phases so each lands sorry-free and build-green in isolation. Phase 4.2 is the
residual risk and carries the blocked-honesty exit to Phase 7.

#### Phase 4.1: Single-node interpretation-raise step [COMPLETED]

- **Goal:** Prove the inductive step of Simpson's Lifting Lemma 8.1.3 (chunks 0154-0155): raising
  the interpretation at ONE node preserves the raw edge-cond and Γ-cond, threading F1/F2.
- **Tasks:**
  - [x] State `boxI_raise_step`: given a raw-edge-cond interpretation `ρ`, a node `x`, and any
        `w ≥ ρ x`, produce `ρ'` with `ρ' x = w`, `ρ' z ≥ ρ z` for all `z`, re-establishing the raw
        edge-cond via F1 (down) / F2 (up) and Γ-cond via `ckforces_persistence` (Forcing.lean:122).
        Landed at `Soundness.lean:472`, scoped to one designated raw-`R`-neighbour `n` of `x` per
        call (down via `R x n`/F1, up via `R n x`/F2); `ρ'` agrees with `ρ` off `{x, n}` via an
        explicit `if`-based re-interpretation (`classical` for the `Decidable` instances). Phase
        4.2 iterates this atomic step node-by-node over the finite tree.
  - [x] Prove it sorry-free for a single raise. Keep the freshness bookkeeping explicit and finite.
        Sorry-free, axiom-clean (`lean_verify`: `propext`/`Classical.choice`/`Quot.sound` only, no
        `sorryAx`). `lake build` green; `lake exe checkInitImports` clean.
- **Estimated output:** ~120-220 lines. **Bounded unit:** one lemma about a single raise; stopping
  condition = it compiles and re-establishes both invariants. If it exceeds ~300 lines or the
  invariant threading does not close, STOP and route to Phase 7 — do NOT open-endedly retry.
- **Timing:** one agent run, hard budget cap.
- **Depends on:** 3
- **Zero-debt contract:** no `sorry`, no new axiom, `cs5FCIncest` unweakened, no Preserved Asset
  touched.
- **Verification / Done when:** `Soundness.lean` builds green; `boxI_raise_step` sorry-free and
  axiom-clean.

#### Phase 4.2: Iterate the raise over the finite tree; close the boxI case [BLOCKED]

- **Goal:** Iterate `boxI_raise_step` over the finite derivation tree to obtain the full lifting
  lemma `boxI_lift`, then discharge the `NIK.boxI` case (Deduction.lean:297-300): raise so `ρ x`
  lands at the adversarial `w'`, map the fresh child to `u` exactly (Simpson §8.1.2, chunk 0156).
- **Tasks:**
  - [~] Prove `boxI_lift` by finite induction over the tree, invoking `boxI_raise_step` node-by-node
        (the raising, not any exact edge, accommodates `w' ≥ ρ x`). PARTIAL: landed
        `boxI_lift_star` (Soundness.lean, "Star-lifting" section), generalizing the single-neighbour
        raise to a finite `Finset` of `x`'s DIRECT raw-neighbours (sorry-free, axiom-clean). Does
        NOT close the full recursive cascade to grandchildren -- see
        `handoffs/04_phase4-2-boxI-lift-blocked.md` for the machine-checked reason (a fully general
        cascade needs a rank/unique-parent "tree-shape" invariant on `Graph` that does not yet
        exist anywhere in this codebase; a concrete 3-cycle counterexample shows "unique parent"
        alone is insufficient).
  - [ ] Close the `boxI` obligation of the main induction using `boxI_lift` + the fresh-eigenvariable
        mapping `ρ' y = v`. NOT REACHED (depends on the full `boxI_lift`, not yet landed).
  - [x] If the recursion genuinely stalls within the budget, STOP and route to **Phase 7**
        (`[BLOCKED]` handoff), NOT a `sorry`, NOT an undirected retry. DONE: this is that stop —
        see `handoffs/04_phase4-2-boxI-lift-blocked.md`.
- **Estimated output:** ~150-300 lines. **Bounded unit:** the finite-tree induction + the boxI case
  closure; concrete stopping condition = the boxI case closes OR the documented budget is hit and
  Phase 7 fires. **Landed this dispatch:** ~95 lines (`boxI_lift_star` + docstring), sorry-free,
  axiom-clean, build green.
- **Timing:** one agent run, hard budget cap.
- **Depends on:** 4.1
- **Zero-debt contract:** no `sorry`, no new axiom, `cs5FCIncest` unweakened, no Preserved Asset
  touched. Verified: `boxI_lift_star` depends only on `[propext, Classical.choice, Quot.sound]`.
- **Blocked-honesty sub-gate:** stall at budget → **Phase 7** (`[BLOCKED]`), never a `sorry`.
  TRIGGERED this dispatch -- routed to Phase 7, see handoff above.
- **Verification / Done when:** `Soundness.lean` builds green; `boxI_lift` and the boxI case
  sorry-free and axiom-clean. NOT YET MET (build IS green; `boxI_lift`/boxI case not yet landed).

### Phase 5: Assemble nik_TS5_soundness through the NIK induction [NOT STARTED]

- **Goal:** Complete the 12-constructor `NIK` induction generalized over an arbitrary interpretation
  `ρ` and model (reusing the `nik_soundness_onePoint` skeleton, Soundness.lean:345), carrying the
  **raw** edge-cond + Γ-cond, and land `nik_TS5_soundness` (report 02 step 4).
- **Tasks:**
  - [ ] Generalize the `nik_soundness_onePoint` induction over `ρ` and model, carrying the raw
        edge-cond invariant `∀ a b, G.R a b → r (ρa)(ρb)` (MMS Def 5.1, chunk 0026) and Γ-cond.
  - [ ] Discharge `boxE` / `diaI` (Deduction.lean:289-303) via `box_iff_TClosure` / `dia_iff_TClosure`
        (Phase 2) + the here-helpers (Phase 3) — never by validating the closed edge.
  - [ ] Discharge `boxI` via `boxI_lift` (Phase 4.2); `diaE` via `le_refl` (no lift; propositional
        and fresh-label bookkeeping verbatim from `nik_soundness_onePoint`).
  - [ ] Land `nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ` by specializing to
        `Graph.trivial` / `[]` (Deduction.lean:316-317).
  - [ ] Update the `Soundness.lean` module docstring: mark the general theorem LANDED; remove the
        stale INTRACTABLE / "What remains" notes.
- **Estimated output:** ~150-300 lines. **Bounded unit:** the assembled induction + the final
  corollary; stopping condition = `nik_TS5_soundness` compiles sorry-free.
- **Timing:** one agent run.
- **Depends on:** 2, 4
- **Zero-debt contract:** no `sorry`, no new axiom, `cs5FCIncest` unweakened, no Preserved Asset
  touched.
- **Verification / Done when:** `nik_TS5_soundness` sorry-free; `Soundness.lean` builds green;
  `lean_verify nik_TS5_soundness` axiom-clean; no tactic `sorry`.

### Phase 6: Regression gate + full-project verification [NOT STARTED]

- **Goal:** Confirm the full project is green and unregressed, the biconditional is complete, and no
  debt was added anywhere.
- **Tasks:**
  - [ ] Full `lake build` green.
  - [ ] `lean_verify nik_TS5_soundness` reports no `sorryAx` and no new axioms.
  - [ ] `grep '\bsorry\b'` on `Soundness.lean`: no *tactic* `sorry` (docstring prose excepted);
        `grep '^axiom '`: zero new axioms.
  - [ ] Spot-verify the six Preserved Assets still build sorry-free (`cs5_completeness`,
        `nik_TS5_consistent`, `nik_soundness_onePoint`, `cs5FCIncest_lift`, `ckforces_persistence`,
        `cs5_soundness_derivable_incest`).
  - [ ] `lake lint`, `lake exe lint-style <file>`, `lake shake`, `lake exe checkInitImports`,
        `lake test` all unregressed against the task-517 baseline.
- **Estimated output:** verification only; docstring touch-ups if any (~0-30 lines).
- **Timing:** one agent run.
- **Depends on:** 5
- **Zero-debt contract:** no `sorry`, no new axiom, no weakening, no regression.
- **Verification / Done when:** all checks above pass; the Simpson 8.1.4 biconditional is complete.

### Phase 7: BLOCKED handoff to follow-up (contingency only) [NOT STARTED]

- **Goal:** If — contra the ~80-85% estimate — the Phase 4.2 `boxI` recursion genuinely stalls,
  record an honest `[BLOCKED]` terminal state WITHOUT adding any debt, and write a handoff routing
  to a follow-up task. This is the sanctioned no-loop, no-sorry response; the MAIN LINE is the
  direct proof (Phases 1-6), which this phase does not pre-empt.
- **Tasks:**
  - [ ] Write a `[BLOCKED]` handoff under `specs/537.../handoffs/` naming the exact blocker (the
        specific freshness/tree-invariant step of `boxI_lift` that did not close), the green state
        of Phases 1-4.1, and the current build status.
  - [ ] Recommend a follow-up task scoped narrowly to the `boxI` tree-lifting recursion, carrying
        forward the landed Phases 1-4.1 lemmas as its foundation.
  - [ ] Confirm zero debt: `grep` finds no tactic `sorry` in `Soundness.lean`; `lake build` green;
        `cs5FCIncest` unweakened; all Preserved Assets unregressed.
- **Estimated output:** documentation only; no `.lean` proof edits.
- **Timing:** short; one agent run.
- **Depends on:** 4.2 stall (or a Phase 5 escalation).
- **Zero-debt contract:** no `sorry`, no new axiom, no weakening, no regression — verified before
  writing the handoff.
- **Verification / Done when:** `[BLOCKED]` recorded with a durable handoff naming a concrete
  blocker and a follow-up route; build green; zero debt.

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness` green after every
      phase that touches `.lean` (H9 green-milestone commit).
- [ ] Full `lake build` green at each phase completion.
- [ ] `lean_verify` axiom-clean on each new lemma as it lands, and on `nik_TS5_soundness` at Phase 5/6.
- [ ] `grep '\bsorry\b'` on `Soundness.lean`: no *tactic* `sorry` (docstring prose excepted).
- [ ] `grep '^axiom '` on modified files: zero new axioms.
- [ ] `lake lint`, `lake exe lint-style <file>`, `lake shake`, `lake exe checkInitImports`,
      `lake test`: all unregressed against the task-517 green baseline.
- [ ] Preserved Assets unregressed (spot-verify the six listed theorems build sorry-free).

## Artifacts & Outputs

- plans/02_direct-route.md (this file)
- Modified: Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean (all phases)
- handoffs/ blocked handoff (contingency, Phase 7 only)
- summaries/02_direct-route-summary.md (on completion)

## Rollback/Contingency

- Each phase commits only its own green result (H9 incremental commit). If a phase fails to reach
  green, leave the prior committed state intact; fix forward — never destructive git on a dirty
  tree (see `.claude/rules/git-workflow.md`, "No Destructive Git on Uncommitted Work").
- The blocked-honesty path (Phase 7) IS the sanctioned contingency for a genuine Phase 4.2 stall:
  a `[BLOCKED]` handoff with a concrete blocker and a follow-up route, zero debt, build green —
  never a `sorry` skeleton and never a return to the refuted clique/exact-symmetry decomposition.
