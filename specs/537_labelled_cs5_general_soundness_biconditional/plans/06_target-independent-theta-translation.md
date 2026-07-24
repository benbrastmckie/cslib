# Implementation Plan: General Labelled CS5 Soundness via a TARGET-INDEPENDENT `Θ ⊃ place` Translation

- **Task**: 537 - Prove the general labelled soundness direction, completing Simpson 1994 Thm 8.1.4's biconditional
- **Status**: [IMPLEMENTING]
- **Effort**: 35-55 hours remaining (Phases 1-7 landed; Phase 8's translation is machine-refuted and closed; the remaining work is decomposed into fourteen agent-run-sized phases 9-22, plus Phase 23 as a documented terminal)
- **Dependencies**: 517 (delivered completeness + anti-vacuity + landed Hilbert-side soundness `cs5_soundness_derivable_incest`)
- **Research Inputs**:
  - reports/06_falseness-machine-check.md (Tier 0, MACHINE-PROVEN, AUTHORITATIVE — supersedes all prior analytical verdicts on the translation shape)
  - reports/05_efq-orE-motive-defect-and-path.md (Tier 1 — diagnoses the target-dependence root cause and proposes the retarget)
  - probes/nik_adequacy_falseness.lean (compiles clean, zero `sorryAx` — the executable form of report 06)
  - reports/04_crosslabel-motive-audit.md (Tier 1, carried forward — route selection, Simpson source mapping)
  - reports/03_tree-shape-invariant-audit.md, reports/02_direct-route-from-sources.md (carried forward — landed Phases 1-7)
- **Artifacts**: plans/06_target-independent-theta-translation.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/plan-format-enforcement.md
  - .claude/rules/plan-compliance.md
  - .claude/rules/cslib.md
  - .claude/context/formats/plan-format.md
  - .claude/context/contracts/wrap-up.md
  - .claude/context/contracts/reference-grounding.md
- **Type**: cslib
- **Plan version**: 6 (supersedes plans/05_tree-recursive-hilbert-bridge.md)
- **reports_integrated**: 06_falseness-machine-check.md, 05_efq-orE-motive-defect-and-path.md, 04_crosslabel-motive-audit.md, 03_tree-shape-invariant-audit.md, 02_direct-route-from-sources.md

## Overview

Prove `nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ` in
`Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`, closing the soundness
direction (2⟹1) of Simpson Thm 8.1.4, by composing a labelled→Hilbert adequacy bridge with the
landed `cs5_soundness_derivable_incest`.

Plan v5 committed to that bridge with a **target-oriented** translation `nikTr`, which walks the
*target label's* ancestor spine. That translation is now **machine-proven to make the intended
`nik_adequacy` statement FALSE**. This plan retargets the bridge onto a **target-independent**
translation of the shape `Θ(G,Γ) ⊃ place(x,A)`, where the antecedent `Θ` depends only on the
graph and context — never on the conclusion label — and only the *placement* of `A` depends on
`x`. This removes the entire family of refutations at a stroke, because a target-independent
antecedent cannot forget anything.

### The established facts this revision is built on (do NOT re-litigate)

These are proven, not analytical. `probes/nik_adequacy_falseness.lean` compiles with
`lake env lean` at exit 0, zero errors, zero warnings, zero `sorry`, and `#print axioms` on every
reductio reports `[propext, Classical.choice, Quot.sound]` only — **no `sorryAx`**. `Cslib/` was
untouched by that probe.

1. **The plan-v5 target statement is FALSE.** `nik_adequacy_is_false` derives `False` from it.
   Witness: `G = Graph.trivial ℕ` (a derivation forest via the landed `forest_trivial`),
   `Γ = [var 0 ∶ ⊥]`, conclusion label `var 1 ∉ G.X`, `A = ⊥`, via a two-constructor derivation
   (`.assumption` then cross-label `.efq`), landing on the landed `cs5_consistent_incest`.
   `nikTr_yy_explicit` pins the translation exactly:
   `nikTr Gt Ctx Gt_fin (var 1) A = ((⊥⊃⊥) ∧ (⊥⊃⊥)) ⊃ A` — **graph and context discarded
   wholesale**.

2. **Root-connectivity is REFUTED as the fix, twice over.** `rooted_restricted_adequacy_is_false`
   refutes the statement even when restricted to `x ∈ G.X` over a single-rooted forest: move the
   `⊥` to an out-of-graph *context* label (`Γ = [var 1 ∶ ⊥]`) and conclude at the root
   `var 0 ∈ G.X`. The escape hatch simply migrates from the conclusion label to the context label.
   **The planned `IsRootedForest` root-connectivity invariant work is DELETED as the fix.** It is
   retained in this plan only for a different, narrow purpose: the redesigned translation needs to
   *name the root* that anchors `Θ` and defines `place`'s depth (Phase 10).

3. **The label-restricted variant is UNINDUCTIVE, not merely insufficient.** Adding both
   `x ∈ G.X` and `labels(Γ) ⊆ G.X` was not refutable and may well be true, but `ctx_labels_in_X` +
   `premise_escapes_graph` exhibit a context all of whose labels lie in `G.X` from which `NIK`
   nevertheless derives `⊥` at a label **outside** `G.X`. In the `efq` case the premise's label is
   exactly such a label, so the induction hypothesis does not apply. **Do NOT spend a dispatch on
   this variant.**

4. **Do NOT fix this by restricting the `efq`/`orE` rules.** Their cross-label form (unrestricted
   conclusion label `y`) is deliberate and load-bearing. The `efq` docstring
   (`Deduction.lean:243-247`) records that the label-local form is "a strict, defect-causing
   weakening" because Simpson's Lemma 5.3.1 consistency step needs the cross-label form for
   *disconnected* labels; the `orE` docstring (`:259-266`) records that the label-local
   restriction blocks the disjunction-property step. Restricting them would break exactly what
   they exist for. **The object system stays as-is; the TRANSLATION is what changes.**

5. **Root cause (confirmed and sharpened).** `nikTr`'s antecedent is target-*dependent*: it walks
   the target's ancestor spine and threads in only that spine's off-spine siblings. Every
   refutation above is an instance of "the target-dependent antecedent forgets a `⊥` living off
   the target's ancestor spine." Simpson's faithful `(Γ⊢_G x:A)^T` uses a target-INDEPENDENT
   graph+context antecedent.

### The retarget: `Θ(G,Γ) ⊃ place(x,A)`

- **`Θ(G,Γ)`** — target-independent. Built from the landed `sigAt G Γ hfin root` evaluated at the
  single distinguished root (reusable **verbatim**), extended by an orphan-context component (see
  the mandatory gate obligation below). Depends on `(G,Γ)` only.
- **`place(x,A)`** — `A` boxed to `x`'s depth-from-root: `□^{d(x)} A`, with `d(x)` the graded-rank
  distance available from the landed `ht` / `ht_le_of_reflTransGen` content, and `d(x) = 0` for any
  label not reachable from the root (including `x ∉ G.X`).
- **`efq` closes via the CS5 `T` axiom.** `CS5ModalAxiom.tBox : □φ ⊃ φ` (`CS5.lean:171-173`) is a
  landed constructor. From the IH `⊢ Θ ⊃ place(x,⊥) = Θ ⊃ □^{d(x)}⊥`, iterate `tBox` to get
  `⊢ Θ ⊃ ⊥`, then `CS5ModalAxiom.efq : ⊥ ⊃ φ` gives `⊢ Θ ⊃ place(y,A)` for **any** `y`, including
  the disconnected case. Both premise and conclusion sit under the **same** `Θ`, which is the
  entire point of the retarget.
- **`orE` combines under the shared `Θ`.** All three IHs (major premise and both branches) sit
  under the same antecedent, so no lowest-common-ancestor computation and no root-propagation walk
  is required.

### Definition of Done

`nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ` lands sorry-free and axiom-clean
in `Soundness.lean`; full `lake build` green; `lean_verify` on `nik_TS5_soundness` reports no
`sorryAx` and no new axioms; `lake lint` / `lint-style` / `shake` / `checkInitImports` / `test`
unregressed against the task-517 green baseline; the retired `nikTrFuel` ancestor-walk lemmas are
deleted (not left as dead code); the stale module-docstring `INTRACTABLE` / `GATE-C` /
"What remains" / "Fifth dispatch" notes retired.

### Research Integration

- **reports/06_falseness-machine-check.md** — NEW, integrated at plan_version 6. **Tier 0 /
  authoritative**: machine-proven, not analytical. Supplies established facts 1-3 above. Its
  operative directives are adopted verbatim: retarget to target-independent `Θ ⊃ place`; delete
  the root-connectivity-as-fix work; do not spend a dispatch on the label-restricted variant;
  `sigAt`/`sigAtFuel`/`factsAt`/`bigAndL` and the `cs5_deriv_*` toolkit are independently
  corroborated (the probe is built entirely out of them); the `nikTrFuel` lemmas are retired sunk
  cost; the OCR source-quality risk is reinforced.
- **reports/05_efq-orE-motive-defect-and-path.md** — NEW, integrated at plan_version 6. Supplies
  the target-dependence diagnosis (established fact 5), the `Θ ⊃ place` design sketch, the `T`-axiom
  route for `efq`, the preserved/retired asset split, and the "resolve the OCR source first"
  precondition. Its falseness claim is **superseded in status** by report 06, which proves it.
- **probes/nik_adequacy_falseness.lean** — NEW, integrated at plan_version 6. The executable
  adversarial suite. It is a **planned input to Phase 9**, not merely evidence: the redesigned
  definition is validated against these exact shapes before any adequacy work begins.
- **reports/04_crosslabel-motive-audit.md** — carried forward from plan_version 4. Route selection
  (Hilbert bridge over the direct semantic route) still stands; its ~70% "known-shape" rating
  applies to the *faithful* construction, which this plan is now actually pursuing. Its Finding 4
  (`orE` needs no coordination) and its confidence in the target-oriented shape are **corrected**
  by report 06.
- **reports/03, reports/02** — carried forward as the provenance of the landed Phases 1-7.

## SOURCE-QUALITY RISK (read before Phase 9)

**This is the single highest-leverage risk in the task and it has already materialised once.**

Simpson's thesis IS in the literature corpus as `simpson_1994_intuitionisticmodallogic`, but
**both load-bearing passages are OCR-damaged**:

- **§6.1, Lemma 6.1.2** — the statement is truncated mid-sentence and its notation is mangled;
  the reflowed markdown (chunks 943-1073) conflates box/diamond glyphs with digits and scrambles
  sub/superscripts. Plan v5's Sub-step 8.1 records that the one worked example in the source could
  not be reproduced consistently from the OCR'd formula alone, and that the translation shape was
  **reconstructed from surrounding prose**.
- **Figure 4-1** — the text layer is destroyed, per the `NIK.efq` docstring
  (`Deduction.lean:243-247`), which flags the raster page (p. 69 / PDF p. 78) as the only legible
  form.

**Two separate reconstructions from this damaged source are load-bearing in this task, and one of
them is now machine-proven false.** The plan-v5 `nikTr` is precisely a prose reconstruction of
Fig. 6-1/6-2 that produced a false-making definition.

**Mitigations, in force:**

1. **The Phase 9 probe gate is the primary mitigation.** It is a hard gate, not a suggestion,
   precisely because a prose reconstruction already produced a false-making definition once and
   this probe methodology is now proven to catch exactly that failure mode.
2. **Obtaining a clean PDF of the thesis would materially derisk the redesign** and is
   recommended before Phase 9 if it can be done cheaply (`/literature` discovery on
   `simpson_1994_intuitionisticmodallogic`; the published thesis; an alternative scan). This is
   **recommended, not blocking** — Phase 9's gate is designed to be sound even against a prose
   reconstruction, which is why it exists.
3. Every definitional choice reconstructed from prose rather than read from the source MUST be
   flagged in the `Soundness.lean` section docstring per the literature-fidelity policy, as
   plan v5's Sub-step 8.1 did. Silent guessing is forbidden.

## Preserved Assets

Complete, landed sorry-free / axiom-clean, MUST NOT regress. Namespace of the landed lemmas is
`Cslib.Logic.Modal.Labelled` (singular `Logic`; the file path uses `Logics`). The file is
2094 lines, builds green (scoped build: 960 jobs, exit 0), and contains **zero real
`sorry`/`admit`/`axiom`** — the six `grep` hits for `sorry` are all docstring prose.

| Component | File:Line | Status | Verified |
|-----------|-----------|--------|----------|
| `cs5_completeness` | Completeness.lean:132 | [COMPLETED] | task 517 |
| `nik_TS5_consistent` (anti-vacuity) | Soundness.lean:900 | [COMPLETED] | task 517 / this task |
| `nik_soundness_onePoint` (12-constructor skeleton) | Soundness.lean:826 | [COMPLETED] | task 517 |
| **`cs5_soundness_derivable_incest` (Hilbert soundness — bridge CRITICAL PATH)** | CS5Canonical.lean:359 | [COMPLETED] | task 517 |
| **`cs5_consistent_incest` (the refutation engine)** | CS5Canonical.lean:428 | [COMPLETED] | task 517 |
| `ckforces_persistence` | Forcing.lean:122 | [COMPLETED] | task 517 |
| `cs5FCIncest_lift` / `cs5FCIncest_raise` / `box_gives_here` | Soundness.lean:363/378/390 | [COMPLETED] | Phases 1-3 |
| `box_iff_base` / `dia_iff_base` | Soundness.lean:416/434 | [COMPLETED] | Phase 1 |
| `box_iff_TClosure` / `dia_iff_TClosure` | Soundness.lean:464/479 | [COMPLETED] | Phase 2 |
| `boxI_raise_step` / `boxI_lift_star` | Soundness.lean:567/656 | [COMPLETED] | Phases 4-5 |
| `IsDerivationForest` + `forest_trivial` + `forest_addEdge_fresh` | Soundness.lean:765/774/784 | [COMPLETED] | Phase 6 |
| `ht_le_of_reflTransGen` / `raise_subtree` / `siblings_disjoint` / `boxI_lift_ancestor` / `boxI_lift` | Soundness.lean:931/950/1128/1182/1329 | [COMPLETED] | Phase 7 |
| `bot_backward` / `bot_iff_edge` / `bot_iff_TClosure` (PD.1) | Soundness.lean:509/520/530 | [COMPLETED] | PD.1 |
| **`bigAndL` / `factsAt` / `sigAtFuel` / `sigAt` (Θ's building blocks — REUSED VERBATIM)** | Soundness.lean:1383/1390/1403/1414 | [COMPLETED] | Phase 8.1 |
| **`cs5_deriv_*` toolkit** (`imp_trans`, `imp_and`, `imp_andE1`, `imp_andE2`, `imp_orI1`, `imp_orI2`, `imp_mp`, `imp_of_derivable`, `imp_self`, `imp_trans_under`, `uncurry`, `curry`, `box_mono`, `imp_congr_right`) | Soundness.lean:1512-1932 | [COMPLETED] | Phase 8.2 |
| `bigAndL_mem` / `bigAndL_cons` / `bigAndL_mono` / `bigAndL_imp_of_pointwise` | Soundness.lean:1579/1817/1823/1948 | [COMPLETED] | Phase 8.2 |
| `factsAt_cons_ne` / `factsAt_cons_self` / `hfin_toFinset_card_pos` | Soundness.lean:1753/1761/1641 | [COMPLETED] | Phase 8.2 |
| `sigAtFuel_mono_context` | Soundness.lean:1975 | [COMPLETED] | Phase 8.2 |
| `sigAtFuel_congr_above_rank` | Soundness.lean:1735 | [COMPLETED] | Phase 8.2 (narrower than `mono_context`, still valid) |

**Independent corroboration**: `probes/nik_adequacy_falseness.lean` is built entirely out of
`sigAt`, `sigAtFuel`, `factsAt`, `bigAndL`, `cs5_deriv_imp_self`, `IsDerivationForest`, and
`cs5_consistent_incest`, and compiles clean. That is evidence — independent of the failed
translation — that these components are sound and reusable.

## Retired Assets (deliberate retirement, NOT dead code)

The following are **sunk cost under this redesign** and MUST be **deleted** from `Soundness.lean`
in Phase 11, not left in place. They exist only to serve the target-oriented ancestor walk that
report 06 refutes; leaving them would imply the refuted design is still live.

| Component | File:Line | Disposition |
|-----------|-----------|-------------|
| `nikTrFuel` (the ancestor-walk itself) | Soundness.lean:1427 | **DELETE** |
| `nikTr` (target-oriented translation — machine-refuted) | Soundness.lean:1449 | **DELETE** |
| Sanity `example`s 1 and 2 for `nikTr` | Soundness.lean:1467/1484 | **DELETE** (replaced by Phase 11's `Θ`/`place` sanity examples) |
| `nikTrFuel_of_derivable` | Soundness.lean:1604 | **DELETE** |
| `nikTr_of_sigAt_imp` | Soundness.lean:1625 | **DELETE** |
| `nikTrFuel_mono` | Soundness.lean:1934 | **DELETE** |
| `sigAtFuel_mono_fuel` / `sigAtFuel_mono_fuel_le` | Soundness.lean:1996/2011 | **DELETE** unless Phase 12 finds a direct consumer (they are unconditional fuel-monotonicity facts; re-land only on demand) |
| `nikTrFuel_succ_eq` | Soundness.lean:2040 | **DELETE** |
| `nikTrFuel_no_parent` | Soundness.lean:2055 | **DELETE** |
| `nikTrFuel_fuel_invariant_step` | Soundness.lean:2066 | **DELETE** |
| `sigAt_assumption` / `sigAt_andI` / `sigAt_andE1` / `sigAt_andE2` / `sigAt_orI1` / `sigAt_orI2` / `sigAt_impE` / `sigAt_impI` / `sigAt_cons_self_imp` / `sigAt_imp_of_factsAt_imp` | Soundness.lean:1663-1911 | **RETARGET, do not blind-delete.** These prove `sigAt`-level "core" facts at the *target* label. Their propositional content transfers to the depth-indexed `place` shape; Phases 13-14 re-state them against `Θ`/`place` and delete the target-oriented originals once the replacements are green. |

Approximately **200-250 lines** are removed outright, plus roughly 250 lines retargeted. This is
acknowledged sunk cost, spent buying the machine-checked refutation that made the redesign
possible.

## Source-to-Implementation Mapping (H3, Tier 1)

BibKeys VERIFIED in `references.bib`: `Simpson1994` (`@phdthesis`),
`MarinMoralesStrassburger2021` (`@article`).

| Source | Prop / Location | Lean Identifier | Role | Status |
|--------|-----------------|-----------------|------|--------|
| Simpson1994 | §6.1 Fig. 6-1/6-2 translation `(·)^T` (reflowed 943-1073; **OCR-DAMAGED**) | `theta` (`Θ`) + `place` | the retargeted translation — Phase 11 | to land |
| Simpson1994 | Lemma 6.1.2 `Γ ⊢_G x:A ⟹ (Γ⊢_G x:A)^T ∈ IK` (**OCR-DAMAGED, truncated**) | `nik_adequacy` | the bridge core — Phases 13-19 | to land |
| Simpson1994 | Thm 6.2.1 / Lemma 6.2.3: extension to `Ax(𝒯)`, `𝒯 = {χ_T,χ_B,χ_4}` = `IKTB4` | axiom-set instantiation = `CS5ModalAxiom` | matches `CS5ModalAxiom` | to land |
| Simpson1994 | Fig. 4-1 `(⊥E)` / `(∨E)` cross-label form (**text layer destroyed**) | `NIK.efq` / `NIK.orE` | LANDED, **not to be modified** | LANDED |
| Simpson1994 | §8.1.2: direct `N(𝒯)` has unavoidable non-tree excursions; route via Hilbert | route selection | motivates the bridge | ROUTE SELECTION |
| Simpson1994 | Thm 8.1.4, tree case | `nik_TS5_soundness` | the goal | Phase 21 |
| — (CSLib landed) | `CS5ModalAxiom.tBox : □φ ⊃ φ` | `T`-iteration lemma (Phase 12) | discharges `efq` | CS5.lean:171-173 |
| — (CSLib landed) | `CS5ModalAxiom.efq : ⊥ ⊃ φ` | ex falso at the Hilbert level | discharges `efq` | CS5.lean:174-176 |
| MarinMoralesStrassburger2021 | Thm 7.1 / 7.2 | `cs5_soundness_derivable_incest` | Hilbert-side soundness | LANDED (task 517) |

## Goals & Non-Goals

- **Goals**:
  - Probe-validate a target-independent `Θ ⊃ place` definition against the exact adversarial
    shapes in `probes/nik_adequacy_falseness.lean` **before** any adequacy-induction work
    (Phase 9, hard gate).
  - Land `IsRootedForest` + root naming + preservation lemmas, used solely to anchor `Θ` and
    define `place`'s depth (Phase 10).
  - Land `Θ`, `place`, and the depth accessor; delete the retired `nikTrFuel` ancestor-walk
    (Phase 11).
  - Land the iterated-box toolkit (`□^k` iteration, K-distribution, `T`-iteration `⊢ □^k⊥ ⊃ ⊥`,
    box-monotonicity, `Θ`-injection, `Θ` graph-extension monotonicity) (Phase 12).
  - Prove the 12 `NIK` constructor cases in bounded, independently-verifiable groups: propositional
    (13), `impI` (14), cross-label `efq` (15), cross-label `orE` (16), eigenvariable /
    graph-extension `boxI`+`diaE` (17), geometric `TClosure` + `boxE`+`diaI` (18).
  - Assemble `nik_adequacy` (19), specialise to `nik_TS5_to_hilbert` (20), assemble
    `nik_TS5_soundness` and retire stale docstrings (21), pass the full regression gate (22).
  - Keep every intermediate state green and committed (commit-per-green-substep mandate).
  - Preserve every landed asset in the Preserved Assets table (no regression).
- **Non-Goals**:
  - Any change to the `Graph` structure, `cs5FCIncest`, `NIK`, the completeness direction, or the
    anti-vacuity certificate.
  - Re-planning or re-deriving the landed Phases 1-7 or PD.1.
  - **Restricting `NIK.efq` / `NIK.orE`** to `y ∈ G.X` or any label-local form (established fact 4).
  - **Adding root-connectivity as the fix for the cross-label cases** (established fact 2). It is
    added only to name the root.
  - **The `x ∈ G.X` + `labels(Γ) ⊆ G.X` restricted variant** (established fact 3, uninductive).
  - Retrying either flat-translation shortcut (split-by-label flat; fully-boxed flat), both
    machine-refuted under plan v4.
  - Retaining the target-oriented `nikTr` ancestor-walk in any form.
  - Implementing the direct semantic route PD (its `efq` residual is genuinely open; Phase 23).

## Postmortem Constraints

Binding rules for all implementation dispatches under this plan.

**Do NOT**:
- Do NOT re-litigate the five established facts in the Overview. They are machine-proven or
  documented in the object system's own docstrings.
- Do NOT restrict `NIK.efq` or `NIK.orE` (established fact 4). The object system is not the defect.
- Do NOT plan, prove, or invoke root-connectivity **as the fix** for the cross-label cases
  (established fact 2). Phase 10 adds `IsRootedForest` for the single narrow purpose of naming the
  root and defining `place`'s depth, and its phase text says so explicitly.
- Do NOT pursue the `x ∈ G.X` + `labels(Γ) ⊆ G.X` restricted variant (established fact 3).
- Do NOT resurrect `nikTr`/`nikTrFuel` or any target-dependent antecedent.
- Do NOT retry either flat-translation shortcut (split-by-label flat; fully-boxed flat).
- Do NOT begin Phase 10+ before Phase 9's gate reports PASS. This is a hard ordering constraint.
- Do NOT resume Phase 8. It is a closed historical record.
- Do NOT introduce `sorry` anywhere under `Cslib/` — not "temporary", not "strategic". A `sorry`
  scaffold inside `lean_multi_attempt` or a scratch/probe buffer is fine ONLY if it is never
  written to a committed `Cslib/` file. A genuinely blocked sub-goal routes to a `[BLOCKED]`
  handoff (Phase 23).
- Do NOT add any new `axiom` under `Cslib/`, and do NOT use any vacuous definition
  (`def X := True`, `theorem X := trivial`, etc. — see `.claude/rules/cslib.md`).
- Do NOT weaken `cs5FCIncest` (do not drop or relax any of its five conjuncts) or modify `Graph`.
- Do NOT touch or re-derive any Preserved Asset row.
- Do NOT expand file scope beyond `Soundness.lean` (plus `probes/` for Phase 9). No new library
  file is introduced.
- Do NOT hand-analyze a "wall" and escalate without first machine-checking the blocking sub-goal
  with `lean_run_code` / `lean_multi_attempt` / `lean_goal`. The probe methodology in Phase 9 is
  the template.
- Do NOT leave the retired assets in the file as dead code (see Retired Assets).

**MUST preserve**:
- Every Preserved Asset row (sorry-free, axiom-clean, unregressed).
- Existing full-project green state: `lake build`, `lake lint`, `lint-style`, `shake`,
  `checkInitImports`, `lake test`. Pre-existing unrelated sorries in Propositional Tableau files
  are the known baseline — do not "fix" or count them.

**Settled design decisions** (do not re-open without a machine-checked counterexample):
- `nik_TS5_soundness` is TRUE and provable (report 04 verdict, unaffected by report 06 — report 06
  refutes a *translation*, not the theorem).
- The route is the Hilbert adequacy bridge with a **target-independent** antecedent.
- `Θ` is anchored at the single root and reuses `sigAt` verbatim as its in-graph component.
- `efq` closes via iterated `CS5ModalAxiom.tBox` plus `CS5ModalAxiom.efq`.

## Risks & Mitigations

- **Risk (highest, materialised once): a prose reconstruction of an OCR-damaged source produces
  another false-making definition.** See the SOURCE-QUALITY RISK section above.
  **Mitigation**: the Phase 9 hard probe gate, plus the recommendation to obtain a clean PDF.

- **Risk (known-in-advance, Phase 9 must resolve): the naive `Θ := sigAt G Γ hfin root` is
  ALREADY refuted by probe #2.** `rooted_restricted_adequacy_is_false`'s witness puts the `⊥` at a
  *context* label `var 1 ∉ G.X`. `sigAt`'s walk descends `G`'s edges from the root, so it never
  sees `factsAt Γ (var 1)` — `Θ` would reduce to a tautology while `place(root,⊥) = ⊥`, giving the
  false statement `⊢ ⊤ ⊃ ⊥`. **Mitigation**: `Θ` must include an **orphan-context component**:
  the facts of `Γ` at labels not reachable from the root, conjoined at depth 0. This strengthens
  the antecedent, which makes the adequacy implication *easier*, and it does not perturb the
  Phase 20 collapse (at `Graph.trivial` with `Γ = []` there are no orphan labels). Phase 9's gate
  MUST confirm this concretely rather than assuming it.

- **Risk (primary residual, concentrated in Phase 16): `orE` under box-conflation.** `place`'s
  `□^d` conflates all labels at the same depth. That conflation is *helpful* for injecting a
  hypothesis into `Θ` (Phase 12's `Θ`-injection lemma), but for `orE` the natural currying route
  needs `□^d(A∨B) ⊃ □^d A ∨ □^d B`, which is **the same non-theorem that killed the fully-boxed
  flat shortcut** under plan v4. **Mitigation**: Phase 16 is a dedicated, separately-budgeted
  phase; its first task is to machine-check whether the conflation route actually requires that
  non-theorem or whether the shared-`Θ` structure sidesteps it (the three IHs sit under one
  antecedent, unlike the flat shortcut where they did not). Phase 9's gate includes a `d ≥ 1`
  `orE` shape specifically so this is discovered at gate time, not at Phase 16. If `orE` genuinely
  requires the non-theorem, that is a concrete machine-checked obstruction against the `□^d`
  *placement* design (not against target-independence) → re-enter Phase 9 with a revised `place`
  (e.g. a nested `Θ_0 ⊃ □(Θ_1 ⊃ □(…))` layered form whose per-level antecedents cover the whole
  depth layer, keeping the antecedent target-independent while avoiding the flat conflation), and
  only then Phase 23 if that also fails.

- **Risk (Phase 14): `impI` under depth-indexed discharge.** Discharging `(x∶A)` from the context
  means removing a conjunct nested at depth `d(x)` inside `Θ` and re-emitting it as
  `□^{d(x)}(A ⊃ B)`. This is the depth-indexed analogue of `sigAt_cons_self_imp`, which was the
  hardest of the eight landed propositional cases. **Mitigation**: its own phase, with the
  `Θ`-injection lemma from Phase 12 as the prerequisite tool.

- **Risk (Phase 17): `boxI`/`diaE` change the graph.** Their premises live over `G.addEdge x y`
  for cofinitely many fresh `y`, so the IH's antecedent is `Θ(G.addEdge x y, Γ)`, not `Θ(G,Γ)`.
  **Mitigation**: Phase 12 lands a `Θ` graph-extension monotonicity lemma
  (`⊢ Θ(G,Γ) ⊃ Θ(G.addEdge x y, Γ)` for fresh `y`, whose new subtree translation is a
  `⊤`-surrogate) as an explicit prerequisite; `forest_addEdge_fresh` and Phase 10's
  rooted-preservation lemma supply the invariant side.

- **Risk (Phase 18): the geometric `TClosure` cases.** `boxE`/`diaI` relate `x` and `y` by
  `TClosure 𝒯 G.R`, not by a raw edge, so `d(y)` is unrelated to `d(x) + 1`. Discharging them
  needs the CS5 axioms corresponding to `𝒯 = {T, B, 4}` (`tBox`/`tDia`, `bBox`/`bDia`,
  `fourBox`/`fourDia` — all landed `CS5ModalAxiom` constructors) via an induction on the
  `TClosure` derivation. **Mitigation**: separate phase, with the `TClosure` induction isolated
  as its own named bridge lemma before the two constructor cases consume it.

- **Risk: accretion without closure.** The task has spent ~14 orchestration cycles and ~700 lines
  of infrastructure without closing a single cross-label case. **Mitigation**: hard per-phase
  dispatch budgets (stated in each phase), each phase independently green and committed, and a
  standing instruction that a phase overrunning its budget with a **concrete machine-checked**
  obstruction routes to Phase 23 rather than accreting more infrastructure.

- **Risk: a phase silently regresses a Preserved Asset.** **Mitigation**: every phase's zero-debt
  contract re-verifies the assets build sorry-free before commit; `lean_verify` on each new lemma.

- **Risk: file-territory contention.** Phases 10-22 all write the single file `Soundness.lean`.
  **Mitigation**: strictly sequential execution; no parallel dispatch. Phase 9 is the only phase
  with a different territory (`probes/`) and it still runs first, alone.

## Implementation Phases

> **DISPATCH DIRECTIVE.** The first **dispatchable** phase of this plan is **Phase 9** (the
> mandatory probe gate). Phases 1-7 are landed. **Phase 8 is a closed historical record whose
> target statement is machine-refuted — it MUST NOT be resumed or re-dispatched**, notwithstanding
> its non-`[COMPLETED]` marker. Document order below equals execution order from Phase 9 onward.

**Dependency Analysis**:

Every phase from 10 onward writes the single file `Soundness.lean` (one owner), so execution is
**strictly sequential** — no two phases may be dispatched in parallel. Phase 9 owns `probes/` only
and still runs first, alone.

| Wave | Phases | Blocked by |
|------|--------|------------|
| (landed) | 1, 2, 3, 4, 5, 6, 7 | -- (historical; all [COMPLETED]) |
| (closed) | 8 | -- (historical; [BLOCKED], machine-refuted; not dispatchable) |
| 1 | 9 | -- (**HARD GATE**) |
| 2 | 10 | 9 |
| 3 | 11 | 9, 10 |
| 4 | 12 | 11 |
| 5 | 13 | 12 |
| 6 | 14 | 13 |
| 7 | 15 | 12, 13 |
| 8 | 16 | 12, 13, 15 |
| 9 | 17 | 12, 13 |
| 10 | 18 | 12, 13, 17 |
| 11 | 19 | 13, 14, 15, 16, 17, 18 |
| 12 | 20 | 19 |
| 13 | 21 | 20 |
| 14 | 22 | 21 |
| (terminal) | 23 | not on the critical path |

Each wave contains exactly one phase: the plan is fully sequential by file territory.

### Phase 1: Base forcing-equivalence lemmas box_iff_base, dia_iff_base [COMPLETED]

- **Landed**: `box_iff_base` (Soundness.lean:416), `dia_iff_base` (:434). Sorry-free, axiom-clean.
  **Do NOT re-plan or re-derive.** Preserved Asset.

### Phase 2: TClosure-class extension box_iff_TClosure, dia_iff_TClosure [COMPLETED]

- **Landed**: `box_iff_TClosure` (:464), `dia_iff_TClosure` (:479). **Do NOT re-derive.**
  Preserved Asset. Still relevant: Phase 18's geometric bridge is the syntactic analogue of these
  semantic facts.

### Phase 3: F2 target-raise + reflexive here-extraction helpers [COMPLETED]

- **Landed**: `cs5FCIncest_raise` (:378); `box_gives_here` (:390). **Do NOT re-derive.**

### Phase 4: Single-node interpretation-raise step boxI_raise_step [COMPLETED]

- **Landed**: `boxI_raise_step` (:567). **Do NOT re-derive.**

### Phase 5: Star-lifting over all direct raw-neighbours boxI_lift_star [COMPLETED]

- **Landed**: `boxI_lift_star` (:656). **Do NOT re-derive.**

### Phase 6: Derivation-forest invariant IsDerivationForest + preservation lemmas [COMPLETED]

- **Landed**: `IsDerivationForest` (:765), `forest_trivial` (:774), `forest_addEdge_fresh` (:784).
  **Do NOT re-derive.** On the critical path: its graded-rank / unique-parent content supplies
  `place`'s depth index (Phase 11) and `forest_addEdge_fresh` supports Phase 17.

### Phase 7: Tree-cascade lifting lemma boxI_lift [COMPLETED]

- **Landed**: `ht_le_of_reflTransGen` (:931), `raise_subtree` (:950), `siblings_disjoint` (:1128),
  `boxI_lift_ancestor` (:1182), `boxI_lift` (:1329). **Do NOT re-derive.** `ht_le_of_reflTransGen`
  feeds `place`'s depth accessor (Phase 11).

### Phase 8: Target-oriented nikTr bridge — MACHINE-REFUTED, CLOSED [BLOCKED]

**CLOSED HISTORICAL RECORD. Do NOT resume or re-dispatch this phase.** Its sub-steps 8.2
(`efq`/`orE`), 8.3 (modal cases), and 8.4 (specialisation) are superseded by Phases 9-22. Its
output splits three ways:

- **Preserved** (see Preserved Assets): `bigAndL`, `factsAt`, `sigAtFuel`, `sigAt`, the entire
  `cs5_deriv_*` toolkit, `bigAndL_*`, `factsAt_*`, `sigAtFuel_mono_context`,
  `sigAtFuel_congr_above_rank`, `hfin_toFinset_card_pos`. Independently corroborated by the
  falseness probe, which is built from them.
- **Retargeted**: the ten `sigAt_*` core case lemmas (see Retired Assets, last row) — their
  propositional content transfers to the `Θ`/`place` shape in Phases 13-14.
- **Retired outright** (deleted in Phase 11): `nikTr`, `nikTrFuel`, and the nine lemmas /
  two sanity examples that serve the ancestor walk. ~200-250 lines.

- **Blocked:** 2026-07-24 — `nik_adequacy` against `nikTr` machine-proven FALSE
  (`probes/nik_adequacy_falseness.lean`; reports/06_falseness-machine-check.md).

### Phase 9: MANDATORY PROBE GATE — adversarial validation of `Θ ⊃ place` [IN PROGRESS]

**This is a hard gate, not a suggestion. No Phase 10+ work may begin until this phase reports
PASS.** Rationale: a prose reconstruction from a damaged source already produced a false-making
definition once, and this probe methodology is now proven to catch exactly that failure mode.

- **Goal:** Establish, by machine check, that the candidate target-independent definition is not
  refutable by the known adversarial shapes — before a single line of adequacy induction is
  attempted.
- **Territory:** `specs/537_labelled_cs5_general_soundness_biconditional/probes/` **only**.
  `Cslib/` MUST remain untouched this phase (`git status --short Cslib/` empty at phase end).
- **Tasks:**
  - [ ] (Recommended, non-blocking) Attempt to obtain a legible copy of Simpson §6.1 Fig. 6-1/6-2
        (`/literature` discovery on `simpson_1994_intuitionisticmodallogic`, a cleaner PDF, or the
        published thesis). Record whether it was obtained. Every definitional choice still
        reconstructed from prose MUST be flagged as such in the probe's header comment.
  - [ ] Write `probes/theta_place_validation.lean`, importing `Soundness.lean` and `CS5Canonical`,
        and define the candidate `Θ (G Γ hfin)` and `place (G hfin x A)` **there** (scratch, NOT in
        `Cslib/`). Start from `Θ := sigAt G Γ hfin root` per reports/05-06, and
        `place := □^{d(x)} A`.
  - [ ] **Resolve the known-in-advance orphan-context defect.** Re-run probe #2's witness
        (`Γ = [var 1 ∶ ⊥]` with `var 1 ∉ G.X`, conclusion at the root `var 0 ∈ G.X`) against the
        candidate. The naive `Θ := sigAt … root` IS refuted by it (see Risks). Extend `Θ` with an
        orphan-context component — the `Γ`-facts at labels not reachable from the root, conjoined
        at depth 0 — and re-run. Do not proceed until this witness fails to refute.
  - [ ] **Adversarial case A — disconnected conclusion.** Port `nik_adequacy_is_false`'s witness
        (`G = Graph.trivial ℕ`, `Γ = [var 0 ∶ ⊥]`, conclusion at `var 1 ∉ G.X`, `.assumption` then
        `.efq`) to the candidate statement. Show the reductio **cannot** be completed, and
        positively: derive `Θ ⊃ place(var 1, A)` for the candidate (it should follow because `Θ`
        contains `⊥`).
  - [ ] **Adversarial case B — disconnected context.** As above for
        `rooted_restricted_adequacy_is_false`'s witness.
  - [ ] **Adversarial case C — the `premise_escapes_graph` shape.** Exhibit the same context (all
        labels in `G.X`) deriving `⊥` at a label outside `G.X`, and confirm the candidate statement
        is *still* provable there — i.e. that the candidate does not merely dodge the refutation by
        re-introducing an uninductive side condition. **The candidate statement MUST carry no
        `x ∈ G.X` and no `labels(Γ) ⊆ G.X` hypothesis** (established fact 3).
  - [ ] **Forward-looking case D — `orE` at depth ≥ 1.** Build a two-level graph with a disjunction
        at a depth-1 label and an `orE` conclusion at an unrelated label, and machine-check whether
        closing it requires `□^d(A∨B) ⊃ □^d A ∨ □^d B` (the non-theorem that killed the flat
        shortcut) or whether the shared-`Θ` structure sidesteps it. Record the finding explicitly —
        this is the primary residual risk and must be surfaced now, not at Phase 16.
  - [ ] **Forward-looking case E — collapse at `Graph.trivial`.** Confirm `Θ (Graph.trivial) []` is
        a CS5 tautology and `place root φ = φ`, so `⊢ Θ ⊃ place root φ` yields `⊢ φ` by modus
        ponens (the Phase 20 collapse). Reuse the existing probe's `bigAndL_nil_deriv` /
        `deriv_and` pattern.
  - [ ] Write the gate verdict into the probe's header comment: PASS/FAIL per case, plus the final
        `Θ`/`place` definitions to be transcribed into `Cslib/` in Phase 11.
- **PASS criterion (the gate):** cases A, B, C each fail to refute the candidate — the reductio
  does **not** compile while the corresponding positive derivation **does** — AND case E's collapse
  compiles, AND case D's finding is recorded. The probe file compiles under `lake env lean` at exit
  0 with zero `sorry`, and `#print axioms` shows no `sorryAx` on every reductio-attempt and every
  positive derivation.
- **FAIL handling:** if any of A/B/C still refutes, or D shows the non-theorem is genuinely
  required, **iterate on the definition inside this phase** (e.g. a nested layered form
  `Θ_0 ⊃ □(Θ_1 ⊃ □(…))` whose per-level antecedents cover the whole depth layer, keeping the
  antecedent target-independent while avoiding the flat conflation). Only if no candidate survives
  within the phase budget does this route to Phase 23.
- **Timing:** one to three agent runs (hard cap: three).
- **Estimated output:** ~150-350 lines of probe code.
- **Depends on:** none (reuses landed `sigAt`/`bigAndL`/`cs5_deriv_*` and the existing probe).
- **Zero-debt contract:** `Cslib/` untouched; probe file compiles clean; no `sorryAx`.

### Phase 10: `IsRootedForest` + root naming + preservation lemmas [NOT STARTED]

- **Goal:** Name the single root that anchors `Θ` and defines `place`'s depth. **This is NOT the
  fix for the cross-label cases** — that use is machine-refuted (established fact 2). It is
  bookkeeping for the translation's definition.
- **Tasks:**
  - [ ] Define `IsRootedForest G := IsDerivationForest G ∧ ∃ root, ∀ z ∈ G.X, Relation.ReflTransGen G.R root z`
        (or as a fourth conjunct on `IsDerivationForest`; choose whichever keeps `forest_trivial` /
        `forest_addEdge_fresh` reusable without re-proof).
  - [ ] `rooted_trivial` — `Graph.trivial`'s single node reaches itself.
  - [ ] `rooted_addEdge_fresh` — `addEdge x y` for fresh `y` preserves reachability-from-root (the
        root already reaches `x`; extend by one step). Mirror `forest_addEdge_fresh`.
  - [ ] A `root` accessor plus `root_mem` / `root_reaches` lemmas usable by `Θ` and `place`.
- **Timing:** one agent run. **Estimated output:** ~100-200 lines.
- **Depends on:** 9
- **Verification / Done when:** all lemmas compile sorry-free; scoped build
  `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness` green; `lean_verify`
  axiom-clean on each; commit.
- **Zero-debt contract:** no `sorry`, no new axiom, no Preserved Asset touched.

### Phase 11: Land `Θ` / `place` / depth accessor; DELETE the retired ancestor walk [NOT STARTED]

- **Goal:** Transcribe Phase 9's validated definitions into `Cslib/`, and remove the refuted ones.
- **Tasks:**
  - [ ] Define the depth accessor `depth G root x` (0 for labels unreachable from `root`),
        grounded in the landed graded-rank `ht` / `ht_le_of_reflTransGen` content.
  - [ ] Define `place G hfin x A := □^{depth …} A` (iterated box; the iterator itself lands in
        Phase 12 — define `place` against a minimal local `boxIter` here and reconcile, or land
        `boxIter` here and have Phase 12 build on it; pick one and state it).
  - [ ] Define `Θ G Γ hfin` **exactly as validated in Phase 9**, including the orphan-context
        component. Reuse `sigAt` verbatim for the in-graph part.
  - [ ] Land the replacement sanity `example`s: `Θ (Graph.trivial) []` is a CS5 tautology;
        `place root A = A`; `place` at a one-edge child adds exactly one `□`. Reproduce Phase 9
        case E here.
  - [ ] **DELETE every Retired Assets row marked DELETE**, including the two old `nikTr` sanity
        examples. Confirm with `grep -n 'nikTrFuel'` that no references survive.
  - [ ] Update the section docstring: record the retarget, cite the falseness probe by path, and
        flag every definitional choice still reconstructed from OCR-damaged prose.
- **Timing:** one to two agent runs. **Estimated output:** ~150-300 lines net (≈ +350 new,
  ≈ −220 deleted).
- **Depends on:** 9, 10
- **Verification / Done when:** `Θ`, `place`, `depth` type-check and reduce; sanity `example`s
  compile; retired declarations are gone; scoped build green; `lean_verify` axiom-clean; commit.
- **Zero-debt contract:** no `sorry`, no new axiom, `cs5FCIncest` unweakened, `Graph` unmodified,
  no Preserved Asset touched.

### Phase 12: Iterated-box toolkit [NOT STARTED]

- **Goal:** The `Derivable CS5ModalAxiom`-level tools every constructor case will consume. Land
  these BEFORE any case, so no case dispatch is spent building infrastructure.
- **Tasks:**
  - [ ] `boxIter k A` (`□^k A`) plus `boxIter_zero` / `boxIter_succ` reduction lemmas.
  - [ ] `boxIter`-monotonicity: from `⊢ A ⊃ B` derive `⊢ □^k A ⊃ □^k B` (iterate the landed
        `cs5_deriv_box_mono`).
  - [ ] `boxIter` K-distribution over `∧`: `⊢ □^k(A ∧ B) ⊃ □^k A ∧ □^k B` and the converse (both
        hold in a normal system; the `∧`-introduction direction uses `CS5ModalAxiom.k` + `andI`).
  - [ ] **`T`-iteration**: `⊢ □^k ⊥ ⊃ ⊥`, by iterating `CS5ModalAxiom.tBox` (`CS5.lean:171-173`).
        This is the lemma that discharges `efq` (Phase 15).
  - [ ] **`Θ`-injection**: `⊢ Θ(G,Γ) ∧ □^{d(x)} A ⊃ Θ(G, (x∶A) :: Γ)`. The box-conflation makes
        this *easier*, not harder: `□^d A` supplies `A` at every depth-`d` position, a superset of
        what `Θ(G,(x∶A)::Γ)` needs at `x`. Prove by induction down the box path, base case
        `σ_x ∧ A ⊃ σ_x[A]`.
  - [ ] **`Θ` context-monotonicity** at the whole-`Θ` level (lift the landed
        `sigAtFuel_mono_context` plus the orphan component).
  - [ ] **`Θ` graph-extension monotonicity**: `⊢ Θ(G,Γ) ⊃ Θ(G.addEdge x y, Γ)` for `y` fresh (the
        new subtree's translation is a `⊤`-surrogate). Prerequisite for Phase 17.
- **Timing:** two to three agent runs. **Estimated output:** ~250-400 lines.
- **Depends on:** 11
- **Verification / Done when:** each lemma compiles sorry-free; scoped build green; `lean_verify`
  axiom-clean; commit **after each lemma** (commit-per-green-substep mandate).
- **Zero-debt contract:** as Phase 11.

### Phase 13: Adequacy statement + propositional constructor group [NOT STARTED]

- **Goal:** State the adequacy target and discharge the seven label-local, context-preserving
  constructors.
- **Scope:** `assumption`, `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `impE`.
- **Tasks:**
  - [ ] State the target
        `nik_adequacy : IsRootedForest G → NIK TS5 G Γ (x ∶ A) → Derivable CS5ModalAxiom (Θ G Γ hfin ⊃ place G hfin x A)`.
        **The statement MUST carry no `x ∈ G.X` and no `labels(Γ) ⊆ G.X` hypothesis** (established
        fact 3). Instantiate the axiom set to `CS5ModalAxiom` (= `IKTB4`, Simpson Thm 6.2.1).
  - [ ] Land the seven cases as named standalone lemmas (`theta_assumption`, `theta_andI`, …),
        each proving the `Θ ⊃ place` fact directly. Follow plan v5's landed pattern: standalone
        lemmas first, consumed by the single `induction` block in Phase 19.
  - [ ] Retire the corresponding target-oriented originals (`sigAt_assumption`, `sigAt_andI`,
        `sigAt_andE1`, `sigAt_andE2`, `sigAt_orI1`, `sigAt_orI2`, `sigAt_impE`,
        `sigAt_imp_of_factsAt_imp`) once their replacements are green.
  - [ ] `assumption` note: the case must handle a `Γ`-fact at an **orphan** label (not reachable
        from the root) via `Θ`'s orphan component at depth 0. Do not assume `x ∈ G.X`.
- **Timing:** two to three agent runs. **Estimated output:** ~250-400 lines.
- **Depends on:** 12
- **Verification / Done when:** all seven lemmas compile sorry-free; scoped build green;
  `lean_verify` axiom-clean on each; retired originals removed; commit per lemma.
- **Zero-debt contract:** as Phase 11.

### Phase 14: `impI` — depth-indexed context discharge [NOT STARTED]

- **Goal:** Discharge the one propositional constructor that removes a context entry.
- **Tasks:**
  - [ ] Land the depth-indexed analogue of `sigAt_cons_self_imp`: from
        `⊢ Θ(G,(x∶A)::Γ) ⊃ □^{d(x)} B` derive `⊢ Θ(G,Γ) ⊃ □^{d(x)} (A ⊃ B)`. Route via Phase 12's
        `Θ`-injection lemma (`Θ(G,Γ) ∧ □^d A ⊃ Θ(G,(x∶A)::Γ)`), then `cs5_deriv_curry` and
        `boxIter` K-distribution to pull `A ⊃ ·` under the boxes.
  - [ ] Land `theta_impI`.
  - [ ] Retire `sigAt_impI` and `sigAt_cons_self_imp` once green.
- **Timing:** one to two agent runs (this was the hardest of the eight landed propositional cases;
  budget accordingly). **Estimated output:** ~120-250 lines.
- **Depends on:** 13
- **Verification / Done when:** `theta_impI` compiles sorry-free; scoped build green;
  `lean_verify` axiom-clean; commit.
- **Zero-debt contract:** as Phase 11.

### Phase 15: `efq` — the cross-label `⊥` case via iterated `T` [NOT STARTED]

- **Goal:** Discharge `NIK.efq` — the constructor whose cross-label form refuted the previous
  translation.
- **Tasks:**
  - [ ] Land `theta_efq`: from the IH `⊢ Θ ⊃ place(x,⊥) = Θ ⊃ □^{d(x)}⊥`, apply Phase 12's
        `T`-iteration (`⊢ □^k⊥ ⊃ ⊥`) to get `⊢ Θ ⊃ ⊥`, then `CS5ModalAxiom.efq` (`⊥ ⊃ φ`) and
        `cs5_deriv_imp_trans` to get `⊢ Θ ⊃ place(y,A)` for an **arbitrary** `y`.
  - [ ] Explicitly exercise the disconnected `y` (`y ∉ G.X`, `d(y) = 0`, `place(y,A) = A`) — this
        is the exact shape of the falseness witness and MUST go through with no side condition
        on `y`.
  - [ ] Cross-check against Phase 9 cases A and B (same witnesses, now inside `Cslib/`).
- **Timing:** one agent run. **Estimated output:** ~80-180 lines.
- **Depends on:** 12, 13
- **Verification / Done when:** `theta_efq` compiles sorry-free with **no** hypothesis on `y`;
  scoped build green; `lean_verify` axiom-clean; commit.
- **Zero-debt contract:** as Phase 11. Additionally: **no restriction may be added to `NIK.efq`**.

### Phase 16: `orE` — the cross-label disjunction case (PRIMARY RESIDUAL RISK) [NOT STARTED]

- **Goal:** Discharge `NIK.orE`, whose three premises share the antecedent `Θ` but whose major
  premise sits at a depth possibly different from the conclusion's.
- **Tasks:**
  - [ ] **First task is a machine check, not a proof attempt**: open the concrete goal and confirm
        Phase 9 case D's recorded finding — whether closing `orE` requires
        `□^d(A∨B) ⊃ □^d A ∨ □^d B` (a **non-theorem**, and the exact obstruction that killed the
        fully-boxed flat shortcut under plan v4) or whether the shared-`Θ` structure sidesteps it.
        Use `lean_goal` / `lean_multi_attempt` before writing any proof.
  - [ ] If sidestepped: land `theta_orE`, combining the two branch IHs
        (`⊢ Θ(G,(x∶A)::Γ) ⊃ □^{d(y)}C`, `⊢ Θ(G,(x∶B)::Γ) ⊃ □^{d(y)}C`) with the major-premise IH
        (`⊢ Θ(G,Γ) ⊃ □^{d(x)}(A∨B)`) under the shared `Θ`, via Phase 12's `Θ`-injection and the
        landed `cs5_deriv_imp_orI1`/`_orI2` plus `CS5ModalAxiom.orE`.
  - [ ] If NOT sidestepped: this is a **concrete machine-checked obstruction against the `□^d`
        placement design** (not against the target-independent antecedent). Return to **Phase 9**
        with a revised `place` — the layered `Θ_0 ⊃ □(Θ_1 ⊃ □(…))` form whose per-level antecedents
        cover the whole depth layer, keeping target-independence while avoiding the flat
        conflation. Route to Phase 23 only if that also fails under machine check.
  - [ ] Either way: record the outcome in the phase completion note, since it determines whether
        Phases 17-18 proceed against the same `place`.
- **Timing:** two to three agent runs (hard cap: three). **Estimated output:** ~150-350 lines.
- **Depends on:** 12, 13, 15
- **Verification / Done when:** `theta_orE` compiles sorry-free with **no** hypothesis on `y`;
  scoped build green; `lean_verify` axiom-clean; commit. OR: the obstruction is machine-documented
  and the phase routes back to Phase 9 (or forward to Phase 23).
- **Zero-debt contract:** as Phase 11. Additionally: **no restriction may be added to `NIK.orE`**.

### Phase 17: Eigenvariable / graph-extension cases `boxI` and `diaE` [NOT STARTED]

- **Goal:** Discharge the two constructors whose premises live over an extended graph
  `G.addEdge x y` for cofinitely many fresh `y`.
- **Tasks:**
  - [ ] `theta_boxI`: from `∀ y ∉ L, ⊢ Θ(G.addEdge x y, Γ) ⊃ place(y, A)` (where
        `d(y) = d(x) + 1`), derive `⊢ Θ(G,Γ) ⊃ place(x, □A) = Θ(G,Γ) ⊃ □^{d(x)}(□A)`. Note
        `□^{d(x)}(□A) = □^{d(x)+1}A = place(y,A)` definitionally, so the case reduces to Phase 12's
        `Θ` graph-extension monotonicity plus instantiating the cofinite premise at one fresh
        witness. Use `hL.Finite` + `G.X.Finite` to produce a fresh label.
  - [ ] `theta_diaE`: from `⊢ Θ(G,Γ) ⊃ place(x,◇A)` and
        `∀ y ∉ L, ⊢ Θ(G.addEdge x y, (y∶A)::Γ) ⊃ place(z,B)`, derive `⊢ Θ(G,Γ) ⊃ place(z,B)`.
        Combines the graph-extension monotonicity with the `Θ`-injection (for `(y∶A)`) and
        `CS5ModalAxiom.kdia`.
  - [ ] Thread `IsRootedForest` preservation through both via Phase 10's `rooted_addEdge_fresh`
        and the landed `forest_addEdge_fresh`.
- **Timing:** two to three agent runs. **Estimated output:** ~200-400 lines.
- **Depends on:** 12, 13
- **Verification / Done when:** both lemmas compile sorry-free; scoped build green; `lean_verify`
  axiom-clean; commit per lemma.
- **Zero-debt contract:** as Phase 11.

### Phase 18: Geometric `TClosure` bridge + `boxE` and `diaI` [NOT STARTED]

- **Goal:** Discharge the two constructors whose relational premise ranges over the **𝒯-closure**
  of `G.R` rather than a raw edge. This is where Simpson's Thm 6.2.1 / Lemma 6.2.3 extension to
  `Ax(𝒯)` (`𝒯 = {χ_T, χ_B, χ_4}`) is actually consumed — the "geometric" group.
- **Tasks:**
  - [ ] Land the bridge lemma by induction on `TClosure TS5 G.R x y`: for each constructor
        (`base`, `refl`, `symm`, `trans`; `eucl` is unreachable since `Five ∉ TS5` — confirm and
        discharge that case), derive `⊢ place(x, □A) ⊃ place(y, A)` and the `◇`-dual, using the
        matching landed `CS5ModalAxiom` constructors: `k`/`kdia` for `base`, `tBox`/`tDia` for
        `refl`, `bBox`/`bDia` for `symm`, `fourBox`/`fourDia` for `trans`.
        **Note `d(y)` is NOT `d(x) + 1` in general here** — the depths are unrelated, which is
        exactly why this needs its own named lemma rather than an inline step.
  - [ ] `theta_boxE` and `theta_diaI` as corollaries of that bridge plus the corresponding IH.
- **Timing:** two to three agent runs. **Estimated output:** ~200-400 lines.
- **Depends on:** 12, 13, 17
- **Verification / Done when:** the `TClosure` bridge and both constructor lemmas compile
  sorry-free; scoped build green; `lean_verify` axiom-clean; commit per lemma.
- **Zero-debt contract:** as Phase 11.

### Phase 19: Assemble `nik_adequacy` (the real 12-case induction) [NOT STARTED]

- **Goal:** Wire the twelve standalone case lemmas into the single `induction h with …` block Lean
  requires, producing the actual `nik_adequacy` theorem.
- **Tasks:**
  - [ ] Open `induction h with` over all 12 `NIK` constructors, discharging each by its
        Phase 13-18 lemma. Generalise over `Γ`/`G` where the graph- or context-extending
        constructors (`impI`, `orE`, `boxI`, `diaE`) require it.
  - [ ] Confirm the motive threads `IsRootedForest` correctly across the graph-extending cases.
  - [ ] `lean_verify` on `nik_adequacy`: no `sorryAx`, no new axioms.
- **Timing:** one to two agent runs. **Estimated output:** ~100-250 lines.
- **Depends on:** 13, 14, 15, 16, 17, 18
- **Verification / Done when:** `nik_adequacy` compiles sorry-free across all 12 constructors;
  scoped build green; `lean_verify` axiom-clean; commit.
- **Zero-debt contract:** as Phase 11.

### Phase 20: Specialise to `nik_TS5_to_hilbert` over `Graph.trivial` [NOT STARTED]

- **Goal:** `nik_TS5_to_hilbert : NIKTheorem TS5 φ → Derivable CS5ModalAxiom φ`.
- **Tasks:**
  - [ ] Instantiate `nik_adequacy` at `G := Graph.trivial`, `Γ := []`,
        `x := (Graph.trivial).nonempty.choose` (which IS the root), discharging `IsRootedForest`
        by Phase 10's `rooted_trivial`.
  - [ ] Collapse: `place root φ = □^0 φ = φ`; `Θ (Graph.trivial) []` is the `⊤`-surrogate
        `(⊥⊃⊥) ∧ (⊥⊃⊥)` with an empty orphan component, CS5-derivable by the probe's
        `bigAndL_nil_deriv` / `deriv_and` pattern. Discharge the implication by modus ponens.
  - [ ] Reconcile implicit `Atom`/`φ` binders and universe variables.
- **Timing:** one agent run. **Estimated output:** ~40-120 lines.
- **Depends on:** 19
- **Verification / Done when:** `nik_TS5_to_hilbert` compiles with the exact stated signature;
  scoped build green; `lean_verify` axiom-clean; commit.
- **Zero-debt contract:** as Phase 11.

### Phase 21: Corollary assembly nik_TS5_soundness + docstring cleanup [NOT STARTED]

- **Goal:** Assemble the goal theorem as the corollary composing the Phase 20 bridge with the
  landed Hilbert soundness, and retire the stale module-docstring notes.
- **Tasks:**
  - [ ] Land `nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ` as
        `fun h => cs5_soundness_derivable_incest (nik_TS5_to_hilbert h)` (`CS5Canonical.lean:359`).
        Reconcile universe variables (`cs5_soundness_derivable_incest` is `.{u, v}`-polymorphic)
        and implicit `Atom`/`φ` binders.
  - [ ] Update the `Soundness.lean` module docstring: mark the general theorem LANDED via the
        Hilbert bridge; remove the stale `INTRACTABLE` / `GATE-C` / "What remains" /
        "Fifth dispatch" notes; record the retargeted translation and cite the falseness probe as
        the reason the target-oriented shape was abandoned.
- **Timing:** one agent run. **Estimated output:** ~10-50 lines (mostly docstring).
- **Depends on:** 20
- **Verification / Done when:** `nik_TS5_soundness` sorry-free; scoped build green; `lean_verify`
  on `nik_TS5_soundness` axiom-clean.
- **Zero-debt contract:** no `sorry`, no new axiom, no weakening, no Preserved Asset regressed.

### Phase 22: Regression gate + full-project verification [NOT STARTED]

- **Goal:** Confirm the full project is green and unregressed, the Simpson 8.1.4 biconditional is
  complete, and no debt was added anywhere.
- **Tasks:**
  - [ ] Full `lake build` green.
  - [ ] `lean_verify` on `nik_TS5_soundness` reports no `sorryAx` and no new axioms.
  - [ ] `grep -nE '\bsorry\b'` on `Soundness.lean`: no tactic `sorry` (docstring prose excepted);
        `grep -nE '^axiom '`: zero.
  - [ ] Confirm every Retired Asset is actually gone (`grep -n 'nikTrFuel\|\bnikTr\b'` returns only
        docstring/history mentions, if any).
  - [ ] Confirm `git diff` on `Deduction.lean` is empty (`NIK.efq`/`NIK.orE` unmodified).
  - [ ] Spot-verify the Preserved Asset rows still build sorry-free.
  - [ ] `lake lint`, `lake exe lint-style <file>`, `lake shake`, `lake exe checkInitImports`,
        `lake test` all unregressed against the task-517 baseline.
- **Timing:** one agent run. **Estimated output:** verification only (~0-20 lines).
- **Depends on:** 21
- **Verification / Done when:** all checks pass; the Simpson 8.1.4 biconditional is complete.
- **Zero-debt contract:** no `sorry`, no new axiom, no weakening, no regression.

### Phase 23: Sanctioned terminal + route-(b) research recommendation [BLOCKED]

**Not an implementation step.** The sanctioned terminal if the retargeted bridge itself overruns
with a **concrete, machine-checked** obstruction (never a hand-waved wall): a documented
`[BLOCKED]` handoff scoped to the precise obstruction, with all landed assets intact, build green,
zero debt, and a route-(b) research task recommended (dedicated cut-admissibility / `⊥`-locality
research for `N_IK(𝒯)`, taking the preserved PD.2 corrected motive — 11 of 12 constructors,
summaries/10 — as its starting point).

- **PD.1 — LANDED (Preserved Asset).** `bot_backward` / `bot_iff_edge` / `bot_iff_TClosure`. Note:
  these are `CKForces` (semantic) facts and are **NOT** reusable for the syntactic Hilbert bridge —
  plan v5's expectation that they would discharge `efq` was disproved. They remain preserved for
  the route-(b) research.
- **PD.3 — the `efq` residual on the SEMANTIC route remains genuinely open.** This is a different
  gap from the one this plan closes: the Hilbert route discharges disconnected `⊥` via the `T`
  axiom, which the intuitionistic Kripke semantics cannot.
- **Escalation bar:** invoked only after a phase's machine-checked obstruction survives its
  dispatch budget, and (for the `orE` case) only after Phase 16's re-entry into Phase 9 with a
  revised `place` has also failed. **Never a `sorry`, never a new axiom, never a vacuous
  definition, never a return to the refuted connectivity-lemma / clique / exact-symmetry
  decompositions, never a retry of the two refuted flat-translation shortcuts, and never a
  restriction of `NIK.efq`/`NIK.orE`.**

## Testing & Validation

- [ ] **Phase 9 gate**: `lake env lean probes/theta_place_validation.lean` exits 0 with zero
      errors, zero warnings, zero `sorry`; `#print axioms` on every reductio-attempt and positive
      derivation shows no `sorryAx`; `git status --short Cslib/` empty for that phase.
- [ ] **Phase 9 gate verdict recorded**: PASS/FAIL per adversarial case A, B, C, D, E in the probe
      header comment.
- [ ] `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness` green after every
      phase and every green sub-step that touches `.lean`.
- [ ] Full `lake build` green at Phase 22.
- [ ] `lean_verify` axiom-clean on each new definition/lemma as it lands (`Θ`, `place`, `depth`,
      the Phase 12 toolkit, each `theta_*` case lemma, `nik_adequacy`, `nik_TS5_to_hilbert`,
      `nik_TS5_soundness`).
- [ ] Replacement sanity `example`s (Phase 11): `Θ (Graph.trivial) []` tautologous;
      `place root A = A`; a one-edge child adds exactly one `□`.
- [ ] **Retirement check**: `grep -n 'nikTrFuel\|\bnikTr\b' Soundness.lean` returns no
      declarations (docstring/history mentions only).
- [ ] **Statement-shape check**: `nik_adequacy`'s signature carries no `x ∈ G.X` and no
      `labels(Γ) ⊆ G.X` hypothesis; `NIK.efq` and `NIK.orE` in `Deduction.lean` are byte-identical
      to their pre-task form (`git diff` on `Deduction.lean` empty).
- [ ] `grep -nE '\bsorry\b'` on `Soundness.lean`: no tactic `sorry` (docstring prose excepted);
      `grep -nE '^axiom '`: zero.
- [ ] `Graph` structure unmodified; `cs5FCIncest` unweakened.
- [ ] `lake lint`, `lake exe lint-style <file>`, `lake shake`, `lake exe checkInitImports`,
      `lake test`: all unregressed against the task-517 green baseline.
- [ ] Preserved Assets unregressed (spot-verify every row builds sorry-free).

## Artifacts & Outputs

- plans/06_target-independent-theta-translation.md (this file)
- probes/theta_place_validation.lean (Phase 9 gate artifact; scratch, never imported by `Cslib/`)
- probes/nik_adequacy_falseness.lean (existing; a **planned input** to Phase 9, retained as the
  permanent record of why the target-oriented translation was abandoned)
- Modified: Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean (Phases 10-22)
- handoffs/ blocked handoff (contingency only, if a phase's machine-checked obstruction survives
  its budget → Phase 23)
- summaries/06_target-independent-theta-translation-summary.md (on completion)

## Rollback/Contingency

- Each phase (and each green sub-step within a phase) commits only its own green result. If a step
  fails to reach green, leave the prior committed state intact and fix forward — never destructive
  git on a dirty tree (`.claude/rules/git-workflow.md`, "No Destructive Git on Uncommitted Work").
- **Phase 9 FAIL is not an escalation** — it is the gate doing its job. Iterate on the definition
  inside Phase 9 (up to its three-run cap), including the layered `Θ_0 ⊃ □(Θ_1 ⊃ □(…))` alternative
  to flat `□^d` placement.
- **Phase 16's `orE` obstruction** (the `□^d(A∨B) ⊃ □^d A ∨ □^d B` non-theorem) routes **back to
  Phase 9** with a revised `place`, not directly to Phase 23. The target-independent antecedent is
  not what would be at fault there; the placement encoding is.
- **Phase 11's deletions are reversible via git** — the retired declarations remain recoverable
  from history if a later phase discovers an unanticipated consumer. Do not hedge by leaving them
  in the file.
- The only sanctioned terminal, if a phase's **concrete, machine-checked** obstruction survives its
  dispatch budget, is the Phase 23 `[BLOCKED]` handoff + route-(b) research recommendation, scoped
  to the precise obstruction, with all Preserved Assets intact, build green, and zero debt —
  **never a `sorry`, never a new axiom, never a vacuous definition, never a restriction of
  `NIK.efq`/`NIK.orE`, never a revival of root-connectivity-as-the-fix or the label-restricted
  variant, and never a retry of the two refuted flat-translation shortcuts.**
