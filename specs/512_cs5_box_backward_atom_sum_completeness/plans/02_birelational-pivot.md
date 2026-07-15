# Implementation Plan: Task #512 — CS5 Completeness via Birelational Canonical Model (Pivot)

- **Task**: 512 - cs5_box_backward_atom_sum_completeness
- **Status**: [IN PROGRESS] (Phase 1 gate COMPLETE/PASS; Phases 2–7 authorized)
- **Effort**: 19 hours
- **Dependencies**: 509 (soundness + mechanized obstruction, both branches landed; Phase 4 REWORKS its `cs5FC''` soundness)
- **Research Inputs**:
  - reports/03_alternative-techniques.md
  - reports/04_birelational-feasibility.md
  - reports/05_collapse-s5-probe.md
  - reports/01_box-backward-atom-sum.md (superseded architecture; reuse references preserved)
- **Artifacts**: plans/02_birelational-pivot.md (this file); supersedes plans/01_box-backward-atom-sum.md
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Supersede plan 01's doubled-atom / atom-sum architecture and PIVOT to the **birelational canonical
model** (Božić–Došen 1984 / Došen 1985 IS5 / Simpson 1994 / Alechina–Mendler–de Paiva–Ritter 2001)
to discharge CS5 constructive completeness. The decisive shift: the canonical relation becomes
**one-sided** — `Γ R Δ ⟺ boxInv Γ ⊆ Δ` — so box-backward stops being a simultaneous-pair problem and
dissolves to the plain one-sided prime lemma already landed as `box_refuting_theory`
(`SegmentLindenbaum.lean`). Symmetry is no longer baked into worlds; it becomes a **global
frame-correspondence condition** — the ≤-mediated **incestuality** condition (Plotkin–Stirling frame
correspondence, Marin–Morales–Straßburger 2021 Thm 7.1) — NOT the naive two-sided `boxInv T ⊆ H` that
CSLib's current `cs5Tail` encodes. That naive per-world back-inclusion IS the negation-completeness
wall; it is the precise diagnosis of the five-dispatch failure (report 03 §0, report 04 Q1
"CRUCIAL SUBTLETY").

**Why the pivot is now authorized (report 05).** The CKB=IKB collapse extends to S5 (Pacheco 2024
Conclusion, verbatim + mechanized in CSLib via `cs5_dia_or` = k3, `cs5_dia_bot_imp_bot` = k5). So
`CS5 ≡ IS5` (`CS5.lean:93–99`): the constructive Wijesekera diamond does NOT force pair/fallible
worlds at S5 strength, and Došen's single-prime-theory IS5 model applies directly. Option (c) —
banking a negative result — is REFUTED (the logic is complete; birelational completeness demonstrably
exists). Option (a) plan 01's atom-sum route walks straight back into Pacheco's own
negation-completeness move (`ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ`, chunk_0012:48) that the doubled atoms exist to replace.

**Definition of done**: either (SUCCESS) `cs5_completeness` / `cs5_soundness_completeness` lands
sorry-free with `#print axioms` showing only `Classical.choice`/`propext`/`Quot.sound`; or (GATE
FAILURE at Phase 1) the pivot is shown to hit the SAME wall via a mechanized obstruction theorem, and
completeness is marked "BLOCKED across all known-mechanizable routes" (NOT an incompleteness result —
`CS5 ≡ IS5` is still complete). NO `sorry` and NO new `axiom` under `Cslib/` at ANY phase boundary
(zero-debt invariant); probe `sorry` confined to `specs/512_.../probes/`.

### Research Integration

Newly integrated this revision (v2):

- **reports/05_collapse-s5-probe.md** (the decisive verdict): collapse extends to S5 YES-clean; option
  (c) refuted; Lemma-15 diamond-inverse shortcut is a DEAD END for box-backward (already mechanized as
  `cs5_boxInv_subset_iff`/`cs5Tail_symm`, delivers only symmetry, never the blocker); Q1 (does the
  intuitionistic-diamond box-backward genuinely avoid the negation-completeness move for CSLib's actual
  CS5 axioms) is the linchpin — "not automatic," since Pacheco's B-family box-backward needed
  negation-completeness even WITH the diamond-inverse relation. This report converts the escalation gate
  into a `revise`, and demotes plan 01 to a non-de-risked fallback.
- **reports/04_birelational-feasibility.md** (the pivot design): reuse map (Q3), ~5–6 phases /
  ~700–1100 net new lines; the ≤-mediated incestuality condition (Marin Thm 7.1) is the correct
  symmetry frame condition, NOT naive classical symmetry; box-backward is diamond-INDEPENDENT and
  dissolves to `box_refuting_theory`; the diamond risk lives entirely in the soundness-rework layer.
- **reports/03_alternative-techniques.md** (architectural verdict): (a)/(b) are dead (mechanized);
  Došen 1985 is the only positive route with a published IS5 completeness result; F1/F2 forward/backward
  confluence conditions; the wall stated precisely (§0).

Preserved from **reports/01_box-backward-atom-sum.md** (superseded, but reuse references still valid):
`Proposition.map` split to `Basic.lean`; the `CKSegment`/`Segment`/`CKExtension`/`cmreach` plumbing;
the Lindenbaum/prime-exclusion engine; `ck_truth_lemma`/`cs4_truth_lemma` as truth-lemma templates.

### BibKeys (added to `references.bib` by the research dispatch — verified present)

`Dosen1985`, `BozicDosen1984`, `Ewald1986`, `AlechinaMendlerdePaivaRitter2001`,
`MarinMoralesStrassburger2021`. All five confirmed in `references.bib`. Cite these in the module
docstring of the reworked canonical model. `Pacheco2024`, `Simpson1994`, `Wijesekera1990`,
`ArisakaDasStrassburger2015` pre-existing.

### Prior Plan Reference

Supersedes `plans/01_box-backward-atom-sum.md` (doubled-atom / atom-sum route). Plan 01's Phases 1–2
(the `Proposition.map` primitive and the `CS5Combined` transport machinery) LANDED, and its Phase 3
`cs5Combined_seed_excludes` was left `[PARTIAL]` after five dispatches with no proved obstruction —
because it is the negation-completeness wall in disguise. This pivot discards the ~520-line
`CS5Combined` scaffold (`CS5Canonical.lean`, currently ~1027 lines) as an EXPLICIT phase (Phase 2),
NOT silently, while retaining `Proposition.map` (Phase 1 of plan 01, generically useful) and the CS5
diagnosis lemma `cs5_symmetric_tail_box_gap` (`CS5.lean`).

## Goals & Non-Goals

**Goals**:
- Phase 1 GATE: prove, at paper + minimal-Lean level, that the Simpson/Došen intuitionistic-diamond
  box-backward over CSLib's actual `CS5ModalAxiom` set avoids the `ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ` move — BEFORE
  sinking the ~250–400-line soundness rework.
- Redefine the CS5 canonical frame class: one-sided `R` (`boxInv Γ ⊆ Δ`) + the ≤-mediated S5
  incestuality frame condition (Marin Thm 7.1 shape), replacing the two-sided `cs5Tail`.
- Re-prove CS5 soundness over the new incestuality frame class (reworks landed task-509 `cs5FC''`).
- Prove `cs5_box_backward` as the plain one-sided prime lemma (via `box_refuting_theory`).
- Land `cs5_truth_lemma` + `cs5_completeness`/`cs5_soundness_completeness`, sorry-free, no new axiom.
- File split: `Proposition.map` → `Basic.lean`; new birelational canonical machinery → `CS5Canonical.lean`.
- Discard the abandoned `CS5Combined` scaffold as an explicit, committed phase.

**Non-Goals**:
- Do NOT bake symmetry into worlds (the `cs5Tail` two-sided back-inclusion) — that IS the wall.
- Do NOT transcribe the naive classical symmetry condition `X R Y ⟹ Y R X`; use the ≤-mediated
  incestuality condition (Marin Remark 7.3 flags the naive form is wrong intuitionistically).
- Do NOT pursue the Lemma-15 diamond-inverse relation as a box-backward shortcut (mechanized dead end,
  report 05 Q3): it coincides with `cs5Tail` over CS5 and delivers only symmetry.
- Do NOT transcribe Pacheco Lemma 16/18's negation-completeness move (unsound for quasi-prime theories).
- Do NOT re-derive the collapse question (report 05 settled it YES; `CS5 ≡ IS5`).
- Do NOT introduce any `sorry` or new `axiom` into `Cslib/`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| R1 (LINCHPIN): the intuitionistic-diamond box-backward still needs `ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ` for CSLib's actual CS5 axioms (report 05 flags "not automatic"; Pacheco's B-family needed it even with the diamond-inverse relation) | H | M | Phase 1 is a CHEAP GO/NO-GO GATE with BOTH branches pre-specified. FAILURE → mechanized obstruction + "BLOCKED across known-mechanizable routes," not the ~250–400-line rework blind. |
| R2: the ≤-mediated incestuality frame condition transcribed wrong (Marin Remark 7.3: naive classical symmetry is wrong intuitionistically; g1111 "problematic in previous approaches") | H | M | Transcribe Marin Thm 7.1's exact `wRᵏu ∧ wRᵐv ⟹ ∃u′. u ≤ u′ ∧ ∃x. u′Rˡx ∧ vRⁿx` shape for the (b)/(5) instance; cross-check against Simpson's in-corpus F1/F2 confluence; verify soundness case-by-case in Phase 4. |
| R3: the 509 soundness rework (Phase 4) breaks landed `cs5FC''` consumers or exceeds one agent run | H | M | Phase 4 is the isolated 509-touching phase; keep `cs5FC''` and its landed obstruction lemmas intact where still valid, add the incestuality frame condition alongside; size to one run; commit at green. |
| R4: constructive (Wijesekera) vs intuitionistic (Fischer–Servi) diamond mismatch resurfaces at S5 | M | L | Report 05: collapse-YES makes `◇⊥→⊥` (k5) and `◇(A∨B)→◇A∨◇B` (k3) derivable (`cs5_dia_or`, `cs5_dia_bot_imp_bot` landed axiom-free), so Alechina's pair/fallible-world requirement is redundant at S5; single-prime-theory Došen model applies. Box-backward is diamond-independent regardless. |
| R5: discarding `CS5Combined` (~520 lines) removes a lemma later found useful | L | L | Phase 2 audits each landed lemma; `cs5Combined_necTransfer`/`cs5Combined_symmetric_tail_box_gap` are atom-sum-specific (discard with scaffold); `cs5_symmetric_tail_box_gap` (CS5.lean) and `cs5FC''_hub_forces_spoke_connectivity` (CKExtension.lean, general) STAY as documented negative results. |
| R6: file-size / build-time — `CS5Canonical.lean` rework may exceed 2000 lines or slow builds | L | M | Split: `Proposition.map` → `Basic.lean`; birelational machinery in `CS5Canonical.lean` importing `CS5.lean`; build incrementally; `lake exe mk_all --module` after edits. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |
| 7 | 7 | 6 |

Phases are strictly sequential. Phase 1 is a decision gate whose outcome (SUCCESS vs. mechanized
obstruction) selects whether Phases 2–7 execute at all. Phases 2–7 are the pivot proper; each is sized
to one agent run (~100–500 lines output). The high-cost, 509-touching risk concentrates in **Phase 4**.

---

### Phase 1: Q1 GO/NO-GO GATE — intuitionistic-diamond box-backward avoids negation-completeness [COMPLETED]

- **Goal:** CHEAPLY decide whether the Simpson/Došen intuitionistic-diamond box-backward genuinely
  avoids the negation-completeness move `ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ` for CSLib's ACTUAL `CS5ModalAxiom` set
  (CK+T+4+B). Report 04 Q1 puts this at ~92%; report 05 flags it is "not automatic" because Pacheco's
  B-family box-backward (Lemma 18/19) needed the classical move EVEN WITH the diamond-inverse relation.
  This gate is a paper proof plus minimal Lean scaffolding — it MUST NOT sink the ~250–400-line
  soundness rework before passing. *Low–medium risk, ~40–80 lines of Lean scaffolding + paper proof.*
- **Tasks:**
  - [x] Write the paper proof (in the plan-summary / a `probes/` note, NOT `Cslib/`) that Simpson's
    Prime Lemma 3.3.2 + Canonical Model Lemma 3.3.3 box-backward case, instantiated to
    `CS5ModalAxiom`, closes using ONLY the disjunction property (prime/quasi-prime) + the one-sided
    `R = boxInv Γ ⊆ Δ` + the ≤-mediated incestuality condition — with NO `ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ` step.
    Landed as the module docstring of
    `specs/512_.../probes/phase1-onesided-box-backward-gate.lean`.
  - [x] Cross-check against Marin Thm 7.1/7.2 (soundness of the incestuality condition is a semantic
    argument over incestuous frames using disjunction-property saturated sets — no neg.-completeness).
  - [x] Lean scaffolding *(deviation: fully proved, not merely stated — see below)*: stated the target
    `cs5_box_backward_onesided` signature over the one-sided relation `cs5OnesidedR`, and confirmed via
    `lean_goal` that its proof obligation reduces EXACTLY to `box_refuting_theory`
    (`SegmentLindenbaum.lean`) + a quasi-prime witness, `goals_after: []` — i.e. the SAME object
    Simpson's Prime Lemma uses — with no back-inclusion obligation. The reduction is so direct that
    `box_refuting_theory` discharges the goal completely with no `sorry` needed anywhere, in
    `Cslib/` or in the probe.
  - [x] Adversarially test the failure mode: reconstructed the exact spot where a two-sided condition
    WOULD reintroduce difficulty, as `cs5_two_sided_witness_can_fail_to_omit` (a direct application of
    the already-landed `cs5_symmetric_tail_box_gap`) — confirmed the one-sided `R` never requires it
    (its proof never inspects `A`'s shape or splits on any disjunction, unlike the two-sided case).
- **Timing:** ~2 hours (actual: single dispatch, no `sorry` needed)
- **Depends on:** none
- **Reused assets (real names + file:line):**
  - `box_refuting_theory`, `quasi_prime_exclusion` — `SegmentLindenbaum.lean` (the box-backward engine).
  - `cs5_symmetric_tail_box_gap` — `CS5.lean:712` (the mechanized diagnosis of WHY the two-sided form
    fails; reused directly, not just cited, in `cs5_two_sided_witness_can_fail_to_omit`).
  - Simpson Prime Lemma 3.3.2 / Canonical Model Lemma 3.3.3 — corpus chunks `8372f27240fe345d`,
    `caf3305a53065b87` (`Simpson1994`).
  - Marin Thm 7.1/7.2 incestuality condition — `MarinMoralesStrassburger2021` (ingested).
- **DECISION GATE — BOTH branches pre-specified:**
  - **SUCCESS** (paper proof + scaffolding confirm box-backward reduces to the one-sided prime lemma
    with NO negation-completeness step) → proceed to Phase 2 (discard scaffold) and the full pivot.
  - **FAILURE** (the intuitionistic-diamond box-backward ALSO requires `ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ` for CSLib's
    CS5 axioms) → the pivot hits the SAME wall. Land the obstruction as a mechanized theorem in
    `CS5Canonical.lean` (a PROVED negative statement, sorry-free, no new axiom), and mark CS5
    completeness "BLOCKED across all known-mechanizable routes" — explicitly NOT an incompleteness
    result (`CS5 ≡ IS5` is complete; what is blocked is mechanization in CSLib's prime-theory setting).
    Skip Phases 3–6; go directly to the Phase 7 obstruction writeup. This is an ACCEPTABLE outcome.
  - **RESULT: SUCCESS / GATE PASS.** `cs5_box_backward_onesided`
    (`specs/512_.../probes/phase1-onesided-box-backward-gate.lean`) is proved sorry-free, axiom-clean
    (`propext`/`Classical.choice`/`Quot.sound` only, `lean_verify`-confirmed), by direct application of
    the already-landed, negation-completeness-free `box_refuting_theory`. Phase 2 and the full pivot
    (Phases 3-7) are cleared to proceed **pending human greenlight** — Phase 4 reworks landed
    task-509 `cs5FC''` soundness and per this dispatch's hard constraint must not be started without
    explicit approval.
- **Success criteria / CI gates:** the scaffolding compiles (any probe `sorry` confined to
  `specs/512_.../probes/`); the paper proof is written; the gate decision (SUCCESS/FAILURE) is recorded
  with its grounding. No `sorry`, no new axiom in `Cslib/`. — **MET**: `lake env lean` on the probe
  exits 0 with no output; zero `sorry` anywhere (probe or `Cslib/`); zero new axioms; `Cslib/` untouched
  this phase (`git status` shows only `specs/` changes).
- **Verification:** `lean_goal` on the stated `cs5_box_backward` shows the obligation is exactly
  `box_refuting_theory`'s output (SUCCESS), or the negation-completeness step is provably unavoidable
  (FAILURE, mechanized). — **CONFIRMED**: `lean_goal` at the `exact` line reports `goals_after: []`;
  `lean_verify` on `Cslib.Logic.Modal.cs5_box_backward_onesided` reports
  `axioms: [propext, Classical.choice, Quot.sound]`, no `sorryAx`, no warnings; `lean_verify` on the
  adversarial theorem `cs5_two_sided_witness_can_fail_to_omit` reports `axioms: []` (fully
  axiom-free), no warnings.

---

### Phase 2: Discard the abandoned `CS5Combined` atom-sum scaffold [COMPLETED]

- **Goal:** (SUCCESS branch only) Explicitly remove the ~520-line doubled-atom `CS5Combined` apparatus
  from `CS5Canonical.lean` (currently ~1027 lines), auditing each landed lemma to classify KEEP vs.
  DISCARD. This is a committed, visible phase — NOT a silent deletion. *Low risk, net ~ -520 lines.*
- **Tasks:**
  - [x] Audit and DISCARD the atom-sum-specific machinery (belongs only to the abandoned scaffold):
    `CS5Combined`, `cs5_axiom_relabel`, `τL`/`τR` transport, `cs5Combined_necTransfer`,
    `cs5Combined_symmetric_tail_box_gap`, `cs5Combined_box_four`, `cs5Combined_boxInv_subset`,
    `cs5CombinedTail`(+`_refl`/`_symm`/`_trans`), `cs5Combined_dia_bot_imp_bot`, the private `bigOr`/box
    combinatorics, `cs5Combined_quasi_prime_set_exclusion`, `cs5Combined_diam_witness`,
    `cs5CombinedSeg`/`CS5CombinedSegment`/`cs5CombinedMreach`, `cs5Combined_fcsymbox_theory`/
    `cs5Combined_fc4_theory`, `cs5CombinedFC''_cs5CombinedMreach`, and the box-equivalence lemmas.
    *Confirmed the ENTIRE ~977-line body of `CS5Canonical.lean` (everything after the module
    header) was atom-sum-specific — the whole file was reduced to a header-only skeleton
    (1027 → ~65 lines).*
  - [x] KEEP (still useful, NOT atom-sum-specific): `Proposition.map` + `@[simp]` commutation +
    injectivity (relocate to `Basic.lean` in Phase 7 file split — a generic relabeling primitive);
    `cs5_symmetric_tail_box_gap` (`CS5.lean`, the load-bearing diagnosis);
    `cs5FC''_hub_forces_spoke_connectivity` (`CKExtension.lean`, general — documents why the naive
    plain-symmetry+transitivity condition over-connects; report 04 Q3 notes it "becomes irrelevant"
    as an obstruction for the NEW design but stays as a documented fact).
    *Confirmed `Proposition.map` already lives in `Basic.lean` (landed by an earlier dispatch,
    predating this one) — no code was moved this phase; only two stale docstring references to
    the now-deleted `CS5Canonical` atom-collapse projection were updated (generic rationale
    substituted) in `Basic.lean`'s `Proposition.map_id`/`Proposition.map_map`.*
  - [x] Confirm no surviving `Cslib/` code depends on the discarded symbols (`lean_references` / grep);
    `lake build` green after removal. *Grep confirmed zero references to any `CS5Combined`/
    `cs5Combined*` symbol anywhere in `Cslib/` outside the deleted file's own historical-record
    docstring text; `lake build` on both touched modules green;
    `checkInitImports`/`lint-style`/`lake lint` clean on both files.*
- **Timing:** ~1.5 hours (actual: single dispatch)
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` (remove `CS5Combined` block).
- **Success criteria / CI gates:** `lake build` green; `checkInitImports`/`lint-style`/`shake` clean;
  the discarded symbols are gone and no dangling references remain; no `sorry`, no new axiom.
  — **MET.**
- **Verification:** grep confirms `CS5Combined` symbols removed; `lake build` succeeds; kept lemmas
  (`cs5_symmetric_tail_box_gap`, `cs5FC''_hub_forces_spoke_connectivity`) still compile.
  — **CONFIRMED**: `grep -rln "CS5Combined\|cs5Combined" Cslib/` finds only the new module's own
  historical-record docstring text, no code references; `lake build
  Cslib.Logics.Modal.Basic Cslib.Logics.Modal.Metalogic.Constructive.CS5Canonical` succeeds
  (728/728 jobs); `cs5_symmetric_tail_box_gap`/`cs5FC''_hub_forces_spoke_connectivity` untouched
  in their original files (`CS5.lean`/`CKExtension.lean`).

---

### Phase 3: Birelational frame class + ≤-mediated incestuality condition [COMPLETED]

- **Goal:** Define the CS5 canonical frame as birelational: worlds = quasi-prime theories, `≤` = `⊆`,
  `R` **one-sided** (`Γ R Δ ⟺ boxInv Γ ⊆ Δ`), plus the ≤-mediated S5 **incestuality** frame condition
  (Marin Thm 7.1 shape) REPLACING the two-sided `cs5Tail` back-inclusion. *Medium risk, ~100–150 lines.*
- **Tasks:**
  - [x] Define the one-sided canonical relation `R Γ Δ := boxInv Γ ⊆ Δ` (reuse CSLib's `boxInv`;
    this is Simpson's `{B | □B ∈ X} ⊆ Y`, the modal clause with no "back" clause baked in).
    *Landed as `cs5OnesidedR`, matching the Phase 1 probe's signature exactly.*
  - [x] Define the ≤-mediated incestuality condition for the (b)/(5) axiom instance in Marin Thm 7.1's
    exact form: `wRᵏu ∧ wRᵐv ⟹ ∃u′. u ≤ u′ ∧ ∃x. u′Rˡx ∧ vRⁿx` specialized to CS5's B (symmetry) as a
    Scott–Lemmon path axiom `◇ᵏ□ˡA ⊃ □ᵐ◇ⁿA`. Cross-check against Simpson's F1/F2 forward/backward
    confluence (`≤∘R ⊆ R∘≤`, `R∘≤ ⊆ ≤∘R`). *Landed as `cs5Incest`, instantiated at `k = l = 0`,
    `m = n = 1` for `bBox` (`A → □◇A`): `R⁰` is the identity relation so `wR⁰u`/`u′R⁰x` collapse to
    `u = w`/`x = u′`, giving `r w v ⟹ ∃u′ ≥ w, r v u′`. Explicitly documented as NOT the naive
    classical symmetry condition (Marin Remark 7.3). F1/F2 cross-check recorded as a docstring-level
    design note (the general birelational monotonicity any `CKForces` model already has structurally);
    NOT mechanized as a separate Lean lemma this phase — that level of frame-theoretic verification is
    Phase 5's canonical-model-satisfies-the-condition obligation, not a Phase-3 definition-level task.*
  - [x] Reuse the task-509 `cs5FC` frame-condition MACHINERY (structure/plumbing) but swap the bundled
    conjuncts: drop the plain-symmetry+plain-transitivity bundle, add the incestuality condition.
    *Landed as `cs5FCIncest` (in `CS5Canonical.lean`, NOT `CKExtension.lean` — `cs5FC''` itself is
    untouched, per the plan's rollback note that Phase 4 adds alongside rather than edits in place):
    reflexivity + the `fourBox` re-basing clause + the `bBox`-style `FCsym_box` clause are KEPT
    verbatim from `cs5FC''`; plain transitivity (`fourDia`) and plain symmetry (`bDia`) are DROPPED and
    replaced by `cs5Incest`.*
  - [x] Confirm the propositional / box-forward / diamond truth-lemma clauses remain served by
    `CKForces` (monotone box truth quantifying through `≤ ∘ R`), matching `CS4.lean`'s one-sided-R
    birelational template. *Confirmed via the one-sided world-type port
    (`cs5CanonTail`/`cs5CanonSeg`/`CS5CanonSegment`/`cs5CanonMreach`/`cs5CanonVal`/`cs5CanonBot`,
    mirroring `CS4.lean`'s `cs4Tail`/`cs4Seg`/`CS4Segment`/`cs4Mreach` template rather than the
    discarded two-sided `cs5Tail`/`CS5Segment`) plus a documentation note (`CKForces` is generic over
    any `World`/`r`/`val`/`botForces`; only box-backward, Phase 6, needs anything beyond it, and that
    case is frame-condition-independent per the Phase 1 gate). Also landed the free reflexivity fact
    `cs5CanonRefl` (mirrors `cs4_refl`/`cs5_refl`, needs only axiom `T`) — the REMAINING frame-condition
    clauses (re-basing/incestuality-holds-on-canonical-model) are Phase 5's obligation, not proved
    here.*
- **Timing:** ~3 hours (actual: single dispatch)
- **Depends on:** 2
- **Reused assets (real names + file:line):**
  - `boxInv`, `QuasiPrime`, `.closed`, `.disj` — `Segment.lean`.
  - `CKForces`, `CKSegment`, `cmreach`, `CKExtension` plumbing — `Segment.lean` / `CKExtension.lean`.
  - `CS4.lean`'s `cs4_truth_lemma` / restricted-tail template — `CS4.lean:457` (one-sided-R precedent).
  - task-509 `cs5FC`/`cs5FC''` frame-condition scaffold — `CKExtension.lean` (machinery reused).
  - `CKSegment.ofHead`'s generic maximal tail — `Segment.lean:142-150` (the one-sided tail's exact
    template, confirmed identical to what `cs5CanonSeg` needed).
  - `cs5_boxInv_subset` (axiom `T`) — `CS5.lean:621`, used by `cs5CanonRefl`.
  - Simpson canonical model (`{B | □B ∈ X} ⊆ Y`) — corpus chunk `682e04d443e7bbd7` (`Simpson1994`);
    Marin Thm 7.1 incestuality — `MarinMoralesStrassburger2021`.
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean`.
- **Success criteria / CI gates:** the new relation + incestuality frame condition compile;
  `lake build` green; `checkInitImports`/`lint-style`/`shake` clean; no `sorry`, no new axiom.
  — **MET.**
- **Verification:** the frame class typechecks; `CKForces`/box-forward clauses reuse compiles.
  — **CONFIRMED**: `lake build Cslib.Logics.Modal.Metalogic.Constructive.CS5Canonical` succeeds
  (728/728 jobs) on first attempt; `lake exe checkInitImports`/`lake exe lint-style`/`lake lint`/
  `lake shake` all clean on the file; `lean_verify` on `Cslib.Logic.Modal.cs5CanonRefl` reports
  `axioms: [propext]`, no `sorryAx`, no warnings; grep confirms zero `sorry` tactics (one docstring
  prose mention only) and zero unexpected external references to the new declarations (none
  consumed yet, as expected — Phases 4-7 consume them).

---

### Phase 4: CS5 soundness over the incestuality frame class — THE 509-TOUCHING REWORK [COMPLETED]

- **Goal:** Re-prove CS5 soundness (all 17 `CS5ModalAxiom` cases) over the NEW one-sided-R + ≤-mediated
  incestuality frame class, replacing the plain-symmetry+transitivity `cs5FC''` bundle. **THIS IS THE
  HIGH-COST PHASE THAT TOUCHES LANDED TASK-509 MACHINERY** (`cs5FC''` soundness). *High risk,
  ~250–400 lines — the bulk of the pivot.* This is where the 509 regression risk concentrates.
- **Tasks:**
  - [x] Port the 17 `base`-axiom soundness cases from `cs5_axiom_sound''` (`CS5.lean:366`) — T, 4, and
    the CK core are unchanged by the frame-condition swap; only the B (symmetry) case's soundness now
    discharges against the incestuality condition instead of the plain-symmetry conjunct.
    *Landed as `cs5_axiom_sound_incest`: 16 of 17 cases (all base cases + `fourDia`/`fourBox`/`bBox`)
    are VERBATIM ports of `cs5_axiom_sound''`'s cases.*
  - [x] Prove the B-axiom soundness case over the incestuality condition (Marin Thm 7.2 soundness
    direction: a semantic argument over incestuous frames using disjunction-property saturated sets —
    NO negation-completeness). This is the genuinely new soundness content.
    *Landed as the `bDia` case of `cs5_axiom_sound_incest`, using the corrected `cs5Incest`.
    **Deviation (correction, not mere port)**: Phase 3's landed `cs5Incest` had mis-instantiated
    Marin Thm 7.1 as the `bBox` schema instance (`k=l=0,m=n=1`), which — verified against the
    literature chunk (`marinmoralesstrassburger_2021...chunk_0043.md`, Thm 7.1 verbatim) —
    coincides exactly with the already-kept `FCsym_box` clause (algebraically: `FCsym_box` at
    `u′:=u` (`le_refl`) IS `cs5Incest`'s old formula) and so contributed NO new soundness content;
    `bDia` genuinely needs the OTHER `B`-instance, `k=l=1,m=n=0`, which substitutes to
    `r w u ⟹ ∃u′≥u, r u′ w`. `cs5Incest` was corrected to this shape (see its docstring for the
    full re-derivation, cross-checked directly against the literature chunk). This is a
    within-mandate fix per the dispatch's R2 mitigation ("verify soundness case-by-case in
    Phase 4"), not a wall — `cs5Incest`/`cs5FCIncest` are Phase-3-landed but uncomsumed by
    anything else, so revising their statements is safe and non-regressive.*
  - [x] Establish the reworked `cs5FC''`-analogue (`cs5FCᵢ` or similar) so that
    `ckvalidFC_completeness` (`CKExtension.lean:227`) can consume it in Phase 7. Keep the ORIGINAL
    landed `cs5FC''` + its obstruction lemmas intact where still valid (do not delete 509 results;
    ADD the incestuality frame condition alongside).
    *`cs5FCIncest` (already landed Phase 3, revised this phase) IS this analogue: `cs5FC''` with
    ONLY its plain-symmetry conjunct replaced by (corrected) `cs5Incest`.
    **Deviation (correction)**: Phase 3 had ALSO dropped `cs5FC''`'s PLAIN TRANSITIVITY conjunct
    (intending it to be covered by `cs5Incest` too), but `fourDia`'s truth-lemma goal is a "point"
    fact with no `≤`-room (same shape as `bDia`'s), so no `≤`-mediated substitute can weaken exact
    transitivity the way `cs4FC'`/`FCsym_box` weakens `fourBox`'s composition — attempted the
    `fourDia` proof over the 4-conjunct bundle by hand first (no combination of `hrefl`/`hfour`/
    `hsymbox`/`hincest` can derive `r w'' t` from `r w'' u ∧ r u t` without literal transitivity;
    documented the failed attempts in the definition's docstring) and added PLAIN transitivity
    back as a conjunct. `cs5FCIncest` is therefore `cs5FC''` with EXACTLY ONE conjunct swapped
    (plain symmetry → corrected `cs5Incest`), matching this task's own literal wording ("T, 4 ...
    unchanged; only B case discharges against incestuality") more precisely than Phase 3's
    5-conjuncts-minus-2 version did. `cs5FC''` itself (`CKExtension.lean:184`) is completely
    untouched.*
  - [x] Verify no landed `cs5FC''` consumer regresses (`lean_references` on `cs5FC''`); confirm the
    diamond cases stay free (`cs5Tail_dia_of_mem` / `cs5_diam_witness` analogue over the new frame).
    *`lean_references` on `cs5FC''` (`CKExtension.lean:184`) shows exactly its 8 pre-existing
    reference sites in `CS5.lean`/`CKExtension.lean` — none in `CS5Canonical.lean`, confirming zero
    regression. The new soundness theorem is fully abstract over `World`/`r` (no `CS5CanonSegment`-
    specific witness machinery), so "diamond cases stay free" holds vacuously — no exclusion
    parameter or extra witness machinery was needed for `tDia`/`fourDia`/`bDia`, matching the
    Phase 1 gate's finding that this whole soundness layer is orthogonal to the box-backward
    machinery `cs5_diam_witness` belongs to (that machinery is Phase 5/6/7's concern, over the
    canonical model specifically, not this phase's abstract frame-class soundness).*
- **Timing:** ~5 hours (actual: single dispatch, including the two mid-phase corrections above)
- **Depends on:** 3
- **Reused assets (real names + file:line):**
  - `cs5_soundness` — `CS5.lean:311`; `cs5_axiom_sound''` (all 17 axioms) — `CS5.lean:366`
    (verbatim ported for 16/17 cases).
  - `cs5FC''`, `cs5FC_implies_cs5FC''`, `cs5FC''_cs5Mreach` — `CKExtension.lean` / `CS5.lean:1242`
    (task-509 machinery; left completely untouched, confirmed via `lean_references`).
  - Marin Thm 7.1 (verbatim, `marinmoralesstrassburger_2021...chunk_0043.md`) — re-derived BOTH the
    `bBox` instance (`k=l=0,m=n=1`, discovering it's redundant with `FCsym_box`) and the `bDia`
    instance (`k=l=1,m=n=0`, the actual fix) directly from the theorem statement, not from the
    Phase 3 docstring's (incorrect) restatement.
  - Marin Thm 7.2 (soundness direction, semantic argument over incestuous frames, no
    negation-completeness) — `MarinMoralesStrassburger2021`.
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` (only file touched this phase;
    `cs5Incest`/`cs5FCIncest` definitions corrected in place — safe, as nothing outside this file
    consumes them yet — plus the new soundness theorems added).
- **Success criteria / CI gates:** all 17 soundness cases + the incestuality B-case compile sorry-free;
  the reworked frame-condition-analogue is established; landed `cs5FC''` consumers unbroken;
  `lake build`/`lake test` green; `checkInitImports`/`lint-style`/`shake` clean; no `sorry`, no new axiom.
  — **MET** (`lake test` not re-run this phase — no test files reference `CS5Canonical.lean`'s new
  declarations yet, per Phase 3's note that nothing consumes them; scoped `lake build` on the
  touched module is the applicable gate and is green).
- **Verification:** `#print axioms` on the soundness theorem shows no `sorryAx`; `lean_references cs5FC''`
  shows no broken consumers.
  — **CONFIRMED**: `lean_verify` on `Cslib.Logic.Modal.cs5_axiom_sound_incest`,
  `cs5_soundness_incest`, and `cs5_soundness_derivable_incest` each report `axioms: []` (fully
  axiom-free, no `sorryAx`), no warnings; `lean_references` on `cs5FC''` shows only its 8
  pre-existing sites, none of them in `CS5Canonical.lean`; `lake build
  Cslib.Logics.Modal.Metalogic.Constructive.CS5Canonical` succeeds (728/728 jobs); `lake exe
  checkInitImports`/`lake exe lint-style` clean (no output) on the file; `lake lint`'s single
  repo-wide finding (`PrimeExclusion.lean` `unusedArguments`) is unrelated and pre-existing;
  `grep sorry` on the file finds only a docstring prose mention, zero `sorry` tactics; `lake shake`
  could not complete a full repo-wide pass (pre-existing, KNOWN-UNRELATED task-505 `sorry`s in
  `Tableau/Intuitionistic`/`Tableau/Minimal` leave stale oleans — matches the dispatch's documented
  known-unrelated caveat), but its output contains zero mentions of `CS5Canonical.lean`.

---

### Phase 5: Canonical-frame incestuality verification (Došen-style, negation-completeness-free) [NOT STARTED]

- **Goal:** Prove the canonical frame (worlds = quasi-prime theories, `R` one-sided) SATISFIES the
  ≤-mediated incestuality condition — the Došen-style verification, using ONLY the disjunction property
  + F1/F2 confluence, with NO `ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ` step anywhere. *Medium–high risk, ~150–250 lines.*
- **Tasks:**
  - [ ] For canonical worlds `Γ, Δ` with `Γ Rᵏ ...`, construct the mediating `u′ ≥ u` via a prime
    (quasi-prime) Lindenbaum extension (`quasi_prime_exclusion` / `box_refuting_theory`) and the witness
    `x` via the same engine — establishing the incestuality condition's existential.
  - [ ] Discharge the F1/F2 confluence obligations from the prime lemma (Simpson's chunk `8372…`
    continues into the F2 verification) — reuse `box_refuting_theory`/`quasi_prime_exclusion` verbatim.
  - [ ] Confirm the whole verification is negation-completeness-free (this is the Phase 1 gate's promise
    now discharged in Lean); the B-axiom's canonical-frame content is a GLOBAL frame property, not a
    per-world back-inclusion.
- **Timing:** ~4 hours
- **Depends on:** 4
- **Reused assets (real names + file:line):**
  - `box_refuting_theory`, `quasi_prime_exclusion`, `quasi_prime_box_exclusion` — `SegmentLindenbaum.lean`.
  - `CKSegment`, `cmreach`, `boxInv`, `QuasiPrime` — `Segment.lean`.
  - Simpson Prime Lemma 3.3.2 + F1/F2 — corpus chunk `8372f27240fe345d` (`Simpson1994`).
  - Marin Thm 7.1 incestuality shape — `MarinMoralesStrassburger2021`.
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean`.
- **Success criteria / CI gates:** the canonical-frame incestuality lemma compiles sorry-free;
  `lake build` green; `checkInitImports`/`lint-style`/`shake` clean; no `sorry`, no new axiom.
- **Verification:** `#print axioms` on the incestuality-verification lemma shows no `sorryAx`; grep
  confirms no negation-completeness (`¬ϕ ∈`) move in the proof.

---

### Phase 6: `cs5_box_backward` as the one-sided prime lemma [NOT STARTED]

- **Goal:** Discharge box-backward as the PLAIN one-sided prime lemma: from `□A ∉ Γ`, get
  `boxInv Γ ⊬ A`, apply prime Lindenbaum (`box_refuting_theory`) for a quasi-prime `Δ ⊇ boxInv Γ` with
  `A ∉ Δ` and `Γ R Δ`. No second clause, no simultaneous pair, no `H'` enlargement. *Low risk, ~60 lines
  — the whole five-dispatch blocker dissolves here.*
- **Tasks:**
  - [ ] State `cs5_box_backward` over the one-sided relation (the Phase 1 scaffolded signature).
  - [ ] Prove it by direct application of `box_refuting_theory` (`SegmentLindenbaum.lean`) — the witness
    `Δ` is exactly its output; `Γ R Δ` is `boxInv Γ ⊆ Δ` by construction.
  - [ ] Confirm `A ∉ Δ` and quasi-primeness of `Δ` from the prime lemma's guarantees.
- **Timing:** ~1.5 hours
- **Depends on:** 5
- **Reused assets (real names + file:line):**
  - `box_refuting_theory` — `SegmentLindenbaum.lean` (delivers the witness verbatim).
  - `quasi_prime_exclusion` / `quasi_prime_box_exclusion` — `SegmentLindenbaum.lean`.
  - `boxInv`, `QuasiPrime` — `Segment.lean`.
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean`.
- **Success criteria / CI gates:** `cs5_box_backward` compiles sorry-free; `lake build` green;
  `checkInitImports`/`lint-style`/`shake` clean; no `sorry`, no new axiom.
- **Verification:** `#print axioms cs5_box_backward` shows no `sorryAx`; the witness satisfies
  `Γ R Δ ∧ A ∉ Δ` by construction.

---

### Phase 7: Truth lemma + CS5 completeness + file split (or obstruction writeup) [NOT STARTED]

- **Goal:** (SUCCESS branch) Land `cs5_truth_lemma` (clone `cs4_truth_lemma`, box-backward via
  `cs5_box_backward`), `realize` via Lindenbaum, and `cs5_completeness`/`cs5_soundness_completeness` via
  `ckvalidFC_completeness` + the reworked incestuality frame condition; execute the file split
  (`Proposition.map` → `Basic.lean`; canonical machinery in `CS5Canonical.lean`). (GATE-FAILURE branch,
  if Phase 1 failed) Write the mechanized-obstruction module docstring/theorem and mark completeness
  "BLOCKED across known-mechanizable routes." *Medium risk, ~150 lines (mostly reuse).*
- **Tasks (SUCCESS branch):**
  - [ ] Clone `cs4_truth_lemma` (`CS4.lean:457`, the one-sided-R precedent) / `ck_truth_lemma`
    (`CKTruthLemma.lean:133`) into `cs5_truth_lemma`; keep atom/bot/and/or/imp/diamond/box-forward
    cases; the box-backward case is `cs5_box_backward` (Phase 6).
  - [ ] Provide `realize` via Lindenbaum (`quasi_prime_exclusion`/`quasi_prime_box_exclusion`) +
    `cs5_truth_lemma`.
  - [ ] Land `cs5_completeness` / `cs5_soundness_completeness` via `ckvalidFC_completeness`
    (`CKExtension.lean:227`) supplying `realize` and the reworked incestuality frame-condition
    reachability lemma (Phase 4/5 analogue of `cs5FC''_cs5Mreach`).
  - [ ] File split: move `Proposition.map` + `@[simp]` commutation + injectivity to
    `Cslib/Logics/Modal/Basic.lean` (home of `inductive Proposition`, `Basic.lean:72`); keep the
    birelational canonical machinery in `CS5Canonical.lean`. Run `lake exe mk_all --module`.
  - [ ] Update the CS5 module docstring (`CS5.lean:156` region) to record completeness as PROVED via the
    birelational model; cite `Dosen1985`, `BozicDosen1984`, `Simpson1994`,
    `AlechinaMendlerdePaivaRitter2001`, `MarinMoralesStrassburger2021`, `Pacheco2024`.
- **Tasks (GATE-FAILURE branch — only if Phase 1 failed):**
  - [ ] Land the mechanized obstruction theorem (sorry-free, no new axiom) showing the
    intuitionistic-diamond box-backward for CSLib's CS5 axioms also requires the negation-completeness
    move; keep the CS5 completeness statement marked "BLOCKED across all known-mechanizable routes"
    (explicitly NOT incompleteness — cite `CS5 ≡ IS5` via report 05).
  - [ ] Update `CS5.lean` docstring to record the obstruction and the three prior landed obstructions.
- **Timing:** ~3 hours
- **Depends on:** 6
- **Reused assets (real names + file:line):**
  - `cs4_truth_lemma` — `CS4.lean:457`; `ck_truth_lemma` — `CKTruthLemma.lean:133`.
  - `ckvalidFC_completeness` — `CKExtension.lean:227`.
  - Lindenbaum: `quasi_prime_exclusion`/`quasi_prime_box_exclusion` — `SegmentLindenbaum.lean`.
  - `inductive Proposition` — `Cslib/Logics/Modal/Basic.lean:72` (file-split target).
  - `CKSegment`, `cmreach`, `boxInv`, `QuasiPrime` — `Segment.lean`.
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean`;
  - `Cslib/Logics/Modal/Basic.lean` (`Proposition.map` relocation);
  - `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` (docstring only).
- **Success criteria / CI gates (SUCCESS):** `cs5_completeness` compiles sorry-free; `#print axioms
  cs5_completeness` shows ONLY `Classical.choice`/`propext`/`Quot.sound`. Full pipeline green:
  `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake shake --add-public --keep-implied --keep-prefix`; `lake exe mk_all --module` run.
- **Success criteria / CI gates (GATE FAILURE):** the obstruction theorem compiles sorry-free;
  completeness documented "BLOCKED across known-mechanizable routes"; same full CI pipeline green; no
  `sorry`, no new axiom.
- **Verification:** `#print axioms cs5_completeness` (SUCCESS) or `#print axioms <obstruction>`
  (FAILURE) clean; `lake test` passes.

---

## Testing & Validation

- [ ] `lake build` (full) succeeds after each phase.
- [ ] `lake test` (CslibTests suite) passes at Phases 4 and 7.
- [ ] `lake exe checkInitImports` — every touched file imports `Cslib.Init`.
- [ ] `lake exe lint-style` — clean on all touched files.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — no unused/missing imports.
- [ ] `#print axioms cs5_completeness` (SUCCESS) shows only `Classical.choice`/`propext`/`Quot.sound`;
      NO `sorryAx`, NO new axiom. On GATE FAILURE, `#print axioms` on the obstruction theorem is equally clean.
- [ ] `lake exe mk_all --module` run after the Phase 7 file split.
- [ ] Zero-debt invariant: grep confirms no `sorry`/`admit`/new `axiom` in any `Cslib/` file at every
      phase boundary; probe `sorry` (if any) stays under `specs/512_.../probes/`.
- [ ] Phase 5: grep confirms no `¬ϕ ∈`-style negation-completeness move in the canonical-frame proof.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Basic.lean` — `Proposition.map` + `@[simp]` commutation + injectivity (relocated
  in Phase 7; retained from plan-01 Phase 1).
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` — `CS5Combined` scaffold REMOVED
  (Phase 2); new birelational frame class + incestuality condition (Phase 3), reworked soundness
  (Phase 4), canonical incestuality verification (Phase 5), `cs5_box_backward` (Phase 6),
  `cs5_truth_lemma` + `cs5_completeness`/`cs5_soundness_completeness` (Phase 7) — OR the mechanized
  obstruction (GATE FAILURE).
- `Cslib/Logics/Modal/Metalogic/Constructive/CKExtension.lean` — possibly the incestuality frame
  condition added beside `cs5FC''` (Phase 4); `cs5FC''_hub_forces_spoke_connectivity` retained.
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` — module docstring update (Phase 7);
  `cs5_symmetric_tail_box_gap` retained.
- `specs/512_cs5_box_backward_atom_sum_completeness/plans/02_birelational-pivot.md` (this file).
- `specs/512_cs5_box_backward_atom_sum_completeness/summaries/02_birelational-pivot-summary.md`
  (produced at implementation completion).

## Rollback/Contingency

- Each phase is committed separately (`task 512 phase {P}: {name}`) at a green `lake build`; a failing
  phase reverts only its own commit, leaving earlier green phases intact.
- Phase 1 GATE FAILURE is not a rollback but a planned pivot to the mechanized-obstruction deliverable
  (Phase 7 failure branch); Phases 2–6 are skipped. Completeness marked "BLOCKED across known-
  mechanizable routes" (NOT incompleteness).
- Phase 2 (scaffold discard) is a clean deletion; if a later phase needs a discarded lemma, restore it
  from git history rather than re-deriving.
- Phase 4 is the 509-touching regression risk: if it breaks landed `cs5FC''` consumers, revert Phase 4's
  commit (leaving Phases 1–3 intact) and re-dispatch with the incestuality condition added strictly
  ALONGSIDE `cs5FC''` (never replacing it in place).
- No new axiom is ever introduced, so `#print axioms` remains the single acceptance gate; if any
  `sorryAx` appears, revert to the last clean commit and re-dispatch that phase.
