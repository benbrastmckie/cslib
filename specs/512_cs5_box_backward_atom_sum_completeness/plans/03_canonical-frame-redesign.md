# Implementation Plan: Task #512 — CS5 Completeness via Birelational Canonical Model (Frame Redesign)

- **Task**: 512 - cs5_box_backward_atom_sum_completeness
- **Status**: [IN PROGRESS] (Phases 1-4 LANDED; Phase 5 BLOCKED negative-result; Phases 6-10 = the frame redesign, NOT STARTED)
- **Effort**: ~15 hours remaining (Phases 6-10 redesign); ~19 hours already invested in Phases 1-5
- **Dependencies**: 509 (soundness + mechanized obstruction, both branches landed; Phase 8 RE-CHECKS soundness alongside — never editing — `cs5FC''`)
- **Research Inputs**:
  - reports/06_incestuality-collapse-verdict.md (NEW this revision — the decision-settling verdict)
  - reports/05_collapse-s5-probe.md
  - reports/04_birelational-feasibility.md
  - reports/03_alternative-techniques.md
  - reports/01_box-backward-atom-sum.md (superseded architecture; reuse references preserved)
- **Artifacts**: plans/03_canonical-frame-redesign.md (this file); **supersedes** plans/02_birelational-pivot.md
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

**This plan supersedes `plans/02_birelational-pivot.md`. It does NOT change the strategic
architecture** — the birelational canonical model (Božić–Došen 1984 / Došen 1985 IS5 /
Simpson 1994 / Alechina–Mendler–de Paiva–Ritter 2001 / Marin–Morales–Straßburger 2021) remains the
route. What it fixes is a single, precisely diagnosed **canonical-frame bug** found by report 06
after plan 02's Phase 5 mechanized a collapse.

**The bug (report 06, verdict A).** Plan 02 Phase 3 defined the canonical relation *one-sided* —
`cs5OnesidedR Γ Δ := boxInv Γ ⊆ Δ` (`CS5Canonical.lean:128`) — and DROPPED Simpson's genuine
**diamond clause** `{◇A | A ∈ Δ} ⊆ Γ` (its diamond witness was hard-wired to the exploding world
`Ω = Set.univ`, `CS5Canonical.lean:161`). With no diamond information in `R`, Marin's `(1,1,0,0)`
`bDia`-incestuality witness `u′ ≥ u` sits on the `boxInv`-**domain** side, where `boxInv`-monotonicity
forces it to degenerate to plain symmetry — the collapse Phase 5 mechanized as
`cs5Incest_cs5CanonMreach_false` (`CS5Canonical.lean:~465`, verified a real declaration). Report 06
proves this collapse is a property of the *degenerate one-sided frame* (box-only `R` + retained `Ω`),
**not** of Marin's condition: `cs5Incest` (`CS5Canonical.lean:234`) is a **faithful** transcription of
Marin Thm 7.1's `(1,1,0,0)` instance and is **verified on the standard IS5 canonical model** (Simpson
§3.3, Marin Thm 7.2, Došen 1985) via the **prime lemma over a two-sided R carrying the diamond clause**.
The `(0,0,1,1)` sibling does NOT collapse under the same monotonicity, and Marin's own Thm 7.2
canonical model satisfies the identical `(1,1,0,0)` condition — so option (B) (structural wall) is
refuted. `report 05`'s settled `CS5 ≡ IS5` + Alechina's redundancy remark license excluding `Ω`.

**The redesign (four moves, from report 06 §4).**
1. **Restore Simpson's genuine two-sided R**: `Γ R Δ ⟺ (boxInv Γ ⊆ Δ) ∧ ({◇A | A ∈ Δ} ⊆ Γ)` — the
   box-inverse *forward* clause AND the diamond *backward* clause. **The diamond clause is verified via
   the PRIME LEMMA / disjunction property (`dia_refuting_theory`, `quasi_prime_exclusion`), NOT
   negation-completeness** — so it is NOT the old `cs5Tail` symmetry wall. This distinction is the whole
   point of the redesign.
2. **Exclude the degenerate exploding world `Ω` (head `= univ`)** via a hereditary invariant on the
   canonical world type, following CS4's `excl`/`excl_head`/`CS4Segment` precedent (task 508). The
   ◇-exclusion propagates through the entire reachability.
3. **Verify the UNCHANGED `cs5Incest` on the redesigned frame via the DIAMOND side** — construct the
   `(1,1,0,0)` mediating witness using `dia_refuting_theory` (the ◇-refuting world), exactly as CS4
   verifies `cs4FC'_cs4Mreach` via the ◇ side rather than the □ side. **This is the crux of the redesign
   and where the ~85% confidence / ~15% residual lives** — it is the go/no-go gate (Phase 7).
4. **Re-check CS5 soundness over the two-sided frame class** — adapt Phase 4's `cs5_axiom_sound_incest`:
   the `bDia` case now discharges against the two-sided R + `cs5Incest`; confirm it still holds,
   axiom-free.

Then box-backward (the one-sided box-inverse clause of the two-sided R still gives it via
`box_refuting_theory`), truth lemma, `cs5_completeness`, file split.

**Definition of done**: either (SUCCESS) `cs5_completeness` / `cs5_soundness_completeness` lands
sorry-free with `#print axioms` showing only `Classical.choice`/`propext`/`Quot.sound`; or (GATE
FAILURE at Phase 7) `cs5Incest` is shown to fail *even on the redesigned two-sided frame* via a
mechanized obstruction — i.e. option (B) was real after all — completeness marked "BLOCKED across all
known-mechanizable routes" (NOT incompleteness: `CS5 ≡ IS5` is complete), and the result is escalated
to a human (do NOT force, no `sorry`). NO `sorry` and NO new `axiom` under `Cslib/` at ANY phase
boundary (zero-debt invariant); probe `sorry` confined to `specs/512_.../probes/`.

### Research Integration

Newly integrated this revision (v3):

- **reports/06_incestuality-collapse-verdict.md** (the decision-settling verdict): the Phase-5 collapse
  is **(A) a canonical-frame artifact**, not a structural wall. `cs5Incest` is faithful to Marin Thm 7.1;
  the artifact is Phase 3's one-sided R (diamond clause stripped) + retained exploding `Ω`. Refutes (B)
  via the monotonicity-friendly `(0,0,1,1)` sibling and Marin Thm 7.2's own two-sided-R prime model.
  Prescribes: restore the two-sided R, exclude `Ω` (CS4 `excl_head` precedent, licensed by settled
  `CS5 ≡ IS5` + Alechina redundancy), verify `cs5Incest` via the DIAMOND side (`dia_refuting_theory`,
  analogous to CS4's `cs4FC'_cs4Mreach`). `next_action_hint = revise`; confidence ~85% (residual ~15% =
  soundness-rework over two-sided R — scoped, known work).

Carried from plan 02 (reports 03/04/05 integrated there): the birelational pivot design (report 04:
reuse map, ~5–6 phases / ~700–1100 net lines, box-backward diamond-independent), the settled
`CS5 ≡ IS5` collapse (report 05: `cs5_dia_or`/`cs5_dia_bot_imp_bot` landed axiom-free), and the
architectural verdict (report 03: Došen 1985 is the only positive route; §0 wall statement).

### BibKeys (verified present in `references.bib`)

`Dosen1985`, `BozicDosen1984`, `Ewald1986`, `AlechinaMendlerdePaivaRitter2001`,
`MarinMoralesStrassburger2021`, `Simpson1994`, `Pacheco2024`, `Wijesekera1990`,
`ArisakaDasStrassburger2015`. Cite `Simpson1994` (two-sided R), `MarinMoralesStrassburger2021`
(Thm 7.1/7.2 incestuality), `Dosen1985`/`AlechinaMendlerdePaivaRitter2001` (`Ω`-redundancy) in the
reworked module docstring.

### Relationship to plan 02 (what is preserved vs. superseded)

- **Phases 1, 2 [COMPLETED]** — preserved verbatim; fully done and unaffected by the redesign.
- **Phase 3 [COMPLETED, SUPERSEDED-IN-PART]** — the world-type plumbing
  (`cs5CanonSeg`/`CS5CanonSegment`/`cs5CanonMreach`/`cs5CanonVal`/`cs5CanonBot`/`cs5CanonRefl`) is a
  REUSABLE template; but its **one-sided `cs5OnesidedR` is superseded** by Phase 6's two-sided R, and its
  unrestricted world type is superseded by Phase 6's `Ω`-excluding type. `cs5Incest` (the *condition*)
  is faithful and UNCHANGED.
- **Phase 4 [COMPLETED, RE-CHECK REQUIRED]** — `cs5_axiom_sound_incest`/`cs5_soundness_incest`/
  `cs5_soundness_derivable_incest` are SOUND & axiom-free over `cs5FCIncest`, but they were proved over
  the *one-sided* R. Because the redesign moves R to Simpson two-sided, **Phase 8 re-checks / adapts this
  soundness over the two-sided frame class** (report 06's residual ~15%). `cs5Incest` itself does NOT
  change — only the frame/relation it is bundled with does.
- **Phase 5 [BLOCKED]** — retained as a **documented negative result about the OLD one-sided frame**. Its
  mechanized obstruction lemmas (`cs5CanonMreach_to_univ`, `cs5Incest_cs5CanonMreach_forces_univ`,
  `cs5_consistent_incest`, `cs5Incest_cs5CanonMreach_false`) stay in `CS5Canonical.lean` as a load-bearing
  account of WHY the one-sided frame fails; the redesign (Phases 6-10) replaces that frame. They are NOT
  deleted (they document the diagnosis) and NOT reworked.

## Goals & Non-Goals

**Goals**:
- Restore Simpson's genuine **two-sided** canonical relation: box-inverse forward clause
  `boxInv Γ ⊆ Δ` **and** diamond backward clause `{◇A | A ∈ Δ} ⊆ Γ`, built ALONGSIDE the existing
  one-sided `cs5OnesidedR` (which stays as the documented negative-result frame).
- Introduce a hereditary `Ω`-exclusion invariant on a new canonical world type (CS4 `excl_head`
  precedent), so the exploding `Set.univ` world is excluded from the subtype completeness is
  instantiated at.
- **Verify the UNCHANGED `cs5Incest` on the redesigned frame via the DIAMOND side** (the go/no-go gate),
  sourcing the `(1,1,0,0)` mediating witness from `dia_refuting_theory` — disjunction property only, no
  negation-completeness, no `boxInv`-monotonicity trap.
- Re-check / adapt CS5 soundness (all 17 `CS5ModalAxiom` cases) over the two-sided frame class; the
  `bDia` case discharges against two-sided R + `cs5Incest`, axiom-free.
- Prove `cs5_box_backward` as the plain one-sided prime lemma via `box_refuting_theory` (the two-sided
  R's box-inverse clause still supplies it — box-backward is frame-condition-independent, Phase 1 gate).
- Land `cs5_truth_lemma` + `cs5_completeness`/`cs5_soundness_completeness`, sorry-free, no new axiom;
  execute the file split (`Proposition.map` → `Basic.lean`).

**Non-Goals**:
- Do NOT touch task-509 `cs5FC''` (`CKExtension.lean:184`) — build the new two-sided frame ALONGSIDE.
- Do NOT rework Phase 4's landed `cs5Incest`/`cs5FCIncest` *statements* (the condition is faithful);
  Phase 8 re-verifies their *soundness* over the new frame, adding alongside as needed.
- Do NOT delete Phase 5's mechanized negative-result lemmas (they document the one-sided-frame diagnosis).
- Do NOT transcribe the naive classical symmetry condition `X R Y ⟹ Y R X` (Marin Remark 7.3: wrong
  intuitionistically) — the diamond clause is verified via the prime lemma, NOT per-world back-inclusion.
- Do NOT re-attempt plan 01's atom-sum route (report 05 refuted it) nor a Phase-5 in-flight retry.
- Do NOT introduce any `sorry` or new `axiom` into `Cslib/`; on gate FAILURE, escalate rather than force.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| R1 (LINCHPIN, ~15% residual): the diamond-side verification of `cs5Incest` on the redesigned frame does not close — `dia_refuting_theory` cannot produce the `(1,1,0,0)` witness `u′ ≥ u` with `u′ R w` even with the diamond clause + `Ω` excluded (i.e. (B) was real after all) | H | L–M | **Phase 7 is an EARLY GO/NO-GO GATE** with BOTH branches pre-specified, placed BEFORE the soundness re-check and completeness work. FAILURE → mechanized obstruction over the two-sided frame + "BLOCKED across known-mechanizable routes" + **escalate to human** (do NOT force, no `sorry`). Mirrors how plan 02's Phase 1 front-loaded its cheap gate before the ~250–400-line soundness rework. |
| R2: the two-sided R / diamond clause transcribed wrong relative to Simpson's `{◇A | A ∈ Δ} ⊆ Γ` | H | L | Transcribe Simpson's exact two clauses (corpus chunk `682e04d443e7bbd7`); cross-check the diamond clause direction against `cs5_boxInv_subset_iff` (`boxInv T ⊆ H ↔ T ⊆ diaInv H`, `CS5.lean:589`) and `diaInv` (`Segment.lean:106`); verify `bDia` soundness case-by-case in Phase 8. |
| R3: the `Ω`-exclusion hereditary invariant (CS4 `excl_head` port) does not propagate cleanly through two-sided reachability, or the closure lemma (analogue of `cs4_not_dia_dia`) fails over the two-sided R | M | M | Port `CS4Segment`'s `excl`/`excl_head` + `cs4_not_dia_dia` (`CS4.lean:317/373/379`) directly; the excluded object is `⊥`/`univ`-membership (prime *consistent* worlds), licensed by settled `CS5 ≡ IS5` (report 05) + Alechina redundancy so no completeness is lost. Phase 6 lands the definitions + closure lemma before Phase 7 depends on them. |
| R4: the soundness re-check (Phase 8) over the two-sided frame breaks a Phase-4 result or exceeds one agent run | M | L | Phase 8 adds the two-sided-frame soundness ALONGSIDE Phase 4's one-sided version (never edits it in place); 16/17 axiom cases are unchanged (T, 4, CK core, `fourBox`/`bBox`); only `bDia` re-discharges. `cs5FC''` (509) stays untouched — confirm via `lean_references`. |
| R5: box-backward regresses now that R has a second (diamond) clause | L | L | Box-backward uses ONLY the box-inverse clause (`boxInv Γ ⊆ Δ`) of the two-sided R; the diamond clause is irrelevant to it (Phase 1 gate: box-backward is frame-condition-independent). `box_refuting_theory` (`SegmentLindenbaum.lean:177`) delivers the witness verbatim. |
| R6: file-size / build-time — `CS5Canonical.lean` grows past ~2000 lines or slows builds | L | M | Split `Proposition.map` → `Basic.lean` in Phase 10; build incrementally per phase; `lake exe mk_all --module` after the split. Currently ~476 lines. |

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
| 8 | 8, 9 | 7 |
| 9 | 10 | 8, 9 |

Phases 1–5 are LANDED history (1,2 completed; 3 completed/superseded-in-part; 4 completed/re-check;
5 blocked negative-result). Phases 6–10 are the redesign. **Phase 7 is the redesign's go/no-go gate**:
its outcome (SUCCESS vs. mechanized obstruction) selects whether Phases 8–10 execute at all. Phases 8
(abstract frame-class soundness) and 9 (canonical box-backward) are independent given the gate passes
and can run in parallel. Each phase is sized to one agent run (~100–400 lines output).

---

### Phase 1: Q1 GO/NO-GO GATE — intuitionistic-diamond box-backward avoids negation-completeness [COMPLETED]

- **Goal:** CHEAPLY decide whether the Simpson/Došen intuitionistic-diamond box-backward avoids the
  negation-completeness move `ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ` for CSLib's ACTUAL `CS5ModalAxiom` set. *(Preserved from
  plan 02 — unchanged by the redesign; box-backward remains frame-condition-independent.)*
- **RESULT: SUCCESS / GATE PASS.** `cs5_box_backward_onesided`
  (`specs/512_.../probes/phase1-onesided-box-backward-gate.lean`) proved sorry-free, axiom-clean
  (`propext`/`Classical.choice`/`Quot.sound`), by direct application of the negation-completeness-free
  `box_refuting_theory`. Adversarial `cs5_two_sided_witness_can_fail_to_omit` (fully axiom-free)
  confirms the one-sided box clause never needs the classical move.
- **Depends on:** none
- **Reused assets:** `box_refuting_theory`, `quasi_prime_exclusion` — `SegmentLindenbaum.lean:177/73`;
  `cs5_symmetric_tail_box_gap` — `CS5.lean:712`; Simpson Prime Lemma 3.3.2 / Canonical Model Lemma 3.3.3
  (`Simpson1994`); Marin Thm 7.1/7.2 (`MarinMoralesStrassburger2021`).
- **Status note (v3):** Retained as-is. This gate's promise — box-backward reduces to the one-sided prime
  lemma with no negation-completeness — is what Phase 9 (box-backward over the two-sided R's box clause)
  cashes in.

---

### Phase 2: Discard the abandoned `CS5Combined` atom-sum scaffold [COMPLETED]

- **Goal:** Explicitly remove the ~977-line doubled-atom `CS5Combined` apparatus from `CS5Canonical.lean`,
  auditing each landed lemma KEEP vs. DISCARD. *(Preserved from plan 02 — unchanged.)*
- **RESULT: DONE.** The entire ~977-line atom-sum body was discarded (file reduced to a ~65-line
  header-only skeleton, since rebuilt by Phases 3–5). KEPT: `Proposition.map` (already in `Basic.lean`),
  `cs5_symmetric_tail_box_gap` (`CS5.lean`), `cs5FC''_hub_forces_spoke_connectivity` (`CKExtension.lean`).
  `lake build`/`checkInitImports`/`lint-style`/`shake` clean; zero surviving references to discarded
  symbols; no `sorry`, no new axiom.
- **Depends on:** 1
- **Status note (v3):** Retained as-is. General negative lemmas kept.

---

### Phase 3: One-sided birelational frame class + `cs5Incest` condition [COMPLETED, SUPERSEDED-IN-PART]

- **Goal (as executed):** Define the CS5 canonical frame birelational: worlds = quasi-prime theories,
  `≤` = `⊆`, `R` one-sided (`cs5OnesidedR Γ Δ ⟺ boxInv Γ ⊆ Δ`), plus the ≤-mediated `cs5Incest`
  condition (Marin Thm 7.1 shape).
- **RESULT: DONE (frame landed), but the frame is SUPERSEDED-IN-PART by the redesign.** Landed:
  `cs5OnesidedR` (`CS5Canonical.lean:128`), the world-type plumbing
  `cs5CanonTail`/`cs5CanonSeg`/`CS5CanonSegment`/`cs5CanonMreach`/`cs5CanonVal`/`cs5CanonBot`
  (`:147/:154/:166/:176/:195/:198`), the free reflexivity fact `cs5CanonRefl` (`:189`, axiom `T`), and
  `cs5Incest` (`:234`, later corrected in Phase 4 to the true `bDia` `(1,1,0,0)` instance) bundled into
  `cs5FCIncest` (`:255`).
- **What the redesign changes (see Phases 6–7):**
  - **SUPERSEDED:** `cs5OnesidedR` (one-sided, diamond clause dropped, diamond witness hard-wired to
    `Ω = Set.univ` at `:161`) → replaced by Phase 6's **two-sided** R. The unrestricted `CS5CanonSegment`
    (admits the exploding `Ω`) → replaced by Phase 6's `Ω`-excluding world type.
  - **REUSABLE TEMPLATE:** the `cs5CanonSeg`/`CS5CanonSegment`/`cs5CanonMreach`/`cs5CanonVal`/
    `cs5CanonBot`/`cs5CanonRefl` plumbing (mirrors `CS4.lean`'s `cs4Tail`/`cs4Seg`/`CS4Segment`/
    `cs4Mreach`) — Phase 6 clones it with the diamond clause + `excl_head`-style invariant added.
  - **UNCHANGED:** `cs5Incest` (the *condition*) is faithful to Marin Thm 7.1 (report 06); Phase 7
    re-verifies it on the new frame, Phase 8 re-checks its soundness contribution.
- **Depends on:** 2
- **Reused assets:** `boxInv`, `QuasiPrime`, `quasiPrime_univ` — `Segment.lean`; `CKForces`/`CKSegment`/
  `cmreach`/`CKExtension` — `Segment.lean`/`CKExtension.lean`; `cs4_truth_lemma` one-sided-R template —
  `CS4.lean:457`; `cs5_boxInv_subset` (axiom `T`) — `CS5.lean:621`; Simpson canonical model chunk
  `682e04d443e7bbd7`; Marin Thm 7.1 (`MarinMoralesStrassburger2021`).

---

### Phase 4: CS5 soundness over the one-sided incestuality frame class [COMPLETED, RE-CHECK REQUIRED]

- **Goal (as executed):** Re-prove CS5 soundness (all 17 `CS5ModalAxiom` cases) over the one-sided-R +
  `cs5Incest` frame class (`cs5FCIncest`).
- **RESULT: DONE & AXIOM-FREE (over the one-sided frame).** Landed `cs5_axiom_sound_incest`
  (`CS5Canonical.lean:278`), `cs5_soundness_incest`, `cs5_soundness_derivable_incest` (`:336`), each
  `axioms: []` (`lean_verify`). 16/17 cases are verbatim ports of `cs5_axiom_sound''` (`CS5.lean:366`);
  the `bDia` case discharges against the corrected `cs5Incest` (`(1,1,0,0)`, `r w u ⟹ ∃u′ ≥ u, r u′ w`).
  `cs5FC''` (`CKExtension.lean:184`) left completely untouched — `lean_references` shows its 8
  pre-existing sites, none in `CS5Canonical.lean`.
- **RE-CHECK REQUIRED (Phase 8):** this soundness was proved with `r` = the one-sided `cs5OnesidedR`-style
  abstract relation. `cs5_axiom_sound_incest` is abstract over `World`/`r` satisfying `cs5FCIncest`, so it
  MAY already transfer to the two-sided frame unchanged (the two-sided R still satisfies each retained
  conjunct) — **but this must be VERIFIED, not assumed**: the `bDia` case now discharges against a
  two-sided R whose `cs5Incest` witness is sourced from the diamond clause. Phase 8 confirms the soundness
  holds axiom-free over the two-sided frame class (report 06's residual ~15%), adding a two-sided-frame
  analogue alongside if the abstract statement does not transfer verbatim.
- **Depends on:** 3
- **Reused assets:** `cs5_soundness` — `CS5.lean:311`; `cs5_axiom_sound''` (17 axioms) — `CS5.lean:366`;
  `cs5FC''`/`cs5FC''_cs5Mreach` — `CKExtension.lean`/`CS5.lean:1242` (untouched); Marin Thm 7.1/7.2
  (`MarinMoralesStrassburger2021`, chunk_0043 verbatim).

---

### Phase 5: One-sided-frame incestuality obstruction [BLOCKED — retained as documented negative result]

- **Goal (as executed):** Prove the one-sided canonical frame SATISFIES `cs5Incest`.
- **RESULT: BLOCKED — the goal is FALSE for the one-sided frame, mechanized as a complete, sorry-free,
  axiom-clean counterexample.** `boxInv` is monotone under `⊆`, so the `(1,1,0,0)` witness `u′ ≥ u` on the
  `boxInv`-domain side cannot help; the goal collapses to plain symmetry, which fails via the exploding
  `Ω` (`head = Set.univ`, reachable from every world, cannot route back). Landed:
  `cs5CanonMreach_to_univ`, `cs5Incest_cs5CanonMreach_forces_univ`, `cs5_consistent_incest`,
  `cs5Incest_cs5CanonMreach_false` (`CS5Canonical.lean:~419/430/~450/~465`).
- **Status note (v3) — RETAINED, NOT REWORKED:** report 06 shows this collapse is a property of the
  *one-sided frame + retained `Ω`*, not of `cs5Incest` (which is faithful). These four lemmas STAY as a
  load-bearing, mechanized account of WHY the one-sided frame fails — the precise diagnosis that motivates
  the redesign. The redesign (Phases 6–10) builds the two-sided `Ω`-excluding frame ALONGSIDE; it does NOT
  delete or edit these negative results. They also directly seed Phase 7's FAILURE-branch obstruction
  template.
- **Depends on:** 4
- **Reused assets:** `box_refuting_theory`/`quasi_prime_exclusion`/`quasi_head_realization` —
  `SegmentLindenbaum.lean:177/73/251`; `quasiPrime_univ` — `Segment.lean`; `CS4Segment`'s `excl`/
  `excl_head` + `cs4FC'`'s existential weakening — `CS4.lean:373/379` / `CKExtension.lean` (the two
  unblock precedents, now realized as Phases 6–7).

---

### Phase 6: Restore Simpson's two-sided R + `Ω`-excluding canonical world type [NOT STARTED]

- **Goal:** Build, ALONGSIDE the one-sided frame, (a) the genuine **two-sided** canonical relation with
  the restored diamond clause, and (b) an `Ω`-**excluding** canonical world type carrying a hereditary
  consistency invariant (CS4 `excl_head` precedent), with the free plumbing (reflexivity, valuation,
  bottom, and the hereditary-closure lemma) ported. This is the definitional + CS4-port setup that the
  Phase 7 gate stands on. *Medium risk, ~150–300 lines (mostly a CS4 port + one new clause).*
- **Tasks:**
  - [ ] Define the two-sided canonical relation (suggested `cs5TwoSidedR`, name at implementer's
    discretion): `cs5TwoSidedR Γ Δ := boxInv Γ ⊆ Δ  ∧  (∀ A, (◇A) ∈ Δ → (◇A) ∈ Γ)` — Simpson's box
    clause `{B | □B ∈ Γ} ⊆ Δ` (= `boxInv Γ ⊆ Δ`, the FORWARD clause, kept from `cs5OnesidedR`) AND the
    restored diamond clause `{◇A | A ∈ Δ} ⊆ Γ` (the BACKWARD clause, dropped in Phase 3). Cross-check the
    diamond clause direction against `cs5_boxInv_subset_iff` (`boxInv T ⊆ H ↔ T ⊆ diaInv H`, `CS5.lean:589`)
    and `diaInv` (`Segment.lean:106`). **Document in the definition's docstring that the diamond clause is
    discharged via the prime lemma / disjunction property (Phase 7), NOT via per-world back-inclusion /
    negation-completeness — this is what distinguishes it from the discarded two-sided `cs5Tail` symmetry
    wall.**
  - [ ] Define the `Ω`-excluding canonical world type (suggested `CS5PrimeSegment`), cloning
    `CS5CanonSegment` (`CS5Canonical.lean:166`) BUT adding an `excl`/`excl_head`-style hereditary invariant
    excluding the exploding case, exactly mirroring `CS4Segment`'s `excl : Option (Proposition Atom)` +
    `excl_head : ∀ A, excl = some A → (◇A) ∉ seg.head` (`CS4.lean:377/379`). Here the excluded object is
    `⊥`/`univ`-membership, giving prime *consistent* (non-exploding) worlds. Licensed by settled
    `CS5 ≡ IS5` (report 05) + Alechina redundancy (report 04 Q2): at CS5 strength the fallible/exploding
    worlds are redundant, so excluding them loses NO completeness.
  - [ ] Port the hereditary-closure lemma (analogue of `cs4_not_dia_dia`, `CS4.lean:317`) that makes the
    `Ω`-exclusion propagate through the transitive closure of the two-sided reachability — the closure fact
    the diamond-side witness (Phase 7) relies on to stay non-exploding.
  - [ ] Port the free plumbing over the new type: reflexivity (clone `cs5CanonRefl`, `:189`, still just
    axiom `T` on the box clause), valuation `cval`/`cbotForces` (clone `cs5CanonVal`/`cs5CanonBot`,
    `:195/:198`), and the two-sided reachability `cmreach` port (clone `cs5CanonMreach`, `:176`).
  - [ ] Confirm the propositional / box-forward / diamond truth-lemma clauses remain served by `CKForces`
    over the new type (same as Phase 3's one-sided port; `CKForces` is generic over `World`/`r`/`val`).
- **Timing:** ~3 hours
- **Depends on:** 5
- **Reused assets (real names + file:line):**
  - `CS4Segment` (structure) / `excl` / `excl_head` — `CS4.lean:373/377/379` (the `Ω`-exclusion template).
  - `cs4_not_dia_dia` — `CS4.lean:317` (hereditary-closure lemma template).
  - `cs4Tail`/`cs4Seg`/`cs4Mreach` — `CS4.lean:341/…/386` (world-type plumbing template).
  - `CS5CanonSegment`/`cs5CanonMreach`/`cs5CanonRefl`/`cs5CanonVal`/`cs5CanonBot` — `CS5Canonical.lean:166/176/189/195/198` (Phase 3 one-sided plumbing to clone).
  - `boxInv`, `QuasiPrime`, `quasiPrime_univ`, `cmreach`, `diaInv` — `Segment.lean` (`diaInv` at `:106`).
  - `cs5_boxInv_subset_iff` — `CS5.lean:589`; `cs5_boxInv_subset` (axiom `T`) — `CS5.lean:621`.
  - Simpson two-sided canonical R (`{◇A | A ∈ Y} ⊆ X ∧ {B | □B ∈ X} ⊆ Y`) — corpus chunk
    `682e04d443e7bbd7` (`Simpson1994`).
- **Files to modify:** `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` (new defs ALONGSIDE
  the one-sided frame; `cs5FC''` in `CKExtension.lean` untouched).
- **Success criteria / CI gates:** the two-sided R + `Ω`-excluding world type + closure lemma + plumbing
  compile; `lake build` green; `checkInitImports`/`lint-style`/`shake` clean; no `sorry`, no new axiom;
  the Phase-5 negative-result lemmas still compile untouched.
- **Verification:** the new frame class typechecks; `lean_verify` on the reflexivity/closure lemmas shows
  no `sorryAx`; `lean_references cs5FC''` unchanged (8 pre-existing sites).

---

### Phase 7: GO/NO-GO GATE — verify UNCHANGED `cs5Incest` on the redesigned frame via the DIAMOND side [NOT STARTED]

- **Goal:** Prove the redesigned two-sided `Ω`-excluding canonical frame SATISFIES the UNCHANGED
  `cs5Incest` (`CS5Canonical.lean:234`), constructing the `(1,1,0,0)` mediating witness `u′ ≥ u` with
  `u′ R w` from the **DIAMOND clause** of the two-sided R via `dia_refuting_theory` — exactly as CS4
  verifies `cs4FC'_cs4Mreach` (`CS4.lean:441`) via the ◇-refuting world (`dia_refuting_theory`,
  `excl_head`), NOT via a box-refuting world. **This is the crux of the redesign and the go/no-go gate.**
  *High risk — report 06's ~85% confidence / ~15% residual concentrates HERE. ~150–300 lines.*
- **Why this can work now (and why Phase 5 could not):** under the one-sided R the witness had to come
  from the `boxInv`-domain side, where monotonicity was fatal (Phase 5). With the diamond clause restored
  and `Ω` excluded, the witness is sourced from `{◇A | A ∈ Δ} ⊆ Γ` via a prime/quasi-prime Lindenbaum
  extension — the disjunction property only, NO negation-completeness, NO `boxInv`-monotonicity trap
  (report 06 §2–§4; Simpson 3.3.2/3.3.3, Marin Thm 7.2 F2).
- **Tasks (SUCCESS path):**
  - [ ] For worlds `w, u` of the `Ω`-excluding type with `w R u` (two-sided), construct the mediating
    `u′ ≥ u` and establish `u′ R w` by a diamond-sourced prime extension: apply `dia_refuting_theory`
    (`SegmentLindenbaum.lean:203`) — which yields, from `◇B ∈ H` and `◇A ∉ H`, a quasi-prime `T` with
    `boxInv H ⊆ T`, `B ∈ T`, `A ∉ T` — to build the witness on the DIAMOND side, discharging the
    incestuality existential. Keep the witness non-exploding via the Phase-6 hereditary `excl_head`
    closure (so `u′ ≠ Ω`).
  - [ ] Discharge the two-sided R's diamond clause for the constructed witnesses from the same prime
    lemma (mirroring how `cs4FC'_cs4Mreach` chains `dia_refuting_theory` through `cs4_not_dia_dia`).
  - [ ] Land the canonical-frame incestuality lemma (suggested `cs5Incest_cs5PrimeMreach` / a
    `cs5FCIncest`-over-two-sided reachability lemma) — the analogue of `cs4FC'_cs4Mreach` (`CS4.lean:441`)
    — sorry-free, axiom-clean, grep-confirmed free of any `¬ϕ ∈`-style negation-completeness move.
- **DECISION GATE — BOTH branches pre-specified:**
  - **SUCCESS** (`cs5Incest` verified on the redesigned frame via the diamond side, sorry-free, no
    negation-completeness) → proceed to Phase 8 (soundness re-check) + Phase 9 (box-backward) + Phase 10
    (completeness). The redesign is validated; report 06's verdict (A) is confirmed in Lean.
  - **FAILURE** (the diamond-side witness ALSO cannot be constructed even with the two-sided R + `Ω`
    excluded — i.e. option (B) was real after all) → **do NOT force, no `sorry`.** Land the obstruction
    as a mechanized negative theorem over the two-sided frame (sorry-free, no new axiom), extending
    Phase 5's negative-result family; mark CS5 completeness "BLOCKED across all known-mechanizable routes"
    (explicitly NOT incompleteness — `CS5 ≡ IS5` is complete, report 05); skip Phases 8–9 and route to the
    Phase 10 FAILURE branch (obstruction writeup); **escalate to a human** with the mechanized account.
- **Timing:** ~4 hours
- **Depends on:** 6
- **Reused assets (real names + file:line):**
  - `dia_refuting_theory` — `SegmentLindenbaum.lean:203` (the ◇-side witness engine — from `◇B ∈ H`,
    `◇A ∉ H`, yields quasi-prime `T ⊇ boxInv H` with `B ∈ T`, `A ∉ T`).
  - `quasi_prime_exclusion` — `SegmentLindenbaum.lean:73`; `quasi_head_realization` — `:251`.
  - `cs4FC'_cs4Mreach` — `CS4.lean:441` (THE diamond-side canonical-verification precedent to mirror);
    `cs4_not_dia_dia` — `CS4.lean:317` (hereditary ◇-exclusion closure); `excl_head` — `CS4.lean:379`.
  - `cs5Incest` (UNCHANGED condition) — `CS5Canonical.lean:234`; Phase-6 two-sided R + `Ω`-excluding type.
  - `cs5_boxInv_subset_iff` (`boxInv T ⊆ H ↔ T ⊆ diaInv H`) — `CS5.lean:589`; `diaInv` — `Segment.lean:106`.
  - Simpson Prime Lemma 3.3.2 / Canonical Model Lemma 3.3.3, F2 incestuality verification — corpus chunks
    `8372f27240fe345d`, `caf3305a53065b87` (`Simpson1994`); Marin Thm 7.2 (`MarinMoralesStrassburger2021`).
  - Phase 5's `cs5Incest_cs5CanonMreach_false` family — `CS5Canonical.lean:~419/430/465` (FAILURE-branch
    obstruction template; and the contrast that isolates the one-sided frame as the artifact).
- **Files to modify:** `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean`.
- **Success criteria / CI gates:** SUCCESS — the incestuality-on-redesigned-frame lemma compiles
  sorry-free, `#print axioms` clean, grep confirms no `¬ϕ ∈` move. FAILURE — the obstruction theorem
  compiles sorry-free, no new axiom, and is escalated. Either way `lake build`/`checkInitImports`/
  `lint-style`/`shake` clean; no `sorry`, no new axiom in `Cslib/`.
- **Verification:** `lean_verify` on the gate lemma (or the obstruction) shows no `sorryAx`;
  `grep -n "¬.*∈"` over the file returns no negation-completeness move; Phase 5 lemmas still compile.

---

### Phase 8: Re-check CS5 soundness over the two-sided frame class [NOT STARTED]

- **Goal:** (SUCCESS branch only) Confirm CS5 soundness (all 17 `CS5ModalAxiom` cases) holds axiom-free
  over the NEW two-sided-R + `Ω`-excluding + `cs5Incest` frame class, adapting Phase 4's
  `cs5_axiom_sound_incest`. **This carries report 06's residual ~15%.** *Medium risk, ~100–250 lines —
  much may transfer verbatim since `cs5_axiom_sound_incest` is abstract over `World`/`r`.*
- **Tasks:**
  - [ ] Check whether Phase 4's abstract `cs5_axiom_sound_incest` (`CS5Canonical.lean:278`, over any `r`
    satisfying `cs5FCIncest`) transfers to the two-sided R unchanged — the two-sided R still satisfies each
    retained conjunct (reflexivity, `fourBox`/`bBox` re-basing, plain transitivity, `cs5Incest`). If it
    transfers, this phase is a confirmation + a thin bundling lemma; if not, add a two-sided-frame analogue
    ALONGSIDE (never editing the Phase-4 theorem in place).
  - [ ] Re-discharge the `bDia` case against the two-sided R + `cs5Incest` whose witness is now
    diamond-sourced (Phase 7); confirm it stays axiom-free (Marin Thm 7.2 soundness direction — a semantic
    argument over incestuous frames with disjunction-property saturated sets, NO negation-completeness).
  - [ ] Confirm the diamond truth-lemma cases stay free over the two-sided frame (the diamond clause of R
    is now non-trivial — verify `cs5_diam_witness`-analogue reachability still holds).
  - [ ] Verify no landed `cs5FC''` (509) consumer regresses (`lean_references cs5FC''` — expect the 8
    pre-existing sites, none in `CS5Canonical.lean`); Phase 4's one-sided soundness stays untouched.
- **Timing:** ~4 hours
- **Depends on:** 7
- **Reused assets (real names + file:line):**
  - `cs5_axiom_sound_incest`/`cs5_soundness_incest`/`cs5_soundness_derivable_incest` —
    `CS5Canonical.lean:278/…/336` (Phase 4; abstract over `World`/`r` — candidate for verbatim transfer).
  - `cs5_axiom_sound''` (17 axioms) — `CS5.lean:366`; `cs5_soundness` — `CS5.lean:311`.
  - `cs5FC''`/`cs5FC''_cs5Mreach` — `CKExtension.lean:184`/`CS5.lean:1242` (untouched; regression check).
  - Marin Thm 7.2 soundness direction — `MarinMoralesStrassburger2021`.
- **Files to modify:** `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean`.
- **Success criteria / CI gates:** all 17 cases + the `bDia` case compile axiom-free over the two-sided
  frame; `lean_references cs5FC''` shows no regression; `lake build`/`checkInitImports`/`lint-style`/
  `shake` clean; no `sorry`, no new axiom.
- **Verification:** `lean_verify` on the two-sided soundness theorem shows `axioms: []` (or clean subset);
  `lean_references cs5FC''` shows only pre-existing sites.

---

### Phase 9: `cs5_box_backward` as the one-sided prime lemma (over the two-sided R's box clause) [NOT STARTED]

- **Goal:** (SUCCESS branch only) Discharge box-backward as the PLAIN one-sided prime lemma over the
  two-sided R's **box-inverse clause**: from `□A ∉ Γ`, get `boxInv Γ ⊬ A`, apply `box_refuting_theory`
  for a quasi-prime `Δ ⊇ boxInv Γ` with `A ∉ Δ` and `Γ R Δ` (the box clause holds by construction; the
  diamond clause plays NO role here). No second clause, no simultaneous pair. *Low risk, ~60–100 lines —
  the whole original five-dispatch blocker dissolves here (Phase 1 gate already proved this reduction).*
- **Tasks:**
  - [ ] State `cs5_box_backward` over the two-sided relation for the `Ω`-excluding world type (the
    Phase 1 probe's scaffolded signature, adapted to the new type).
  - [ ] Prove it by direct application of `box_refuting_theory` (`SegmentLindenbaum.lean:177`) — the
    witness `Δ` is exactly its output; the box clause `boxInv Γ ⊆ Δ` holds by construction. Confirm the
    diamond clause of `Γ R Δ` is not needed for box-backward (frame-condition-independent, Phase 1).
  - [ ] Confirm `A ∉ Δ`, quasi-primeness, and non-explosion (`excl_head`) of `Δ` from the prime lemma.
- **Timing:** ~1.5 hours
- **Depends on:** 7 (needs the two-sided R + `Ω`-excluding type; independent of Phase 8, may run parallel)
- **Reused assets (real names + file:line):**
  - `box_refuting_theory` — `SegmentLindenbaum.lean:177` (delivers the witness verbatim).
  - `quasi_prime_exclusion` — `SegmentLindenbaum.lean:73`.
  - `cs5_box_backward_onesided` (Phase 1 probe) — `specs/512_.../probes/phase1-onesided-box-backward-gate.lean`.
  - `boxInv`, `QuasiPrime` — `Segment.lean`.
- **Files to modify:** `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean`.
- **Success criteria / CI gates:** `cs5_box_backward` compiles sorry-free; `lake build` green;
  `checkInitImports`/`lint-style`/`shake` clean; no `sorry`, no new axiom.
- **Verification:** `#print axioms cs5_box_backward` shows no `sorryAx`; the witness satisfies
  `Γ R Δ ∧ A ∉ Δ` by construction.

---

### Phase 10: Truth lemma + CS5 completeness + file split (or obstruction writeup) [NOT STARTED]

- **Goal:** (SUCCESS branch) Land `cs5_truth_lemma` (clone `cs4_truth_lemma`, box-backward via
  `cs5_box_backward`), `realize` via Lindenbaum, and `cs5_completeness`/`cs5_soundness_completeness` via
  `ckvalidFC_completeness` + the reworked two-sided incestuality frame condition; execute the file split.
  (GATE-FAILURE branch, if Phase 7 failed) Write the mechanized-obstruction module docstring/theorem and
  mark completeness "BLOCKED across known-mechanizable routes." *Medium risk, ~150 lines (mostly reuse).*
- **Tasks (SUCCESS branch):**
  - [ ] Clone `cs4_truth_lemma` (`CS4.lean:457`, one-sided-R precedent) / `ck_truth_lemma`
    (`CKTruthLemma.lean:133`) into `cs5_truth_lemma` over the `Ω`-excluding type; box-backward case is
    `cs5_box_backward` (Phase 9); atom/bot/and/or/imp/diamond/box-forward cases served by `CKForces`.
  - [ ] Provide `realize` via Lindenbaum (`quasi_prime_exclusion` / `quasi_head_realization`,
    `SegmentLindenbaum.lean:73/251`) + `cs5_truth_lemma`.
  - [ ] Land `cs5_completeness` / `cs5_soundness_completeness` via `ckvalidFC_completeness`
    (`CKExtension.lean:227`) supplying `realize` and the Phase-7 two-sided incestuality reachability lemma
    (the `cs5FC''_cs5Mreach` analogue over the redesigned frame).
  - [ ] File split: move `Proposition.map` + `@[simp]` commutation + injectivity to
    `Cslib/Logics/Modal/Basic.lean` (home of `inductive Proposition`, `Basic.lean:72`) if not already
    there; keep the birelational canonical machinery in `CS5Canonical.lean`. Run `lake exe mk_all --module`.
  - [ ] Update the CS5 module docstring (`CS5.lean` header region) to record completeness as PROVED via the
    two-sided birelational model; cite `Dosen1985`, `BozicDosen1984`, `Simpson1994`,
    `AlechinaMendlerdePaivaRitter2001`, `MarinMoralesStrassburger2021`, `Pacheco2024`.
- **Tasks (GATE-FAILURE branch — only if Phase 7 failed):**
  - [ ] Land the mechanized obstruction theorem (sorry-free, no new axiom) showing `cs5Incest` fails even
    on the two-sided `Ω`-excluding frame; keep CS5 completeness marked "BLOCKED across all
    known-mechanizable routes" (explicitly NOT incompleteness — cite `CS5 ≡ IS5` via report 05); escalate.
  - [ ] Update `CS5.lean` docstring to record the obstruction alongside the prior landed negatives.
- **Timing:** ~3 hours
- **Depends on:** 8, 9
- **Reused assets (real names + file:line):**
  - `cs4_truth_lemma` — `CS4.lean:457`; `ck_truth_lemma` — `CKTruthLemma.lean:133`.
  - `ckvalidFC_completeness` — `CKExtension.lean:227`.
  - Lindenbaum: `quasi_prime_exclusion`/`quasi_head_realization` — `SegmentLindenbaum.lean:73/251`.
  - `inductive Proposition` — `Cslib/Logics/Modal/Basic.lean:72` (file-split target).
  - `CKSegment`, `cmreach`, `boxInv`, `QuasiPrime` — `Segment.lean`.
- **Files to modify:** `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean`;
  `Cslib/Logics/Modal/Basic.lean` (`Proposition.map`, if a move is needed);
  `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` (docstring only).
- **Success criteria / CI gates (SUCCESS):** `cs5_completeness` compiles sorry-free; `#print axioms
  cs5_completeness` shows ONLY `Classical.choice`/`propext`/`Quot.sound`. Full pipeline green:
  `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake shake --add-public --keep-implied --keep-prefix`; `lake exe mk_all --module` run.
- **Success criteria / CI gates (GATE FAILURE):** the obstruction theorem compiles sorry-free;
  completeness documented "BLOCKED across known-mechanizable routes"; same full CI pipeline green; no
  `sorry`, no new axiom; escalated to human.
- **Verification:** `#print axioms cs5_completeness` (SUCCESS) or `#print axioms <obstruction>` (FAILURE)
  clean; `lake test` passes.

---

## Testing & Validation

- [ ] `lake build` (full) succeeds after each phase.
- [ ] `lake test` (CslibTests suite) passes at Phases 8 and 10.
- [ ] `lake exe checkInitImports` — every touched file imports `Cslib.Init`.
- [ ] `lake exe lint-style` — clean on all touched files.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — no unused/missing imports (accounting for
      the pre-existing, KNOWN-UNRELATED task-505 `sorry`s in `Tableau/Intuitionistic`/`Tableau/Minimal`
      that leave stale oleans — they do not mention `CS5Canonical.lean`).
- [ ] `#print axioms cs5_completeness` (SUCCESS) shows only `Classical.choice`/`propext`/`Quot.sound`;
      NO `sorryAx`, NO new axiom. On GATE FAILURE, `#print axioms` on the obstruction theorem is clean.
- [ ] `lake exe mk_all --module` run after the Phase 10 file split.
- [ ] Zero-debt invariant: grep confirms no `sorry`/`admit`/new `axiom` in any `Cslib/` file at every
      phase boundary; probe `sorry` (if any) stays under `specs/512_.../probes/`.
- [ ] Phase 7: grep confirms no `¬ϕ ∈`-style negation-completeness move in the diamond-side verification.
- [ ] `lean_references cs5FC''` at Phases 6, 8 confirms the task-509 machinery stays untouched.
- [ ] Phase 5's negative-result lemmas (`cs5Incest_cs5CanonMreach_false` family) still compile after each
      redesign phase (they are retained, not deleted).

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` — the two-sided R + `Ω`-excluding world
  type + hereditary-closure lemma (Phase 6), the diamond-side incestuality verification (Phase 7),
  re-checked two-sided soundness (Phase 8), `cs5_box_backward` (Phase 9), `cs5_truth_lemma` +
  `cs5_completeness`/`cs5_soundness_completeness` (Phase 10) — OR the mechanized obstruction (GATE
  FAILURE). The one-sided frame + Phase-5 negative-result lemmas are RETAINED alongside as documented
  diagnosis.
- `Cslib/Logics/Modal/Basic.lean` — `Proposition.map` + `@[simp]` commutation + injectivity (already
  present; relocation confirmed in Phase 10).
- `Cslib/Logics/Modal/Metalogic/Constructive/CKExtension.lean` — `cs5FC''` and
  `cs5FC''_hub_forces_spoke_connectivity` retained UNTOUCHED.
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` — module docstring update (Phase 10);
  `cs5_symmetric_tail_box_gap` retained.
- `specs/512_cs5_box_backward_atom_sum_completeness/plans/03_canonical-frame-redesign.md` (this file;
  supersedes `plans/02_birelational-pivot.md`).
- `specs/512_cs5_box_backward_atom_sum_completeness/summaries/03_canonical-frame-redesign-summary.md`
  (produced at implementation completion).

## Rollback/Contingency

- Each phase is committed separately (`task 512 phase {P}: {name}`) at a green `lake build`; a failing
  phase reverts only its own commit, leaving earlier green phases intact.
- **Phase 7 GATE FAILURE is not a rollback** but the planned pivot to the mechanized-obstruction
  deliverable (Phase 10 failure branch) + human escalation; Phases 8–9 are skipped. Completeness marked
  "BLOCKED across known-mechanizable routes" (NOT incompleteness). Do NOT force, no `sorry`.
- Phase 6/7 build the two-sided frame ALONGSIDE the one-sided frame — if the redesign is abandoned, the
  one-sided frame + Phase-5 negatives remain intact as the standing documented result.
- Phase 8 is the 509-adjacent regression check: it ADDS two-sided-frame soundness alongside Phase 4's
  one-sided version and never edits `cs5FC''`; if a `cs5FC''` consumer regresses, revert Phase 8's commit
  only.
- No new axiom is ever introduced, so `#print axioms` remains the single acceptance gate; if any
  `sorryAx` appears, revert to the last clean commit and re-dispatch that phase.
