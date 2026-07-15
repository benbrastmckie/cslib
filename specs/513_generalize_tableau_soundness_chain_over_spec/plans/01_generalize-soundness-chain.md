# Implementation Plan: Task #513 — Generalize the Tableau SOUNDNESS Chain over the Rule-Application Interface

- **Task**: 513 - Generalize the tableau soundness chain over the abstract rule-application interface
- **Status**: [COMPLETED]
- **Effort**: 9 hours
- **Dependencies**: 510 (completeness-chain generalization — landed)
- **Research Inputs**: reports/01_generalize-soundness-chain-over-spec.md
- **Artifacts**: plans/01_generalize-soundness-chain.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Generalize the tableau soundness chain — the ~500-line `modalStepBranch_preserves_sat`
(`SoundnessStep.lean:443`) and its fuel-induction wrapper — over an abstract
`apply : RuleApply Atom` plus a frame condition `FC`, so that `modalTableauT φ = .closed → tValid φ`
(and, one-liner downstream, `Decidable (tValid φ)` for task 503 Phase 6) follows by instantiation,
and tasks 505 (B) / 504 (S5) inherit the entire generic chain. The completeness direction (task
510) generalized cleanly because it never reads a propagating rule's payload; **soundness does the
opposite** — the box-positive and diamond-negative arms read the propagating payload directly, so
the generic step requires three *new, frame-relativized* semantic obligations that cannot be
`RuleApplicationSpec` fields (that structure is frame-agnostic and on a parallel import branch).
These three facts are passed as **raw hypotheses** into new generic lemmas in `FrameSoundness.lean`;
K/T instantiation lands in `FrameCompleteness.lean` (the unique merge point).

Definition of done: `modalStepBranchGen_preserves_satIn`, `modalExpandBranchesGen_closed_unsatIn`,
`modalTableauT_sound`, `tValid_decides`, `instDecidableTValid` all land sorry-free and axiom-clean;
K's public soundness API (`modalTableau_sound`, `modalTableau_decides`, `instDecidableKValid`)
remains **byte-identical and untouched**; full CSLib CI green at every phase milestone.

### Research Integration

This plan encodes the 6-phase decomposition from `reports/01_generalize-soundness-chain-over-spec.md`
(§6), which is authoritative. Key findings carried into the phases:

- **The crux asymmetry with 510** (report §0): the box-positive arm (`SoundnessStep.lean:566-598`)
  and diamond-negative arm (`:948-977`) *read* the propagating payload, so the soundness field is
  irreducibly semantic and irreducibly frame-relativized. No `∃ out` weakening applies.
- **Interface finding** (report §3): of the 11/12 `RuleApplicationSpec` fields, only `freshLocal`
  (F1) is reused — and only for freshness maintenance in the fuel wrapper. The three new
  obligations — **(S-agree)** agreement off the two propagating shapes, **(S-boxPos)** box-positive
  semantic soundness, **(S-diaNeg)** diamond-negative semantic soundness — are passed as **raw
  hypotheses** (mirroring 510's `modalStepBranch_preserves_accFreshInv_gen`), NOT added to
  `RuleApplicationSpec`. An optional `RuleSoundnessSpec FC apply` bundle is deferred until B/S5 land.
- **Import topology** (report §2): `SoundnessStep`/`Soundness`/`FrameSoundness` are on a branch
  parallel to `GenericDriver`; they merge only at `FrameCompleteness`. Generic soundness lemmas
  therefore live in `FrameSoundness.lean` (raw hypotheses); K/T instantiation +
  `tValid_decides`/`instDecidableTValid` live in `FrameCompleteness.lean`.
- **Universe boundary** (report §4): `branchSatisfiableIn FC` is fixed at `W : Type` (universe 0),
  whereas K's `branchSatisfiable` is `Type*`. The K monolith is kept byte-identical (510 keep-both
  precedent); K is re-instantiated at universe 0 via `modalTableau_sound_frame`/`trivialFC` as a
  zero-regression demonstration, WITHOUT collapsing K's `.{v,u}` binder.
- **Already-proven assets** (report §1): `branchSatisfiableIn_reflFC_boxPos_mem`,
  `branchSatisfiableIn_reflFC_diaNeg_mem`, `modalTBoxSelf_sound`, `modalTDiaNegSelf_sound`
  (`FrameSoundness.lean:162-229`) are the T-specific reflexivity soundness — consumed, not reproven.
  `modalTableauT_complete` (`FrameCompleteness.lean:882`) already exists for the decidability wiring.
- **Load-bearing structural fact** (report §0, task 503 Phase 6): the ambient Kripke model `(W, m)`
  is never replaced — only `f` is redefined at fresh worlds — so the `FC m.r` witness threads
  through every `refine ⟨W, m, f, …⟩` tuple unchanged. This is what makes the crux port mechanical.

### Prior Plan Reference

No prior plan. This is the first plan for task 513.

### Roadmap Alignment

ROADMAP.md exists but was consulted read-only and not modified (no `roadmap_flag` set for this
dispatch). This task advances the modal-tableau decidability line: completing the shared soundness
blocker unblocks `Decidable (tValid)` (task 503 Phase 6), `Decidable (bValid)` (task 505), and
`Decidable (s5Valid)` (task 504).

## Goals & Non-Goals

**Goals**:
- Generalize `modalStepBranch_preserves_sat` and its fuel wrapper over `(FC, apply)` with three raw
  frame-relativized soundness hypotheses, landing `modalStepBranchGen_preserves_satIn` and
  `modalExpandBranchesGen_closed_unsatIn` in `FrameSoundness.lean`.
- Derive the exact interface from what the proof consumes: reuse only `freshLocal` (F1); introduce
  the three new obligations (S-agree, S-boxPos, S-diaNeg) as raw hypotheses, not `RuleApplicationSpec`
  fields.
- Re-instantiate K at universe 0 as a zero-regression demonstration; keep K's public `Type*` API
  byte-identical and untouched.
- Instantiate at `modalApplyOneT` to expose `modalTableauT_sound`; complete
  `tValid_decides` / `instDecidableTValid` (task 503 Phase 6 target) in `FrameCompleteness.lean`.
- Every phase ends at a green scoped `lake build` + full CI, zero `sorry`, zero added axiom
  (axiom-trio only via `#print axioms`).

**Non-Goals**:
- Widening `branchSatisfiableIn`/`FrameCondition` to `Type*` or re-deriving K's monolith at `Type*`
  (out of scope; T/B/S5 all live at universe 0 — report §4).
- Adding fields to `RuleApplicationSpec` (frame-agnostic, off the soundness import branch — report §3.3).
- Introducing a `RuleSoundnessSpec` bundle now (deferred until B/S5 actually land — report §3.3).
- Landing B (task 505) or S5 (task 504) soundness discharges; this task only unblocks them.
- Replacing ported K arms with `aesop`/`simp`-bulldozing (would break auditable byte-identity — report §7).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| P2 crux (~420-line FC-threaded port) hits an elaboration snag threading the `FC` witness in a minting arm | H | L | The model `(W, m)` is never rebuilt; `FC m.r` is a literal passenger (report §0, §5). If it occurs, split P2 into P2a (propositional + atom/bot arms) / P2b (two minting arms) — the two propagating arms are already externalized as hypotheses, so the split is clean. Correct fallback is `[BLOCKED]` with the exact goal state recorded on the specific arm — never a `sorry`. |
| K public API accidentally perturbed (regression) | H | L | Keep `modalStepBranch_preserves_sat`, `modalExpandBranches_closed_unsat`, `modalTableau_sound`, `kValid` byte-identical and untouched; P4 confirms via `git diff` that the K monolith and public API are unchanged. |
| `negImp_alpha_preserved` is `private`, blocking the `impNeg` arm port | M | M | P1 de-privatizes + FC-lifts it (~5-line variant) before the crux consumes it. |
| Initial `branchSatisfiableIn reflFC` witness in `modalTableauT_sound` lacks the `Std.Refl m.r` proof | M | L | `tValid = frameValid reflFC` quantifies reflexive models, so the `by_contra` falsifying model is reflexive by hypothesis; confirm the `Std.Refl` field is threaded into the initial-branch tuple (report §4 flagged point). |
| Scoped `git add` collides with concurrent sessions | M | M | Add only the specific Tableau files touched per phase; run `git status` before each commit. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4, 5 | 3 |
| 5 | 6 | 5 |

Phases within the same wave can execute in parallel. P4 (K zero-regression) and P5 (T soundness)
both depend only on the generic chain from P3 (and the K arm lemmas from P1) and are independent of
each other, so they may run in parallel.

### Phase 1: Extract K arm lemmas + prep helpers [COMPLETED]

- **Goal:** Externalize the two propagating-arm proofs and the closed-branch fact so the crux (P2)
  can consume them as hypotheses, with zero proof-content change.
- **Tasks:**
  - [ ] Extract the box-positive arm of `modalStepBranch_preserves_sat` (`SoundnessStep.lean:555-598`)
    into a standalone `RuleResultSat`-valued lemma `modalApplyOne_boxPos_sound` (`FC` unused; drop it;
    `.snd = acc` conjunct records non-minting).
  - [ ] Extract the diamond-negative arm (`SoundnessStep.lean:948-977`) into
    `modalApplyOne_diaNeg_sound` (dual).
  - [ ] De-privatize `negImp_alpha_preserved` (`SoundnessStep.lean:414`, currently `private`) and add
    an `FC`-lifted variant (~5 lines) for the `impNeg` arm.
  - [ ] Add `modalClosed_unsatIn (FC) (b) (hclosed) (acc) : ¬ branchSatisfiableIn FC b acc` in
    `FrameSoundness.lean` (trivial generalization of `modalClosed_unsat`; proof reuses the frame-free
    `modalClosed_unsat` via the `branchSatisfiableIn` destructuring — report §4).
  - [ ] Scoped `lake build` on the two files; full CI sweep.
- **Timing:** ~1 hour
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/SoundnessStep.lean` — extract two arm lemmas; de-privatize + FC-lift `negImp_alpha_preserved`
  - `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` — add `modalClosed_unsatIn`
- **Verification:**
  - `lake build` green on both files; the extracted lemmas type-check as `RuleResultSat`-valued.
  - `modalStepBranch_preserves_sat` still compiles (arms now delegate to the extracted lemmas, or are
    left untouched pending P4 — extraction must not alter the K monolith's byte output; if inlining
    the delegation risks that, extract as *new* standalone lemmas and leave the monolith untouched).
  - Zero `sorry`, zero added axiom.

### Phase 2: CRUX — generic frame-relativized single-step sat preservation [COMPLETED]

- **Goal:** Land `modalStepBranchGen_preserves_satIn (FC) (apply)` with raw hypotheses `hAgree`
  (S-agree), `hBoxPos` (S-boxPos), `hDiaNeg` (S-diaNeg) — the ~420-line FC-threaded port of the
  monolith (report §5).
- **Tasks:**
  - [ ] State `modalStepBranchGen_preserves_satIn` with the three raw hypotheses and the signature from
    report §4 (`branchSatisfiableIn FC` conclusion `∃ b' ∈ newBs, branchSatisfiableIn FC b' newAcc`).
  - [ ] Port the 10 propositional arms + `atom`/`bot` arms via `hAgree → modalApplyOne`, threading the
    `FC m.r` witness (unchanged `m`) into each `refine ⟨…, W, m, f, hacc, …⟩` tuple; optionally route
    through the already-generic `tryAllPropRules_sat`.
  - [ ] Port the `impNeg` arm using P1's de-privatized FC-lifted `negImp_alpha_preserved`.
  - [ ] Replace the box-positive arm by `hBoxPos`; replace the diamond-negative arm by `hDiaNeg`.
  - [ ] Port the two minting arms (`diamondPos` `:599-727`, `boxNeg` `:803-947`) verbatim, inserting
    only the `FC m.r` component into the witness tuple (identical `m`; `f'` extension, `hInv`,
    `modalNextWorld_gt`, edge bookkeeping all unchanged — report §5).
  - [ ] Scoped `lake build` on `FrameSoundness.lean`; full CI sweep; `#print axioms`.
- **Timing:** ~3.5 hours (bulk of the task)
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` — add `modalStepBranchGen_preserves_satIn`
- **Verification:**
  - `lake build` green on `FrameSoundness.lean`; lemma sorry-free.
  - `#print axioms modalStepBranchGen_preserves_satIn` shows the axiom-trio only.
- **Blocked-outcome note:** This is the only plausible `[BLOCKED]` site. If a minting-arm port hits an
  unexpected elaboration snag, mark the phase `[BLOCKED]` with the exact goal state recorded on the
  specific arm and, if useful, land the clean split P2a (propositional + atom/bot arms) as a partial
  green milestone before recording the block on P2b. **Never a `sorry`, never a vacuous placeholder.**

### Phase 3: Generic frame-relativized fuel induction [COMPLETED]

- **Goal:** Land `modalExpandBranchesGen_closed_unsatIn (FC) (apply)` — the ~160-line port of
  `modalExpandBranches_closed_unsat`, swapping in the generic step (P2), the generic freshness lemma
  `modalStepBranch_preserves_accFreshInv_gen` (already generic from task 510), and `modalClosed_unsatIn`
  (P1).
- **Tasks:**
  - [ ] State `modalExpandBranchesGen_closed_unsatIn` with raw `hFreshLocal` (F1-shape) + `hAgree`/
    `hBoxPos`/`hDiaNeg` and the `List.Forall₂` conclusion from report §4.
  - [ ] Port the fuel induction, feeding `modalStepBranchGen_preserves_satIn` at the step and
    `modalClosed_unsatIn` at the closed leaf.
  - [ ] Scoped `lake build`; full CI; `#print axioms`.
- **Timing:** ~1.5 hours
- **Depends on:** 2
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` — add `modalExpandBranchesGen_closed_unsatIn`
- **Verification:**
  - `lake build` green; lemma sorry-free; axiom-trio only.

### Phase 4: K zero-regression re-instantiation [COMPLETED]

- **Goal:** Exhibit K as a trivial universe-0 instance of the generic chain WITHOUT touching K's
  canonical `Type*` API.
- **Tasks:**
  - [ ] Re-derive `modalTableau_sound_frame` (`FrameSoundness.lean:135`, K soundness through
    `frameValid`, universe 0) via `modalExpandBranchesGen_closed_unsatIn trivialFC modalApplyOne`,
    discharging `hAgree` by `fun _ _ _ _ _ => rfl`, `hBoxPos`/`hDiaNeg` by P1's
    `modalApplyOne_boxPos_sound`/`modalApplyOne_diaNeg_sound`, `hFreshLocal` by `modalApplyOne_fresh`.
  - [ ] Confirm via `git diff` that `modalStepBranch_preserves_sat`, `modalExpandBranches_closed_unsat`,
    `modalTableau_sound`, `kValid`, `modalTableau_decides`, `instDecidableKValid` are byte-identical
    and untouched.
  - [ ] Scoped `lake build`; full CI.
- **Timing:** ~0.5 hours
- **Depends on:** 3
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` — re-derive `modalTableau_sound_frame` via generic chain
- **Verification:**
  - `lake build` green; K public API diff is empty (byte-identical); axiom-trio only.

### Phase 5: T soundness discharges + `modalTableauT_sound` [COMPLETED]

- **Goal:** Discharge the three soundness facts for T and land `modalTableauT_sound`.
- **Tasks:**
  - [ ] `hAgreeT`: discharge S-agree by `modalApplyOneT_eq_of_not_boxPos_diaNeg` verbatim
    (`FrameRules.lean:113` — zero new proof content).
  - [ ] `modalApplyOneT_boxPos_soundIn` (S-boxPos at `apply := modalApplyOneT`, `FC := reflFC`): split
    `RuleResultSat` over the `kForms ++ selfNew.filter …` append (`modalApplyOneT_boxPos_fst`,
    `TDriver.lean:176`); `kForms` half = P1's `modalApplyOne_boxPos_sound`; `selfNew` half =
    `branchSatisfiableIn_reflFC_boxPos_mem` / `modalTBoxSelf_sound` (~15-25 lines).
  - [ ] `modalApplyOneT_diaNeg_soundIn` (dual, via `branchSatisfiableIn_reflFC_diaNeg_mem` /
    `modalTDiaNegSelf_sound`).
  - [ ] `modalTableauT_sound (φ) (h : modalTableauT φ = .closed) : tValid φ` — contrapositive over
    `reflFC` (mirror `modalTableau_sound`, `Soundness.lean:361`), feeding
    `modalExpandBranchesGen_closed_unsatIn reflFC modalApplyOneT (modalApplyOneT_spec.freshLocal)
    hAgreeT hBoxPosT hDiaNegT (modalFuel φ)` at `[[⟨.neg,φ,0⟩]] [[]] [Accessibility.empty]`; supply the
    initial reflexive witness (`Std.Refl m.r` from the reflexive falsifying model — report §4 note).
  - [ ] Scoped `lake build`; full CI; `#print axioms modalTableauT_sound`.
- **Timing:** ~1.5 hours
- **Depends on:** 3
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — T discharges + `modalTableauT_sound` (merge point)
  - (optionally `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` if a T discharge lands more naturally beside its generic source)
- **Verification:**
  - `lake build` green; `modalTableauT_sound` sorry-free; axiom-trio only.

### Phase 6: Decidability wiring + final CI/axiom sweep [COMPLETED]

- **Goal:** Complete `tValid_decides` and `instDecidableTValid` (task 503 Phase 6 target) as
  one-liners mirroring K's `modalTableau_decides` / `instDecidableKValid`.
- **Tasks:**
  - [ ] `tValid_decides (φ0) : modalTableauT φ0 = .closed ↔ tValid φ0` (`.mp` = `modalTableauT_sound`;
    `.mpr` via `modalTableauT_complete`, `FrameCompleteness.lean:882`).
  - [ ] `instDecidableTValid (φ0) : Decidable (tValid φ0)` (match on `modalTableauT φ0`).
  - [ ] Full CSLib CI: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
    `lake shake --add-public --keep-implied --keep-prefix`.
  - [ ] `#print axioms` sweep over `modalTableauT_sound`, `tValid_decides`, `instDecidableTValid`
    (axiom-trio only).
- **Timing:** ~0.5 hours
- **Depends on:** 5
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — `tValid_decides`, `instDecidableTValid`
- **Verification:**
  - Full CI green; all three declarations sorry-free and axiom-clean.

## Testing & Validation

- [ ] Scoped `lake build` green at the end of every phase.
- [ ] Full CSLib CI green at each milestone: `lake test`, `lake exe checkInitImports`,
  `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] `#print axioms` on each new theorem shows the standard axiom-trio only (zero added axiom).
- [ ] Zero `sorry` in any landed file.
- [ ] `git diff` confirms K's public soundness API (`modalTableau_sound`, `modalTableau_decides`,
  `instDecidableKValid`) and the K monolith are byte-identical and untouched (P4).
- [ ] `modalTableauT_sound`, `tValid_decides`, `instDecidableTValid` land and type-check against
  `Cube.T` / `Satisfies.t`, unblocking task 503 Phase 6.

## Artifacts & Outputs

- plans/01_generalize-soundness-chain.md (this file)
- summaries/01_generalize-soundness-chain-summary.md (on completion)
- New declarations in `FrameSoundness.lean`: `modalClosed_unsatIn`,
  `modalStepBranchGen_preserves_satIn`, `modalExpandBranchesGen_closed_unsatIn`, extracted K arm
  lemmas, re-derived `modalTableau_sound_frame`.
- New declarations in `FrameCompleteness.lean`: `modalApplyOneT_boxPos_soundIn`,
  `modalApplyOneT_diaNeg_soundIn`, `modalTableauT_sound`, `tValid_decides`, `instDecidableTValid`.
- De-privatized + FC-lifted `negImp_alpha_preserved` in `SoundnessStep.lean`.

## Rollback/Contingency

- Each phase is an isolated green `lake build` + scoped commit; revert a phase by `git revert` of its
  commit without disturbing earlier phases.
- If P2 blocks: land the clean P2a split as a partial green milestone, mark P2b `[BLOCKED]` with the
  exact recorded goal state, and stop — the two propagating arms are already externalized so no debt
  is introduced. Do NOT insert `sorry` or vacuous placeholders.
- If K byte-identity is inadvertently broken (P4 diff non-empty): restore the monolith from HEAD and
  re-derive K only through the universe-0 `modalTableau_sound_frame` path, never by editing the
  `Type*` API.
- Scope every `git add` to the specific Tableau files touched; run `git status` before each commit to
  avoid clobbering concurrent sessions.
