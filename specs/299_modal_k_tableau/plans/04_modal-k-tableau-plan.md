# Implementation Plan: Task #299 (Revised, v3)

- **Task**: 299 - Modal K Tableau Decision Procedure
- **Status**: [IN PROGRESS]
- **Effort**: 9.25 hours remaining (Phases 5a-7; soundness Phases 1-4 done, ~11h sunk)
- **Dependencies**: None
- **Research Inputs**: specs/299_modal_k_tableau/reports/01_modal-k-tableau-research.md; specs/299_modal_k_tableau/reports/03_completeness-decomposition.md
- **Artifacts**: plans/04_modal-k-tableau-plan.md (this file); supersedes plans/02_modal-k-tableau-plan.md
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, CSLib CONTRIBUTING.md (zero-sorry / zero-new-axiom)
- **Type**: cslib
- **Lean Intent**: false

## Overview

Implement a sound and complete tableau decision procedure for basic modal logic K under
`Cslib/Logics/Modal/Tableau/`, instantiating the label-generic CSLib Foundations tableau layer
with `F = Cslib.Logic.Modal.Proposition Atom` and `L = WorldIndex` (Nat).

**Soundness is DONE.** Phases 1-4 (Defs, Rules+Branch, Closure+Saturation, Soundness) are
[COMPLETED] and the whole-library build is GREEN at commit `3660ac0c`. Soundness was finished via
the spawned tasks 364/384, which split `Soundness.lean` and landed the per-step preservation lemma
(`modalStepBranch_preserves_sat`, now in `SoundnessStep.lean:187`) and the fuel/worklist loop
invariant (`modalExpandBranches_closed_unsat`, `Soundness.lean:226`) together with reusable
`List.Forall₂` worklist helpers (`Soundness.lean:156-219`) and `accFreshInv` machinery. None of the
soundness phases are re-planned here.

This revision (v3) exists for ONE reason: **Phase 5 (completeness scaffolding) was an oversized
single-shot phase that twice overflowed the implementer's context** because the modal truth lemma
must mirror two large reference proofs at once (the propositional `classicalTruthLemma` and the
Bimodal box cases of `truthLemma_pos`/`truthLemma_neg`), forcing large reference-file reads. v3 folds
the completeness decomposition from `reports/03_completeness-decomposition.md` into four
single-dispatch sub-phases (5a-5d) plus the existing Phase 6 (loop invariant) and Phase 7 (finalize),
and inlines the exact reference signatures so the implementer needs minimal large-file reading.

### Research Integration

This v3 revision integrates the new report `reports/03_completeness-decomposition.md`. Its
load-bearing findings, applied below:

- **Re-split of Phase 5 (5a-5d)**: the report's REVISED decomposition splits along *what forced the
  context overflow* (the per-rule semantic-bridge helpers, 5b) rather than along a positive/negative
  induction boundary. The pos/neg split is rejected with justification: modal K's `imp`-positive is a
  branching Łukasiewicz rule whose `[F(a)]` sub-branch consumes the *negative* IH, and `imp`-negative
  consumes the *positive* IH, so the two directions are mutually recursive and MUST live in ONE
  conjunction lemma (`induction φ` proving `pos ∧ neg` together), exactly like `classicalTruthLemma`.
- **Inlined reference-signature table**: exact `item | signature | file:line` rows are embedded into
  5a/5b/5c/5d so the implementer mirrors the templates without opening the 1340-line Classical or
  1095-line Bimodal files.
- **Phase 6 de-risk**: `modalExpandBranches_hintikka` does not yet exist, but the hard worklist/fuel
  plumbing was already solved for the closed direction by tasks 384/364
  (`modalExpandBranches_closed_unsat`, the `forall₂_*` helpers, `accFreshInv`). Phase 6 mirrors that
  skeleton plus `classicalExpandBranches_hintikka` for the open/Hintikka logic.
- **Refactor**: hoist the generic `forall₂_*` list helpers out of `Soundness.lean` into a shared
  module so `Completeness.lean` reuses them WITHOUT importing the heavy soundness file (folded into 5a
  as a preliminary).
- **Two corrections to the stale v2 declaration map**:
  (a) `modalStepBranch_preserves_sat` now lives in `SoundnessStep.lean:187` (the v2 plan's
  declaration map is stale post-task-384); (b) `modalHintikkaSet` carries NO standalone box/diamond
  edge-closure conjunct — box-positive edge-closure is folded into the `.persistent` branch of
  `modalApplyOne`, so the generic `.persistent nf => ∀ sf' ∈ nf, sf' ∈ b` clause IS the edge-closure
  condition; the truth lemma's box case must read it through `modalApplyOne … = .persistent`, not a
  separate predicate.

The original report `reports/01_modal-k-tableau-research.md` remains fully integrated (reuse
Foundations layer, classical architecture template, Bimodal modal-mechanics, K-vs-S5 box-rule
correctness). Reports integrated: see `reports_integrated` in state metadata.

### Prior Plan Reference

Supersedes `plans/02_modal-k-tableau-plan.md` (v2, which itself superseded v1). Phases 1-4
(soundness) are carried over as [COMPLETED] (finished via spawned tasks 364/384, build green at
`3660ac0c`) and are not re-planned. Only Phases 5-7 are restructured: Phase 5 is re-split into
5a-5d per report 03; Phases 6 and 7 are retained and refined.

### Roadmap Alignment

ROADMAP.md exists but no `roadmap_flag` was provided; this plan does not add roadmap review/update
phases and does not modify ROADMAP.md. Task 299 is part of the modal/temporal tableau series
(tasks 299-301); completing it advances the Modal Logic decidability line.

## Goals & Non-Goals

**Goals**:
- A `modalTableau φ` decision procedure for modal K returning `closed` or an open branch.
- `modalTableau_sound`: closed result ⇒ φ valid over all Kripke models. **(DONE, Phase 4.)**
- `modalTableau_complete`: open result yields a finite Kripke countermodel refuting φ. (Phases 5-6.)
- A `modalTableau_decides` iff and a `Decidable` instance (no `Fintype Atom` requirement). (Phase 7.)
- All files under `Cslib/Logics/Modal/Tableau/` build with ZERO `sorry` and ZERO new axioms; full
  CSLib CI pipeline green.

**Non-Goals**:
- Any modal system beyond K (no T/D/4/5/B/S4/S5 frame conditions).
- Optimised/performant saturation; fuel-based correctness suffices.
- Reusing or modifying the Bimodal/Classical tableau code in place (reference only).
- A canonical-model / Lindenbaum completeness proof (countermodel extraction is the route).
- Re-planning or re-touching soundness (Phases 1-4) — they are complete and green.
- Over-abstracting a shared "tableau→model" helper (modal `Model` carries both `r` and `v`, unlike
  the valuation-only temporal/bimodal models; `extractModel` is ~10 new lines).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Completeness dispatch overflows context again (the v2 failure) | H | M | Phase 5 re-split into 5a-5d each bounded to one agent run (~100-300 lines output); 5b isolates the per-rule semantic bridges that caused the reference-file reads; inline signature tables remove the need to open Classical/Bimodal files |
| Implementer treats box edge-closure as a standalone `modalHintikkaSet` conjunct (does not exist) | H | M | Correction inlined into 5b/5c: box-pos edge-closure is the `.persistent` output of `modalApplyOne (T(□ψ)@w)`; the bridge `hintikka_box_pos` encapsulates this so 5c never re-derives it |
| Implementer follows the stale v2 declaration map (`modalStepBranch_preserves_sat` in `Soundness.lean`) | M | M | Correction inlined: it is in `SoundnessStep.lean:187`; soundness is done and not edited here anyway |
| `imp` pos/neg mutual recursion mis-split across dispatches, leaving a non-compiling half | H | M | 5c is a single conjunction lemma (`induction φ` proving `pos ∧ neg`); it is NOT split by sign |
| Phase 6 loop invariant (`modalExpandBranches_hintikka`) cannot be closed | H | M | De-risked by reusing the 384/364 infra (`modalExpandBranches_closed_unsat`, `forall₂_*`, `accFreshInv`); zero-debt fallback: keep 5a-5d committed sorry-free, mark Phase 6 [BLOCKED], `/spawn` follow-up; never ship sorry/axioms |
| `Completeness.lean` pulls the heavy ~970-line `Soundness.lean` into its build via the `forall₂_*` helpers | M | M | Refactor in 5a: hoist `forall₂_*` to a shared `LoopInduction.lean` so completeness reuses them without importing soundness |
| World-creation interleaving (box-pos re-firing as new successors appear) breaks the fuel bound | M | M | `modalFuel` (`Saturation.lean:89`, `(4n+4)(n+2)+2`) should suffice; adjust in `Saturation.lean` ONLY if the Phase 6 invariant proof exposes a concrete gap |
| Concurrent sessions clobber WIP `Completeness.lean` | M | M | Environment hazard (below); serialize sessions or use a git worktree; commit each green sub-phase immediately |

**Environment hazard**: multiple concurrent Claude sessions share this one checkout; a sibling
`git add -A` previously swept WIP into an unrelated commit. Serialize sessions or use separate git
worktrees before resuming. All completeness work is in the single new file `Completeness.lean`
(plus the small `LoopInduction.lean` refactor), disjoint from any soundness file, so it is territory-
isolated.

## Context-Budget Protocol (MANDATORY for every completeness sub-phase)

The reference files are large (Classical `Completeness.lean` 1340 lines, Bimodal
`CountermodelExtraction.lean` 1095 lines). Implementation agents MUST NOT read them in full — the
load-bearing fragments are inlined in the sub-phases below. For every sub-phase 5a-7:

1. **Navigate, do not bulk-read.** Use lean-lsp:
   - `lean_file_outline` to locate declarations; `lean_diagnostic_messages` for the authoritative
     current error set (not the line numbers in this plan).
   - `lean_goal` + `lean_hover_info` at a targeted line to inspect proof state before editing;
     `lean_multi_attempt` to test a tactic without committing an edit.
   - `Read` with `offset`/`limit` for only the ±40 lines around a target site, AND ONLY when the
     inline signature table below is insufficient.
   - On first use of `Satisfies.box_iff_forall` and (if mirrored) `truthLemma_pos`, run
     `lean_hover_info` to confirm elaboration in the current build.
2. **Build truncated, single-module.** Use
   `lake build Cslib.Logics.Modal.Tableau.Completeness 2>&1 | tail -60`. Reserve the whole-library
   `lake build` for Phase 7 (CI).
3. **Per-sub-phase gate**: targeted declarations report NO errors via `lean_diagnostic_messages`; NO
   `sorry` and NO new axioms introduced (5a-5c and 5d in the no-sorry variant must be fully
   sorry-free); commit `task 299 phase 5{x}: …`. The whole-library build already passes from
   soundness, so completeness sub-phases keep `main` green throughout.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 (done) | -- |
| 2 | 2 (done) | 1 |
| 3 | 3 (done) | 2 |
| 4 | 4a, 4b, 4c, 4d (all done) | 3 (soundness chain, completed via tasks 364/384) |
| 5 | 5a | 3 |
| 6 | 5b | 5a |
| 7 | 5c | 5b |
| 8 | 5d | 5c |
| 9 | 6 | 5d |
| 10 | 7 | 6, 4d |

Phases within the same wave can execute in parallel. The soundness chain (Phases 1-4) is COMPLETE
(green at `3660ac0c`) and shown here for the full dependency picture. The completeness chain
(5a → 5b → 5c → 5d → 6) is strictly sequential because each sub-phase consumes the previous one's
declarations from `Completeness.lean`. Phase 7 joins after Phase 6 (and the already-done Phase 4d).

---

### Phase 1: Defs — types, complexity, Lukasiewicz decomposition [COMPLETED]

**Goal**: Establish `Cslib/Logics/Modal/Tableau/Defs.lean` with all foundational definitions the
rest of the procedure consumes.

**Tasks**:
- [x] `Defs.lean` (namespace `Cslib.Logic.Modal.Tableau`); `abbrev WorldIndex := Nat`;
  `Hashable (Proposition Atom)`; `Modal.Proposition.complexity`; Łukasiewicz decomposition functions
  (`negOf?`/`orOf?`/`andOf?`/`impOf?`/`boxOf?`/`diaOf?`) with `@[simp]` reduction lemmas.

**Timing**: 2 hours (sunk)

**Depends on**: none

**Completed**: 2026-06-24 (committed).

---

### Phase 2: Rules — K modal rules + accessibility edges [COMPLETED]

**Goal**: Define the K rule application in `Rules.lean` and `Branch.lean`, with explicit
accessibility-edge tracking that makes box-positive propagation K-sound (not S5).

**Tasks**:
- [x] `Branch.lean`: `Accessibility` (edges list), `empty`/`addEdge`/`successorsOf`/`allWorlds`/
  `hasEdge`, `boxPositivesOf`, `boxPropagation`, world helpers.
- [x] `Rules.lean`: `modalApplyOne` dispatching prop rules + the four K modal cases (`boxPos`/
  `diamondPos`/`boxNeg`/`diamondNeg`) producing `RuleResult` + edge updates; box-positive propagation
  scoped to the edge relation ONLY (K-vs-S5 correctness invariant).

**Timing**: 2.5 hours (sunk)

**Depends on**: 1

**Completed**: 2026-06-24 (committed).

---

### Phase 3: Closure + Saturation — fuel loop and entry point [COMPLETED]

**Goal**: Wire closure and the fuel-based saturation loop, producing the runnable `modalTableau φ`
entry point and the Hintikka predicate completeness needs.

**Tasks**:
- [x] `Closure.lean`: `isModalClosed` (T(⊥) or T(φ)/F(φ) clash); `Saturation.lean`:
  `ModalTableauResult`, `modalStepBranch`, `modalExpandBranches` + `processNext` worklist,
  `modalFuel φ = (4n+4)(n+2)+2` with `termination_by`, world-subset blocking, entry point
  `modalTableau φ`, and `modalHintikkaSet b acc` downward-saturation predicate.

**Timing**: 2.5 hours (sunk)

**Depends on**: 2

**Completed**: 2026-06-24 (committed).

---

### Phase 4: Soundness — modalTableau_sound [COMPLETED]

**Goal**: Prove `modalTableau_sound` against Kripke semantics over all models.

**Status note**: Completed via spawned tasks **364/384**, which decomposed the original oversized
single-shot phase into sub-phases, split `Soundness.lean`, and landed:
- `modalStepBranch_preserves_sat` (per-step satisfiability preservation) — now in
  **`SoundnessStep.lean:187`** (NOT `Soundness.lean`; the v2 plan's declaration map is stale).
- `modalExpandBranches_closed_unsat` (`Soundness.lean:226`) — fuel induction + inner `processNext`
  induction over per-branch `List.Forall₂` accs.
- Reusable `forall₂_*` worklist helpers (`Soundness.lean:156-219`) and `accFreshInv` /
  `accFreshInv_empty` (`SoundnessStep.lean:165/172`), `modalStepBranch_preserves_accFreshInv`
  (`Soundness.lean:110`).
- `modalTableau_sound` discharged; whole-library build GREEN at commit **`3660ac0c`**.

**Tasks**:
- [x] All soundness sub-phases (prop-rule cases, box-positive membership, loop-invariant acc
  threading, main theorem + import re-wire) — done via tasks 364/384.

**Timing**: ~4.75 hours (sunk, across tasks 364/384)

**Depends on**: 3

**Completed**: via tasks 364/384; build green at `3660ac0c`. Not re-planned in v3.

---

### Phase 5a: Skeleton + model extraction + atom reflection + forall₂ refactor [NOT STARTED]

**Goal**: Stand up `Completeness.lean`, define `extractModel`, prove atom-reflection, and hoist the
generic `forall₂_*` helpers into a shared module so completeness never imports `Soundness.lean`.

**Tasks**:
- [ ] **Refactor (preliminary)**: hoist the generic list helpers `forall₂_of_zip_mem`
  (`Soundness.lean:156`), `forall₂_replicate_right` (`:177`), `forall₂_append_aux` (`:197`),
  `forall₂_drop_aux` (`:205`), `forall₂_take_aux` (`:212`) out of `Soundness.lean` into a new
  `Cslib/Logics/Modal/Tableau/LoopInduction.lean` (de-`private` and re-export). Update `Soundness.lean`
  to import them from there. Verify `Soundness.lean` still builds green (no proof changes — pure
  relocation). This lets Phase 6 reuse the plumbing WITHOUT importing the heavy soundness file.
- [ ] Create `Completeness.lean` (namespace `Cslib.Logic.Modal.Tableau`, `import Cslib.Init` + the
  Tableau modules `Defs`/`Branch`/`Rules`/`Closure`/`Saturation`; do NOT import `Soundness`).
- [ ] Define `extractModel` (NEW, ~10 lines — no exact analog because modal `Model` carries BOTH `r`
  and `v`):
  ```
  def extractModel (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
      Model WorldIndex Atom where
    r w w' := acc.hasEdge w w' = true
    v w p  := b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w) = true
  ```
  Use `acc.hasEdge` (the same edge accessor `modalApplyOne`/`modalHintikkaSet` propagate along) so the
  box case's `intro w' hr` aligns with the saturation condition.
- [ ] Prove `extractModel_atom_sat_iff` mirroring temporal
  `extractModel_atom_sat_iff` (`Cslib/Logics/Temporal/Tableau/Completeness.lean:100`, proof
  `simp only [Satisfies.atom_iff, extractModel]`), plus `extractModel_bot_false`.
- [ ] Prove the two "open branch ⇒ no T(⊥), no contradiction" helpers mirroring temporal
  `openBranch_noBotPos` (`…/Temporal/Tableau/Completeness.lean:167`) /
  `openBranch_noContradiction` (`:194`), OR reuse `isModalClosed b = false` directly.

**Reference signatures (inline — do not open the source files)**:
| Item | File:Line | Signature |
|------|-----------|-----------|
| `Model` | `Cslib/Logics/Modal/Basic.lean:63` | `structure Model (World Atom : Type*) where r : World → World → Prop; v : World → Atom → Prop` |
| Temporal `extractModel` | `…/Temporal/Tableau/Completeness.lean:92` | `def extractModel (b) : TemporalModel Nat Atom where valuation t p := b.any fun sf => sf.sign == .pos && sf.label == t && sf.formula == .atom p` |
| Temporal `extractModel_atom_sat_iff` | `…/Temporal/Tableau/Completeness.lean:100` | `lemma … : Satisfies (extractModel b) t (.atom p) ↔ b.any (fun sf => sf.sign == .pos && sf.label == t && sf.formula == .atom p)` |
| `Accessibility.hasEdge` | `Cslib/Logics/Modal/Tableau/Branch.lean:80` | `def hasEdge (acc) (w w') : Bool := acc.edges.any fun (src, tgt) => src == w && tgt == w'` |
| `SignedFormula` | `Cslib/Foundations/Logic/Tableau/SignedFormula.lean:49` | `structure SignedFormula (F L) where sign : Sign; formula : F; label : L` (membership `⟨.pos, φ, w⟩ ∈ b`) |
| `forall₂_*` helpers | `Soundness.lean:156/177/197/205/212` | relocate to `LoopInduction.lean` |

**Optional (additive, keeps 5b/5c clean)**: add `hasEdge_iff_mem_successors` to `Branch.lean` next to
the API (`:80`) relating `acc.hasEdge w w' = true` to membership in `successorsOf`/`edges`.

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/LoopInduction.lean` - new file (hoisted `forall₂_*` helpers)
- `Cslib/Logics/Modal/Tableau/Soundness.lean` - import the hoisted helpers (no proof change)
- `Cslib/Logics/Modal/Tableau/Completeness.lean` - new file (extractModel + atom reflection)
- `Cslib/Logics/Modal/Tableau/Branch.lean` - optional `hasEdge_iff_mem_successors`

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.Completeness` green, ZERO sorry; `Soundness.lean` still
  green after the refactor.
- Commit `task 299 phase 5a: completeness skeleton + extractModel + forall₂ refactor`.

---

### Phase 5b: Per-rule semantic bridge lemmas [NOT STARTED]

**Goal**: Prove the small per-rule bridges the truth lemma consumes, fully encapsulating the
`modalApplyOne` / `modalHintikkaSet` unfolding so the main induction (5c) never re-reads
`Rules.lean` / `Saturation.lean`. **This is the isolation win** — it is where the v2 dispatch had to
read the large Bimodal/Classical files.

**Tasks**:
- [ ] `hintikka_box_pos`: `T(□ψ)@w ∈ b → acc.hasEdge w w' → T(ψ)@w' ∈ b`. **CRITICAL**: derive this
  from the `.persistent` output of `modalApplyOne (T(□ψ)@w) b acc` via the `modalHintikkaSet`
  `.persistent nf => ∀ sf' ∈ nf, sf' ∈ b` clause. `modalHintikkaSet` has NO standalone box
  edge-closure conjunct — box-positive edge-closure is folded into the `.persistent` branch, so the
  generic clause IS the edge-closure condition (see report 03 §5 CRITICAL note).
- [ ] `hintikka_box_neg`: `F(□ψ)@w ∈ b → ∃ w', acc.hasEdge w w' ∧ F(ψ)@w' ∈ b` (the `boxNeg` linear
  rule created the witness edge + `F(ψ)@w'`).
- [ ] `hintikka_imp_pos` / `hintikka_imp_neg`: unpack the branching/linear `modalApplyOne` result via
  the `modalHintikkaSet` `∀ sf ∈ b, match …` clause, mirroring `classicalTruthLemma`'s `imp` handling
  (positive `imp` is branching `[F(a)] ∨ [T(c)]`; consume via `∃ br ∈ branches, ∀ sf' ∈ br, sf' ∈ b`).
- [ ] Diamond is derived (`◇ψ = ¬□¬ψ`); add `hintikka_diamond_*` ONLY if `modalApplyOne` matches the
  diamond shape directly (check `Defs.lean diaOf?`); otherwise the box bridges + `Satisfies.
  diamond_iff_exists` suffice in 5c.

**Reference signatures (inline)**:
| Item | File:Line | Signature |
|------|-----------|-----------|
| Bimodal `sat_box_pos` | `…/Bimodal/…/CountermodelExtraction.lean:549` | `(T(□ψ)@(w,t) ∈ b) → ∀ w', <edge> → ⟨.pos, ψ, ⟨w',t⟩⟩ ∈ b` |
| Bimodal `sat_box_neg` | `…/CountermodelExtraction.lean:589` | `(F(□ψ)@(w,t) ∈ b) → ∃ w', <edge w w'> ∧ ⟨.neg, ψ, ⟨w',t⟩⟩ ∈ b` |
| `modalHintikkaSet` | `Cslib/Logics/Modal/Tableau/Saturation.lean:207` | `def … (b) (acc) : Prop := isModalClosed b = false ∧ ∀ sf ∈ b, let (result, _) := modalApplyOne sf b acc; match result with \| .linear nf => ∀ sf' ∈ nf, sf' ∈ b \| .branching brs => ∃ br ∈ brs, ∀ sf' ∈ br, sf' ∈ b \| .persistent nf => ∀ sf' ∈ nf, sf' ∈ b \| .notApplicable => True` |
| `modalApplyOne` | `Cslib/Logics/Modal/Tableau/Rules.lean:68` | `def modalApplyOne (sf) (b) (acc : Accessibility) : RuleResult (Proposition Atom) WorldIndex × Accessibility` (boxPos/diamondNeg are `.persistent`, Rules.lean:65-67) |
| `Accessibility.successorsOf` | `Branch.lean:70` | `def successorsOf (acc) (w) : List WorldIndex := acc.edges.filterMap fun (src, tgt) => if src == w then some tgt else none` |
| `classicalHintikkaSet` (imp template) | `…/Classical/Completeness.lean:68` | branch-condition `match classicalApplyOne sf with .branching branches => ∃ br ∈ branches, ∀ sf' ∈ br, sf' ∈ b …` |

**Timing**: 1.25 hours

**Depends on**: 5a

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Completeness.lean` - add the `hintikka_*` bridge lemmas

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.Completeness` green, ZERO sorry; each bridge a few lines.
- Commit `task 299 phase 5b: per-rule semantic-bridge lemmas`.

---

### Phase 5c: Main truth lemma modalTruthLemma [NOT STARTED]

**Goal**: Prove the modal truth lemma as ONE conjunction lemma (classical shape), kept thin by
calling only the 5b bridges.

**Tasks**:
- [ ] Prove, by `induction φ generalizing w` (the `generalizing` is MANDATORY — the box case needs
  the IH at the successor world `w'`):
  ```
  lemma modalTruthLemma (b) (acc) (hH : modalHintikkaSet b acc) :
      ∀ (φ : Proposition Atom) (w : WorldIndex),
        (<T(φ)@w ∈ b> → Satisfies (extractModel b acc) w φ) ∧
        (<F(φ)@w ∈ b> → ¬ Satisfies (extractModel b acc) w φ)
  ```
- [ ] This is a SINGLE conjunction lemma proving `pos ∧ neg` simultaneously — do NOT split by sign.
  Justification (report 03 §Justification): modal K's `imp`-positive is branching Łukasiewicz whose
  `[F(a)]` sub-branch needs the *negative* IH of `a`, and `imp`-negative needs the *positive* IH of
  `a` plus the negative IH of `c`; the directions are mutually recursive, so they live in one
  `induction φ`. (Bimodal's two separate `truthLemma_pos`/`truthLemma_neg` theorems work only because
  its T(imp) is always expanded — `imp`-pos is `exfalso`; this does NOT hold for K.)
- [ ] Cases:
  - `atom p`: pos → `extractModel_atom_sat_iff` gives valuation `true`; neg → if T(atom p) also
    present the branch is closed, contradicting `isModalClosed b = false`.
  - `bot`: pos → T(⊥) ⇒ closed ⇒ contradiction; neg → `Satisfies … bot = False` by simp.
  - `imp a c` (with `ih_a ih_c`): use `hintikka_imp_pos`/`hintikka_imp_neg` (5b) to unpack the
    branch condition, case on which branch is present, apply IHs.
  - `box ψ`: pos → `intro w' hr` (`Satisfies.box_iff_forall` is `Iff.rfl`, so the box goal is
    literally `∀ w', m.r w w' → …`); `m.r w w'` is `acc.hasEdge w w' = true`; apply `hintikka_box_pos`
    to get `T(ψ)@w' ∈ b`, then the world-generalized IH at `w'`. neg → `hintikka_box_neg` gives a
    witness `w'` with `F(ψ)@w'`; apply the IH at `w'`.
  - diamond via `Satisfies.diamond_iff_exists` (or the derived `◇ = ¬□¬` shape).

**Reference signatures (inline)**:
| Item | File:Line | Signature |
|------|-----------|-----------|
| `classicalTruthLemma` (shape template) | `…/Classical/Completeness.lean:84` | `lemma … (b) (hH : classicalHintikkaSet b) (φ) : (b.any (·.sign==.pos && ·.formula==φ) → BoolEvaluate (extractValuation b) φ = true) ∧ (b.any (·.sign==.neg …) → … = false)` — single conjunction, `induction φ` |
| Bimodal `truthLemma_pos` (box-pos case L914-920) | `…/CountermodelExtraction.lean:895` | box: `simp only [branchTruth]; intro w' hw'; have hbox := sat_box_pos …; exact ih w' t (hbox w' hw')` |
| Bimodal `truthLemma_neg` (box-neg case L957-964) | `…/CountermodelExtraction.lean:934` | box: `intro h; have ⟨w', hw'mem, hw'neg⟩ := sat_box_neg …; exact (ih w' t hw'neg) (h w' …)` |
| `Satisfies` | `Basic.lean:145` | `\| .box φ => ∀ w', m.r w w' → Satisfies m w' φ` |
| `Satisfies.box_iff_forall` | `Basic.lean:235` | `⇓Modal[m,w ⊨ □φ] ↔ ∀ w', m.r w w' → ⇓Modal[m,w' ⊨ φ] := Iff.rfl` (`@[scoped grind =]`) |
| `Satisfies.diamond_iff_exists` | `Basic.lean:241` | `⇓Modal[m,w ⊨ ◇φ] ↔ ∃ w', m.r w w' ∧ ⇓Modal[m,w' ⊨ φ]` (`@[scoped grind =]`) |

**Timing**: 1.5 hours

**Depends on**: 5a, 5b

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Completeness.lean` - the `modalTruthLemma` conjunction lemma

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.Completeness` green, **ZERO sorry** (the truth lemma itself
  must be sorry-free — this is the deliverable that previously overflowed).
- Commit `task 299 phase 5c: modalTruthLemma (single conjunction lemma)`.

---

### Phase 5d: Countermodel wrapper + reduced completeness statement [NOT STARTED]

**Goal**: Build the open-branch countermodel wrapper and reduce `modalTableau_complete` to the single
Phase-6 dependency, keeping the committed tree sorry-free.

**Tasks**:
- [ ] `modalOpenBranch_countermodel`: a `modalHintikkaSet b acc` branch yields `extractModel b acc`
  refuting `φ` — apply `modalTruthLemma … .2` (the negative conjunct) to the initial `F(φ)@0`
  membership. Mirror classical `classicalOpenBranch_countermodel` (`…/Classical/Completeness.lean:1299`).
- [ ] **PREFERRED no-sorry variant**: stop 5d at `modalOpenBranch_countermodel` and defer
  `modalTableau_complete` wholesale to Phase 6. This keeps the committed tree sorry-free per the CSLib
  hard rule. (The alternative — stating `modalTableau_complete := <proof calling
  modalExpandBranches_hintikka>` with the loop invariant as a `theorem … := by sorry` marked TODO
  Phase 6 — introduces a temporary `sorry` and is NOT preferred.)

**Reference signatures (inline)**:
| Item | File:Line | Signature |
|------|-----------|-----------|
| `classicalOpenBranch_countermodel` | `…/Classical/Completeness.lean:1299` | apply truth lemma `.2` to initial `F(φ)` membership ⇒ countermodel refutes φ |
| `classicalTableau_complete` | `…/Classical/Completeness.lean:1328` | reduced completeness statement template |

**Timing**: 0.5 hours

**Depends on**: 5c

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Completeness.lean` - `modalOpenBranch_countermodel`

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.Completeness` green; the ONLY outstanding obligation is
  `modalExpandBranches_hintikka` (Phase 6). Committed tree sorry-free (no-sorry variant).
- Commit `task 299 phase 5d: open-branch countermodel wrapper`.

---

### Phase 6: Completeness loop invariant + final completeness [NOT STARTED]

**Goal**: Prove `modalExpandBranches_hintikka` (returned open branch is a Hintikka set) and discharge
`modalTableau_complete` fully — the dominant remaining risk, but de-risked by the 384/364 soundness
infra.

**Intended statement** (to prove):
```
theorem modalExpandBranches_hintikka (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility) (b) (acc : Accessibility),
      <length invariants> →
      modalExpandBranches branches expandedSets accs fuel = .openBranch b acc →
      modalHintikkaSet b acc
```

**Tasks**:
- [ ] Mirror `modalExpandBranches_closed_unsat` (`Soundness.lean:226`) for the acc-threading: fuel
  induction + inner `processNext` induction over per-branch `List.Forall₂` accs, reusing the
  `forall₂_*` helpers (now in `LoopInduction.lean` from the 5a refactor) and `accFreshInv`. This is
  the previously-hard plumbing that tasks 384/364 already solved for the closed direction.
- [ ] Mirror `classicalExpandBranches_hintikka` (`…/Classical/Completeness.lean:924`) for the
  open/Hintikka logic.
- [ ] Add the genuinely-new saturation-characterisation lemma: when `modalStepBranch b e a = none`
  (saturated, returns `.openBranch b a`), prove `modalHintikkaSet b a` ("no applicable rule fired" ⇒
  "every rule's outputs already present"). Use classical
  `classicalStepBranch_none_saturated` (`…/Classical/Completeness.lean:694`) and
  `classicalStepBranch_hintikka_inv` (`:722`) as the proof PATTERN (they are Unit-label-specific, so
  reference only — no code reuse).
- [ ] Handle the world-creation interleaving (box-pos re-firing as new successors appear). The fuel
  bound `modalFuel φ` (`Saturation.lean:89`, `(4n+4)(n+2)+2`) should suffice; adjust in
  `Saturation.lean` ONLY if the invariant proof exposes a concrete gap.
- [ ] Discharge `modalTableau_complete` fully (contrapositive: open ⇒ Hintikka ⇒ countermodel via
  `modalOpenBranch_countermodel`). Remove any temporary sorry. Run
  `#print axioms modalTableau_complete`.

**Reusable infra (inline)**:
| Item | File:Line | Role |
|------|-----------|------|
| `modalExpandBranches_closed_unsat` | `Soundness.lean:226` | acc-threading structural template (fuel + inner `processNext` induction, L256-385) |
| `forall₂_*` helpers | `LoopInduction.lean` (hoisted in 5a) | worklist plumbing |
| `accFreshInv` / `accFreshInv_empty` | `SoundnessStep.lean:165/172` | freshness invariant |
| `modalStepBranch` / `modalExpandBranches` / `.processNext` | `Saturation.lean:99/135/149` | recursion being inducted over |
| `classicalExpandBranches_hintikka` | `…/Classical/Completeness.lean:924` | open/Hintikka logic template |
| `classicalStepBranch_none_saturated` / `_hintikka_inv` | `…/Classical/Completeness.lean:694/722` | saturation-characterisation pattern (reference only) |

**Timing**: 3 hours (may need 1-2 dispatches; ~200-400 lines)

**Depends on**: 5d

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Completeness.lean` - loop invariant + finalize `modalTableau_complete`
- `Cslib/Logics/Modal/Tableau/Saturation.lean` - possible fuel-bound adjustment ONLY if required

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.Completeness` green, ZERO sorry.
- `#print axioms modalTableau_complete` shows only standard axioms (no new axioms).
- Commit `task 299 phase 6: completeness loop invariant + modalTableau_complete`.

**Contingency (zero-debt fallback)**: if the world-creation interleaving cannot close in one genuine
attempt, keep 5a-5d committed sorry-free, mark Phase 6 [BLOCKED] with the precise residual obligation,
and `/spawn` a follow-up. Never ship `sorry` or new axioms (CSLib hard requirement). The soundness
direction and the truth lemma are independently shippable.

---

### Phase 7: Decision procedure, barrel, and CI verification [NOT STARTED]

**Goal**: Package the iff + `Decidable` instance, add the module barrel, remove any temporary sorry,
confirm `#print axioms` shows no new axioms, and pass the full CSLib CI pipeline with zero sorry.

**Tasks**:
- [ ] In `Completeness.lean` (or a small `DecisionProcedure` section), prove
  `modalTableau_decides : modalTableau φ = .closed ↔ <φ valid over all models>` from
  `modalTableau_sound` + `modalTableau_complete`, and provide a `Decidable` instance via
  `isTrue`/`isFalse` (requires only `DecidableEq + Hashable`, no `Fintype Atom`).
- [ ] Confirm NO temporary `sorry` remains anywhere under `Cslib/Logics/Modal/Tableau/` (grep clean).
- [ ] `#print axioms modalTableau_sound`, `modalTableau_complete`, `modalTableau_decides` — confirm
  only standard axioms (no new axioms).
- [ ] Add module-level doc comments and the barrel/import-aggregator (`lake exe mk_all --module` or
  the appropriate import root per ORGANISATION.md) so the tableau modules (including the new
  `LoopInduction.lean` and `Completeness.lean`) are reachable.
- [ ] Run the full CI pipeline and fix any violations: `lake build`, `lake test`,
  `lake exe checkInitImports`, `lake exe lint-style`,
  `lake shake --add-public --keep-implied --keep-prefix`.

**Timing**: 1.5 hours

**Depends on**: 6, 4d (done)

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Completeness.lean` - decision procedure iff + `Decidable` instance
- barrel/import file under `Cslib/` as required by ORGANISATION.md

**Verification**:
- All CI commands exit 0.
- `#print axioms modalTableau_decides` shows only standard axioms.
- No `sorry` anywhere under `Cslib/Logics/Modal/Tableau/` (grep clean).
- Commit `task 299 phase 7: decision procedure + barrel + CI green`.

---

## Testing & Validation

- [ ] `lake build` of all `Cslib/Logics/Modal/Tableau/*.lean` files succeeds (Defs, Branch, Rules,
  Closure, Saturation, SoundnessStep, Soundness, LoopInduction, Completeness).
- [ ] `lake test` (CslibTests) passes.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake exe lint-style` passes.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no issues.
- [ ] Zero `sorry` and zero new axioms across the directory (grep + `#print axioms` on
  `modalTableau_sound`, `modalTableau_complete`, `modalTableau_decides`).
- [ ] Smoke `#eval`: K-valid `□(p ⟶ q) ⟶ (□p ⟶ □q)` returns `closed`; K-invalid `□p ⟶ p` returns an
  open branch with a refuting countermodel.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Tableau/Defs.lean` (Phase 1, done)
- `Cslib/Logics/Modal/Tableau/Branch.lean` (Phase 2, done; optional 5a `hasEdge_iff_mem_successors`)
- `Cslib/Logics/Modal/Tableau/Rules.lean` (Phase 2, done)
- `Cslib/Logics/Modal/Tableau/Closure.lean` (Phase 3, done)
- `Cslib/Logics/Modal/Tableau/Saturation.lean` (Phase 3, done; possible Phase 6 fuel-bound tweak)
- `Cslib/Logics/Modal/Tableau/SoundnessStep.lean` (Phase 4, done via tasks 364/384)
- `Cslib/Logics/Modal/Tableau/Soundness.lean` (Phase 4, done via tasks 364/384; 5a hoist of `forall₂_*`)
- `Cslib/Logics/Modal/Tableau/LoopInduction.lean` (Phase 5a, new — hoisted `forall₂_*` helpers)
- `Cslib/Logics/Modal/Tableau/Completeness.lean` (Phases 5a-7)
- barrel/import file per ORGANISATION.md (Phase 7)
- `modalTableau`, `modalTableau_sound` (done), `modalTableau_complete`, `modalTableau_decides`, and a
  `Decidable` instance.

## Rollback/Contingency

- Soundness (Phases 1-4) is committed and green at `3660ac0c`; it is not touched except for the
  pure-relocation `forall₂_*` hoist in 5a (revert by moving the helpers back and dropping the import).
- All completeness work is additive in the new files `LoopInduction.lean` + `Completeness.lean`;
  rollback = remove those files (and the barrel entry) and revert the 5a hoist.
- Each completeness sub-phase commits incrementally at a green, zero-sorry milestone
  (`task 299 phase 5{a,b,c,d}`, `phase 6`, `phase 7`); the whole-library build stays green throughout
  because soundness is already done and completeness is import-isolated.
- If Phase 6 (loop invariant) stalls, apply the zero-debt fallback documented there: spawn a follow-up
  task for the invariant, keep the sorry-free 5a-5d committed, and mark task 299 `[BLOCKED]`/`[PARTIAL]`.
  Never commit `sorry` or new axioms (CSLib hard requirement).
