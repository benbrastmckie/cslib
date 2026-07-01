# Implementation Plan: Task #299 (Revised, v5)

- **Task**: 299 - Modal K Tableau Decision Procedure
- **Status**: [BLOCKED] (Phase 6 — modal expansion-measure / fuel-sufficiency infrastructure missing; Phase 5c truth lemma delivered GREEN + committed sorry-free)
- **Effort**: Phases 1-4 (soundness) done; Phase 5a/5b/5c/5d (completeness truth lemma) done + GREEN; Phase 6 BLOCKED (research-level measure proof, ~1 dedicated task); Phase 7 (decision procedure + CI) NOT STARTED, gated on Phase 6
- **Dependencies**: None
- **Research Inputs**: reports/01_modal-k-tableau-research.md; reports/03_completeness-decomposition.md; reports/04_truth-lemma-architecture.md
- **Artifacts**: plans/05_modal-k-tableau-plan.md (this file); supersedes plans/04_modal-k-tableau-plan.md
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/plan-format-enforcement.md
  - CSLib CONTRIBUTING.md (zero-sorry / zero-new-axiom)
- **Type**: cslib

## Overview

Implement a sound and complete tableau decision procedure for basic modal logic K under
`Cslib/Logics/Modal/Tableau/`, instantiating the label-generic CSLib Foundations tableau layer with
`F = Cslib.Logic.Modal.Proposition Atom` and `L = WorldIndex` (Nat). Soundness is DONE and green;
the completeness skeleton, model extraction, box-bridge lemmas, and countermodel wrapper are DONE and
green. This revision (v4) exists for ONE reason: the previously-planned completeness path is
**blocked by a proof-architecture flaw** — `hintikka_imp_pos` / `hintikka_imp_neg` are unprovable as
stated, so the truth lemma must be restructured. Definition of done: `modalTableau_complete` and
`modalTableau_decides` proved with ZERO sorry and ZERO new axioms, full CSLib CI green.

### Research Integration

This v4 revision integrates the new report **`reports/04_truth-lemma-architecture.md`** (strong-
induction truth-lemma architecture), confirmed against current source and the
`.orchestrator-handoff.json` blocker note. How it resolves the prior blocker:

- **Root cause (confirmed).** The modal `Proposition` is purely Łukasiewicz (`atom`, `bot`, `imp`,
  `box` only). and/or/neg are *encoded* as nested `imp`: `¬a = imp a bot`, `a∨c = imp (imp a bot) c`,
  `a∧b = imp (imp a (imp b bot)) bot`. `modalApplyOne` runs `tryAllPropRules` in fixed order
  `[andPos, andNeg, orPos, orNeg, impPos, impNeg, negPos, negNeg]` and returns the FIRST applicable
  rule. So `T((a'→(b'→⊥))→⊥)` fires `andPos` and yields `.linear [T(a')@w, T(b')@w]` — **neither
  `F(a)@w` nor `T(c)=T(⊥)`**. The old `hintikka_imp_pos` claimed `F(a)@w ∈ b ∨ T(c)@w ∈ b` for
  *every* `T(imp a c)@w`, which is genuinely false for conjunction/disjunction encodings. Since
  `modalTruthLemma` called the bridge uniformly for every `imp`, the factoring is unsound (the 15
  build errors in the handoff). The plan v3 `imp` bridges (Phase 5b) are therefore deleted.
- **Why structural induction cannot be patched (the real blocker).** Closing the conjunction leaf
  needs `Satisfies w a'` and `Satisfies w b'` from `T(a')@w`, `T(b')@w` — i.e. the truth-lemma IH at
  the *grandchildren* `a'`, `b'`, which `induction φ` over `Proposition` never supplies (it gives IH
  only at the immediate children `a`, `c`). Disjunction likewise needs IH at `a''`, a subterm of the
  antecedent. So v3's plan to keep `induction φ` as a single conjunction lemma cannot work either.
- **Resolution — adopt report 04 option (b): strong induction + inlined connective case analysis.**
  Convert `modalTruthLemma` to STRONG induction on `sizeOf φ` via a size-bounded helper
  `modalTruthLemma_aux` (IH available for every strictly-smaller subformula `a', b', a'', c, a`), and
  inline the four-shape connective dispatch (conjunction / disjunction / proper-imp / negation) for
  both polarities directly in the `imp` case. **Keep `hintikka_box_pos` / `hintikka_box_neg`
  unchanged** (□ is primitive; both are correct and green). **Delete** `hintikka_imp_pos` /
  `hintikka_imp_neg`; their mechanics (extract `hcond`, unfold `modalApplyOne`, pull members) migrate
  into the new leaves. Two verified mechanical sub-fixes (add `Option.getD_some` to the imp unfolding
  simp set; write `List.mem_cons_self` with NO explicit args) carry into the proper-imp / negation
  leaves. This restructure is contained entirely in Phase 5c — Phases 6 and 7 are unchanged.

Prior reports remain integrated: `reports/01` (reuse Foundations layer, classical/Bimodal templates,
K-vs-S5 box-rule correctness) and `reports/03` (per-rule bridge isolation, the corrected declaration
map, the `forall₂_*` hoist for Phase 6). Reports integrated: see `reports_integrated` in metadata.

### Prior Plan Reference

Supersedes `plans/04_modal-k-tableau-plan.md` (v3). Phases 1-4 (soundness, green at `3660ac0c` via
tasks 364/384) and the green completeness pieces (5a skeleton/extractModel/atom-reflection/closure
helpers; 5b box bridges; 5d countermodel wrapper) are carried over as [COMPLETED] and not re-planned.
Only the truth lemma (Phase 5c) is restructured per report 04; Phases 6-7 are retained and refined.

### Roadmap Alignment

`specs/ROADMAP.md` exists but no roadmap update flag was provided; this plan does not add roadmap
phases and does not modify ROADMAP.md. Task 299 is part of the modal/temporal tableau series
(299-301); completing it advances the Modal Logic decidability line.

## Goals & Non-Goals

**Goals**:
- A `modalTableau φ` decision procedure for modal K returning `closed` or an open branch.
- `modalTableau_sound`: closed result ⇒ φ valid over all Kripke models. **(DONE, Phase 4.)**
- `modalTableau_complete`: open result yields a finite Kripke countermodel refuting φ. (Phases 5c-6.)
- `modalTableau_decides` iff + a `Decidable` instance (no `Fintype Atom` requirement). (Phase 7.)
- All files under `Cslib/Logics/Modal/Tableau/` build with ZERO `sorry` and ZERO new axioms; full
  CSLib CI pipeline green.

**Non-Goals**:
- Any modal system beyond K (no T/D/4/5/B/S4/S5 frame conditions).
- Optimised/performant saturation; fuel-based correctness suffices.
- Reusing or modifying the Bimodal/Classical/Propositional tableau code in place (reference only).
- A canonical-model / Lindenbaum completeness proof (countermodel extraction is the route).
- Re-planning soundness (Phases 1-4) or the green completeness pieces (5a/5b-box/5d).
- Reviving the `imp` bridge-lemma factoring — it is unprovable and is deleted, not repaired.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Strong-induction `sizeOf` bound obligations (`sizeOf ψ ≤ n`) cause `termination`/`omega` friction | M | M | Use the size-bounded `modalTruthLemma_aux` form (report 04 §4.2), not `termination_by`; discharge subformula bounds with `simp only [Proposition.imp.sizeOf_spec, …] at hsz ⊢; omega` |
| Implementer re-splits the truth lemma by sign or reverts to `induction φ` | H | M | Phase 5c mandates ONE size-indexed `induction n` proving `pos ∧ neg` together; report 04 §2 justification inlined (conj/disj need deep IH) |
| `imp` case dispatch matches the wrong encoded shape | H | M | Exact four-shape dispatch table (andPos/orPos/impPos/negPos and andNeg/orNeg/impNeg/negNeg) inlined from report 04 §4.3; classifier `@[simp]` lemmas `modalAndOf?/modalOrOf?/modalImpOf?/modalNegOf?` reused |
| `hcond` stays stuck after unfolding `modalApplyOne` | M | M | Add `Option.getD_some` to the imp unfolding simp set (verified fix #1, report 04 §4.4) |
| `List.mem_cons_self _ _` fails to elaborate | M | M | Write `List.mem_cons_self` with NO explicit args (verified fix #2, report 04 §4.4) |
| Phase 6 loop invariant (`modalExpandBranches_hintikka`) cannot be closed | H | M | Reuse 384/364 infra (`modalExpandBranches_closed_unsat`, `forall₂_*`, `accFreshInv`); zero-debt fallback: keep 5c committed sorry-free, mark Phase 6 [BLOCKED], `/spawn` follow-up; never ship sorry/axioms |
| `Completeness.lean` pulls heavy `Soundness.lean` via the `forall₂_*` helpers | M | M | Phase 6 prerequisite: hoist `forall₂_*` into a shared `LoopInduction.lean` so completeness reuses them without importing soundness |
| Concurrent sessions clobber WIP `Completeness.lean` | M | M | Serialize sessions or use a git worktree; commit each green milestone immediately |

**Environment hazard**: multiple concurrent Claude sessions share this one checkout; a sibling
`git add -A` previously swept WIP into an unrelated commit. Serialize sessions or use separate git
worktrees before resuming. All remaining work is in `Completeness.lean` (plus the small
`LoopInduction.lean` hoist in Phase 6), disjoint from any green soundness file.

## Context-Budget Protocol (MANDATORY for every remaining sub-phase)

The reference files are large. Implementation agents MUST NOT bulk-read them — the load-bearing
fragments are inlined below. For every remaining phase:

1. **Navigate, do not bulk-read.** Use lean-lsp: `lean_file_outline` to locate declarations;
   `lean_diagnostic_messages` for the authoritative current error set; `lean_goal` + `lean_hover_info`
   at a targeted line to inspect proof state; `lean_multi_attempt` to test a tactic without editing.
   `Read` with `offset`/`limit` for only ±40 lines around a target, and ONLY when the inline material
   is insufficient.
2. **Build truncated, single-module**: `lake build Cslib.Logics.Modal.Tableau.Completeness 2>&1 | tail -60`.
   Reserve the whole-library `lake build` for Phase 7 (CI).
3. **Per-phase gate**: targeted declarations report NO errors via `lean_diagnostic_messages`; NO
   `sorry` and NO new axioms; `grep -rn 'sorry\|admit\|^axiom' Cslib/Logics/Modal/Tableau/` empty;
   commit `task 299 phase 5{x}: …`. The whole-library build already passes from soundness.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 (done) | -- |
| 2 | 2 (done) | 1 |
| 3 | 3 (done) | 2 |
| 4 | 4 (done) | 3 |
| 5 | 5a (done) | 3 |
| 6 | 5b (done) | 5a |
| 7 | 5c | 5a, 5b |
| 8 | 5d (done) | 5c (statement only; wrapper already compiles against the restated lemma) |
| 9 | 6 | 5c, 5d |
| 10 | 7 | 6 |

Phases 1-4 (soundness) and 5a/5b/5d (green completeness pieces) are COMPLETE and shown for the full
dependency picture. The only remaining critical-path completeness work is the Phase 5c truth-lemma
restructure, then Phase 6 (loop invariant) and Phase 7 (decision procedure + CI). 5d's
`modalOpenBranch_countermodel` already compiles and consumes the public `modalTruthLemma` statement,
which is preserved by the restructure (only its proof body changes), so 5d needs no rework.

---

### Phase 1: Defs — types, complexity, Lukasiewicz decomposition [COMPLETED]

**Goal**: `Cslib/Logics/Modal/Tableau/Defs.lean` with all foundational definitions.

**Tasks**:
- [x] `Defs.lean`: `abbrev WorldIndex := Nat`; `Hashable (Proposition Atom)`; `complexity`;
  Łukasiewicz classifiers `modalNegOf?`/`modalOrOf?`/`modalAndOf?`/`modalImpOf?`/`boxOf?`/`diaOf?`
  with `@[simp]` reduction lemmas.

**Timing**: 2 hours (sunk)

**Depends on**: none

**Completed**: 2026-06-24.

---

### Phase 2: Rules — K modal rules + accessibility edges [COMPLETED]

**Goal**: K rule application in `Rules.lean` + `Branch.lean` with accessibility-edge tracking
(K-sound box-positive propagation, not S5).

**Tasks**:
- [x] `Branch.lean`: `Accessibility`, `empty`/`addEdge`/`successorsOf`/`allWorlds`/`hasEdge`,
  `boxPositivesOf`, `boxPropagation`.
- [x] `Rules.lean`: `modalApplyOne` dispatching prop rules + the four K modal cases; box-positive
  propagation scoped to the edge relation ONLY.

**Timing**: 2.5 hours (sunk)

**Depends on**: 1

**Completed**: 2026-06-24.

---

### Phase 3: Closure + Saturation — fuel loop and entry point [COMPLETED]

**Goal**: Closure + fuel-based saturation loop, `modalTableau φ` entry point, Hintikka predicate.

**Tasks**:
- [x] `Closure.lean`: `isModalClosed`; `Saturation.lean`: `ModalTableauResult`, `modalStepBranch`,
  `modalExpandBranches` + `processNext` worklist, `modalFuel φ = (4n+4)(n+2)+2` with `termination_by`,
  entry point `modalTableau φ`, `modalHintikkaSet b acc`.

**Timing**: 2.5 hours (sunk)

**Depends on**: 2

**Completed**: 2026-06-24.

---

### Phase 4: Soundness — modalTableau_sound [COMPLETED]

**Goal**: `modalTableau_sound` against Kripke semantics over all models.

**Status note**: Completed via spawned tasks **364/384** which split `Soundness.lean` and landed
`modalStepBranch_preserves_sat` (**`SoundnessStep.lean:187`**), `modalExpandBranches_closed_unsat`
(`Soundness.lean:226`), the reusable `forall₂_*` worklist helpers (`Soundness.lean:156-219`), and
`accFreshInv`/`accFreshInv_empty` (`SoundnessStep.lean:165/172`). `modalTableau_sound` discharged;
whole-library build GREEN at commit **`3660ac0c`**.

**Tasks**:
- [x] All soundness sub-phases — done via tasks 364/384.

**Timing**: ~4.75 hours (sunk)

**Depends on**: 3

**Completed**: via tasks 364/384; build green at `3660ac0c`.

---

### Phase 5a: Skeleton + model extraction + atom reflection + closure helpers [COMPLETED]

**Goal**: Stand up `Completeness.lean`, define `extractModel`, prove atom-reflection and the
open-branch closure helpers.

**Status note**: GREEN per `.orchestrator-handoff.json`. `Completeness.lean` exists (imports
`Defs`/`Branch`/`Rules`/`Closure`/`Saturation`, not `Soundness`); `extractModel`,
`extractModel_atom_sat_iff` / `extractModel_bot_false`, and `openBranch_noTBot` /
`openBranch_noContradiction` all compile sorry-free. (`Branch.findContradiction b` dot-notation fix
applied — `Branch` is an abbrev for `List`, so `b.findContradiction` misresolved.)

**Tasks**:
- [x] `Completeness.lean` skeleton + `extractModel` (`r w w' := acc.hasEdge w w' = true`;
  `v w p := b.any (sign=.pos ∧ formula=.atom p ∧ label=w)`).
- [x] `extractModel_atom_sat_iff`, `extractModel_bot_false`.
- [x] `openBranch_noTBot`, `openBranch_noContradiction`.

**Timing**: 1 hour (sunk)

**Depends on**: 3

**Completed**: green, committed; zero sorry.

---

### Phase 5b: Box bridge lemmas [COMPLETED]

**Goal**: The per-rule box bridges the truth lemma consumes (□ is primitive).

**Status note**: GREEN. `hintikka_box_pos` (`Completeness.lean:~140`) fixed and committed
(`8ccdf6e9`); `hintikka_box_neg` (`~189`) green. Both derive from the `.persistent` (box-pos) /
linear-witness (box-neg) output of `modalApplyOne` via the `modalHintikkaSet` clause — there is NO
standalone box edge-closure conjunct (it is folded into `.persistent`).

**Tasks**:
- [x] `hintikka_box_pos`: `T(□ψ)@w ∈ b → acc.hasEdge w w' → T(ψ)@w' ∈ b`.
- [x] `hintikka_box_neg`: `F(□ψ)@w ∈ b → ∃ w', acc.hasEdge w w' ∧ F(ψ)@w' ∈ b`.

**Note (carried into Phase 5c)**: the two **imp** bridges `hintikka_imp_pos` (`~204`) /
`hintikka_imp_neg` (`~284`) are UNPROVABLE as stated (report 04 §1) and are DELETED in Phase 5c, not
repaired. The box bridges stay untouched.

**Timing**: 1.25 hours (sunk)

**Depends on**: 5a

**Completed**: box bridges green, committed.

---

### Phase 5c: Truth lemma restructure — strong induction (modalTruthLemma) [COMPLETED]

**Goal**: Replace the blocked structural-induction truth lemma. Delete the two unprovable `imp`
bridges and prove `modalTruthLemma` via STRONG induction on `sizeOf φ`, inlining the connective case
analysis for the `imp` case. This is the core of the v4 revision and the entire remaining blocker.

**Tasks**:
- [x] **Delete** `hintikka_imp_pos` and `hintikka_imp_neg` from `Completeness.lean`; confirm no
  remaining references (`grep -n hintikka_imp Cslib/Logics/Modal/Tableau/Completeness.lean` empty).
- [x] Introduce the size-bounded helper `modalTruthLemma_aux` (report 04 §4.2):
  ```lean
  private lemma modalTruthLemma_aux
      (b : List (SignedFormula (Proposition Atom) WorldIndex))
      (acc : Accessibility) (hH : modalHintikkaSet b acc) :
      ∀ (n : ℕ) (φ : Proposition Atom), sizeOf φ ≤ n → ∀ (w : WorldIndex),
        (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModel b acc) w φ) ∧
        (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModel b acc) w φ) := by
    intro n
    induction n with
    | zero => intro φ hsz w; exact absurd hsz (by cases φ <;> simp <;> omega)
    | succ n ih =>
      intro φ hsz w
      cases φ with
      | atom p => …   -- as current atom case (w unused)
      | bot   => …   -- as current bot case
      | box ψ => …   -- as current box case, but IH via `ih ψ (by simp_all; omega) w'`
      | imp a c => …  -- NEW connective dispatch, below
  ```
  Then keep the PUBLIC statement unchanged so `modalOpenBranch_countermodel` (5d) still compiles:
  ```lean
  lemma modalTruthLemma (b) (acc) (hH : modalHintikkaSet b acc) :
      ∀ (φ : Proposition Atom) (w : WorldIndex),
        (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModel b acc) w φ) ∧
        (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModel b acc) w φ) :=
    fun φ w => modalTruthLemma_aux b acc hH (sizeOf φ) φ le_rfl w
  ```
  Discharge each `sizeOf ψ ≤ n` obligation from `hsz : sizeOf φ ≤ n+1` via
  `simp only [Proposition.imp.sizeOf_spec, …] at hsz ⊢; omega` (every strict subformula is strictly
  smaller). For `atom`/`bot`/`box`, port the current case bodies (they only ever use child IH).
- [x] **`imp a c` POSITIVE leaf** (`T(imp a c)@w ∈ b → Satisfies M w (imp a c)`, `M := extractModel b acc`).
  Open with the shared extraction: `have hcond := (hH.2.1) ⟨.pos, .imp a c, w⟩ hmem`; unfold with
  `simp only [modalApplyOne, tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?, modalImpOf?,
  modalNegOf?, RuleResult.isApplicable, Option.getD_some] at hcond` (**`Option.getD_some` is
  mandatory**, verified fix #1). Dispatch by `cases c` then `cases a` (or `split_ifs` on the
  classifier `if`s) in `modalApplyOne` priority order `andPos > orPos > impPos > negPos`:
  1. **Conjunction** `a = imp a' (imp b' bot)`, `c = bot` → `andPos` `.linear [T(a')@w, T(b')@w]`.
     Pull both members (`hcond _ List.mem_cons_self`, etc.), get `Satisfies M w a' := (ih a' _ w).1 …`
     and `Satisfies M w b'` via **deep IH**; close the reduced goal
     `(Sat a' → Sat b' → False) → False` with `fun h => h ‹Sat a'› ‹Sat b'›`.
  2. **Disjunction** `a = imp a'' bot` → `orPos` `.branching [[T(a'')@w],[T(c)@w]]`.
     `obtain ⟨br, hbr_mem, hbr⟩ := hcond; rcases hbr_mem`; branch `[T(a'')]` uses deep IH
     `(ih a'' _ w).1`, branch `[T(c)]` uses child IH `(ih c _ w).1`.
  3. **Proper imp** `c ≠ bot`, `a ≠ imp _ bot` → `impPos` `.branching [[F(a)@w],[T(c)@w]]`.
     `[F(a)]` → `(ih a _ w).2`; `[T(c)]` → `(ih c _ w).1` (child IH only).
  4. **Negation** `c = bot`, `a` not and-shape and not `imp _ bot` → `negPos` `.linear [F(a)@w]`.
     `(ih a _ w).2`; close `Sat a → False`. (Note `T(◇φ)=T(¬□¬φ)` lands here with `a = □(φ→⊥)`.)
- [x] **`imp a c` NEGATIVE leaf** (`F(imp a c)@w ∈ b → ¬Satisfies M w (imp a c)`), same shape split,
  priority `andNeg > orNeg > impNeg > negNeg`:
  1. **Conjunction** → `andNeg` `.branching [[F(a')@w],[F(b')@w]]`; deep IH `(ih a' _ w).2` /
     `(ih b' _ w).2`; close `¬Satisfies M w (a'∧b')`.
  2. **Disjunction** → `orNeg` `.linear [F(a'')@w, F(c)@w]`; deep IH `(ih a'' _ w).2`, child IH
     `(ih c _ w).2`.
  3. **Proper imp** → `impNeg` `.linear [T(a)@w, F(c)@w]`; `(ih a _ w).1`, `(ih c _ w).2`; close
     `¬(Sat a → Sat c)` with `fun hf => absurd (hf ‹Sat a›) ‹¬Sat c›`.
  4. **Negation** → `negNeg` `.linear [T(a)@w]`; `(ih a _ w).1`; close `¬(Sat a → False)`.
- [x] Throughout, write `List.mem_cons_self` with **NO explicit args** (verified fix #2); build
  `any`-witnesses with `List.any_eq_true.mpr ⟨_, hmem_fact, by simp [SignedFormula.pos]⟩` (the
  existing idiom from the box bridges). Reuse the `@[simp]` classifiers, not re-derivations.

**Reference signatures (inline — do not open the source files)**:
| Item | File:Line | Signature / note |
|------|-----------|------------------|
| `Satisfies` (imp/box) | `Cslib/Logics/Modal/Basic.lean:145-149` | `imp a c => Sat a → Sat c`; `box a => ∀ w', m.r w w' → Sat w' a` |
| Łukasiewicz encodings | `Cslib/Logics/Modal/Tableau/Defs.lean:110-201` | `¬a=imp a bot`; `a∨c=imp (imp a bot) c`; `a∧b=imp (imp a (imp b bot)) bot`; classifiers `modalAndOf?/modalOrOf?/modalImpOf?/modalNegOf?` with `@[simp]` |
| `tryAllPropRules` order | `Foundations/Logic/Tableau/PropositionalRules.lean:147-155` | first applicable of `[andPos,andNeg,orPos,orNeg,impPos,impNeg,negPos,negNeg]` |
| `applyPropRule` outputs | `PropositionalRules.lean:94-143` | per-rule `RuleResult` table (report 04 §1) |
| `modalHintikkaSet` clause | `Saturation.lean:207` | `∀ sf ∈ b, match (modalApplyOne sf b acc).1 with .linear nf => ∀∈; .branching brs => ∃ br ∈ brs, ∀∈; .persistent nf => ∀∈; .notApplicable => True` |
| `classicalTruthLemma` (shape only) | `Propositional/Tableau/Classical/Completeness.lean:84` | conjunction `pos ∧ neg`; NOTE its `imp` case differs — propositional `Proposition` has native and/or, so it never sees encodings (report 04 §3) |
| size lemma | (auto) | `Proposition.imp.sizeOf_spec : sizeOf (imp a c) = 1 + sizeOf a + sizeOf c` |

**Timing**: 1.5 hours (may need a small second dispatch for the negative leaf)

**Depends on**: 5a, 5b

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Completeness.lean` — delete `hintikka_imp_*`; add `modalTruthLemma_aux`;
  rewrite `modalTruthLemma` as the strong-induction wrapper.

**Verification**:
- `grep -n hintikka_imp Cslib/Logics/Modal/Tableau/Completeness.lean` empty.
- `lake build Cslib.Logics.Modal.Tableau.Completeness` green, **ZERO sorry** (the truth lemma is the
  deliverable that previously had 15 errors).
- `lean_verify Cslib.Logic.Modal.Tableau.modalTruthLemma` — no new axioms.
- Commit `task 299 phase 5c: modalTruthLemma via strong induction (delete imp bridges)`.

---

### Phase 5d: Countermodel wrapper [COMPLETED]

**Goal**: Open-branch countermodel wrapper reducing completeness to the Phase-6 invariant.

**Status note**: GREEN per `.orchestrator-handoff.json`. `modalOpenBranch_countermodel`
(`Completeness.lean:~398`) compiles: applies `modalTruthLemma … .2` (negative conjunct) to the
initial `F(φ)@0` membership. Its statement consumes the PUBLIC `modalTruthLemma` signature, which the
Phase 5c restructure preserves verbatim — only the proof body changes — so 5d requires no rework once
5c compiles.

**Tasks**:
- [x] `modalOpenBranch_countermodel`: a `modalHintikkaSet b acc` branch yields `extractModel b acc`
  refuting `φ`.

**Timing**: 0.5 hours (sunk)

**Depends on**: 5c (statement only)

**Completed**: green; will re-verify after 5c recompiles the file.

---

### Phase 6: Completeness loop invariant + final completeness [BLOCKED]

**Goal**: Prove `modalExpandBranches_hintikka` (returned open branch is a Hintikka set) and discharge
`modalTableau_complete` fully.

**BLOCKER** (Phase 6):
- **What failed**: `modalExpandBranches_hintikka` cannot be stated/proved because the modal
  expansion-**measure** infrastructure needed to discharge the `fuel = 0` branch of
  `modalExpandBranches` does not exist. At `fuel = 0` the loop returns the first *open* (but not
  necessarily *saturated*) branch, so `modalHintikkaSet b acc` is NOT provable for that branch
  unless we know `fuel = 0` is never reached with an unsaturated open branch — i.e. that the fuel
  bound `modalFuel φ = (4n+4)(n+2)+2` dominates a decreasing expansion measure.
- **What was tried / verified**:
  - Confirmed (grep) that NONE of the required modal infrastructure exists yet:
    `modalExpMeasure`, `modalBranchComplexity`, a `modalExpMeasure_step_lt` decrease lemma,
    `modalStepBranch_none_saturated`, `modalExpandBranches_hintikka`, `modalTableau_complete`.
  - Confirmed the soundness proof (`modalExpandBranches_closed_unsat`) does NOT use any measure —
    it works for arbitrary fuel because `closed ⇒ unsat` holds regardless of fuel. The measure is
    ONLY needed for the completeness (`openBranch ⇒ Hintikka`) direction.
  - Studied the classical template `classicalExpandBranches_hintikka`
    (`…/Propositional/Tableau/Classical/Completeness.lean:924`): it threads a
    `classicalExpMeasure branches expandedSets ≤ fuel` hypothesis and discharges `fuel = 0` by
    showing `measure = 0 ⇒ branches = []` (each per-branch term `3^C ≥ 1`).
- **Why it's stuck (root cause)**: The classical measure `3^(branchComplexity)` works because
  classical tableaux create NO new worlds. The modal K procedure's `boxNeg`/`diamondPos` rules
  create a FRESH world (`modalNextWorld b`) and `boxPos`/`diamondNeg` re-fire *persistently* as new
  successors appear. A sound modal measure must therefore bound the TOTAL expansion steps INCLUDING
  world creation and box re-firing, and one must prove `modalExpMeasure initial ≤ modalFuel φ`. This
  world-creation-interleaving bound is the plan's flagged HIGH risk and is a genuinely hard,
  research-level obligation — not a mechanical transcription.
- **What is needed to unblock** (concrete, ordered):
  1. Define `modalBranchComplexity` / `modalExpMeasure branches expandedSets accs` accounting for
     unexpanded formulas AND worlds still eligible for box re-firing.
  2. Prove `modalExpMeasure_step_lt`: every non-saturating `modalStepBranch` strictly decreases the
     measure (the delicate case: `diamondPos`/`boxNeg` add a world but consume the existential).
  3. Prove the fuel-sufficiency bound `modalExpMeasure [initial] [[]] [empty] ≤ modalFuel φ` (or
     revise `modalFuel` if a gap is exposed).
  4. Prove `modalStepBranch_none_saturated` (saturated ⇒ each `sf` is in `expanded` or yields
     `notApplicable`) — modal analog of `classicalStepBranch_none_saturated`.
  5. Prove `modalExpandBranches_hintikka` by fuel induction + inner `Forall₂`-acc induction (mirror
     `modalExpandBranches_closed_unsat`), using items 1-4 to discharge `fuel = 0` and the saturated
     leaf.
- **Prohibited workarounds**: Do NOT use `sorry`, `admit`, `def X := True`, or any vacuous
  placeholder, and do NOT introduce axioms. Recommend `/spawn 299` to create a dedicated task for
  the modal expansion-measure + fuel-sufficiency proof (items 1-3), which is the true blocker.

**Delivered before block**: Phase 5c `modalTruthLemma` is fully GREEN and committed sorry-free
(30 compile errors → 0). `modalOpenBranch_countermodel` (5d) already reduces
`modalTableau_complete` to `modalExpandBranches_hintikka` once item 5 lands.

**Prerequisite refactor**: hoist the generic `forall₂_*` list helpers (`forall₂_of_zip_mem`
`Soundness.lean:156`, `forall₂_replicate_right` `:177`, `forall₂_append_aux` `:197`, `forall₂_drop_aux`
`:205`, `forall₂_take_aux` `:212`) into a new `Cslib/Logics/Modal/Tableau/LoopInduction.lean`
(de-`private`, re-export); update `Soundness.lean` to import them (pure relocation, no proof change);
verify `Soundness.lean` still builds green. This lets `Completeness.lean` reuse the plumbing WITHOUT
importing the heavy soundness file.

**Intended statement**:
```lean
theorem modalExpandBranches_hintikka (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility) (b) (acc : Accessibility),
      <length invariants> →
      modalExpandBranches branches expandedSets accs fuel = .openBranch b acc →
      modalHintikkaSet b acc
```

**Tasks**:
- [ ] Do the `forall₂_*` hoist into `LoopInduction.lean`; import it into `Completeness.lean` and
  `Soundness.lean`.
- [ ] Mirror `modalExpandBranches_closed_unsat` (`Soundness.lean:226`) for the acc-threading: fuel
  induction + inner `processNext` induction over per-branch `List.Forall₂` accs, reusing the hoisted
  `forall₂_*` helpers and `accFreshInv`.
- [ ] Mirror `classicalExpandBranches_hintikka` (`…/Classical/Completeness.lean:924`) for the
  open/Hintikka logic.
- [ ] Add the saturation-characterisation lemma: when `modalStepBranch b e a = none` (saturated,
  returns `.openBranch b a`), prove `modalHintikkaSet b a`. Use classical
  `classicalStepBranch_none_saturated` (`…/Classical/Completeness.lean:694`) and
  `classicalStepBranch_hintikka_inv` (`:722`) as the PATTERN (Unit-label-specific — reference only).
- [ ] Handle world-creation interleaving (box-pos re-firing as new successors appear); the fuel bound
  `modalFuel φ` (`Saturation.lean:89`) should suffice; adjust ONLY if the invariant exposes a gap.
- [ ] Discharge `modalTableau_complete` (contrapositive: open ⇒ Hintikka ⇒ countermodel via
  `modalOpenBranch_countermodel`). `#print axioms modalTableau_complete`.

**Reusable infra (inline)**:
| Item | File:Line | Role |
|------|-----------|------|
| `modalExpandBranches_closed_unsat` | `Soundness.lean:226` | acc-threading structural template |
| `forall₂_*` helpers | `LoopInduction.lean` (hoisted here) | worklist plumbing |
| `accFreshInv` / `accFreshInv_empty` | `SoundnessStep.lean:165/172` | freshness invariant |
| `modalStepBranch` / `modalExpandBranches` / `.processNext` | `Saturation.lean:99/135/149` | recursion being inducted over |
| `classicalExpandBranches_hintikka` | `…/Classical/Completeness.lean:924` | open/Hintikka logic template |
| `classicalStepBranch_none_saturated` / `_hintikka_inv` | `…/Classical/Completeness.lean:694/722` | saturation-characterisation pattern |

**Timing**: 3 hours (may need 1-2 dispatches; ~200-400 lines)

**Depends on**: 5c, 5d

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/LoopInduction.lean` — new (hoisted `forall₂_*` helpers)
- `Cslib/Logics/Modal/Tableau/Soundness.lean` — import hoisted helpers (no proof change)
- `Cslib/Logics/Modal/Tableau/Completeness.lean` — loop invariant + finalize `modalTableau_complete`
- `Cslib/Logics/Modal/Tableau/Saturation.lean` — possible fuel-bound adjustment ONLY if required

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.Completeness` green, ZERO sorry; `Soundness.lean` green after
  the hoist.
- `#print axioms modalTableau_complete` shows only standard axioms.
- Commit `task 299 phase 6: completeness loop invariant + modalTableau_complete`.

**Contingency (zero-debt fallback)**: if world-creation interleaving cannot close in one genuine
attempt, keep 5a-5d committed sorry-free, mark Phase 6 [BLOCKED] with the precise residual obligation,
`/spawn` a follow-up. Never ship `sorry` or new axioms.

---

### Phase 7: Decision procedure, barrel, and CI verification [NOT STARTED]

**Goal**: Package the iff + `Decidable` instance, add the module barrel, confirm `#print axioms` shows
no new axioms, pass the full CSLib CI pipeline with zero sorry.

**Tasks**:
- [ ] Prove `modalTableau_decides : modalTableau φ = .closed ↔ <φ valid over all models>` from
  `modalTableau_sound` + `modalTableau_complete`; provide a `Decidable` instance via `isTrue`/`isFalse`
  (requires only `DecidableEq + Hashable`, no `Fintype Atom`).
- [ ] Confirm NO `sorry` anywhere under `Cslib/Logics/Modal/Tableau/` (grep clean).
- [ ] `#print axioms modalTableau_sound`, `modalTableau_complete`, `modalTableau_decides` — only
  standard axioms.
- [ ] Add module doc comments + barrel/import-aggregator (`lake exe mk_all --module` or the
  ORGANISATION.md root) so `LoopInduction.lean` and `Completeness.lean` are reachable.
- [ ] Run full CI: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake shake --add-public --keep-implied --keep-prefix`.

**Timing**: 1.5 hours

**Depends on**: 6

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Completeness.lean` — decision procedure iff + `Decidable` instance
- barrel/import file under `Cslib/` per ORGANISATION.md

**Verification**:
- All CI commands exit 0; `#print axioms modalTableau_decides` shows only standard axioms; no `sorry`
  (grep clean).
- Commit `task 299 phase 7: decision procedure + barrel + CI green`.

---

## Testing & Validation

- [ ] `lake build` of all `Cslib/Logics/Modal/Tableau/*.lean` (Defs, Branch, Rules, Closure,
  Saturation, SoundnessStep, Soundness, LoopInduction, Completeness) succeeds.
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
- `Cslib/Logics/Modal/Tableau/Branch.lean` (Phase 2, done)
- `Cslib/Logics/Modal/Tableau/Rules.lean` (Phase 2, done)
- `Cslib/Logics/Modal/Tableau/Closure.lean` (Phase 3, done)
- `Cslib/Logics/Modal/Tableau/Saturation.lean` (Phase 3, done; possible Phase 6 fuel tweak)
- `Cslib/Logics/Modal/Tableau/SoundnessStep.lean` (Phase 4, done)
- `Cslib/Logics/Modal/Tableau/Soundness.lean` (Phase 4, done; Phase 6 hoist of `forall₂_*`)
- `Cslib/Logics/Modal/Tableau/LoopInduction.lean` (Phase 6, new — hoisted `forall₂_*`)
- `Cslib/Logics/Modal/Tableau/Completeness.lean` (Phases 5a-7; truth lemma restructured in 5c)
- barrel/import file per ORGANISATION.md (Phase 7)
- `modalTableau`, `modalTableau_sound` (done), `modalTableau_complete`, `modalTableau_decides`, and a
  `Decidable` instance.

## Rollback/Contingency

- Soundness (Phases 1-4) is committed and green at `3660ac0c`; untouched except the pure-relocation
  `forall₂_*` hoist in Phase 6 (revert by moving helpers back + dropping the import).
- The green completeness pieces (5a/5b-box/5d) are committed; the Phase 5c restructure only edits the
  truth lemma body and deletes two unprovable lemmas — revert by `git checkout` of `Completeness.lean`.
- All remaining work is additive in `LoopInduction.lean` + `Completeness.lean`; rollback = remove
  those edits and the barrel entry.
- Each phase commits incrementally at a green, zero-sorry milestone; the whole-library build stays
  green because soundness is done and completeness is import-isolated.
- If Phase 6 stalls, apply its zero-debt fallback: spawn a follow-up for the invariant, keep the
  sorry-free 5a-5d committed, mark task 299 `[BLOCKED]`/`[PARTIAL]`. Never commit `sorry` or new axioms.
