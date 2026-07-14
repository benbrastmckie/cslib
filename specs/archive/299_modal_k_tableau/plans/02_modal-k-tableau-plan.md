# Implementation Plan: Task #299 (Revised, v2)

- **Task**: 299 - Modal K Tableau Decision Procedure
- **Status**: [IN PROGRESS]
- **Effort**: 16 hours (Phase 4 re-budgeted from 2.5h to ~4.75h across four sub-phases)
- **Dependencies**: None
- **Research Inputs**: specs/299_modal_k_tableau/reports/01_modal-k-tableau-research.md
- **Artifacts**: plans/02_modal-k-tableau-plan.md (this file); supersedes plans/01_modal-k-tableau-plan.md
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, CSLib CONTRIBUTING.md (zero-sorry / zero-new-axiom)
- **Type**: cslib
- **Lean Intent**: false

## Overview

Implement a sound and complete tableau decision procedure for basic modal logic K
under `Cslib/Logics/Modal/Tableau/`, instantiating the label-generic CSLib Foundations
tableau layer with `F = Cslib.Logic.Modal.Proposition Atom` and `L = WorldIndex` (Nat).
Phases 1-3 (Defs, Rules+Branch, Closure+Saturation) are COMPLETE and committed. The
remaining work is soundness (Phase 4), completeness (Phases 5-6), and the decision
procedure + CI wrap-up (Phase 7).

This revision (v2) exists for ONE reason: **Phase 4 (soundness) was an oversized,
single-shot phase that failed autonomous implementation in 4 of 5 dispatch cycles.** All
soundness work lives in one ~970-line file `Cslib/Logics/Modal/Tableau/Soundness.lean`
(imported at `Cslib.lean:408`), which currently fails to build with ~10-12 distinct broken
sites and breaks `main`. Each dispatch overflowed the implementation agent's context because
it tried to hold and reason about the whole file at once. v2 decomposes Phase 4 into four
small, sequenced sub-phases (4a-4d), each bounded to ONE agent run, each targeting one lemma
or one closed cluster of build errors, each with an explicit context-navigation budget and a
"strictly fewer errors, zero new sorries, then commit" gate.

### Research Integration

This v2 revision integrates no new research report; it re-plans Phase 4 in light of the
diagnostics accumulated across the prior implementation dispatches (captured in
`.orchestrator-handoff.json`, `continuation_context.remaining_blockers`). The original
research report (`reports/01_modal-k-tableau-research.md`) remains fully integrated and its
findings (reuse Foundations layer, classical architecture template, Bimodal modal-mechanics,
K-vs-S5 box-rule correctness constraint) are unchanged. Reports integrated: see
`reports_integrated` in state metadata.

Key v2-specific diagnostics driving the Phase 4 decomposition (from prior dispatches):
- **Root cause A (4a)**: the `T(a → ⊥)` / `T(imp a c)` prop cases in
  `modalStepBranch_preserves_sat` call `simp [tryAllPropRules, ...]` / `refine` while the
  formula variable (`a`, `c`) is still generic, so `modalAndOf?` / `tryAllPropRules` cannot
  reduce. A `cases a with` / `cases c with` BEFORE the simp/refine makes the variable concrete
  and is predicted to clear the cascade at ~227, 275, 309-311, 367-377.
- **Root cause B (4b)**: the box-positive `refine` membership proof fails after `subst`
  (~line 232) — the existential/membership goal desugars differently post-`subst`.
- **Root cause C (4c)**: `modalExpandBranches_closed_unsat`'s inner induction (~920/959) has a
  structural mismatch — `acc` vs `newAcc` (accessibility mutated by `boxNeg`/`diamondPos` world
  creation) and `processNext` vs `modalExpandBranches` (different recursion levels). The inner
  `key` lemma captures the outer `hstep` instead of carrying its own; it must be redesigned to
  take an explicit `hstep`-style hypothesis and thread the accessibility invariant.

### WIP-Import Recommendation (Cslib.lean:408)

`Soundness.lean` is imported at `Cslib.lean:408` while broken, so `main` is currently RED.
**Recommendation: temporarily un-wire the import (comment out / remove `Cslib.lean:408`) at
the START of sub-phase 4a, and re-wire it in sub-phase 4d once the file is fully green.**
Rationale: with the import removed, `lake build` of the whole library stays green throughout
4a-4c, so intermediate WIP commits do not regress `main`; per-sub-phase progress is then
verified by a TRUNCATED single-module build of `Soundness.lean` (see Context-Budget Protocol),
not by the whole-library build. The alternative (keeping it imported to "track progress")
keeps `main` red across multiple commits and is rejected: it conflates phase progress with
library health and trips the environment hazard below.

### Prior Plan Reference

Supersedes `plans/01_modal-k-tableau-plan.md`. Phases 1-3 are carried over verbatim and remain
[COMPLETED]; Phases 5-7 are carried over verbatim. Only Phase 4 is restructured.

### Roadmap Alignment

ROADMAP.md exists but no `roadmap_flag` was provided; this plan does not add roadmap
review/update phases and does not modify ROADMAP.md. Task 299 is part of the modal/temporal
tableau series (tasks 299-301) for which the Foundations `RuleResult.persistent` mechanism
was pre-provisioned; completing it advances the Modal Logic decidability line.

## Goals & Non-Goals

**Goals**:
- A `modalTableau φ` decision procedure for modal K returning `closed` or an open branch.
- `modalTableau_sound`: `modalTableau φ = .closed → φ` valid over all Kripke models.
- `modalTableau_complete`: open result yields a finite Kripke countermodel refuting `φ`.
- A `modalTableau_decides` iff and a `Decidable` instance (no `Fintype Atom` requirement).
- All seven files build under `Cslib/Logics/Modal/Tableau/` with ZERO `sorry` and ZERO new
  axioms; full CSLib CI pipeline green.

**Non-Goals**:
- Any modal system beyond K (no T/D/4/5/B/S4/S5 frame conditions).
- Optimised/performant saturation; fuel-based correctness suffices.
- Reusing or modifying the Bimodal tableau code in place (it is reference only; K gets its
  own files to avoid S5 contamination).
- A canonical-model / Lindenbaum completeness proof (countermodel extraction is the route).
- Rewriting `Soundness.lean` from scratch in Phase 4 — the file is ~80% there; v2 is targeted
  repair, not a rewrite.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Phase 4 dispatch overflows context again (the v1 failure) | H | M | Sub-phases 4a-4d each bounded to one agent run, one lemma / one error cluster; mandatory Context-Budget Protocol (navigate via lean-lsp outline/diagnostics, never read the full file; truncated single-module builds only) |
| 4c (`modalExpandBranches_closed_unsat`) restructure is hardest, may exceed one run | H | M | Isolated as its own sub-phase with an explicit redesign recipe (carry `hstep` as a parameter of the inner `key` lemma; thread accessibility invariant); zero-debt fallback: if unclosable in one run, leave 4a/4b committed green and mark 4c [BLOCKED] / spawn follow-up |
| Concurrent sessions clobber WIP `Soundness.lean` | M | M | Environment hazard (below); serialize sessions or use a git worktree; commit each green sub-phase immediately |
| `main` stays red across Phase 4 commits | M | H (if not mitigated) | Un-wire `Cslib.lean:408` at 4a, re-wire at 4d (WIP-Import Recommendation) |
| Completeness loop invariant (`expandBranches_hintikka`) cannot be closed | H | M | Isolated dedicated phase (Phase 6); zero-debt fallback: decompose into a follow-up task or mark [BLOCKED], never ship sorry/axioms |
| S5 box rule accidentally re-introduced during repair (unsound for K) | H | L | Box-positive propagates ONLY to recorded R-successors via the edge list; the `boxPos` preservation step (4b) would fail for the S5 all-worlds variant — do not regress it |

**Environment hazard**: multiple concurrent Claude sessions share this one checkout; a sibling
`git add -A` previously swept WIP into an unrelated commit. Serialize sessions or use separate
git worktrees before resuming Phase 4.

## Context-Budget Protocol (MANDATORY for every Phase 4 sub-phase)

`Soundness.lean` is ~970 lines. Implementation agents MUST NOT read it in full. For every
sub-phase 4a-4d:

1. **Navigate, do not bulk-read.** Use lean-lsp:
   - `lean_file_outline Cslib/Logics/Modal/Tableau/Soundness.lean` to locate declarations.
   - `lean_diagnostic_messages Cslib/Logics/Modal/Tableau/Soundness.lean` to list current
     errors with line numbers (this is the authoritative error set, not the stale line numbers
     in this plan).
   - `lean_goal` + `lean_hover_info` at each targeted line to inspect the proof state before
     editing; `lean_multi_attempt` to test a tactic without committing an edit.
   - Use `Read` with `offset`/`limit` to view only the ±40 lines around a target site.
2. **Build truncated, single-module, never bare `lake build`.** Use:
   `lake build Cslib.Logics.Modal.Tableau.Soundness 2>&1 | tail -60`
   (or `... | grep '^error:' | sort -u` for a deduplicated error list). The whole-library
   `lake build` is reserved for sub-phase 4d (re-wire verification).
3. **Per-sub-phase gate**: the sub-phase's targeted error sites must report NO errors via
   `lean_diagnostic_messages`, the total Soundness error count must strictly decrease, and NO
   `sorry` and NO new axioms may be introduced. With `Cslib.lean:408` un-wired (per the
   WIP-Import Recommendation), commit the sub-phase as `task 299 phase 4{x}: ...` even if
   downstream declarations later in the file still error — those are the next sub-phase's job.
   The FULL "zero errors, zero sorries" whole-file gate is reached at 4d.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4a, 5 | 3 |
| 5 | 4b, 6 | 4a (for 4b); 5 (for 6) |
| 6 | 4c | 4b |
| 7 | 4d | 4c |
| 8 | 7 | 4d, 6 |

Phases within the same wave can execute in parallel. The soundness chain
(4a -> 4b -> 4c -> 4d, all editing `Soundness.lean`) runs in parallel with the completeness
chain (5 -> 6, editing `Completeness.lean`): the two chains touch disjoint files (clean
territory separation), so a second agent may work completeness while soundness is being
repaired. Phase 7 (decision procedure + CI) joins both after 4d and 6 are done.

---

### Phase 1: Defs — types, complexity, Lukasiewicz decomposition [COMPLETED]

**Goal**: Establish `Cslib/Logics/Modal/Tableau/Defs.lean` with all foundational definitions
the rest of the procedure consumes, building cleanly against the Foundations layer.

**Tasks**:
- [x] Create `Defs.lean` in namespace `Cslib.Logic.Modal.Tableau`, importing the Foundations
  `Tableau` modules and `Cslib.Logics.Modal.Basic`.
- [x] Define `abbrev WorldIndex := Nat` and the initial world (`0`).
- [x] Add `Hashable (Proposition Atom)` instance (mirror `instHashableProposition`) — required
  by Foundations `Branch`/`SignedFormula` ops.
- [x] Define `Modal.Proposition.complexity` (mirror `Propositional/Subformula.lean`; `box`
  adds 1; `imp` is structural).
- [x] Define Lukasiewicz decomposition functions matching encoded shapes:
  `negOf? (imp a bot) = some a`; `orOf? (imp (imp a bot) b) = some (a,b)`;
  `andOf? (imp (imp a (imp b bot)) bot) = some (a,b)`; `impOf?` EXCLUDING the encoded
  neg/or/and shapes; `boxOf? (box a) = some a`; `diaOf? (imp (box (imp a bot)) bot) = some a`.
- [x] Add `@[simp]` reduction lemmas for each decomposition function; verify each shape with
  `example`/`#eval` to catch match-ordering bugs.

**Timing**: 2 hours

**Depends on**: none

**Files modified**:
- `Cslib/Logics/Modal/Tableau/Defs.lean` - new file (all of the above)

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.Defs` succeeds, no sorry.
- Each decomposition `@[simp]` lemma proves by `rfl`/`simp`; `impOf?` returns `none` on
  encoded neg/or/and shapes (checked by `example`).

**Completed**: 2026-06-24 (committed).

---

### Phase 2: Rules — K modal rules + accessibility edges [COMPLETED]

**Goal**: Define the K rule application in `Rules.lean` and `Branch.lean`, with explicit
accessibility-edge tracking that makes box-positive propagation K-sound (not S5).

**Tasks**:
- [x] Create `Branch.lean`: define `Accessibility := { edges : List (WorldIndex × WorldIndex) }`
  with `addEdge`, `successorsOf w`, plus `nextWorld`/`knownWorlds`/`maxWorld` helpers over the
  Foundations `Branch`. Add a box-propagation helper (apply T(φ) to all `successorsOf w`).
- [x] Create `Rules.lean`: define `modalApplyOne sf branch acc` dispatching prop rules via
  `tryAllPropRules propAndOf? propOrOf? propImpOf? propNegOf?` (using Phase 1 fns) and the four
  K modal cases producing `RuleResult` + edge updates:
  - `boxPos` T(□φ)@w: `.persistent`, add T(φ)@w' for every `w' ∈ successorsOf w` (re-fires when
    new successors appear).
  - `diamondPos` T(◇φ)@w: create fresh w', add edge w→w', add T(φ)@w', re-apply w's box-
    positives to w'. Existential.
  - `boxNeg` F(□φ)@w: create fresh w', add edge w→w', add F(φ)@w'. Existential.
  - `diamondNeg` F(◇φ)@w: `.persistent`, add F(φ)@w' for every `w' ∈ successorsOf w`. Universal.
- [x] Ensure box-positive propagation is scoped to the edge relation ONLY (no all-worlds
  propagation) — this is the K-vs-S5 correctness invariant.

**Timing**: 2.5 hours

**Depends on**: 1

**Files modified**:
- `Cslib/Logics/Modal/Tableau/Branch.lean` - new file (accessibility, world helpers)
- `Cslib/Logics/Modal/Tableau/Rules.lean` - new file (modal rule dispatch)

**Verification**:
- `lake build` of both files succeeds, no sorry.
- `#eval`/`example` smoke tests: T(□p)@0 with edge 0→1 propagates T(p)@1 but not to an
  unconnected world 2; T(◇p)@0 creates a fresh successor with T(p).

**Completed**: 2026-06-24 (committed).

---

### Phase 3: Closure + Saturation — fuel loop and entry point [COMPLETED]

**Goal**: Wire closure and the fuel-based saturation loop, producing the runnable
`modalTableau φ` entry point and the Hintikka predicate completeness will need.

**Tasks**:
- [x] Create `Closure.lean`: instantiate/re-export `ClassicalClosure` for the modal types
  (T(⊥) or T(φ)/F(φ) at same label). Thin file; no new closure logic.
- [x] Create `Saturation.lean`: define `ModalTableauResult := closed | openBranch (Branch ...)`
  and the fuel-based `modalExpandBranches branches acc expandedSets fuel` with nested
  `processNext` worklist, maintaining `expandedSets.length = branches.length` and an
  `AppliedSet`/expanded guard to stop persistent rules re-firing.
- [x] Define the fuel bound: FMP-derived `modalFuel φ` accounting for world creation
  (worlds ≤ distinct ◇/F(□) occurrences) × subformula closure; cap it. Add
  `termination_by fuel`.
- [x] Add world-subset blocking (retarget Bimodal time-subset blocking to WORLDS): a fresh
  world whose signed-formula set ⊆ an ancestor's is blocked (finite model property).
- [x] Define entry point `modalTableau φ := modalExpandBranches [[F(φ)]] emptyAcc [[]] (modalFuel φ)`.
- [x] Define the `modalHintikkaSet b acc` downward-saturation predicate (open + every rule's
  outputs already present, including box/diamond edge-closure conditions).

**Timing**: 2.5 hours

**Depends on**: 2

**Files modified**:
- `Cslib/Logics/Modal/Tableau/Closure.lean` - new file (closure instance)
- `Cslib/Logics/Modal/Tableau/Saturation.lean` - new file (fuel loop, entry, Hintikka pred)

**Verification**:
- `lake build` succeeds, no sorry; termination accepted by Lean.
- `#eval modalTableau (□p ⟶ p)` etc. on small examples: a K-invalid formula yields an open
  branch, a K-valid formula yields `closed`.

**Completed**: 2026-06-24 (committed).

---

### Phase 4 (overview): Soundness — decomposed into sub-phases 4a-4d

**Goal**: Prove `modalTableau_sound` against Kripke semantics over all models, by repairing the
existing ~970-line `Cslib/Logics/Modal/Tableau/Soundness.lean` (currently RED, ~10-12 broken
sites) WITHOUT a rewrite and WITHOUT ever holding the whole file in one agent's context.

**Current declaration map** (from `lean_file_outline`; verify with fresh diagnostics on resume):
- `branchSatisfiable` (def, ~63), `modalClosed_unsat` (~100), `accFreshInv` (def, ~164),
  `accFreshInv_empty` (~171) — foundation lemmas, mostly fixed; clear any residual
  `unsolved goals` (~99/124/173) as a preliminary in 4a.
- `modalStepBranch_preserves_sat` (~186-796) — the per-rule satisfiability-preservation lemma;
  contains the 4a prop cases and the 4b box-positive case.
- `modalExpandBranches_closed_unsat` (~797-926) — the fuel-induction lift; the 4c target.
- `kValid` (def, ~927) and `modalTableau_sound` (~939-969) — the 4d main theorem.

**Per-rule strategy** (unchanged from v1; reference while repairing):
- prop rules via `Satisfies.and_iff`/`or_iff`/`impl_iff` (`@[scoped grind]` in Basic.lean).
- `boxPos`: `Satisfies m w (□φ) ∧ w→w' → Satisfies m w' φ` via `Satisfies.box_iff_forall`
  (this lemma fails for the S5 all-worlds variant — guards K-correctness; do not regress).
- `diamondPos`: `Satisfies.diamond_iff_exists` gives a witness world; extend the
  label→world assignment to the fresh label.
- `boxNeg`/`diamondNeg`: dual witnesses / universal propagation.
- closed branches unsatisfiable via `modalClosed_unsat` (reuse `ClassicalClosure` reasoning).

**Files modified (all sub-phases)**: `Cslib/Logics/Modal/Tableau/Soundness.lean`; plus
`Cslib.lean` (un-wire line 408 at 4a, re-wire at 4d).

Apply the **Context-Budget Protocol** above to every sub-phase below.

---

### Phase 4a: Prop-rule cases — concrete the formula variable [COMPLETED]

**Goal**: Make the `T(imp a c)` / `T(a → ⊥)` propositional cases of
`modalStepBranch_preserves_sat` compile by case-splitting the formula variable before the
`simp [tryAllPropRules, ...]` / `refine` calls, so `modalAndOf?`/`tryAllPropRules` can reduce.
Predicted to clear the largest cascade of downstream universe-mismatch / unknown-identifier
errors.

**Tasks**:
- [ ] **Preliminary**: un-wire `Soundness.lean` from `Cslib.lean:408` (comment out / remove the
  import) so `main` builds green during 4a-4c. Confirm with `lake build 2>&1 | tail -20`.
- [ ] Clear any residual upstream `unsolved goals` in `modalClosed_unsat` (~99/124) and
  `accFreshInv_empty` (~173) so goal inspection downstream is clean (small, upstream).
- [ ] In `modalStepBranch_preserves_sat`, inside the `| pos =>` → `| imp a c =>` → `| bot =>`
  branch (and every sibling `T(imp a c)` occurrence), add `cases a with` / `cases c with`
  BEFORE the `simp`/`refine` so `a`/`c` are concrete in each branch
  (`| atom p => ... | bot => ... | imp a1 a2 => cases a2 with | bot => ... | _ => ... | box φ => ...`).
- [ ] Re-run diagnostics; confirm the targeted sites (~227, 275, 309-311, 367-377) are clear.

**Timing**: 1 hour

**Depends on**: 3

**Verification (per Context-Budget Protocol)**:
- `lean_diagnostic_messages` shows NO errors at the targeted prop-case sites.
- `lake build Cslib.Logics.Modal.Tableau.Soundness 2>&1 | grep '^error:' | sort -u` shows
  strictly fewer distinct errors than before; no `sorry`, no new axioms.
- `lake build 2>&1 | tail -20` (whole library) green because line 408 is un-wired.
- Commit `task 299 phase 4a: soundness prop-rule cases (concrete formula var)`.

---

### Phase 4b: Box-positive refine / membership after subst [COMPLETED]

**Goal**: Fix the box-positive `refine` membership mismatch after `subst` (~line 232) so the
remaining cases of `modalStepBranch_preserves_sat` compile; after this sub-phase the whole
`modalStepBranch_preserves_sat` lemma is green.

**Tasks**:
- [ ] At the box-positive case (~232), run `lean_goal` AFTER the `subst hnewBs hnewAcc` to read
  the exact goal shape (likely `∃ b' ∈ newBs, P` desugaring differently post-subst).
- [ ] Repair the `refine` / membership proof (e.g. correct `List.mem_cons_self` usage or
  restructure the existential witness) to match the actual goal. Use `lean_multi_attempt` to
  trial tactics without editing.
- [ ] Preserve K-correctness: the box-positive witness must come from `successorsOf w` via the
  edge list, NEVER all worlds. Do not regress to the S5 box rule.
- [ ] Confirm `modalStepBranch_preserves_sat` reports no errors end-to-end via diagnostics.

**Timing**: 0.75 hours

**Depends on**: 4a

**Verification (per Context-Budget Protocol)**:
- `lean_diagnostic_messages` shows NO errors anywhere within `modalStepBranch_preserves_sat`
  (~186-796).
- Single-module error count strictly decreased; no `sorry`, no new axioms; library green
  (408 un-wired).
- Commit `task 299 phase 4b: box-positive refine/membership repaired`.

---

### Phase 4c: Redesign modalExpandBranches_closed_unsat (acc + recursion threading) [COMPLETED]

**Goal**: Fix the structural mismatch in `modalExpandBranches_closed_unsat` (~lines 920/959):
`acc` vs `newAcc` (accessibility mutated by `boxNeg`/`diamondPos` world creation) and
`processNext` vs `modalExpandBranches` (different recursion levels). This is the hardest
sub-phase and is isolated so it gets a full agent run.

**Tasks**:
- [ ] Redesign the inner `key` lemma so it carries its OWN `hstep`-style hypothesis as an
  EXPLICIT parameter instead of capturing the outer one. Concretely, parameterize `key` with:
  `∀ b e newBs newExps newAcc, b ∈ pending → modalStepBranch b e acc_pending = some (newBs, newExps, newAcc) → branchSatisfiable b acc_pending → ∃ b' ∈ newBs, branchSatisfiable b' newAcc`.
- [ ] Thread the accessibility invariant through the induction: relate the current `pending`
  list and `acc`/`newAcc` to the original `branches`, so `processNext` and `modalExpandBranches`
  obligations line up (mirror `classicalExpandBranches_closed_unsat`'s fuel induction + inner
  worklist induction, but with the extra accessibility parameter).
- [ ] Use `lean_goal` at ~920 and ~959 to confirm the inner IH and `hinner` types now unify.
- [ ] Zero-debt fallback: if this cannot be closed in one run, leave 4a/4b committed green,
  mark THIS sub-phase [BLOCKED] with the precise remaining obligation, and `/spawn` a follow-up
  rather than shipping `sorry` or an axiom.

**Timing**: 2 hours

**Depends on**: 4b

**Verification (per Context-Budget Protocol)**:
- `lean_diagnostic_messages` shows NO errors within `modalExpandBranches_closed_unsat`.
- Single-module error count strictly decreased; no `sorry`, no new axioms; library green
  (408 un-wired).
- Commit `task 299 phase 4c: modalExpandBranches_closed_unsat redesigned (acc threading)`.

---

### Phase 4d: Main theorem + full-file green + re-wire import [COMPLETED]

**Goal**: Discharge `modalTableau_sound` (and `kValid`), bring `Soundness.lean` fully green
(zero errors, zero sorries, zero new axioms), re-wire the import, and verify the whole library.

**Tasks**:
- [ ] Repair/finish `kValid` (~927) and the main `modalTableau_sound` (~939-969) theorem
  (by contrapositive: closed ⇒ unsatisfiable via `modalExpandBranches_closed_unsat`, then K
  validity over all models).
- [ ] Run `lake build Cslib.Logics.Modal.Tableau.Soundness 2>&1 | tail -60` and confirm ZERO
  errors and ZERO sorries across the whole file (grep for `sorry`).
- [ ] Re-wire the import at `Cslib.lean:408` (restore `public import Cslib.Logics.Modal.Tableau.Soundness`).
- [ ] `#print axioms modalTableau_sound` — confirm only standard axioms (no new axioms).
- [ ] `lake build 2>&1 | tail -40` (whole library) green with the import restored.

**Timing**: 1 hour

**Depends on**: 4c

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.Soundness` succeeds, no sorry, no new axioms
  (`#print axioms modalTableau_sound` shows only standard axioms).
- Whole-library `lake build` green with `Cslib.lean:408` re-wired.
- Commit `task 299 phase 4d: soundness complete (modalTableau_sound green, import re-wired)`.

---

### Phase 5: Completeness scaffolding — model extraction + truth lemma [IN PROGRESS]

**Goal**: Build the countermodel from an open saturated branch and prove the modal truth
lemma — everything in `Completeness.lean` EXCEPT the loop invariant (deferred to Phase 6).

**Tasks**:
- [ ] Create `Completeness.lean`. Define `extractModel b acc : Model WorldIndex Atom` with
  `World := WorldIndex` (labels on branch), `r w w' := (w,w') ∈ acc.edges`,
  `v w p := T(atom p)@w on branch` (mirror `buildAtomValuation`).
- [ ] Prove the modal truth lemma by induction on φ (mirror the sorry-free classical
  `classicalTruthLemma`; new box/diamond cases): box case uses Hintikka edge-closure (every
  successor has propagated T(φ)) + `Satisfies.box_iff_forall`; diamond case uses the witness
  world + `Satisfies.diamond_iff_exists`. Two mutual inductions (pos/neg) as in Bimodal
  `truthLemma_pos`/`truthLemma_neg`.
- [ ] Prove `modalOpenBranch_countermodel`: a `modalHintikkaSet` branch yields a model
  refuting φ (the open-branch ⇒ ¬⊨φ wrapper that Bimodal leaves unwritten).
- [ ] State `modalTableau_complete` reduced to the loop invariant `modalExpandBranches_hintikka`
  (left as the single explicit dependency for Phase 6 — keep as a clearly-marked `sorry`-free
  `theorem ... := ...` calling an as-yet-unproved lemma, OR a temporary local `sorry` that
  Phase 6 MUST remove before task completion).

**Timing**: 2.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Completeness.lean` - new file (extraction + truth lemma)

**Verification**:
- `lake build` succeeds; the ONLY outstanding obligation is the loop invariant
  `modalExpandBranches_hintikka` (everything else sorry-free). The truth lemma itself has no
  sorry.

---

### Phase 6: Completeness loop invariant (HIGH RISK) [NOT STARTED]

**Goal**: Prove `modalExpandBranches_hintikka` (returned open branch is a Hintikka set) and
discharge `modalTableau_complete` fully — the dominant risk and dominant cost.

**Tasks**:
- [ ] Prove `modalExpandBranches_hintikka`: an open branch returned by the fuel loop satisfies
  the `modalHintikkaSet` predicate. Strategy: strong structural invariant carried through the
  fuel induction (saturation of every applicable rule + edge-closure of box-positives over
  newly created worlds). Reuse the complete classical helpers `mem_extendMany_of_mem`,
  `hintikka_inv_mono` (lifted to the modal worklist).
- [ ] Handle the world-creation/expansion interleaving: prove that when a fresh world is added,
  all box-positives of its predecessor are (eventually) propagated before fuel exhaustion (the
  fuel bound from Phase 3 must guarantee this — adjust the bound here if needed).
- [ ] Discharge `modalTableau_hintikka` and the `F(φ) ∈ b` membership step (the two other
  classical-template sorries), then close `modalTableau_complete` (contrapositive).
- [ ] Remove any temporary `sorry` left from Phase 5; run `#print axioms modalTableau_complete`.

**Timing**: 3 hours

**Depends on**: 5

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Completeness.lean` - prove the loop invariant + finalize
- `Cslib/Logics/Modal/Tableau/Saturation.lean` - possible fuel-bound adjustment if invariant
  requires it

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.Completeness` succeeds with ZERO sorry.
- `#print axioms modalTableau_complete` shows only standard axioms (no new axioms).

**Contingency (zero-debt fallback)**: If the loop invariant cannot be closed within this phase
after a genuine attempt (e.g. the world-creation interleaving requires a structural change to
the saturation loop), DO NOT ship `sorry` or introduce axioms. Instead: (a) split the invariant
out as a follow-up task via `/spawn`, leaving the rest of the procedure (Defs/Rules/Branch/
Closure/Saturation/Soundness + the truth lemma) committed sorry-free; and (b) mark task 299
`[BLOCKED]` (or `[PARTIAL]`) with a precise description of the remaining obligation. The
soundness direction and the truth lemma are independently shippable.

---

### Phase 7: Decision procedure, barrel, and CI verification [NOT STARTED]

**Goal**: Package the iff + `Decidable` instance, add the module barrel, and pass the full
CSLib CI pipeline.

**Tasks**:
- [ ] In `Completeness.lean` (or a small `DecisionProcedure` section), prove
  `modalTableau_decides : modalTableau φ = .closed ↔ <φ valid over all models>` from soundness
  + completeness, and provide a `Decidable` instance via `isTrue`/`isFalse` (requires only
  `DecidableEq + Hashable`, no `Fintype Atom`).
- [ ] Add module-level doc comments and any barrel/import-aggregator file so the tableau
  modules are reachable (follow CSLib ORGANISATION.md; add to the appropriate import root).
- [ ] Run the full CI pipeline and fix any violations: `lake build`, `lake test`,
  `lake exe checkInitImports`, `lake exe lint-style`,
  `lake shake --add-public --keep-implied --keep-prefix`.

**Timing**: 1.5 hours

**Depends on**: 4d, 6

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Completeness.lean` - decision procedure iff + Decidable instance
- barrel/import file under `Cslib/` as required by ORGANISATION.md

**Verification**:
- All CI commands exit 0.
- `#print axioms modalTableau_decides` shows only standard axioms.
- No `sorry` anywhere under `Cslib/Logics/Modal/Tableau/` (grep clean).

---

## Testing & Validation

- [ ] `lake build` of all seven `Cslib/Logics/Modal/Tableau/*.lean` files succeeds.
- [ ] `lake test` (CslibTests) passes.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake exe lint-style` passes.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no issues.
- [ ] Zero `sorry` and zero new axioms across the directory (verified by grep +
  `#print axioms` on the three top-level theorems).
- [ ] Smoke `#eval` checks: K-valid formulas (e.g. `□(p ⟶ q) ⟶ (□p ⟶ □q)`) return `closed`;
  K-invalid formulas (e.g. `□p ⟶ p`) return an open branch with a refuting countermodel.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Tableau/Defs.lean` (Phase 1, done)
- `Cslib/Logics/Modal/Tableau/Rules.lean` (Phase 2, done)
- `Cslib/Logics/Modal/Tableau/Branch.lean` (Phase 2, done)
- `Cslib/Logics/Modal/Tableau/Closure.lean` (Phase 3, done)
- `Cslib/Logics/Modal/Tableau/Saturation.lean` (Phase 3, done)
- `Cslib/Logics/Modal/Tableau/Soundness.lean` (Phase 4a-4d)
- `Cslib/Logics/Modal/Tableau/Completeness.lean` (Phases 5-7)
- `Cslib.lean` import update (un-wire at 4a, re-wire at 4d) + barrel per ORGANISATION.md
- `modalTableau`, `modalTableau_sound`, `modalTableau_complete`, `modalTableau_decides`,
  and a `Decidable` instance.

## Rollback/Contingency

- All work is additive (new files under a new directory). Rollback = remove
  `Cslib/Logics/Modal/Tableau/` and revert the `Cslib.lean` import change; nothing existing
  depends on the new modules until the barrel is wired (Phase 7).
- Phase 4 commits incrementally per sub-phase at each strictly-decreasing-error milestone
  (`task 299 phase 4{a,b,c,d}: ...`), with the import un-wired so `main` stays green throughout;
  the whole-file-green + re-wire milestone is 4d.
- If Phase 4c (the `modalExpandBranches_closed_unsat` redesign) stalls, keep 4a/4b committed
  green, mark 4c [BLOCKED], and `/spawn` a follow-up rather than shipping `sorry`/axioms.
- If Phase 6 (loop invariant) stalls, apply the zero-debt fallback documented there: spawn a
  follow-up task for the invariant, keep the sorry-free remainder committed, and mark task 299
  `[BLOCKED]`/`[PARTIAL]`. Never commit `sorry` or new axioms (CSLib hard requirement).
