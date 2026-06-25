# Implementation Plan: Task #299

- **Task**: 299 - Modal K Tableau Decision Procedure
- **Status**: [IMPLEMENTING]
- **Effort**: 14 hours
- **Dependencies**: None
- **Research Inputs**: specs/299_modal_k_tableau/reports/01_modal-k-tableau-research.md
- **Artifacts**: plans/01_modal-k-tableau-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, CSLib CONTRIBUTING.md (zero-sorry / zero-new-axiom)
- **Type**: cslib
- **Lean Intent**: false

## Overview

Implement a sound and complete tableau decision procedure for basic modal logic K
under `Cslib/Logics/Modal/Tableau/`, instantiating the label-generic CSLib Foundations
tableau layer with `F = Cslib.Logic.Modal.Proposition Atom` and `L = WorldIndex` (Nat).
The approach reuses the Foundations `SignedFormula`/`Branch`/`RuleResult`/`ClosureCondition`
types wholesale, copies the 5-file fuel-based architecture of the classical propositional
tableau, and borrows world-label / fresh-world / countermodel-extraction mechanics from the
proven sorry-free Bimodal tableau — but replaces the Bimodal S5 box rule ("propagate to all
worlds") with a K box rule scoped to an explicitly tracked accessibility edge relation.
Soundness is proved against `Cslib.Logic.Modal` Kripke semantics (validity over ALL models,
the simplest target); completeness is proved by extracting a finite Kripke countermodel from
an open saturated branch plus a modal truth lemma.

### Research Integration

Key findings driving this plan:
- **Reuse wholesale**: the Foundations `Cslib/Foundations/Logic/Tableau/*` layer is generic
  over `(F, L)`; `RuleResult.persistent` was added specifically to support modal box rules
  (tasks 299-301). No new core types are needed.
- **Architecture template**: classical propositional tableau (`Cslib/Logics/Propositional/
  Tableau/Classical/`) gives the fuel-based `expandBranches`/`processNext` worklist loop, the
  `ClassicalTableauResult` shape, the soundness fuel-induction lemma, and the sorry-free
  truth-lemma induction.
- **Modal mechanics template**: Bimodal tableau (`Cslib/Logics/Bimodal/Metalogic/
  Decidability/`) is sorry-free and supplies `WorldIndex = Nat`, `nextWorld`/`knownWorlds`,
  box/diamond rule enumeration, the `TimeOrdering` edge-list pattern (a `List (Nat × Nat)`
  threaded as an accumulating parameter — the direct template for K accessibility), and the
  `SemanticCountermodel` extraction shape with its two-mutual-induction truth lemma.
- **Type/namespace facts (verified)**: namespace is `Cslib.Logic.Modal` (singular Logic);
  formula type is `Proposition Atom` with constructors `atom | bot | imp | box`; and/or/neg/
  diamond are Lukasiewicz-encoded abbrevs, NOT constructors. Kripke `Model`, `Satisfies`,
  `Satisfies.box_iff_forall`, `Satisfies.diamond_iff_exists` exist in `Basic.lean` and are
  `@[scoped grind]`-tagged for reuse.
- **CRITICAL correctness constraint**: the Bimodal box rule is UNSOUND for K. K box-positive
  must propagate `T(φ)` only to recorded R-successors of the world, never to all worlds.
- **Top risk**: the classical completeness loop invariant `classicalExpandBranches_hintikka`
  is left `sorry` in the template (3 sorries) and is harder here because world creation
  interleaves with expansion. It is isolated into its own phase, and the zero-debt fallback
  (decompose or `[BLOCKED]`) is encoded as that phase's contingency.

### Prior Plan Reference

No prior plan.

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

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Completeness loop invariant (`expandBranches_hintikka`) cannot be closed | H | M | Isolated dedicated phase (Phase 6); prove a strong structural invariant (saturation + edge-closure of box-positives) up front in Phase 5; zero-debt fallback: decompose into a follow-up task or mark [BLOCKED], never ship sorry/axioms |
| Termination / fuel bound insufficient (diamond rules create worlds) | M | M | Use FMP-derived bound: worlds ≤ count of distinct ◇/F(□) subformula occurrences; cap fuel at subformula-closure × world bound; mirror Bimodal `soundFuel`/world-subset blocking, retargeted from times to worlds |
| Lukasiewicz decomposition match-ordering bugs (`impOf?` vs neg/or/and) | M | M | Write `@[simp]` reduction lemmas per encoded shape in Phase 1; `impOf?` must exclude encoded neg/or/and shapes; unit-test each shape with `#eval`/`example` before downstream use |
| S5 box rule accidentally copied (unsound for K) | H | L | Phase 2 explicitly scopes box-positive propagation to `successorsOf w` via the edge list; soundness Phase 4 has a `boxPos` preservation lemma that would fail for the S5 version |
| Hashable instance for `Proposition` missing | L | L | Mirror existing `instHashableProposition` pattern in Phase 1 (required by Foundations `Branch` ops) |
| Namespace/type drift from task description (`Formula` vs `Proposition`) | L | L | Use verified `Cslib.Logic.Modal.Proposition`; ignore the task description's `Formula` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4, 5 | 3 |
| 5 | 6 | 5 |
| 6 | 7 | 4, 6 |

Phases within the same wave can execute in parallel. Phase 4 (soundness) and Phase 5
(completeness scaffolding) both depend only on Phase 3 and are independent of each other, so
they may run concurrently; Phase 6 (the loop invariant) depends on Phase 5; Phase 7 (decision
procedure + CI) closes out after both soundness and completeness are done.

---

### Phase 1: Defs — types, complexity, Lukasiewicz decomposition [COMPLETED]

**Goal**: Establish `Cslib/Logics/Modal/Tableau/Defs.lean` with all foundational definitions
the rest of the procedure consumes, building cleanly against the Foundations layer.

**Tasks**:
- [ ] Create `Defs.lean` in namespace `Cslib.Logic.Modal.Tableau`, importing the Foundations
  `Tableau` modules and `Cslib.Logics.Modal.Basic`.
- [ ] Define `abbrev WorldIndex := Nat` and the initial world (`0`).
- [ ] Add `Hashable (Proposition Atom)` instance (mirror `instHashableProposition`) — required
  by Foundations `Branch`/`SignedFormula` ops.
- [ ] Define `Modal.Proposition.complexity` (mirror `Propositional/Subformula.lean`; `box`
  adds 1; `imp` is structural).
- [ ] Define Lukasiewicz decomposition functions matching encoded shapes:
  `negOf? (imp a bot) = some a`; `orOf? (imp (imp a bot) b) = some (a,b)`;
  `andOf? (imp (imp a (imp b bot)) bot) = some (a,b)`; `impOf?` EXCLUDING the encoded
  neg/or/and shapes; `boxOf? (box a) = some a`; `diaOf? (imp (box (imp a bot)) bot) = some a`.
- [ ] Add `@[simp]` reduction lemmas for each decomposition function; verify each shape with
  `example`/`#eval` to catch match-ordering bugs.

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Defs.lean` - new file (all of the above)

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.Defs` succeeds, no sorry.
- Each decomposition `@[simp]` lemma proves by `rfl`/`simp`; `impOf?` returns `none` on
  encoded neg/or/and shapes (checked by `example`).

---

### Phase 2: Rules — K modal rules + accessibility edges [COMPLETED]

**Goal**: Define the K rule application in `Rules.lean` and `Branch.lean`, with explicit
accessibility-edge tracking that makes box-positive propagation K-sound (not S5).

**Tasks**:
- [ ] Create `Branch.lean`: define `Accessibility := { edges : List (WorldIndex × WorldIndex) }`
  with `addEdge`, `successorsOf w`, plus `nextWorld`/`knownWorlds`/`maxWorld` helpers over the
  Foundations `Branch`. Add a box-propagation helper (apply T(φ) to all `successorsOf w`).
- [ ] Create `Rules.lean`: define `modalApplyOne sf branch acc` dispatching prop rules via
  `tryAllPropRules propAndOf? propOrOf? propImpOf? propNegOf?` (using Phase 1 fns) and the four
  K modal cases producing `RuleResult` + edge updates:
  - `boxPos` T(□φ)@w: `.persistent`, add T(φ)@w' for every `w' ∈ successorsOf w` (re-fires when
    new successors appear).
  - `diamondPos` T(◇φ)@w: create fresh w', add edge w→w', add T(φ)@w', re-apply w's box-
    positives to w'. Existential.
  - `boxNeg` F(□φ)@w: create fresh w', add edge w→w', add F(φ)@w'. Existential.
  - `diamondNeg` F(◇φ)@w: `.persistent`, add F(φ)@w' for every `w' ∈ successorsOf w`. Universal.
- [ ] Ensure box-positive propagation is scoped to the edge relation ONLY (no all-worlds
  propagation) — this is the K-vs-S5 correctness invariant.

**Timing**: 2.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Branch.lean` - new file (accessibility, world helpers)
- `Cslib/Logics/Modal/Tableau/Rules.lean` - new file (modal rule dispatch)

**Verification**:
- `lake build` of both files succeeds, no sorry.
- `#eval`/`example` smoke tests: T(□p)@0 with edge 0→1 propagates T(p)@1 but not to an
  unconnected world 2; T(◇p)@0 creates a fresh successor with T(p).

---

### Phase 3: Closure + Saturation — fuel loop and entry point [COMPLETED]

**Goal**: Wire closure and the fuel-based saturation loop, producing the runnable
`modalTableau φ` entry point and the Hintikka predicate completeness will need.

**Tasks**:
- [ ] Create `Closure.lean`: instantiate/re-export `ClassicalClosure` for the modal types
  (T(⊥) or T(φ)/F(φ) at same label). Thin file; no new closure logic.
- [ ] Create `Saturation.lean`: define `ModalTableauResult := closed | openBranch (Branch ...)`
  and the fuel-based `modalExpandBranches branches acc expandedSets fuel` with nested
  `processNext` worklist, maintaining `expandedSets.length = branches.length` and an
  `AppliedSet`/expanded guard to stop persistent rules re-firing.
- [ ] Define the fuel bound: FMP-derived `modalFuel φ` accounting for world creation
  (worlds ≤ distinct ◇/F(□) occurrences) × subformula closure; cap it. Add
  `termination_by fuel`.
- [ ] Add world-subset blocking (retarget Bimodal time-subset blocking to WORLDS): a fresh
  world whose signed-formula set ⊆ an ancestor's is blocked (finite model property).
- [ ] Define entry point `modalTableau φ := modalExpandBranches [[F(φ)]] emptyAcc [[]] (modalFuel φ)`.
- [ ] Define the `modalHintikkaSet b acc` downward-saturation predicate (open + every rule's
  outputs already present, including box/diamond edge-closure conditions).

**Timing**: 2.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Closure.lean` - new file (closure instance)
- `Cslib/Logics/Modal/Tableau/Saturation.lean` - new file (fuel loop, entry, Hintikka pred)

**Verification**:
- `lake build` succeeds, no sorry; termination accepted by Lean.
- `#eval modalTableau (□p ⟶ p)` etc. on small examples: a K-invalid formula yields an open
  branch, a K-valid formula yields `closed`.

---

### Phase 4: Soundness [IN PROGRESS]

> **RESUME NOTES (orchestrator, last touched this session).** `Soundness.lean` exists as an
> in-progress rewrite that a crashed implementation agent left mid-flight; it does **not**
> build. Current state of `lake build Cslib.Logics.Modal.Tableau.Soundness`: **RED**. The
> orchestrator applied exactly one fix — reordered `omit ... in` to sit *before* the docstring
> on `accFreshInv_empty` (~line 169) to clear a parse error; everything else below is unfixed.
> Detailed machine-readable inventory is in `.orchestrator-handoff.json`
> (`continuation_context.remaining_errors_in_soundness`). Summary of the ~10–12 distinct
> broken sites to fix (zero sorry, zero new axioms):
>
> - **`hnewBs` unknown identifier** at lines 303, 335, 362, 402, 649, 705 (~15 hits) — a binder
>   referenced by the wrong name (`obtain`/rename pattern), copy-pasted across several
>   `modalStepBranch_preserves_sat` case blocks. Fix one block, replicate to the rest.
> - **unsolved goals**: 99, 124, 173, 227
> - **`simp` made no progress**: 100 (remove/replace)
> - **failed to synthesize instance**: 126
> - **application type mismatch**: 129, 131, 151
> - **No goals to be solved**: 228 (delete trailing tactic)
> - **`cases` failed (nested error)**: 275, 624
> - **Duplicate alternative name `imp`**: 746 (in a match/cases)
>
> Use `lean_goal` / `lean_multi_attempt` on each site; do **not** paper over with `sorry`.
> Preserve K-correctness: box-positive propagates ONLY to recorded R-successors (not all
> worlds) — do not regress to the bimodal S5-collapse box rule. Commit "task 299 phase 4:
> soundness repaired to green" once `#print axioms modalTableau_sound` is clean, then proceed
> to Phase 5.
>
> **Environment hazard**: multiple concurrent Claude sessions share this one checkout; a
> sibling `git add -A` already swept this WIP file into commit `task 332 phase 2b`. Serialize
> sessions or use separate git worktrees before resuming.

**Goal**: Prove `modalTableau_sound` against Kripke semantics over all models.

**Tasks**:
- [ ] Create `Soundness.lean`. Define `branchSatisfiable b acc := ∃ (W) (m : Model W Atom)
  (assignment : WorldIndex → W respecting edges), every signed formula holds`.
- [ ] Per-rule satisfiability preservation (`modalRule_preserves_sat`):
  - prop rules via `Satisfies.and_iff`/`or_iff`/`impl_iff` (`@[scoped grind]` in Basic.lean).
  - `boxPos`: `Satisfies m w (□φ) ∧ w→w' → Satisfies m w' φ` via `Satisfies.box_iff_forall`
    (this lemma fails for the S5 all-worlds variant — guards K-correctness).
  - `diamondPos`: `Satisfies.diamond_iff_exists` gives a witness world; extend the
    label→world assignment to the fresh label.
  - `boxNeg`/`diamondNeg`: dual witnesses / universal propagation.
- [ ] Prove closed branches unsatisfiable (reuse `ClassicalClosure` reasoning).
- [ ] Lift via fuel-induction lemma `modalExpandBranches_closed_unsat` (induction on fuel,
  inner induction on pending worklist), mirroring `classicalExpandBranches_closed_unsat`.
- [ ] Prove `modalTableau_sound (h : modalTableau φ = .closed) : <φ valid over all models>` by
  contrapositive.

**Timing**: 2.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Soundness.lean` - new file

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.Soundness` succeeds, no sorry, no new axioms
  (`#print axioms modalTableau_sound` shows only standard axioms).

---

### Phase 5: Completeness scaffolding — model extraction + truth lemma [NOT STARTED]

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
out as a dedicated follow-up task via `/spawn`, leaving the rest of the procedure (Defs/Rules/
Branch/Closure/Saturation/Soundness + the truth lemma) committed sorry-free; and (b) mark task
299 `[BLOCKED]` (or `[PARTIAL]`) with a precise description of the remaining obligation. The
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

**Depends on**: 4, 6

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

- `Cslib/Logics/Modal/Tableau/Defs.lean`
- `Cslib/Logics/Modal/Tableau/Rules.lean`
- `Cslib/Logics/Modal/Tableau/Branch.lean`
- `Cslib/Logics/Modal/Tableau/Closure.lean`
- `Cslib/Logics/Modal/Tableau/Saturation.lean`
- `Cslib/Logics/Modal/Tableau/Soundness.lean`
- `Cslib/Logics/Modal/Tableau/Completeness.lean`
- Barrel/import update per ORGANISATION.md
- `modalTableau`, `modalTableau_sound`, `modalTableau_complete`, `modalTableau_decides`,
  and a `Decidable` instance.

## Rollback/Contingency

- All work is additive (new files under a new directory). Rollback = remove
  `Cslib/Logics/Modal/Tableau/` and revert the barrel/import change; nothing existing depends
  on the new modules until the barrel is wired (Phase 7), so earlier phases are safe to leave
  committed.
- Phases commit incrementally at each green (sorry-free) milestone (`task 299 phase {P}: ...`).
- If Phase 6 (loop invariant) stalls, apply the zero-debt fallback documented there: spawn a
  follow-up task for the invariant, keep the sorry-free remainder committed, and mark task 299
  `[BLOCKED]`/`[PARTIAL]`. Never commit `sorry` or new axioms (CSLib hard requirement).
