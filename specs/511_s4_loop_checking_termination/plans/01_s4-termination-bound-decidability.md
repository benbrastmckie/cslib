# Implementation Plan: Task #511 — S4 Loop-Checking Termination Bound & Decidability

- **Task**: 511 — s4_loop_checking_termination (follow-on to task 506, Phases 8-9)
- **Status**: [BLOCKED] — Phases 1-6 complete (sorry-free world bound); Phase 7 blocked on the
  driver-mismatch bridge, tracked by follow-on task 535 (dependency)
- **Effort**: 16 hours
- **Dependencies**: Task 506 (Phases 1-7 landed green); task 510 (generalized loop lemma — see Phase 7 finding: does NOT unblock S4)
- **Research Inputs**: specs/511_s4_loop_checking_termination/reports/01_s4-termination-guard-redesign.md; specs/511_s4_loop_checking_termination/handoffs/01_research-handoff.json
- **Artifacts**: plans/01_s4-termination-bound-decidability.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; cslib.md; lean4.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Task 506 landed the S4 loop-checking machinery (4-rule, `modalApplyOneS4`/`modalTableauS4`,
`modalHintikkaSetS4`, `extractModelS4`, `modalTruthLemmaS4`, `s4Valid` + soundness; zero
sorry/axiom) but left Phase 8 (the `#worlds` termination bound) and Phase 9 (fuel sufficiency +
`Decidable (s4Valid φ)`) [BLOCKED]. The research report proves both Phase 8 gaps are **structural**:
`worldSetsDistinct` over the live branch cannot be a loop invariant (relevant sets grow
monotonically, so a persistent step can fill the coordinate two worlds differed on — Gap 1), and
the minting guard `blockingWorld` compares the *source* world's set, not the *prospective
successor's* birth content (Gap 2). The fix (research Option A, accepted here) is to re-state the
invariant over **stable per-world birth keys** that never change after a world is born, and to make
the guard block on the successor's prospective content. Two further findings are encoded: the world
bound `2^|Sf|` is too small (the relevant-set notion distinguishes signs → codomain
`2^(2·|Sf|)`), and Phase 9 has an **independent** blocker — task 510's
`modalExpandBranchesGen_hintikka` requires `RuleApplicationSpec` + `ModalLoopInvGen` (rank fields
+ `geomCap`) + K-universe fuel, none of which S4 can supply. Definition of done: Phases 1-6 close
the world bound (`modalStepBranchS4_worldBound`) green; Phase 7 either closes decidability or lands
[BLOCKED] with a documented goal state and a spawned generalization task. Zero sorry, zero axiom
throughout; every phase independently CI-verifiable.

### Research Integration

The plan is a direct encoding of `reports/01_s4-termination-guard-redesign.md`:
- **Section 2 (both gaps proved structural)** → Phases 3-5 rebuild the guard and invariant over
  stable birth keys rather than the live branch.
- **Section 1.3 / Executive-Summary finding 3 (exponent mismatch)** → Phase 1 bumps
  `modalWorldBoundS4` to `2^(2·|Sf|)`.
- **Section 4 Option A (birth-content guard + monotone-lower-bound invariant)** → accepted as the
  design (Planner Decision 1 below); `keysTotal`/`keyLowerBd`/`keysDistinct`/`keysInUniverse`
  fields, threaded `keys` list, `blockingWorldS4` on `successorBirthContent` — Phases 2-5.
- **Section 5 (pigeonhole) + Section 6 reuse table** → Phase 6 uses `Finset.card_powerset`,
  `Finset.card_le_card_of_injOn` / `List.Nodup.length_le_card` (all confirmed present), reuses
  `modalWork`/`modalExpMeasure`/`sameRelevantSet`/`modalHintikkaSetGen` verbatim, and does NOT
  extend `ModalPotentialInv`.
- **Section 3 + Section 7 (Phase 9 independent blocker)** → Phase 7 records the decision (9-A
  shared-file interface vs 9-B S4-local re-derivation) and carries the standing permission to land
  [BLOCKED].

### Prior Plan Reference

The task 506 plan
(`specs/506_.../plans/01_s4-loopchecking-termination-decidability.md`) is reference context only
(not a template). From it and the task 511 description: Phases 1-7 are validated/landed green;
its Phase 8 BLOCKER note anticipated Gap 1 and Gap 2, and its "Task 510 Gate" gated on the
*conclusion* type of 510's loop lemma. The research corrects that gate — the conclusion aligns
(`rfl`) but the *hypotheses* are the real obstruction. The 506 plan's own fallback hint
(saturation-stable invariant) is preserved here as the documented Option B alternative, not the
chosen path. Effort calibration: the 506 machinery phases each ran multi-hour; the crux
(preservation) is budgeted generously (Phase 5, 3h).

### Roadmap Alignment

No `roadmap_path` was provided and no `roadmap_flag` was set for this dispatch; ROADMAP.md was not
consulted or modified. This task advances the modal-logic decidability track (S4 fragment) shared
with tasks 505 (B-system) and 513, which the Phase 7 9-A option would benefit.

## Goals & Non-Goals

**Goals**:
- Correct the S4 world bound to a provable finite value (`2^(2·|Sf|)`).
- Redesign the minting guard to block on the prospective successor's birth content (fixes Gap 2).
- Re-state `S4LoopInv` over stable birth keys so distinctness is a genuine per-step invariant
  (fixes Gap 1), with all four key-fields preserved by every `modalStepBranchS4` step.
- Prove the pigeonhole world bound `modalKnownWorlds_length_le_worldBoundS4` and
  `modalStepBranchS4_worldBound` as loop invariants (closes Phase 8).
- Make the explicit decision on the Phase 9 approach (9-A vs 9-B) and either close
  `Decidable (s4Valid φ)` or land [BLOCKED] with a precise handoff and a spawned task.
- Zero sorry, zero axiom in every landed phase.

**Non-Goals**:
- Modifying `FmpMeasure.lean` or any K/T declarations (research Section 6: `S4LoopInv` is a
  sibling, `ModalPotentialInv` is NOT extended).
- Shipping the tight `2^|Sf|` bound (unprovable for the sign-distinguishing relevant-set notion).
- Implementing the cross-cutting 9-A termination-measure interface *inside* task 511 (it touches
  `CompletenessLoop.lean` / K's consumers and benefits 505/513 — recommended as a separate spawned
  task; see Phase 7).
- Any `sorry`/`axiom`/vacuous-placeholder path (prohibited by cslib.md; Option B is a documented
  alternative design, not a debt shortcut).

## Planner Decisions (resolving the report's open questions)

1. **Guard/invariant design: accept Option A** (birth-key threading via an S4-specific step). It
   yields the tight-enough bound, and Section 3 shows Phase 9 needs an S4-specific loop regardless,
   so the incremental cost of the driver change is low and the two changes compose. Option B
   (saturated-world invariant, no driver change) is retained as a documented fallback if the
   Phase-4 driver change proves too invasive.
2. **Phase 9 approach: recommend 9-A as a SEPARATE spawned task**, not inline. The abstract
   termination-measure interface lives in the shared `CompletenessLoop.lean`, touches K's consumers,
   and benefits tasks 505/513 — it should be coordinated as its own task to avoid churn in 511.
   Within 511, Phase 7 lands the cheap S4-local pieces (the `rfl` Hintikka-alignment bridge) and,
   if 9-A is not yet available, either attempts the 9-B S4-local re-derivation within budget or
   lands [BLOCKED] with a documented goal state and spawns the 9-A task.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Guard rewrite (Phase 3) breaks Phase 5-7 truth-lemma consumers | H | M | Consumers depend only on `modalApplyOneS4`'s *non-minting* behavior, which is unchanged; re-CI the box-pos/dia-neg bridges and `modalTruthLemmaS4` at Phase 3 end and fix any signature drift before proceeding |
| Threading `keys` (Phase 4) means S4 no longer reuses `modalStepBranchGen` definitionally for stepping | M | H (by design) | Section 3 shows Phase 9 needs an S4-specific loop anyway; design Phase 4 and Phase 7's loop together; keep the rule-slot reuse intact |
| `_preserves_keysDistinct` (Phase 5, the crux) resists closing in one run | H | M | Budget 3h; if it resists, mark Phase 5 [BLOCKED] with the exact open goal and split — do NOT weaken the invariant to something vacuous (cslib.md) |
| Phase 9 decidability cannot close without the 9-A/9-B generalization | H | H | Standing permission to land Phase 7 [BLOCKED] with documented goal state; spawn the 9-A task; Phases 1-6 (the world bound) are the self-contained deliverable and stand on their own |
| Exponent bump ripples into `modalUniverseS4_length_le` value | L | L | Only the numeric value changes, not the proof structure (`omega`/`ring`); re-verify at Phase 1 end |
| `modalKnownWorlds` nodup needed for pigeonhole | L | M | Small `modalKnownWorlds_nodup` helper (its `foldl` guards duplicates via `ws.any (· == sf.label)`); likely one-line |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5, 2 |
| 7 | 7 | 6 |

Phases within the same wave can execute in parallel. This plan is a tightly-coupled formal-proof
chain, so each wave contains a single phase.

### Phase 1: Exponent fix — bound `2^(2·|Sf|)` [COMPLETED]

- **Goal:** Correct `modalWorldBoundS4` to the provable pigeonhole codomain size and re-verify the
  universe length bound. Independent, low risk, land first.
- **Tasks:**
  - [ ] Change `modalWorldBoundS4 φ₀` (LoopChecking.lean:868) from `2 ^ (modalSubfmls φ₀).length`
    to `2 ^ (2 * (modalSubfmls φ₀).length)`; update the surrounding docstring (lines 858-869) to
    state the codomain is `powerset(Sign × Sf)`, card `2^(2·|Sf|)`.
  - [ ] Re-verify `modalUniverseS4_length_le` (LoopChecking.lean:884-915) still closes — its RHS
    `2 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1)` is unaffected in *form*; only
    the numeric bound changes. Fix the `omega`/`ring`/`calc` steps if the literal value shift
    perturbs them.
  - [ ] Confirm no other current reference to `modalWorldBoundS4` assumes the old value.
- **Timing:** 1 hour
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — `modalWorldBoundS4`, docstring,
    `modalUniverseS4_length_le`
- **Verification:** `lake build Cslib.Logics.Modal.Tableau.LoopChecking`; `lean_verify` shows zero
  sorry/axiom for `modalWorldBoundS4`, `modalUniverseS4`, `modalUniverseS4_length_le`.

### Phase 2: Finite signed-key infrastructure + powerset cardinality [COMPLETED]

- **Goal:** Introduce the stable-key finite codomain and the cardinality bridge the pigeonhole
  consumes. Pure defs + lemmas, no driver change, CI-green in isolation.
- **Tasks:**
  - [x] Define `signedSubfmls φ₀ : Finset (Sign × Proposition Atom)` (both signs × every
    subformula of `φ₀`) and `relevantSetFinset φ₀ b w : Finset (Sign × Proposition Atom)`
    (the live relevant set `R(b,w)` as a `Finset`, reusing `sameRelevantSet`'s membership notion).
  - [x] Prove `signedSubfmls_card_le : (signedSubfmls φ₀).card ≤ 2 * (modalSubfmls φ₀).length`
    *(deviation: altered -- proved `≤` rather than the plan's stated `=`. `signedSubfmls` is
    defined via `{pos,neg} ×ˢ (modalSubfmls φ₀).toFinset`, a `Finset` construction, so exact
    equality would additionally need `modalSubfmls φ₀` duplicate-free (no such lemma exists in
    `FmpMeasure.lean`). The pigeonhole argument (Phase 6) only ever consumes an upper bound on
    `(signedSubfmls φ₀).card`, so `≤` is sufficient and strictly simpler -- no loss of guarantee.)*
  - [x] Prove `signedSubfmls_powerset_card_le : (signedSubfmls φ₀).powerset.card ≤ modalWorldBoundS4 φ₀`
    via `Finset.card_powerset` and `signedSubfmls_card_le` plus `Nat.pow_le_pow_right`
    *(deviation: altered -- `≤` in place of the plan's stated `=`, same reasoning as above; this
    is why Phase 1 precedes: ties the bound to `2^(2·|Sf|)`)*.
  - [x] Prove `relevantSetFinset_subset_signedSubfmls : relevantSetFinset φ₀ b w ⊆ signedSubfmls φ₀`
    *(deviation: altered -- no `modalUniverseS4`-closure side-condition needed: `relevantSetFinset`
    is defined as a `Finset.filter` of `signedSubfmls φ₀`, so the subset fact is
    `Finset.filter_subset` unconditionally, strictly stronger than the plan anticipated)* and
    `relevantSetFinset_mono : (∀ sf ∈ b, sf ∈ b') → relevantSetFinset φ₀ b w ⊆ relevantSetFinset φ₀ b' w`
    (monotonicity — the fact Gap 1 exploited and the lower-bound invariant survives).
- **Timing:** 2 hours
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — new defs/lemmas in the `S4LoopInv` region
    (or a new `FmpMeasure`-sibling section if the file grows unwieldy; keep in LoopChecking unless
    forced to split)
- **Verification:** `lake build Cslib.Logics.Modal.Tableau.LoopChecking`; `lean_verify` zero
  sorry/axiom for each new lemma; `signedSubfmls_powerset_card` reduces to `modalWorldBoundS4 φ₀`.

### Phase 3: Successor-birth-content guard redesign [COMPLETED]

- **Goal:** Fix Gap 2 — make the guard block on the prospective successor's birth content, not the
  source world's set. Rewrite `modalApplyOneS4` to consult the new guard; re-verify Phase 5-7
  consumers are unaffected.
- **Tasks:**
  - [x] Define `successorBirthContent φ₀ b s φ w : Finset (Sign × Proposition Atom)` — the witness
    `⟨s,φ⟩` plus the S4 box-context transmitted from `w` (`{⟨.pos,ψ⟩ : T(□ψ)@w ∈ b}` ∪
    `{⟨.neg,ψ⟩ : F(◇ψ)@w ∈ b}`), matching the actual K-minting birth content (research Section 1.1,
    Gap 2 in Section 2).
  - [x] Define `blockingWorldS4 φ₀ b s φ w : Option WorldIndex` — block iff some existing known
    world's CURRENT `relevantSetFinset` equals the prospective `successorBirthContent`.
  - [x] Prove the guard contract lemmas: `blockingWorldS4_none_fresh` (when `= none`, the
    prospective birth content differs from every existing world's relevant set) and
    `blockingWorldS4_mem_modalKnownWorlds` *(deviation: altered -- named `_mem_modalKnownWorlds`
    rather than the plan's `_some_mem`, matching the existing `blockingWorld_mem_modalKnownWorlds`
    naming convention it supersedes)* (the returned world is in `modalKnownWorlds b`); also added
    `blockingWorldS4_eq_birthContent` (the `some wBlock` case's positive contract: `wBlock`'s
    *current* relevant set equals the prospective birth content -- needed by Phase 5's
    `_preserves_keysDistinct`, symmetric to the `_none_fresh` negative contract, not explicitly
    named in the plan but implied by "the guard contract lemmas").
  - [x] Rewrite `modalApplyOneS4` (now consulting `blockingWorldS4` at the two minting shapes,
    `⟨.neg,.box φ,w⟩` / `⟨.pos,.diamond φ,w⟩`) in place of `blockingWorld`, which is removed
    (superseded, no external consumers). Leave all *non-minting* arms byte-identical.
  - [x] Re-CI the consumers that depend on `modalApplyOneS4`: `hintikkaS4_box_pos_step`, the
    dia-neg dual, the crux bridges, and `modalHintikkaSetS4`/`modalTruthLemmaS4` (`FrameCompleteness.lean`)
    all still build green unchanged -- their dependence is on `modalApplyOneS4_eq_of_not_boxNeg_diaPos`
    (the non-minting-shape agreement lemma), whose proof did not reference `blockingWorld`'s
    internals and needed no edits.
- **Timing:** 2.5 hours
- **Depends on:** 2
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — `successorBirthContent`, `blockingWorldS4`,
    guard-contract lemmas, `modalApplyOneS4`
  - `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — only if a consumer there references the
    guard
- **Verification:** `lake build Cslib.Logics.Modal.Tableau.LoopChecking` and
  `... .FrameCompleteness`; all Phase 5-7 (of task 506) lemmas still build; `lean_verify` zero
  sorry/axiom on the new guard defs and the rewritten `modalApplyOneS4`.

### Phase 4: Key-threaded S4 step/driver + restated `S4LoopInv` [COMPLETED]

- **Goal:** Thread stable per-world birth keys through an S4-specific step, and replace the broken
  `worldSetsDistinct` field with the four monotone-stable key fields. Structure + driver compiles
  green even before preservation is proved.
- **Tasks:**
  - [x] Define the S4-specific step (`modalStepBranchS4Keyed`) carrying `keys : List (WorldIndex ×
    Finset (Sign × Proposition Atom))` alongside `(b, e, acc)` (research Option A2). On an
    unblocked minting call, appends `(modalNextWorld b, successorBirthContent …)`; on every other
    call (blocked minting-shaped, or non-minting), `keys` is unchanged. Reuses the K rule-slot
    (`modalApplyOneS4 φ₀`) for the formula work — only the stepping wrapper is S4-specific
    *(deviation: no separate bridge lemma to `modalStepBranchS4` was proved in this phase --
    deferred to Phase 5/6 if their preservation proofs need it; not required for Phase 4's
    "compiles green" deliverable)*.
  - [x] Replace `S4LoopInv`'s `worldSetsDistinct` field with: `keysTotal` (∀ known world ∃ recorded
    key), `keyLowerBd` (each key ⊆ its live `relevantSetFinset` — the monotone-stable lower bound),
    `keysDistinct` (distinct worlds ⇒ distinct keys), `keysInUniverse` (each key ⊆ `signedSubfmls
    φ₀`). Keeps the six rule-independent fields (`bClosure`/`eNodup`/`eClosure`/`accFresh`/
    `accKnown`/`outDegEq`) over `modalUniverseS4`. Adds the `keys` parameter to the structure.
  - [x] No other references to `S4LoopInv`/`worldSetsDistinct` existed anywhere in the codebase
    (confirmed via `grep`) — zero ripple.
- **Timing:** 2.5 hours
- **Depends on:** 3
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — S4 step wrapper, `S4LoopInv` structure
- **Verification:** `lake build Cslib.Logics.Modal.Tableau.LoopChecking`; the restated structure
  and the S4 step definition typecheck; `lean_verify` zero sorry/axiom on the new definitions.

### Phase 5: `S4LoopInv` preservation lemmas — the crux [COMPLETED]

- **Goal:** Prove every `modalStepBranchS4Keyed` step preserves the four key fields. This is the
  mathematical heart of the task; budget generously.
- **Tasks:**
  - [x] **Guard redesign** (recorded-keys comparison, the fix the prior dispatch's blocker called
    for): `blockingWorldS4Keyed` -- compares the prospective birth content against `keys`
    directly, not against worlds' live `relevantSetFinset` -- plus its guard-contract lemmas
    (`blockingWorldS4Keyed_eq_birthContent`, `blockingWorldS4Keyed_none_fresh`). `modalApplyOneS4`
    and `blockingWorldS4` (task 511 Phase 3, task 506's Hintikka/truth-lemma bridges) are
    untouched. `modalApplyOneS4Keyed`/`modalStepBranchS4Keyed` redefined to drive BOTH the
    `(b,e,acc)` bookkeeping and the `keys` bookkeeping from this same keys-aware decision
    (blocker's Option (a): bypasses `modalApplyOneS4`'s own internal live-set guard at the two
    minting shapes entirely, rather than threading `keys` into `modalApplyOneS4` itself).
  - [x] `modalStepBranchS4_preserves_keysDistinct` -- **CLOSED** as
    `keysUpdate_preserves_keysDistinct`: the specific fact the prior dispatch proved impossible
    under the live-set guard now follows directly from `blockingWorldS4Keyed_none_fresh`, with
    *no* live-set indirection and *no* freshness argument about the new world index (the one case
    that would need it -- an existing key's world coinciding with the new one -- is vacuously
    excluded by `keysDistinct`'s own `w1 ≠ w2` hypothesis). Standalone, assumption-carrying lemma
    (takes pre-step `keysDistinct` as a hypothesis, as it will be consumed once assembled as an
    induction step).
  - [x] **`keyLowerBd`'s minting-case fact -- CLOSED**, as two standalone lemmas
    `successorBirthContent_boxNeg_subset_relevantSetFinset` /
    `successorBirthContent_diamondPos_subset_relevantSetFinset`: `successorBirthContent φ₀ b s φ w
    ⊆ relevantSetFinset φ₀ (newForms ++ b) (modalNextWorld b)` (only `⊆` is needed --
    `keyLowerBd` itself is stated as a subset, not an equality, narrower than the prior dispatch's
    `Finset.ext` attempt). Technique: convert every `List.any (· == t) = true`/`= false` fact
    to/from a plain `t ∈ l`/`t ∉ l` membership fact immediately (two tiny helper lemmas
    `any_beq_of_mem_S4`/`mem_of_any_beq_S4`), then work purely with `List.mem_*` combinators and
    `List.mem_filterMap` -- this avoided the `Bool`-vs-`Prop` bridging trap the prior dispatch got
    stuck in. Also landed: `modalNextWorld_fresh_beq_S4` (freshness in `any`-form),
    `mem_signedSubfmls_of_formula_S4` (S4-local restatement of `S5Simplification.lean`'s
    file-private `mem_signedSubfmls_of_formula_S5w`). Zero sorry, zero new axiom
    (`lean_verify`: `propext`/`Classical.choice`/`Quot.sound` only).
  - [x] **Driver-level groundwork for the assembly -- landed, reusable**:
    `modalApplyOneS4Keyed_boxNeg_blocked_eq`/`_unblocked_eq`/`_diaPos_blocked_eq`/`_unblocked_eq`
    (four guard-spec lemmas for the keyed rule application, mirroring the existing
    `modalApplyOneS4_boxNeg_blocked_eq` family) and `modalStepBranchS4Keyed_branch_superset` (every
    branch `modalStepBranchS4Keyed` produces is a superset of the pre-step branch, regardless of
    which rule fired -- the fact that lets OLD keys' `keyLowerBd` obligation survive any step via
    `relevantSetFinset_mono`, generically reusable for `keysTotal`/`keysInUniverse` preservation
    too). All landed, green, zero sorry/axiom.
  - [x] **`modalStepBranchS4_preserves_keyLowerBd` -- CLOSED.** Assembled via a reusable
    result-shape-agnostic extraction helper `modalStepBranchS4Keyed_result_keys_eq` (factors the
    "case on `RuleResult`, discard everything but the `keys'` 4th tuple component" boilerplate
    into ONE lemma, since `keys'` never actually depends on `result`'s shape), then a single
    `sf.sign, sf.formula` case split (`rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula
    with _ | _ | _ | _ | _ | ψ | ψ`, 14 goals) closed via `all_goals first | exact hold ... |
    skip` (12 of 14 close uniformly via the old-keys argument) plus two explicit `case
    neg.neg.box =>`/`case neg.pos.diamond =>` blocks for the minting-unblocked leaves, each
    pinning `newForms` exactly via `modalApplyOneS4Keyed_*_unblocked_eq` + the mint_fst lemmas
    and applying the closed subset lemma. Zero sorry, zero new axiom.
  - [x] **`modalStepBranchS4_preserves_keysInUniverse` -- CLOSED.** Simpler than `keyLowerBd`
    (independent of `newBs`): old keys via the `keysInUniverse` hypothesis directly (`keys ⊆
    keys'` always), new keys via a new reusable helper
    `successorBirthContent_subset_signedSubfmls` (the `insert (s,φ)` component needs
    `mem_signedSubfmls_of_formula_S4`; the filtered remainder is `Finset.filter_subset`
    directly). Zero sorry, zero new axiom.
  - [x] **`modalStepBranchS4_preserves_keysTotal` -- CLOSED.** Built the missing known-worlds
    dichotomy for `modalApplyOneS4Rules` (composing K+T+4 layers) via local re-derivations
    (`mem_successorsOf_hasEdge_S4`, `mem_modalKnownWorlds_S4`, `modalKnownWorlds_mono_append_S4`,
    `mintGroup_label_eq_freshWorld_S4` -- all private, cross-file-unavailable originals mirrored
    from `S5Simplification.lean`/`FmpMeasure.lean`), the composed T+4-layer dichotomy
    (`modalApplyOneT_boxPos_diaNeg_known_S4`, `modalApplyOneS4Rules_boxPos_diaNeg_known_S4`),
    the non-modal-shape fact (`modalApplyOne_nonModal_known_S4`), the composite
    `modalApplyOneS4Keyed_nonMint_known_S4` (12 non-minting leaves), and
    `modalStepBranchS4Keyed_keys_subset` (`keys ⊆ keys'` always). Assembled via the SAME
    hkeq/case-split skeleton `keyLowerBd`/`keysInUniverse` used, split top-level on the two
    minting shapes vs the 12 non-minting ones. Zero sorry, zero new axiom (`lean_verify`:
    `propext`/`Classical.choice`/`Quot.sound` only). **All 4 of `S4LoopInv`'s key fields
    (`keysDistinct`/`keyLowerBd`/`keysInUniverse`/`keysTotal`) are now CLOSED.**
  - [x] **`modalStepBranchS4_preserves_keysDistinct` -- driver-level wrapper CLOSED** (the
    combinator `keysUpdate_preserves_keysDistinct` was already closed dispatch 2, but the
    `modalStepBranchS4Keyed`-level wrapper the assembly needs had not been built until this
    dispatch).
  - [x] **`modalStepBranchS4_preserves_eNodup` -- CLOSED.** Fully rule/keys-agnostic (only the
    top-level `RuleResult` constructor shape matters), direct case split mirroring the generic
    `modalStepBranch_preserves_expandedNodup_gen`'s proof shape.
  - [x] **`modalStepBranchS4_preserves_outDegEq` -- CLOSED.** Reuses K's own public
    `modalApplyOne_outDeg_step` at the minting shapes' unblocked sub-case; the blocked sub-case
    reuses the identical `outDeg_addEdge_self_S4`/`_ne_S4` argument since `outDeg`'s bookkeeping
    is insensitive to whether the edge's target is fresh or a recorded-key world.
  - [x] **`modalStepBranchS4_preserves_accFresh`/`_accKnown` -- CLOSED.** Landed a new
    proof-internal auxiliary invariant `keysWorldsKnown` (every recorded key's world is a known
    branch world; NOT a new `S4LoopInv` field -- threaded as an extra hypothesis/conclusion
    alongside the struct instead, to avoid reopening the completed Phase 4 design) plus its own
    preservation lemma. This was the key missing piece the "generic bridge" plan (below, now
    superseded) did not anticipate: `modalApplyOneS4Keyed`'s guard-BLOCKED minting sub-case adds
    an edge to `blockingWorldS4Keyed`'s result (a recorded-key world), NOT a genuinely fresh
    witness, so the standard `hFreshLocal`-style dichotomy the generic `_gen` lemmas need
    (`(apply sf b acc).fst = .linear (wsf::rest)` nonempty, headed by the target) does NOT hold
    there (`modalApplyOneS4Keyed`'s blocked case returns `.linear []`, genuinely empty) --
    `keysWorldsKnown` is what closes the gap instead, via `modalNextWorld_gt`.
  - [x] **Assemble `modalStepBranchS4_preserves_S4LoopInv` -- LANDED, 8/10 fields closed.** The
    four key fields (dispatches 2-5) plus `eNodup`/`outDegEq`/`accFresh`/`accKnown` (this
    dispatch) are fully closed, zero sorry. **`bClosure`/`eClosure` are landed as documented
    strategic-sorry skeletons** (`modalStepBranchS4_preserves_bClosure`/`_eClosure`), each a
    complete, non-vacuous theorem statement with `sorry` body -- see the continuation note below
    for exactly what each needs. **The "generic bridge to `modalStepBranchGen`" plan below is
    SUPERSEDED**: discovered this dispatch that the generic `_gen` lemmas' `hFreshLocal`/
    `hOutDegStep`-style per-call hypotheses do not cleanly retrofit to `modalApplyOneS4Keyed`
    (the guard's blocked case's `.linear []` shape breaks `hFreshLocal`'s dichotomy, and
    `modalStepBranch_eClosure_gen`/generic `bClosure` are keyed to K's own `modalUniverse`/
    `modalWorldBound`, not `modalUniverseS4`/`modalWorldBoundS4`) -- every field actually closed
    this dispatch used a DIRECT case split on `modalStepBranchS4Keyed`'s own definition instead
    (the same style as the four key fields), not the generic bridge.
- **Timing:** ~13 hours across six dispatches (3h dispatch 1: analysis + counterexample, no code;
  ~2h dispatch 2: guard redesign, `keysDistinct` closure, bounded `keyLowerBd` attempt that did not
  close; ~2h dispatch 3: closed `keyLowerBd`'s minting-case fact plus driver-level assembly
  groundwork; ~2h dispatch 4: assembled `modalStepBranchS4_preserves_keyLowerBd` fully, landed
  `modalStepBranchS4_preserves_keysInUniverse`, landed Phase 7's independent
  `modalHintikkaSetS4_eq` bridge; ~2h dispatch 5: closed `modalStepBranchS4_preserves_keysTotal`
  -- the crux -- by building the full K+T+4 known-worlds dichotomy from scratch; this dispatch
  (~2h): closed 4 more fields (`eNodup`/`outDegEq`/`accFresh`/`accKnown`), landed the assembly
  theorem with 8/10 fields fully closed and 2 documented strategic sorries for the remaining
  `bClosure`/`eClosure`).
- **Depends on:** 4

**Continuation note** (this dispatch -- 8/10 `S4LoopInv` fields now CLOSED; `bClosure`/`eClosure`
are documented strategic-sorry skeletons, the last remaining gap before Phase 5 fully closes):

- **What's now closed this dispatch**:
  - `modalStepBranchS4_preserves_keysDistinct` -- driver-level wrapper around the already-closed
    `keysUpdate_preserves_keysDistinct` combinator.
  - `modalApplyOneS4Keyed_nonMint_snd_eq_acc` -- composite: `acc` is literally unchanged at all
    12 non-minting shapes (mirrors `modalApplyOneS4Keyed_nonMint_known_S4`'s case split,
    extracting the `.snd`-half instead of the known-worlds half).
  - `modalStepBranchS4_preserves_eNodup` -- fully rule/keys-agnostic.
  - `outDeg_addEdge_self_S4`/`_ne_S4`, `modalApplyOne_boxNeg_mint_snd_S4`/
    `_diamondPos_mint_snd_S4` (local re-derivations/twins of existing groundwork) plus
    `modalStepBranchS4_preserves_outDegEq` -- reuses K's own public `modalApplyOne_outDeg_step`
    at the unblocked minting sub-case; the blocked sub-case's `outDeg` bookkeeping is insensitive
    to whether the edge target is fresh or a recorded-key world.
  - **`keysWorldsKnown`, a new proof-internal auxiliary invariant** (`∀ w k, (w,k) ∈ keys → w ∈
    modalKnownWorlds b`; deliberately NOT a new `S4LoopInv` struct field, to avoid reopening the
    completed Phase 4 design -- threaded as an extra hypothesis/conclusion alongside the struct
    at every call site instead) plus its own preservation lemma
    `modalStepBranchS4_preserves_keysWorldsKnown`.
  - `accFreshInv_append_S4`/`hasEdge_addEdge_cases_S4` (local re-derivations) plus
    `modalStepBranchS4_preserves_accFresh`/`_accKnown` -- CLOSED, both consuming
    `keysWorldsKnown` at the guard's BLOCKED minting sub-case (see the design-correction note
    below).
  - [x] `modalStepBranchS4_preserves_S4LoopInv` -- **LANDED, ALL 10/10 FIELDS CLOSED, ZERO
    SORRY.** The four key fields (dispatches 2-5) plus `eNodup`/`outDegEq`/`accFresh`/`accKnown`
    (dispatch 6) plus `bClosure`/`eClosure` (this dispatch, closing Phase 5 completely). See the
    "bClosure`/`eClosure`" docstring section in `LoopChecking.lean` (immediately above
    `modalStepBranchS4_preserves_eClosure`) for the closure details: `eClosure` turned out
    immediate (a prior dispatch's continuation note had mis-attributed the T-self/4-propagation
    composite to `eClosure` instead of `bClosure`); `bClosure` needed that composite
    (`modalApplyOneS4Keyed_nonMint_universe_S4`) plus Phase 6's pigeonhole world-bound
    (`modalStepBranchS4_worldBound`) as a genuine prerequisite for its 2 minting shapes.

- **Design correction (dispatch 6, still valid)**: the "generic bridge to `modalStepBranchGen`"
  plan was superseded -- `modalApplyOneS4Keyed`'s guard-BLOCKED minting sub-case's `.linear []`
  shape breaks the generic `_gen` lemmas' `hFreshLocal` dichotomy, and the generic `eClosure`/
  `bClosure` facts are keyed to K's own `modalUniverse`/`modalWorldBound`, not
  `modalUniverseS4`/`modalWorldBoundS4`. Every field in Phase 5, including `bClosure`/`eClosure`
  (this dispatch), used a DIRECT case split on `modalStepBranchS4Keyed`'s own definition
  instead. The bridge lemma was never built and is not needed by any landed proof.

- **Prohibited workarounds**: Did NOT use `def X := True`/`trivial` or any vacuous placeholder
  anywhere, at any point across all dispatches. Did NOT weaken any `S4LoopInv` field's statement
  to force a proof through.

- **Verification:** `lake build Cslib.Logics.Modal.Tableau.LoopChecking` green (scoped). Zero
  `sorry` in the file (`grep -c '\bsorry\b'` on non-comment lines confirms). `lean_verify` on
  `modalStepBranchS4_preserves_S4LoopInv` itself: `propext`/`Classical.choice`/`Quot.sound`
  only, no `sorryAx`. `lake exe checkInitImports`/`lake exe lint-style` clean on the modified
  file. Full-project `lake build` fails entirely in unrelated concurrent-session files
  (`Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination/*.lean`,
  task 517/530/531 sessions per `git status`) -- confirmed not this task's file scope, not a
  regression.

### Phase 6: Pigeonhole world bound (closes Phase 8) [COMPLETED]

- **Goal:** Derive the finite world bound from the preserved invariant — the deliverable that
  closes the original task 506 Phase 8.
- **Tasks:**
  - [x] `modalKnownWorlds_nodup_S4` helper — landed as a local re-derivation of
    `FmpMeasure.lean`'s file-private `modalKnownWorlds_nodup` (unavailable across files),
    mirroring `S5Simplification.lean`'s `modalKnownWorlds_nodup_S5`.
  - [x] `modalKnownWorlds_length_le_worldBoundS4` — landed exactly as specified: injects known
    worlds into `keys` via `keysTotal` (using `Classical.choice`/`Exists.choose` to extract a
    canonical key per known world), injectivity via `keysDistinct`, codomain bound via
    `keysInUniverse` + `signedSubfmls_powerset_card_le`, cardinality via
    `Finset.card_le_card_of_injOn` + `List.toFinset_card_of_nodup`.
  - [x] `modalStepBranchS4_worldBound : modalMaxWorld b < modalWorldBoundS4 φ₀` — landed. The
    "worlds are consecutive from 0" fact needed a genuine new proof-internal auxiliary invariant
    `worldsContiguousS4 b := ∀ w ≤ modalMaxWorld b, w ∈ modalKnownWorlds b` (not anticipated in
    this task list's original wording; NOT an `S4LoopInv` field, mirrors the `keysWorldsKnown`
    precedent from dispatch 6, threaded as an extra hypothesis/conclusion) plus its own
    preservation lemma `modalStepBranchS4_preserves_worldsContiguousS4`, since density of world
    labels does not otherwise follow from `S4LoopInv`'s existing fields alone. Combined with the
    length bound: `modalMaxWorld b + 1 ≤ (modalKnownWorlds b).length ≤ modalWorldBoundS4 φ₀`.
  - [x] Used as a byproduct to discharge `modalStepBranchS4_preserves_bClosure`'s sorry (Phase
    5) — see Phase 5's closure note above.
- **Timing:** ~3 hours (this dispatch, combined with the `bClosure`/`eClosure` closure work).
- **Depends on:** 5, 2
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — pigeonhole lemmas
- **Verification:** `lake build Cslib.Logics.Modal.Tableau.LoopChecking` green. `lean_verify`
  zero sorry/axiom (`propext`/`Classical.choice`/`Quot.sound` only) on
  `modalKnownWorlds_length_le_worldBoundS4`, `modalStepBranchS4_worldBound`, and
  `modalStepBranchS4_preserves_worldsContiguousS4`. This phase closing = original Phase 8
  resolved.

### Phase 7: Phase 9 decidability — decision + closure or documented [BLOCKED]

- **Goal:** Land the cheap S4-local alignment, make the 9-A/9-B decision concrete, and either close
  `Decidable (s4Valid φ)` against `Cube.S4` or land [BLOCKED] with a precise handoff and a spawned
  generalization task.
- **Tasks:**
  - [x] Land the Hintikka-alignment bridge `modalHintikkaSetS4_eq` :
    `modalHintikkaSetS4 φ₀ b acc = modalHintikkaSetGen (modalApplyOneS4 φ₀) b acc` (research
    Section 8: verified `rfl` — Saturation.lean:460 vs LoopChecking.lean, closes by `rfl`).
    This item is independent of Phases 5/6's completion and lands regardless. Zero sorry/axiom.
  - [x] Record the decision (Planner Decision 2): the abstract termination-measure interface (9-A)
    is a shared-file change in `CompletenessLoop.lean` benefiting 505/513 — **spawn it as a separate
    task** (`/spawn 511 "abstract termination-measure interface for S4/B loop lemma"`), do NOT
    inline it. Task 510's `modalExpandBranchesGen_hintikka` is confirmed NOT instantiable for S4
    (requires `RuleApplicationSpec` + `ModalLoopInvGen` rank fields + `geomCap` + K-universe fuel —
    research Section 3). **Update (this dispatch)**: a task 515 dispatch (concurrent/later,
    `CompletenessLoop.lean` commit `ecfa123e`) has ALREADY landed a more general, rank-free
    top-loop lemma `modalExpandBranchesHintikka` parametrized by an abstract `Aux : List SF →
    List SF → Accessibility → Prop` (`AuxStepPreserved`/`AuxBounds`/`ModalLoopInvHintikka`,
    `CompletenessLoop.lean:262-378`), built for S5's needs (`ModalLoopAuxS5w`). This is a strong
    head start on 9-A and should be the entry point for the spawned task's investigation — but
    see the "genuine gap identified" note below: even this generalized interface does not by
    itself close S4, for a structural reason not previously documented.
  - [ ] If the 9-A task is already available (or within budget as 9-B S4-local re-derivation port
    of `processNext`'s fuel induction over `modalUniverseS4` with `S4LoopInv`): wire fuel
    sufficiency from `modalStepBranchS4_worldBound` (Phase 6) and derive
    `Decidable (s4Valid φ)` + `s4Valid` completeness against `Cube.S4`. **NOT closed this
    dispatch** — see below.
  - [x] Otherwise: mark this phase [BLOCKED] with the exact open goal state (fuel-sufficiency /
    Decidable instance), the chosen approach, and the spawned task number; return `partial`/`blocked`.
- **Timing:** 3 hours (this dispatch: ~3h of concrete technical investigation, no closure)
- **Depends on:** 6

**Continuation note (this dispatch — genuine attempt at 9-B, BLOCKED with a sharpened, precise
goal state; the independent Hintikka-alignment item was already landed by a prior dispatch,
confirmed still green and axiom-clean this dispatch via `lean_verify`)**:

**The core finding — a driver/shadow-invariant mismatch not previously documented.** Attempting
the 9-B wiring surfaced a structural gap that Phases 1-6's machinery does not close by itself:

- `s4Valid`'s `Decidable` instance must run the REAL computational driver `modalTableauS4 φ :=
  modalTableauGen (modalApplyOneS4 φ) φ` (LoopChecking.lean:671), whose minting guard is
  `blockingWorldS4` (LoopChecking.lean:391) — this compares a PROSPECTIVE successor's birth
  content against the **CURRENT LIVE** `relevantSetFinset` of each existing known world (fixes
  Gap 2 from the research report, but still reads *live* — i.e. ever-growing — content).
- `S4LoopInv`/`modalStepBranchS4_worldBound` (Phases 4-6), by contrast, are proven ONLY for the
  keyed SHADOW stepper `modalStepBranchS4Keyed`, whose guard `blockingWorldS4Keyed`
  (LoopChecking.lean:459) compares against the **stable, birth-frozen `keys` list** instead of
  live content. Confirmed directly in the theorem signature:
  `modalStepBranchS4_preserves_S4LoopInv`'s hypothesis is
  `modalStepBranchS4Keyed φ₀ b e acc keys = some (...)` (LoopChecking.lean:4625) — NOT
  `modalStepBranchS4`. The two guards are genuinely different decision procedures (`keys ⊆
  relevantSetFinset` per `keyLowerBd` is a **subset**, not equality, so a live-set match/mismatch
  does not determine a keys match/mismatch). Phase 5's own dispatch-2 handoff independently
  confirms this: `blockingWorldS4Keyed` was introduced specifically because the Phase-3
  `blockingWorldS4` guard's live-set freshness contract (`blockingWorldS4_none_fresh`) was
  *insufficient* to prove `keysDistinct` preservation — the exact gap re-derived here from the
  Decidable-instance side.
- **Consequence**: `modalStepBranchS4_worldBound` cannot be "wired" as fuel-sufficiency for the
  REAL `modalTableauS4` as a one-line application — the world-bound guarantee is proven about a
  driver `modalTableauS4` does not run. Closing Phase 7 genuinely requires ONE of:
  (a) **9-B, sharpened**: build a bespoke top-level S4-specific driver
  (`modalExpandBranchesS4Keyed`/`modalTableauS4Keyed`) around `modalStepBranchS4Keyed` (which
  cannot reuse `modalStepBranchGen`/`modalExpandBranchesGen`/`modalTableauGen` even via the new
  `Aux`-parametrized `modalExpandBranchesHintikka`, since `keys` is extra threaded state a fixed
  `apply : RuleApply Atom` closure cannot carry across steps — wrapping it in an existential
  `Aux(b,e,acc) := ∃ keys, …` does NOT help, because `AuxStepPreserved` would then need to
  re-derive `keysDistinct` preservation using the REAL (live-set) guard's contract, which is
  exactly the insufficient argument above), full ~700-line `processNext`-style fuel induction,
  PLUS a re-verification that soundness (`modalTableauS4_sound`, task 506) and the truth lemma
  still connect (this looks tractable in principle — the keyed and unkeyed guards' *non-minting*
  arms and *blocked-target-has-content* contracts agree — but is unverified and adds scope); or
  (b) **9-A, extended**: generalize the driver framework itself (`RuleApply`/`Accessibility` or a
  new `RuleApplyState`-style wrapper) to support extra opaque per-branch threaded state (not just
  a `Prop`-valued `Aux`), so `modalApplyOneS4Keyed`'s `keys` parameter can be threaded generically
  and `modalTableauS4` redefined to consume it directly. This is a materially larger 9-A than the
  plan originally scoped (which only needed to replace `ModalLoopInvGen`'s rank machinery, not
  add threaded state) — but note task 515's `Aux`-parametrized `modalExpandBranchesHintikka` is
  real, useful groundwork already landed for S5's (state-free) case and should be surveyed first.
- **Zero-debt discipline honored**: no `sorry`/`axiom`/vacuous placeholder was introduced while
  investigating this; no code was written that could not close cleanly. `lake build`
  (`Cslib.Logics.Modal.Tableau.LoopChecking` and `.FrameCompleteness`) green; `lean_verify` on
  `modalHintikkaSetS4_eq` and `modalStepBranchS4_worldBound` confirms `propext`/
  `Classical.choice`/`Quot.sound` only, no `sorryAx`.
- **Recommendation**: spawn `abstract termination-measure interface for S4/B loop lemma
  (task 511 Phase 7 follow-on)` scoped to `CompletenessLoop.lean`/`GenericDriver.lean`, briefed
  with this exact finding (the driver/shadow-invariant mismatch, and the requirement that
  whatever interface is built must support threading `S4LoopInv`-style extra per-branch state,
  not just a state-free `Aux : Prop`), shared with tasks 505/513. Phases 1-6 (the world bound
  over the shadow driver) remain a valid, self-contained, sorry-free deliverable regardless of
  Phase 7's outcome.
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean`,
    `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — alignment bridge, fuel sufficiency,
    `Decidable (s4Valid φ)` (if closed)
- **Verification:** `lake build` (full project); `lean_verify` zero sorry/axiom on any landed
  lemma. If [BLOCKED], the handoff records the goal state and the alignment bridge still builds
  green.

## Testing & Validation

- [ ] `lake build` (full project) is green after each landed phase (scoped
  `lake build Cslib.Logics.Modal.Tableau.LoopChecking` at intermediate phase ends).
- [ ] `lean_verify` reports zero `sorry` and zero `axiom` for every new/edited declaration in each
  landed phase.
- [ ] `lake exe checkInitImports` — all touched files import `Cslib.Init`.
- [ ] `lake exe lint-style` and `lake lint` — no new style/environment lint violations.
- [ ] `lake test` — `CslibTests` suite passes.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — no import regressions.
- [ ] Regression: task 506 Phases 5-7 consumers (`modalTruthLemmaS4`, box-pos/dia-neg bridges,
  `s4Valid` soundness) still build after the Phase 3 guard rewrite.
- [ ] `modalStepBranchS4_worldBound` closes (Phase 6) — the definition of done for the original
  Phase 8.

## Artifacts & Outputs

- `specs/511_s4_loop_checking_termination/plans/01_s4-termination-bound-decidability.md` (this plan)
- `specs/511_s4_loop_checking_termination/summaries/01_s4-termination-bound-decidability-summary.md`
  (on completion)
- Modified: `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (primary),
  `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (Phase 7, and Phase 3 if a consumer lives
  there)
- Possible spawned task: abstract termination-measure interface (9-A) in `CompletenessLoop.lean`
  (shared with tasks 505/513)

## Rollback/Contingency

- Each phase is a separate commit (`task 511 phase P: {name}`); revert the offending commit to
  return to the last green state.
- Phase 3 guard rewrite is the highest-ripple change: if consumers cannot be re-verified within
  budget, revert Phase 3 and Phase 4 and reassess Option B (saturated-world invariant, no driver
  change — research Section 4 Option B), which keeps `modalStepBranchGen` reuse at the cost of a
  looser bound and a harder fuel-sufficiency proof.
- Phase 5 (`_preserves_keysDistinct`) and Phase 7 (decidability) carry standing permission to land
  [BLOCKED] with a documented goal state rather than introducing any `sorry`/`axiom`/vacuous
  placeholder. Phases 1-6 (the world bound) are the self-contained deliverable and remain valid
  even if Phase 7 blocks.
