# Implementation Plan: Task #511 — S4 Loop-Checking Termination Bound & Decidability

- **Task**: 511 — s4_loop_checking_termination (follow-on to task 506, Phases 8-9)
- **Status**: [NOT STARTED]
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

### Phase 1: Exponent fix — bound `2^(2·|Sf|)` [NOT STARTED]

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

### Phase 2: Finite signed-key infrastructure + powerset cardinality [NOT STARTED]

- **Goal:** Introduce the stable-key finite codomain and the cardinality bridge the pigeonhole
  consumes. Pure defs + lemmas, no driver change, CI-green in isolation.
- **Tasks:**
  - [ ] Define `signedSubfmls φ₀ : Finset (Sign × Proposition Atom)` (both signs × every
    subformula of `φ₀`) and `relevantSetFinset φ₀ b w : Finset (Sign × Proposition Atom)`
    (the live relevant set `R(b,w)` as a `Finset`, reusing `sameRelevantSet`'s membership notion).
  - [ ] Prove `signedSubfmls_card : (signedSubfmls φ₀).card = 2 * (modalSubfmls φ₀).length`
    (dedup via subformula nodup or `Finset` construction).
  - [ ] Prove `signedSubfmls_powerset_card : (signedSubfmls φ₀).powerset.card = modalWorldBoundS4 φ₀`
    via `Finset.card_powerset` and `signedSubfmls_card` (this is why Phase 1 precedes: ties the
    bound to `2^(2·|Sf|)`).
  - [ ] Prove `relevantSetFinset_subset_signedSubfmls : relevantSetFinset φ₀ b w ⊆ signedSubfmls φ₀`
    (only when the branch is `modalUniverseS4`-closed) and
    `relevantSetFinset_mono : b ⊆ b' → relevantSetFinset φ₀ b w ⊆ relevantSetFinset φ₀ b' w`
    (monotonicity — the fact Gap 1 exploited and the lower-bound invariant survives).
- **Timing:** 2 hours
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — new defs/lemmas in the `S4LoopInv` region
    (or a new `FmpMeasure`-sibling section if the file grows unwieldy; keep in LoopChecking unless
    forced to split)
- **Verification:** `lake build Cslib.Logics.Modal.Tableau.LoopChecking`; `lean_verify` zero
  sorry/axiom for each new lemma; `signedSubfmls_powerset_card` reduces to `modalWorldBoundS4 φ₀`.

### Phase 3: Successor-birth-content guard redesign [NOT STARTED]

- **Goal:** Fix Gap 2 — make the guard block on the prospective successor's birth content, not the
  source world's set. Rewrite `modalApplyOneS4` to consult the new guard; re-verify Phase 5-7
  consumers are unaffected.
- **Tasks:**
  - [ ] Define `successorBirthContent φ₀ b s φ w : Finset (Sign × Proposition Atom)` — the witness
    `⟨s,φ⟩` plus the S4 box-context transmitted from `w` (`{⟨.pos,ψ⟩ : T(□ψ)@w ∈ b}` ∪
    `{⟨.neg,ψ⟩ : F(◇ψ)@w ∈ b}`), matching the actual K-minting birth content (research Section 1.1,
    Gap 2 in Section 2).
  - [ ] Define `blockingWorldS4 φ₀ b s φ w : Option WorldIndex` — block iff some existing known
    world's CURRENT `relevantSetFinset` equals the prospective `successorBirthContent`.
  - [ ] Prove the guard contract lemmas: `blockingWorldS4_none_fresh` (when `= none`, the
    prospective birth content differs from every existing world's relevant set) and
    `blockingWorldS4_some_mem` (the returned world is in `modalKnownWorlds b`).
  - [ ] Rewrite `modalApplyOneS4` (LoopChecking.lean:253-264) to consult `blockingWorldS4` at the
    two minting shapes (`⟨.neg,.box φ,w⟩` / `⟨.pos,.diamond φ,w⟩`) in place of `blockingWorld`.
    Leave all *non-minting* arms byte-identical.
  - [ ] Re-CI the consumers that depend on `modalApplyOneS4`: `hintikkaS4_box_pos_step` (line 421),
    the dia-neg dual (line 510), the crux bridges (lines 603/687/773/785/809/825), and
    `modalHintikkaSetS4`/`modalTruthLemmaS4`. Fix any signature drift; their dependence is on the
    unchanged non-minting behavior, so breakage should be limited to references to `blockingWorld`.
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

### Phase 4: Key-threaded S4 step/driver + restated `S4LoopInv` [NOT STARTED]

- **Goal:** Thread stable per-world birth keys through an S4-specific step, and replace the broken
  `worldSetsDistinct` field with the four monotone-stable key fields. Structure + driver compiles
  green even before preservation is proved.
- **Tasks:**
  - [ ] Define the S4-specific step carrying `keys : List (WorldIndex × Finset (Sign × Proposition
    Atom))` alongside `(b, e, acc)` (research Option A2). On a minting step, append
    `(w', successorBirthContent …)`; on persistent steps, keys are unchanged. Reuse the K rule-slot
    (`modalApplyOneS4`) for the formula work — only the stepping wrapper is S4-specific.
  - [ ] Replace `S4LoopInv`'s `worldSetsDistinct` field (LoopChecking.lean:942-948) with:
    `keysTotal` (∀ known world ∃ recorded key), `keyLowerBd` (each key ⊆ its live
    `relevantSetFinset` — the monotone-stable lower bound), `keysDistinct` (distinct worlds ⇒
    distinct keys), `keysInUniverse` (each key ⊆ `signedSubfmls φ₀`). Keep the six
    rule-independent fields (`bClosure`/`eNodup`/`eClosure`/`accFresh`/`accKnown`/`outDegEq`) over
    `modalUniverseS4`. Add the `keys` parameter to the structure.
  - [ ] Update any current references to `S4LoopInv`/`worldSetsDistinct` to the new signature (the
    structure is only referenced within the Phase 8/9 machinery, currently unproved, so ripple is
    contained).
- **Timing:** 2.5 hours
- **Depends on:** 3
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — S4 step wrapper, `S4LoopInv` structure
- **Verification:** `lake build Cslib.Logics.Modal.Tableau.LoopChecking`; the restated structure
  and the S4 step definition typecheck; `lean_verify` zero sorry/axiom on the new definitions.

### Phase 5: `S4LoopInv` preservation lemmas — the crux [NOT STARTED]

- **Goal:** Prove every `modalStepBranchS4` step preserves the four key fields. This is the
  mathematical heart of the task; budget generously.
- **Tasks:**
  - [ ] `modalStepBranchS4_preserves_keyLowerBd` — persistent steps only add formulas, so live sets
    grow (`relevantSetFinset_mono`); birth keys are unchanged ⇒ `⊆` preserved. (Survives Gap 1.)
  - [ ] `modalStepBranchS4_preserves_keysDistinct` — keys never change on any step; on a *minting*
    step the new key differs from every existing key by the `blockingWorldS4 = none` contract
    (`blockingWorld_none_fresh` combined with `keyLowerBd`), on *persistent* steps no key changes.
    (Fixes Gap 2.) This is the highest-risk sub-lemma.
  - [ ] `modalStepBranchS4_preserves_keysTotal` / `_preserves_keysInUniverse` — bookkeeping (a
    minted world gets a key; the key is a birth content ⊆ `signedSubfmls φ₀`).
  - [ ] Assemble `modalStepBranchS4_preserves_S4LoopInv` (all fields at once, reusing the six
    rule-independent preservation facts already available for the K/T machinery where they
    transfer).
- **Timing:** 3 hours
- **Depends on:** 4
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — preservation lemmas
- **Verification:** `lake build Cslib.Logics.Modal.Tableau.LoopChecking`; `lean_verify` zero
  sorry/axiom on each preservation lemma. **If `_preserves_keysDistinct` resists within budget:**
  mark this phase [BLOCKED] with the exact open goal state, do NOT weaken the invariant, and stop
  (standing permission).

### Phase 6: Pigeonhole world bound (closes Phase 8) [NOT STARTED]

- **Goal:** Derive the finite world bound from the preserved invariant — the deliverable that
  closes the original task 506 Phase 8.
- **Tasks:**
  - [ ] `modalKnownWorlds_nodup` helper (the `foldl` guards duplicates via `ws.any (· == sf.label)`;
    likely one-line).
  - [ ] `modalKnownWorlds_length_le_worldBoundS4` — map each known world to its key
    (`keysTotal`); the map is injective (`keysDistinct`); keys lie in
    `(signedSubfmls φ₀).powerset` (`keysInUniverse`); cardinality via `signedSubfmls_powerset_card`
    (Phase 2) = `modalWorldBoundS4 φ₀`; conclude length ≤ card via
    `List.Nodup.length_le_card` / `Finset.card_le_card_of_injOn`.
  - [ ] `modalStepBranchS4_worldBound : modalMaxWorld b < modalWorldBoundS4 φ₀` — worlds are
    consecutive (`modalMaxWorld b + 1 = #worlds = (modalKnownWorlds b).length` via a small
    dense-labels fact from consecutive minting), then apply the length bound.
- **Timing:** 2 hours
- **Depends on:** 5, 2
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — pigeonhole lemmas
- **Verification:** `lake build Cslib.Logics.Modal.Tableau.LoopChecking`; `lean_verify` zero
  sorry/axiom on `modalKnownWorlds_length_le_worldBoundS4` and `modalStepBranchS4_worldBound`.
  This phase closing = original Phase 8 resolved.

### Phase 7: Phase 9 decidability — decision + closure or documented [BLOCKED] [NOT STARTED]

- **Goal:** Land the cheap S4-local alignment, make the 9-A/9-B decision concrete, and either close
  `Decidable (s4Valid φ)` against `Cube.S4` or land [BLOCKED] with a precise handoff and a spawned
  generalization task.
- **Tasks:**
  - [ ] Land the Hintikka-alignment bridge
    `modalHintikkaSetS4 φ₀ b acc = modalHintikkaSetGen (modalApplyOneS4 φ₀) b acc` (research
    Section 8: verified `rfl` — Saturation.lean:460 vs LoopChecking.lean:373). Cheap, green.
  - [ ] Record the decision (Planner Decision 2): the abstract termination-measure interface (9-A)
    is a shared-file change in `CompletenessLoop.lean` benefiting 505/513 — **spawn it as a separate
    task** (`/spawn 511 "abstract termination-measure interface for S4/B loop lemma"`), do NOT
    inline it. Task 510's `modalExpandBranchesGen_hintikka` is confirmed NOT instantiable for S4
    (requires `RuleApplicationSpec` + `ModalLoopInvGen` rank fields + `geomCap` + K-universe fuel —
    research Section 3).
  - [ ] If the 9-A task is already available (or within budget as 9-B S4-local re-derivation port
    of `processNext`'s fuel induction over `modalUniverseS4` with `S4LoopInv`): wire fuel
    sufficiency from `modalStepBranchS4_worldBound` (Phase 6) and derive
    `Decidable (s4Valid φ)` + `s4Valid` completeness against `Cube.S4`.
  - [ ] Otherwise: mark this phase [BLOCKED] with the exact open goal state (fuel-sufficiency /
    Decidable instance), the chosen approach, and the spawned task number; return `partial`.
- **Timing:** 3 hours
- **Depends on:** 6
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
