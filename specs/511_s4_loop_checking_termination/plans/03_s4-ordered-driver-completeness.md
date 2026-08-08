# Implementation Plan: Task #511

- **Task**: 511 - S4 loop checking termination (close the termination bound and complete decidability)
- **Status**: [IMPLEMENTING]
- **Effort**: 6 hours
- **Dependencies**: 535, 553, 563, 564, 565, 566, 567, 586 (all landed; no live blocker at HEAD)
- **Research Inputs**: `specs/511_s4_loop_checking_termination/reports/03_head-reverification-ordered-driver.md`
- **Artifacts**: plans/03_s4-ordered-driver-completeness.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Complete the S4 decidability capstone by finishing the **completeness half** for the ordered keyed
driver `modalTableauS4KeyedOrdered`, whose soundness is already proved sorry-free and axiom-free
(`modalTableauS4KeyedOrdered_sound`, `FrameCompleteness.lean:8234`). Every non-trivial ingredient
already exists at HEAD; the remaining work is a bounded ~580-line port comprising one new
one-line lemma, one pure relocation, two structural ports of already-proven unordered analogues,
and a three-line decidability capstone mirroring the KB5 template. **Definition of done**:
`instDecidableS4Valid` exists, `lake build` is green on both scope files, and the sorry/axiom
census over `Cslib/Logics/Modal/Tableau/` remains zero.

### Research Integration

Built directly from report `03_head-reverification-ordered-driver.md` (HEAD re-verification at
`5ea7152c`; source tree unchanged at the current HEAD `07f64c9e`, whose only delta is a task-597
research-artifact commit). Findings carried into this plan verbatim:

- **The recorded Phase 7 blocker no longer holds.** It was resolved by a third route neither
  prior handoff anticipated: the project built a *new* decision procedure whose stepper is the
  keyed one the termination proof is about, rather than reconciling the keyed termination proof
  with the live-guard driver `modalTableauS4`.
- **Soundness is FALSE for the UNORDERED keyed driver** — machine-checked countermodel in
  `CslibTests/S4LoopGuardRegression.lean`, documented at `FrameCompleteness.lean:4088-4104`, with
  two independent defects (birth-key staleness; unrestricted redirect reachability). **Soundness
  is TRUE AND PROVED for the ORDERED driver.** All new work in this plan targets the ordered
  driver exclusively. Rule-application order is soundness-critical: the repair was *when* a
  minting shape may fire (settled-context scheduling), not the guard's comparison predicate.
- **Phase 1's new lemma was probed green this dispatch**, not asserted: the exact proof text was
  appended to `LoopChecking.lean`, built (`lake build ... LoopChecking` → 876/876, exit 0), and
  reverted. It is verified-feasible, not speculative.
- **Phase 2's relocation was verified a pure move**: `modalStepBranchS4KeyedOrdered_newExps_eq_map`
  depends only on declarations in `S4/Driver.lean`, all public and all below `LoopChecking.lean`
  in the import order.
- **The deliberate simplification for Phase 3**: use the already-bundled `S4OrderedFuelInv` as the
  per-index hypothesis and `modalStepBranchS4KeyedOrdered_preserves_S4OrderedFuelInv` as the single
  step lemma, rather than widening the unordered proof's four-way per-index conjunction to five.
  This is strictly less bookkeeping than the unordered original.

Anchors independently re-verified against the working tree while authoring this plan:
`S4/Driver.lean:648/678/705/1339` (`_cases`, `_eq_none_iff`, `_selected_mem`, `_branch_superset`),
`S4/HintikkaInvariant.lean:828/840` (`S4OrderedFuelInv`, `_preserves_S4OrderedFuelInv`),
`S4/Hintikka.lean:101/622` (`modalHintikkaSetS4_eq`, `hintikka_congr_S4`),
`LoopChecking.lean:1067/1099/1134/1495` (unordered originals),
`FrameCompleteness.lean:4070/4080/4114/4189/7869/8164/8234`.

### Prior Plan Reference

`plans/01_s4-termination-bound-decidability.md` is **superseded, not resumed**. Its Phases 1-6
landed sorry-free and remain valid in the tree; its Phase 7 targets the wrong driver
(`modalTableauS4`, live-guard) and is obsolete. Lessons carried forward rather than phases:

- **Effort calibration**: structural ports in this subsystem have repeatedly cost more than "copy
  and rename" suggests. The ordered invariant-preservation twins each needed
  `modalStepBranchS4KeyedOrdered_selected_mem` threaded in place of a direct `findSome?`
  extraction. That is a known, bounded shape of friction — budgeted into Phase 3 and Phase 4
  rather than discovered there.
- **Risk shape**: the prior plan blocked because a proof was built against a driver nothing ran.
  This plan mitigates by targeting exactly the driver that already carries a proved soundness
  theorem, and by making the decidability capstone (Phase 5) depend on both halves of the *same*
  driver.
- **Phase isolation**: the prior plan bundled the highest-risk work with adjacent work. Here the
  ~370-line Hintikka port is deliberately alone in Phase 3.

### Roadmap Alignment

`specs/ROADMAP.md` was not passed as `roadmap_path` in the delegation context, and `roadmap_flag`
was not set, so no roadmap-review or roadmap-update phases are added and ROADMAP.md is not
modified by this plan. For information only, the file exists and line 153 carries the matching
item: "**S4** (reflexive-transitive) loop-checking termination bound + decidability ... the last
classical-cube decidability corner". Line 114's "Decidability instances: K, T, B, S5,
5/Euclidean, KB5 (all sorry-free)" is the list this task's Phase 5 extends with S4. Whoever runs
`/todo` at completion should annotate those two lines; that is out of scope here.

## Goals & Non-Goals

**Goals**:
- Prove `modalExpandBranchesS4KeyedOrdered_hintikka` and
  `modalExpandBranchesS4KeyedOrdered_openBranch_initial_mem` in `LoopChecking.lean`.
- Prove `modalTableauS4KeyedOrdered_complete` in `FrameCompleteness.lean`, paired with the
  already-landed `modalTableauS4KeyedOrdered_sound` over the *same* driver.
- Land `s4Valid_decides` and `instDecidableS4Valid`, mirroring `kb5Valid_decides` /
  `instDecidableKb5Valid` (`FrameCompleteness.lean:4070-4082`).
- Preserve the green tree: zero `sorry`, zero added axiom, `lake build` green on both scope files.
- Correct the stale prose notes that assert S4 decidability is out of scope.

**Non-Goals**:
- Retiring `modalTableauS4Keyed` / `modalExpandBranchesS4Keyed` and their unordered proof stack.
  `LoopChecking.lean:188-189` earmarks this as a separate destructive phase, gated on every
  consumer having an ordered replacement — which Phase 5 here is a *precondition for*, not a part
  of.
- Retiring the live-guard `modalTableauS4` (`S4/Driver.lean:219`).
- Any driver-abstraction refactor. The concurrent decision report
  (`specs/597_modal_tableau_driver_abstraction_decision/reports/01_driver-abstraction-decision.md`)
  concluded the per-regime bespoke split is the correct steady state and that this port is
  independent of that decision. Do not generalize `RuleApply`/`RuleApplySt` here.
- Any proof about the **unordered** keyed driver's soundness. It is false as stated; do not
  attempt it.
- The deliberately-weakened per-step soundness scope note in `FrameSoundness.lean`
  (`FrameCompleteness.lean:8212-8221`); untouched by this work.
- Edits to any `Cslib/Logics/Modal/Tableau/S4/*.lean` module. Those ten modules are **read-only**
  sources of already-landed lemmas for this task. `file_scope` is exactly
  `LoopChecking.lean` + `FrameCompleteness.lean`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Phase 3's ~370-line induction exceeds one agent run | H | M | Phase 3 is deliberately alone with no other objective competing for context. If interrupted, the phase lands `[PARTIAL]` and `/implement` resumes it — do NOT introduce a `sorry` to "finish" it (see Rollback/Contingency). |
| Unordered proof destructures the step hypothesis directly; ordered stepper needs `modalStepBranchS4KeyedOrdered_selected_mem` threaded instead | M | H | Named in advance as the expected friction shape. At every site where the unordered original does a direct `findSome?` extraction, substitute `_selected_mem` (`S4/Driver.lean:705`). This is the documented cost of the two prior ordered-twin ports. |
| Widening `S4LoopInv`'s four-way per-index conjunction to five (ordered `_preserves_S4LoopInv` carries an extra `keysOriginS4` hypothesis and conclusion conjunct) | M | M | Do not widen. Use `S4OrderedFuelInv` (`S4/HintikkaInvariant.lean:828`) as the single per-index hypothesis and `_preserves_S4OrderedFuelInv` (`:840`) as the single step lemma. Strictly less bookkeeping than the unordered original. |
| Relocation of `_newExps_eq_map` breaks its existing call site (`FrameCompleteness.lean:8164`) | M | L | The lemma is non-`private` and must stay non-`private` after the move. `FrameCompleteness.lean:10` public-imports `LoopChecking`, so the direction is correct. Phase 2 is an atomic two-file batch precisely because the intermediate state is unavoidably red. |
| Targeting the unordered driver by muscle memory (its analogues are what is being copied) | H | M | Every new declaration name must contain `Ordered`. Phase verification includes grepping the new declaration bodies for unqualified `modalStepBranchS4Keyed` / `modalExpandBranchesS4Keyed` references. Soundness is FALSE for the unordered driver — a completeness proof accidentally routed through it would pair with no valid soundness theorem. |
| A new global `instance instDecidableS4Valid` perturbs typeclass resolution elsewhere | M | L | Phase 5 carries `Verification Tier: full` — the complete repository gate set, not just the two scope modules. |
| Silent axiom introduction (e.g. via `Classical` in a `decide`-adjacent path) | H | L | Final gate includes `lean_verify` on `instDecidableS4Valid` and `modalTableauS4KeyedOrdered_complete`; the control behavior is known (a bogus name errors, so an empty list is a real result). `_sound`'s empty axiom list is the benchmark to preserve. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 1, 2 |
| 4 | 4 | 2, 3 |
| 5 | 5 | 3, 4 |

Phases within the same wave can execute in parallel. This plan is fully sequential: no two phases
are parallel-safe, because Phases 1-4 all edit `LoopChecking.lean` (shared territory) even where
no logical dependency exists.

**Dispatch note**: Phases 1 and 2 are both very small (~15 and ~35 lines). A single implementer
dispatch may complete both back-to-back; they are kept as separate phases because their
verification tiers and commit modes genuinely differ, not to force two dispatches.

---

### Phase 1: Ordered saturation lemma [COMPLETED]

**Goal**: Add `modalStepBranchS4KeyedOrdered_none_saturated` to `LoopChecking.lean` — the ordered
twin of the private `modalStepBranchS4Keyed_none_saturated` (`LoopChecking.lean:1099`), and the
only piece of genuinely new proof content in this plan.

**Tasks**:
- [ ] Add the following `private lemma` to `LoopChecking.lean`, adjacent to the existing unordered
  `modalStepBranchS4Keyed_none_saturated` at `:1099` (place it after that lemma, inside or
  immediately following the `## Top-Loop Induction` section at `:1055`):

  ```lean
  private lemma modalStepBranchS4KeyedOrdered_none_saturated (φ₀ : Proposition Atom)
      (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
      (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
      (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys = none)
      (sf : SignedFormula (Proposition Atom) WorldIndex) (hsfb : sf ∈ b) :
      sf ∈ e ∨ (modalApplyOneS4Keyed φ₀ keys sf b acc).1 = .notApplicable :=
    modalStepBranchS4Keyed_none_saturated φ₀ b e acc keys
      ((modalStepBranchS4KeyedOrdered_eq_none_iff φ₀ b e acc keys).mp hstep) sf hsfb
  ```
- [ ] Write a docstring recording that this is the ordered twin and that the transfer is exactly
  what `modalStepBranchS4KeyedOrdered_eq_none_iff`'s own docstring (`S4/Driver.lean:678`) was
  written to enable.
- [ ] Confirm no other declaration in the file already carries this name.

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: ~15 lines added to one file, and the proof body is the exact three-line term
above. Confirm at implementation time by (a) checking `git diff --stat` shows a single-file,
sub-25-line insertion, and (b) confirming the proof compiles as written with no additional
tactics. If the proof does NOT compile verbatim, stop and report — the report's green probe
(876/876, exit 0) would then have been invalidated by an intervening change, which is a finding,
not something to patch around.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — add one private lemma + docstring.

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.LoopChecking` exits 0.
- No `sorry` introduced (`grep -rn "sorry" Cslib/Logics/Modal/Tableau/` unchanged from zero).

---

### Phase 2: Relocate `_newExps_eq_map` for layering [COMPLETED]

**Goal**: Move `modalStepBranchS4KeyedOrdered_newExps_eq_map` from `FrameCompleteness.lean:7869`
down into `LoopChecking.lean`, so the Phase 3 Hintikka lemma (which lives below
`FrameCompleteness` in the import order) can consume it. Verified in research to be a pure move
with no proof edit.

**Tasks**:
- [ ] Copy the declaration and its full docstring (`FrameCompleteness.lean:7862-7869` onward,
  through the end of its proof) into `LoopChecking.lean`, placed after the ordered-stepper
  material and before the ordered top-loop section that Phase 3 will add.
- [ ] Delete the original from `FrameCompleteness.lean`.
- [ ] Keep the declaration **non-`private`**. Its existing call site at
  `FrameCompleteness.lean:8164` must continue to resolve; `FrameCompleteness.lean:10`
  public-imports `LoopChecking`, so a non-private lemma is visible there.
- [ ] Confirm the moved proof's only dependencies remain satisfied at the new location:
  `modalStepBranchS4KeyedOrdered_cases` (`S4/Driver.lean:648`),
  `modalNonMintCandidates_not_mem_expanded` (`S4/Driver.lean:414`),
  `modalStepBranchS4KeyedBody`, `modalStepBranchS4Keyed`, `modalApplyOneS4Keyed` — all in
  `S4/Driver.lean`, all public, all below `LoopChecking.lean`.

**Timing**: 0.5 hours

**Depends on**: 1

*(Dependency is territory serialization — both phases edit `LoopChecking.lean`. There is no
logical dependency between Phase 1's lemma and this relocation.)*

**Verification Tier**: interface

*(A public symbol changes defining module with a call site in a different file. The enumerated
one-hop dependent set is exactly `FrameCompleteness.lean`.)*

**Commit Mode**: atomic-batch

*(Declared in advance: the file set is `{LoopChecking.lean, FrameCompleteness.lean}` as ONE
objective. Either edit order produces an unavoidable red intermediate — delete-first leaves
`FrameCompleteness.lean:8164` with an unknown identifier; add-first leaves a duplicate
declaration. Intermediate per-file states MUST NOT be committed; one commit covers the batch.)*

**Scope Hypothesis**: ~35 lines moved, zero lines of proof edited, exactly one call site
(`FrameCompleteness.lean:8164`) affected and unchanged in text. Confirm at implementation time by
(a) `grep -c "modalStepBranchS4KeyedOrdered_newExps_eq_map"` over
`Cslib/Logics/Modal/Tableau/` before and after — the total count must be unchanged, with the
declaration site having moved files; and (b) diffing the moved text against the original to
confirm the proof body is byte-identical.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — receives the declaration.
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — loses the declaration; call site at
  `:8164` unchanged.

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.LoopChecking` exits 0.
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` exits 0 (the enumerated dependent).
- Sorry census over `Cslib/Logics/Modal/Tableau/` still zero.

---

### Phase 3: `modalExpandBranchesS4KeyedOrdered_hintikka` [NOT STARTED]

**Goal**: Structural port of `modalExpandBranchesS4Keyed_hintikka`
(`LoopChecking.lean:1134-1493`) to the ordered driver. This is the phase with real risk; it is
deliberately alone.

**Tasks**:
- [ ] Open a new `/-! ## Ordered Top-Loop Induction — modalExpandBranchesS4KeyedOrdered_hintikka -/`
  section in `LoopChecking.lean` and port the statement, substituting
  `modalExpandBranchesS4KeyedOrdered` for `modalExpandBranchesS4Keyed`.
- [ ] **Use `S4OrderedFuelInv` (`S4/HintikkaInvariant.lean:828`) as the per-index hypothesis**, not
  a widened four-way conjunction, and
  `modalStepBranchS4KeyedOrdered_preserves_S4OrderedFuelInv` (`:840`) as the **single** step lemma
  replacing the unordered proof's separate `_preserves_S4LoopInv` /
  `_preserves_S4KeyedHintikkaInv` invocations.
- [ ] Substitute the six stepper-specific facts one for one:

  | Unordered original | Ordered replacement |
  |---|---|
  | `modalStepBranchS4Keyed_none_saturated` (9 call sites, `:1264`-`:1323`) | Phase 1's `modalStepBranchS4KeyedOrdered_none_saturated` |
  | `modalStepBranchS4Keyed_newExps_const` (`:1067`, used `:1345`) | Phase 2's relocated `modalStepBranchS4KeyedOrdered_newExps_eq_map` |
  | `modalStepBranchS4_preserves_S4LoopInv` | folded into `_preserves_S4OrderedFuelInv` |
  | `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv` | folded into `_preserves_S4OrderedFuelInv` |
  | `modalExpMeasure_step_lt_S4Keyed` (`:810`) | `modalExpMeasure_step_lt_S4KeyedOrdered` (`:945`) |
  | `modalHintikkaSetS4_eq` / `hintikka_congr_S4` (the final bridge) | driver-independent; reuse verbatim |
- [ ] Wherever the unordered proof destructures the step hypothesis via a direct `findSome?`
  extraction, thread `modalStepBranchS4KeyedOrdered_selected_mem` (`S4/Driver.lean:705`) instead.
  This is the documented, expected friction point.
- [ ] Grep the finished declaration body for unqualified `modalStepBranchS4Keyed` /
  `modalExpandBranchesS4Keyed` (i.e. without `Ordered`) and confirm every remaining occurrence is
  intentional — routing through the unordered driver here would pair completeness with a driver
  whose soundness is false.

**Timing**: 2 hours

**Depends on**: 1, 2

**Verification Tier**: local

*(Additive: a new theorem in a single module, no existing signature changed.)*

**Commit Mode**: per-substep

**Scope Hypothesis**: ~370 lines added to one file; the port consumes exactly the six
stepper-specific facts tabulated above and introduces no seventh. Confirm at implementation time
by (a) `git diff --stat` on `LoopChecking.lean`; and (b) enumerating the lemmas the finished proof
actually cites and checking the list against the table — a seventh required fact is a real finding
and must be reported, not silently absorbed.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — new theorem in a new section.

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.LoopChecking` exits 0.
- Zero `sorry` in the new declaration and across `Cslib/Logics/Modal/Tableau/`.
- `lean_verify` on the new theorem returns no `sorryAx`.

---

### Phase 4: `modalExpandBranchesS4KeyedOrdered_openBranch_initial_mem` [NOT STARTED]

**Goal**: Structural port of `modalExpandBranchesS4Keyed_openBranch_initial_mem`
(`LoopChecking.lean:1495`) to the ordered driver — the `F(φ₀)@0 ∈ b` initial-membership fact that
`modalTableauS4KeyedOrdered_complete` needs and that
`modalExpandBranchesGen_openBranch_initial_mem` cannot supply (the driver is bespoke, not a
`modalExpandBranchesGen` instance).

**Tasks**:
- [ ] Port the statement and `induction fuel` proof shape from `:1495` verbatim, substituting
  `modalExpandBranchesS4KeyedOrdered` throughout. The statement's five length/membership
  hypotheses (`expandedSets.length = branches.length`, `accs.length = branches.length`,
  `keyss.length = branches.length`, `∀ b₀ ∈ branches, sf ∈ b₀`) carry over unchanged.
- [ ] Substitute `modalStepBranchS4KeyedOrdered_branch_superset` (`S4/Driver.lean:1339`) for the
  unordered superset fact.
- [ ] Substitute Phase 2's relocated `modalStepBranchS4KeyedOrdered_newExps_eq_map` for
  `modalStepBranchS4Keyed_newExps_const` at the length-matching step (unordered call site
  `:1607`).
- [ ] Repeat the Phase 3 `Ordered`-name grep check on the finished body.

**Timing**: 1.5 hours

**Depends on**: 2, 3

*(Logical dependency is on Phase 2 only; Phase 3 is added for territory serialization on
`LoopChecking.lean`.)*

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: ~135 lines added to one file, consuming exactly two ordered substitutions
(`_branch_superset`, `_newExps_eq_map`) beyond the verbatim port. Confirm at implementation time
via `git diff --stat` and by enumerating cited lemmas against that two-item list.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — new theorem.

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.LoopChecking` exits 0.
- Zero `sorry`; `lean_verify` on the new theorem shows no `sorryAx`.

---

### Phase 5: Completeness and the decidability capstone [NOT STARTED]

**Goal**: Land `modalTableauS4KeyedOrdered_complete`, then `s4Valid_decides` and
`instDecidableS4Valid`, and correct the stale prose that asserts S4 decidability is out of scope.

**Tasks**:
- [ ] Add `modalTableauS4KeyedOrdered_complete` to `FrameCompleteness.lean`, as a near-verbatim
  copy of `modalTableauS4Keyed_complete` (`:4189`), fed by the Phase 3 and Phase 4 lemmas plus the
  existing `modalOpenBranchS4_countermodel`.
- [ ] For the seed-state `S4OrderedFuelInv` witness, reuse the expression already assembled
  verbatim inside `modalTableauS4KeyedOrdered_sound` at `FrameCompleteness.lean:8239-8246`:
  `⟨hLoop, hHintikka, hKW, hWC, hKO⟩` from `modalTableauS4Keyed_initial` (`:4114`, four conjuncts)
  plus `keysOriginS4_entry` (`S4/BirthKey.lean:241`, the fifth). Note `modalTableauS4Keyed_initial`
  is `private` and both consumers live in `FrameCompleteness.lean`, so no visibility change is
  needed.
- [ ] Add `s4Valid_decides` and `instDecidableS4Valid` mirroring `kb5Valid_decides` /
  `instDecidableKb5Valid` (`:4070-4082`) — three lines each, pointing at
  `modalTableauS4KeyedOrdered`, paired with the already-landed
  `modalTableauS4KeyedOrdered_sound` (`:8234`). **Do not point the instance at
  `modalTableauS4Keyed` or `modalTableauS4`.**
- [ ] Update the stale prose at `FrameCompleteness.lean:4099-4102` ("The decidability half
  (`s4Valid_decides`/`instDecidableS4Valid`) remains out of scope until both a genuine soundness
  theorem and this completeness theorem exist for the same driver") — that condition is now met,
  for the ordered driver. Preserve the surrounding unsoundness warning about the *unordered*
  driver unchanged; only the out-of-scope claim is stale.
- [ ] Update the stale prose at `LoopChecking.lean:151-152` ("The live `modalTableauS4` is NOT
  redefined; `instDecidableS4Valid` (deferred) would point at this declaration instead") to record
  that the instance now points at `modalTableauS4KeyedOrdered`.

**Timing**: 1.5 hours

**Depends on**: 3, 4

**Verification Tier**: full

*(A new global `instance` changes typeclass resolution repository-wide, and the tie-break rule
resolves upward. The complete repository gate set runs in-phase, not only the two scope modules.)*

**Commit Mode**: per-substep

**Scope Hypothesis**: ~60 lines added across two files, and **exactly two** stale prose notes need
correction (`FrameCompleteness.lean:4099-4102`, `LoopChecking.lean:151-152`). Confirm at
implementation time by grepping both scope files for `out of scope`, `deferred`, and
`instDecidableS4Valid` and checking every hit — a third stale note is a plausible overcount
correction *or* undercount, and either way the confirmed set goes in the summary. If the hypothesis
overcounts, record the difference as a `#### Reasoned Exclusions` subsection on this phase.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — `modalTableauS4KeyedOrdered_complete`,
  `s4Valid_decides`, `instDecidableS4Valid`, prose correction at `:4099-4102`.
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — prose correction at `:151-152`.

**Verification**:
- Full repository gate set green.
- `lean_verify` on `instDecidableS4Valid`, `s4Valid_decides`, and
  `modalTableauS4KeyedOrdered_complete` — no `sorryAx`, and no axiom beyond the standard
  `propext`/`Classical.choice`/`Quot.sound` triple that the existing `modalTableauS4Keyed_complete`
  control also reports.
- `modalTableauS4KeyedOrdered_sound`'s own axiom list still verifies as **empty** (unchanged
  benchmark).

---

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Tableau.LoopChecking` exits 0 (baseline at HEAD: 876 jobs).
- [ ] `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` exits 0 (baseline at HEAD: 910
  jobs).
- [ ] Full repository build green (Phase 5 gate).
- [ ] Sorry census over `Cslib/Logics/Modal/Tableau/` is **zero** — the README's two-pattern
  command. All pre-existing repo sorries live in `Logics/Bimodal/` and
  `Logics/Propositional/Tableau/` and must be unchanged in count.
- [ ] `lean_verify` on `instDecidableS4Valid` — no `sorryAx`, no unexpected axiom.
- [ ] `lean_verify` on `modalTableauS4KeyedOrdered_sound` — still an empty axiom list.
- [ ] `CslibTests/S4LoopGuardRegression.lean` still builds, including the ordered-driver soundness
  smoke row at `:211`.
- [ ] `git diff --stat` confirms only the two `file_scope` files were modified; zero changes under
  `Cslib/Logics/Modal/Tableau/S4/`.
- [ ] Every new declaration name contains `Ordered`; no new proof routes through the unsound
  unordered keyed driver.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — `modalStepBranchS4KeyedOrdered_none_saturated`,
  relocated `modalStepBranchS4KeyedOrdered_newExps_eq_map`,
  `modalExpandBranchesS4KeyedOrdered_hintikka`,
  `modalExpandBranchesS4KeyedOrdered_openBranch_initial_mem`, prose correction.
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — `modalTableauS4KeyedOrdered_complete`,
  `s4Valid_decides`, `instDecidableS4Valid`, prose correction, `_newExps_eq_map` removed.
- `specs/511_s4_loop_checking_termination/summaries/03_s4-ordered-driver-completeness-summary.md`
  — execution summary.
- `specs/511_s4_loop_checking_termination/.orchestrator-handoff.json` — updated per dispatch.

## Rollback/Contingency

- **Per-phase rollback**: each phase is independently `lake build`-verifiable and committed on its
  own (Phase 2 as one declared atomic batch). Reverting a single phase's commit restores a green
  tree without disturbing earlier phases.
- **Phase 3 or 4 does not close within one dispatch**: mark the phase `[PARTIAL]`, commit whatever
  is green, and let `/implement` resume. **Do not introduce a `sorry` to reach a passing build.**
  The task's whole value is a sorry-free, axiom-free decidability instance; a `sorry` here would
  silently invalidate the census gate that the summary reports on.
- **Phase 3 proves structurally harder than a port** (a seventh required fact appears, or the
  `S4OrderedFuelInv` simplification does not carry): report it as a finding and re-block with a
  sharpened goal state rather than widening scope into `S4/*.lean`. That is a genuine research
  result, not a failure to try.
- **Phase 1's probed proof does not compile verbatim**: stop and report. The report's green probe
  would have been invalidated by an intervening change; patching around it silently would hide a
  real regression in `modalStepBranchS4KeyedOrdered_eq_none_iff`.
- **Full revert**: the pre-task baseline is the tree at HEAD, verified green (LoopChecking 876
  jobs, FrameCompleteness 910 jobs, zero sorries under `Cslib/Logics/Modal/Tableau/`). Reverting
  all phase commits restores exactly that state; no schema, no generated file, and no `S4/*.lean`
  module is touched by this plan.
