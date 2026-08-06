# Implementation Plan: Task #564

- **Task**: 564 - Migrate the S4 Keyed drivers onto the St ladder and retire the duplicated `keys'` derivation
- **Status**: [COMPLETED]
- **Effort**: 4.6 hours
- **Dependencies**: 553, 562, 563 (all landed)
- **Research Inputs**: `specs/564_tableau_s4keyed_migration_st_ladder/reports/01_s4keyed-st-ladder-migration.md`
- **Artifacts**: plans/01_migrate-s4keyed-st-ladder.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, cslib.md, lean4.md, plan-compliance.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Two structurally independent halves, sequenced so a failure in one cannot strand the other.
**Half 1 (Phases 2-3)** removes the `S4LoopInv.outDegEq` field and its three orphaned
preservation lemmas — a pure deletion of already-proved material worth roughly 437 lines, which
research established is where *all* of this task's line-count reduction actually lives.
**Half 2 (Phases 4-5)** lands the state-threaded S4 Keyed bridge onto the `RuleApplySt` ladder
**additively**, giving the landed ladder its first real consumer and discharging the "separate,
later task" note in `Saturation.lean`, without redefining any existing declaration.

The plan deliberately does **not** attempt the destructive redefinition of the bespoke drivers,
and does **not** attempt the KeyedOrdered driver. Both exclusions are forced by verified findings,
not by convenience — see Non-Goals.

### Research Integration

The research report overrides the task description on five points, and this plan is built on the
corrected facts, not the description:

1. **The line-count premise in the description is falsified.** Retiring the double `keys'`
   derivation destructively is net **+80 lines** and requires re-verifying 40 downstream proof
   sites, because those sites depend on the *definitional shape* of the steppers and the
   `sf.sign`/`sf.formula` 14-leaf case split is required either way. The reduction lives entirely
   in the `outDegEq` removal, so that goes **first**.
2. **The bridge chain is already compiled and sorry-free.** All four declarations exist verbatim
   at `specs/564_tableau_s4keyed_migration_st_ladder/assets/verified-st-bridge.lean`, compiled
   with `lake env lean` against the live tree. Phase 4 is a transcription phase, not a
   proof-authoring phase. Three specific tactic hazards were found and solved in the asset;
   they are recorded inline in Phase 4 so the implementer does not re-derive them.
3. **The KeyedOrdered driver is structurally unmigratable** onto this ladder.
   `modalStepBranchGenSt` hardwires `b.findSome? f` and abstracts over the *rule*, not the
   *traversal*; `modalStepBranchS4KeyedOrdered` is a two-stage traversal whose minting gate
   depends on a global property of `b`. No choice of `apply : RuleApplySt Atom σ` can express it.
4. **The description's `outDegEq` escape hatch does not trigger.** The cascade is 6 mechanical
   sites, not four destructuring invariant proofs, and the field has **zero** code consumers
   anywhere in `Cslib/`.
5. **All line numbers in the description are stale.** This plan anchors on declaration names and
   carries freshly re-verified line numbers (HEAD `9a3b2370`) as navigation hints only.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `specs/ROADMAP.md` consulted for this task (no `roadmap_path` in the delegation context).

## Goals & Non-Goals

**Goals**:
- Remove `S4LoopInv.outDegEq`, its two provision sites, its two destructuring sites, its
  positional-constructor site in the landed completeness capstone, and the three lemmas orphaned
  by the removal (~437 lines).
- Land `modalApplyOneS4KeyedSt` plus its three bridge theorems additively in `LoopChecking.lean`,
  making `modalExpandBranchesS4Keyed` the `RuleApplySt` ladder's first real consumer.
- Add the tableau-entry-point corollary tying `modalTableauS4Keyed` to
  `modalExpandBranchesGenSt`, and retire the stale "separate, later task, out of scope here" note
  in `Saturation.lean`.
- Hold every verification gate at or better than the recorded baseline, with zero new `sorry`.

**Non-Goals**:
- **Migrating the KeyedOrdered driver.** Structurally impossible against the ladder as it stands
  (research §3). It requires a new stepper-parameterised rung in `Saturation.lean` — a ~55-line
  rung plus two ~50-line bridge proofs, itself roughly net-zero. Recommend a follow-up task.
- **Destructively redefining `modalStepBranchS4Keyed` / `modalExpandBranchesS4Keyed`** as
  instantiations of the generic ones. Net +80 lines and 40 proof sites re-verified (research §5).
  Research explicitly recommends against it, and it would require user sign-off that is not
  obtainable under autonomous orchestration.
- **Adding a fuel parameter to `modalTableauGenSt`.** Would disturb the landed
  `modalTableauGen_eq_St` bridge for zero benefit; `modalExpandBranchesGenSt` already takes fuel
  as an argument.
- **Touching `ModalPotentialInv.outDegEq` (`FmpMeasure.lean`), `modalStepBranch_preserves_outDegEq{,_gen}`,
  or `modalStepBranchGen_preserves_outDegEq`.** Different structure, different driver, serves K.
- Resolving the single pre-existing `sorry` at `FrameSoundness.lean:1251`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Positional constructor at `FrameCompleteness.lean:4130` is miscounted, silently shifting a later field's proof onto the wrong obligation | H | M | The slot to drop is the **6th** position of the inner anonymous constructor = the **4th** `?_`. Its matching bullet is identified by body, not position: `intro w` / `simp [outDeg, Accessibility.successorsOf, Accessibility.empty]` (verified at `:4141-4142`). A miscount surfaces immediately as a build error, not silently — the remaining obligations have incompatible types. |
| Deleting the three lemmas before the field's provision sites leaves the tree red mid-phase | M | H | Phase 2 is declared `Commit Mode: atomic-batch`. Intermediate per-file red states are expected and MUST NOT be committed; one commit covers the whole batch after `lake build Cslib` is green. |
| Asset's `public` modifiers conflict with `LoopChecking.lean`'s file-wide `@[expose] public section` (`:213`) | M | H | Strip every `public` modifier and the `module`/`import`/`namespace`/`open`/`variable`/`end` scaffolding from the asset when inlining. The surrounding declarations (`modalStepBranchS4Keyed:1287`, `modalExpandBranchesS4Keyed:8281`) are bare `def` — match them. |
| `docBlame` lint fires on the four new declarations (asset docstrings say "EXPERIMENT 1/1b/2/3") | M | H | Phase 4 rewrites all four docstrings as real prose before running `lake lint`. Placeholder experiment labels must not land. |
| Re-deriving the solved tactic hazards costs a dispatch and may reach a worse proof | M | M | The three hazards (`dsimp only` before `split`; `rw` not `simp only` for `modalApplyOneS4KeyedSt_eq`; trailing `rfl` in the `fuel = 0` base case) are recorded verbatim in Phase 4. Transcribe the asset; do not re-author. |
| `lake shake` findings count drifts after the deletion (`isMintingShaped`/`outDeg` lose their last `LoopChecking` uses) | L | L | Both are declared in `FmpMeasure.lean`, which `LoopChecking` imports for dozens of other reasons, so no import becomes droppable. Gate on "no Modal/Tableau findings AND count stays 9", never on exit 0. |
| Full `lake build Cslib` turnaround on an 11.7k-line file makes iteration slow | L | H | Use scoped `lake build Cslib.Logics.Modal.Tableau.LoopChecking` during a phase; reserve full `lake build Cslib` for phase-end. |

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

Phases within the same wave can execute in parallel. This plan is a strict linear chain: Phases
2-5 all edit `Cslib/Logics/Modal/Tableau/LoopChecking.lean`, so serialization is a file-territory
requirement, not merely a logical one. Phase 4 has no *logical* dependency on Phases 2-3 (the two
halves touch disjoint declarations) — if the ordering must be broken for recovery, Phase 4 can be
run before Phase 2 without loss, but never concurrently with it.

---

### Phase 1: Re-verify and record the gate baseline [COMPLETED]

**Goal**: Establish that the tree is green *now*, at this HEAD, so that any later gate movement is
attributable to this task's edits rather than inherited.

**Tasks**:
- [x] Record `git log --oneline -1` (expected `9a3b2370` or a descendant). Result: HEAD is
      `789afa7a` (task 564 plan creation), confirmed descendant of `9a3b2370` via
      `git merge-base --is-ancestor`.
- [x] Run `lake exe cache get` to ensure the Mathlib olean cache is present. Result: cache
      already warm ("No files to download", 8651 files already decompressed).
- [x] Run `lake build Cslib`; record exit code and job count. Result: exit 0, "Build completed
      successfully (3313 jobs)".
- [x] Run the sorry census and record the count:
      `grep -rn "^\s*sorry\s*$\|:= sorry\|<;> sorry\|exact sorry" Cslib/Logics/Modal/Tableau/`
      Result: exactly 1 hit, `FrameSoundness.lean:1251`, matching hypothesis.
- [x] Run `lake exe checkInitImports`; record exit code. Result: exit 0.
- [x] Run `lake exe lint-style`; record exit code. Result: exit 0.
- [x] Run `lake shake --add-public --keep-implied --keep-prefix`; record the finding count and
      confirm none are in `Modal/Tableau`. Result: exit 1, 9 findings (TimeM.lean,
      MultiTape/Deterministic.lean, StackTape.lean, Relation/Defs.lean,
      SingleTape/NonDeterministic.lean, Relation/Confluence.lean, Control/Monad/Free.lean,
      CCS/Basic.lean, CombinatoryLogic/Defs.lean), none in `Modal/Tableau`, matching hypothesis.
- [x] Record `wc -l` for the three in-scope files. Result: `LoopChecking.lean` 11761,
      `FrameCompleteness.lean` 8266, `Saturation.lean` 755 — exact match to Scope Hypothesis.

**Timing**: 0.3 hours

**Depends on**: none

**Verification Tier**: full

**Scope Hypothesis**: The baseline is expected to be `lake build Cslib` green, Modal/Tableau sorry
census exactly **1** (`FrameSoundness.lean:1251`), `checkInitImports` and `lint-style` exit 0, and
`lake shake` exit 1 with **9** findings, none in `Modal/Tableau`. `LoopChecking.lean` is expected
at **11761** lines, `FrameCompleteness.lean` at **8266**, `Saturation.lean` at **755**. Confirm by
running each command; if any figure differs, record the actual value and treat *it* as the
baseline rather than adjusting the tree to match this hypothesis.

**Files to modify**:
- None (read-only measurement phase).

**Verification**:
- All seven measurements recorded in the phase notes.
- No edits made.

---

### Phase 2: Remove `S4LoopInv.outDegEq` and its orphaned preservation lemmas [COMPLETED]

**Goal**: Delete the field, all four of its live sites, the positional constructor slot in the
completeness capstone, and the three lemmas the removal orphans — leaving `lake build Cslib`
green with no proof-script authoring at all.

**Tasks**:
- [x] Delete the `outDegEq` field declaration and its docstring line from `structure S4LoopInv`
      (field at `LoopChecking.lean:7690`; structure opens at `:7676`).
- [x] At `LoopChecking.lean:8163`, edit
      `obtain ⟨hbC, heN, heC, haF, haK, hoD, hkT, hkL, hkD, hkI⟩ := hinv` — drop `hoD`, leaving a
      9-way destructure. (Both occurrences at pre-edit `:8161` and `:8223` edited identically.)
- [x] At `LoopChecking.lean:8179-8180`, delete the
      `outDegEq := modalStepBranchS4_preserves_outDegEq …` field assignment (2 lines).
- [x] At `LoopChecking.lean:8225`, apply the same `obtain` edit as above.
- [x] At `LoopChecking.lean:8244-8245`, delete the
      `outDegEq := modalStepBranchS4KeyedOrdered_preserves_outDegEq …` field assignment (2 lines).
- [x] At `FrameCompleteness.lean:4130`, drop the **6th slot** (the **4th** `?_`) from the inner
      anonymous constructor of
      `refine ⟨⟨?_, List.nodup_nil, ?_, accFreshInv_empty _, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨…⟩, ?_, ?_⟩`.
- [x] Delete the matching bullet at `FrameCompleteness.lean:4141-4142`, identified by its body
      (`intro w` followed by
      `simp [outDeg, Accessibility.successorsOf, Accessibility.empty]`) — **not** by position.
      Confirmed the structurally similar `simp [outDeg, …]` at `FrameCompleteness.lean:7836`
      (unrelated `ModalPotentialInv` site) was untouched.
- [x] Delete `lemma modalStepBranchS4KeyedOrdered_preserves_outDegEq` including its docstring
      (found at pre-Phase-2 `:5652-5847` after the field/obtain edits had already shifted line
      numbers by -2 from the plan's stale `:5674-5874` estimate; re-located via fresh `grep -n`
      per the phase's own file-territory sequencing rather than trusting stale numbers).
- [x] Delete `lemma modalStepBranchS4_preserves_outDegEq` including its docstring (found at
      `:5446-5645`, re-located the same way against the plan's stale `:5473-5672` estimate).
- [x] Delete `lemma modalApplyOneS4KeyedMint_outDeg_step` including its `omit` line and docstring
      (found at `:1017-1043`, re-located against the plan's stale `:1017-1042` estimate) —
      orphaned because all four of its call sites lived inside the two lemmas just deleted.
- [x] Confirm zero remaining references: `grep -rn "outDegEq" Cslib/Logics/Modal/Tableau/LoopChecking.lean`
      returns only the 4 prose docstring hits handled in Phase 3
      (`:4617`, `:7237`, `:7716`, `:7762` post-deletion), and
      `grep -rn "modalApplyOneS4KeyedMint_outDeg_step\|modalStepBranchS4_preserves_outDegEq\|modalStepBranchS4KeyedOrdered_preserves_outDegEq" Cslib/`
      returns nothing.
- [x] Run `lake build Cslib` to green. Result: exit 0, "Build completed successfully (3313 jobs)".
      `lake build Cslib.Logics.Modal.Tableau.LoopChecking` (866 jobs) and
      `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` (900 jobs) both green individually
      first, with only the pre-existing `simp_all`/flexible-tactic linter infos (now at
      `FrameCompleteness.lean:5693`/`:5698`, shifted -2 lines from the Phase 1 baseline's
      `:5695`/`:5700` by the constructor-slot deletion) — no new warnings.

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: This phase asserts **6 edit sites across 2 files** and **3 whole-declaration
deletions totalling ~427 lines**, for a combined reduction of roughly **437 lines** once docstring
lines are counted. It further asserts the field has **zero** code consumers — no `.outDegEq`
projection exists anywhere in `Cslib/`. Confirm before deleting by running
`grep -rn "\.outDegEq" Cslib/` and `grep -rn "outDegEq" Cslib/Logics/Modal/Tableau/`; the only
`LoopChecking.lean` bindings should be `hoD` at `:8163` and `:8225`, each used solely to feed the
field back at `:8179` / `:8244`. If a genuine consumer surfaces, stop and mark the phase
`[BLOCKED]` rather than working around it. Confirm the final `wc -l` delta matches the ~437-line
hypothesis; a materially different figure means a boundary was walked wrong.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` - field removal, 2 `obtain` edits, 2 field-assignment
  deletions, 3 whole-declaration deletions.
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` - positional constructor slot + its bullet.

**Verification** (all confirmed):
- `lake build Cslib` exits 0. Confirmed: "Build completed successfully (3313 jobs)".
- Sorry census in `Cslib/Logics/Modal/Tableau/` is still exactly 1. Confirmed:
  `FrameSoundness.lean:1251` only.
- `grep -rn "outDegEq" Cslib/Logics/Modal/Tableau/LoopChecking.lean` returns only prose docstring
  lines. Confirmed: 4 hits at `:4617`, `:7237`, `:7716`, `:7762` (post-Phase-2 line numbers; the
  plan's `:4644`/`:7667`/`:8148`/`:8196` estimates were pre-deletion and are handled in Phase 3).
- `wc -l Cslib/Logics/Modal/Tableau/LoopChecking.lean` shows a reduction of roughly 427 lines
  against the Phase 1 baseline. Confirmed: 11761 -> 11325 = **436 lines removed**
  (`FrameCompleteness.lean` also dropped 8266 -> 8264 = 2 lines from the constructor-slot/bullet
  removal, for a combined 438-line reduction — within the plan's ~437-line hypothesis).

---

### Phase 3: Update the four field-list docstrings [COMPLETED]

**Goal**: Remove `outDegEq` from the four prose docstrings that enumerate `S4LoopInv`'s field
list, so the documentation matches the structure.

**Tasks**:
- [x] Update the field-run enumeration in the docstring at `LoopChecking.lean:4644` (pre-Phase-2
      numbering) — the `accFresh`/`accKnown`/`outDegEq` run. Found post-Phase-2 at `:4617`
      (`modalApplyOneS4Keyed_nonMint_snd_eq_acc` docstring); rewrote "accFresh/accKnown/outDegEq's
      preservation" -> "accFresh/accKnown's preservation" and "those three invariants" ->
      "those two invariants".
- [x] Update the field-run enumeration at `LoopChecking.lean:7667` (the `S4LoopInv` structure
      docstring's `bClosure`/`eNodup`/`eClosure`/`accFresh`/`accKnown`/`outDegEq` run). Found
      post-Phase-2 at `:7237` (the "Correction 1" docstring above `structure S4LoopInv`); dropped
      `outDegEq` from the field-run list and corrected "six rule-independent fields" ->
      "five rule-independent fields".
- [x] Update the field-run enumeration at `LoopChecking.lean:8148`. Found post-Phase-2 at `:7716`
      (`modalStepBranchS4_preserves_S4LoopInv` docstring); dropped `outDegEq` from the
      parenthetical field list and corrected "All ten fields" -> "All nine fields".
- [x] Update the field-list enumeration at `LoopChecking.lean:8196` (the explicit
      `{bClosure,eNodup,eClosure,accFresh,accKnown,outDegEq,keysTotal,keyLowerBd,keysDistinct,keysInUniverse}`
      brace list). Found post-Phase-2 at `:7762`
      (`modalStepBranchS4KeyedOrdered_preserves_S4LoopInv` docstring); dropped `outDegEq` from the
      brace list — the "twelve calls" count directly above (`:7760`) already correctly reads 12
      (9 remaining fields + 3 proof-internal auxiliaries) once `outDegEq` is removed, so no
      further count edit was needed there.
- [x] Re-located each by `grep -n "outDegEq" Cslib/Logics/Modal/Tableau/LoopChecking.lean` after
      Phase 2 — confirmed the plan's pre-deletion line numbers had shifted (`:4644`->`:4617`,
      `:7667`->`:7237`, `:8148`->`:7716`, `:8196`->`:7762`).
- [x] Confirmed `grep -rn "outDegEq" Cslib/Logics/Modal/Tableau/LoopChecking.lean` returns nothing.

**Timing**: 0.4 hours

**Depends on**: 2

**Verification Tier**: prose

**Scope Hypothesis**: Asserts exactly **4** docstring sites in `LoopChecking.lean` enumerating the
field list. Confirm by `grep -n "outDegEq" Cslib/Logics/Modal/Tableau/LoopChecking.lean` after
Phase 2 lands; if the count differs from 4, fix every hit found rather than only four. Missing one
is a doc defect, not a build break — but the phase does not close until the grep is empty.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` - four docstrings, prose only.

**Verification** (all confirmed):
- `grep -rn "outDegEq" Cslib/Logics/Modal/Tableau/LoopChecking.lean` returns no matches. Confirmed.
- `lake build Cslib.Logics.Modal.Tableau.LoopChecking` still green (docstring edits cannot break
  it, but confirm no accidental code-line damage). Confirmed: exit 0, "Build completed
  successfully (866 jobs)".
- `lake exe lint-style` exits 0 (guards against over-length docstring lines). Confirmed: exit 0.

---

### Phase 4: Land the state-threaded S4 Keyed bridge additively [COMPLETED]

**Goal**: Transcribe the four verified declarations from the compiled asset into
`LoopChecking.lean`, giving the `RuleApplySt` ladder its first real consumer without redefining
anything that already exists.

**Tasks**:
- [x] Read `specs/564_tableau_s4keyed_migration_st_ladder/assets/verified-st-bridge.lean` in full.
- [x] Insert the four declarations into `LoopChecking.lean` immediately **after**
      `def modalExpandBranchesS4Keyed` (found post-Phase-2/3 at `:7845-7894`, not the plan's stale
      pre-Phase-2 `:8281` estimate) and before `def modalTableauS4Keyed` (found at `:7896`, not
      the stale `:8346` estimate), preserving the asset's internal order:
      `modalApplyOneS4KeyedSt`, `modalApplyOneS4KeyedSt_proj`, `modalApplyOneS4KeyedSt_eq`,
      `modalStepBranchGenSt_eq_S4Keyed`, `modalExpandBranchesGenSt_eq_S4Keyed`.
- [x] Stripped the asset's module scaffolding when inlining: dropped `module`, the `import` /
      `public import` lines, `namespace Cslib.Logic.Modal.Tableau`, the `open` line, the
      `variable` line, and the trailing `end`. All are already established in `LoopChecking.lean`.
- [x] Stripped every `public` modifier from the transcribed declarations — bare `def`/`theorem`
      matches the surrounding declarations under the file-wide `@[expose] public section`.
- [x] Rewrote all four theorem docstrings as real prose (the `def modalApplyOneS4KeyedSt`
      docstring was already real prose in the asset, not EXPERIMENT-labeled, and was kept with
      light expansion). The asset's `EXPERIMENT 1` / `EXPERIMENT 1b` / `EXPERIMENT 2` /
      `EXPERIMENT 3` labels do NOT land — confirmed by `grep -n "EXPERIMENT"` returning nothing.
      Also added a `/-! ## RuleApplySt Bridge for the Keyed S4 Driver -/` section header
      docstring above the five declarations, matching the file's existing section-header style.
- [x] Confirmed no modification to `modalApplyOneS4Keyed`, `modalStepBranchS4Keyed`,
      `modalStepBranchS4KeyedBody`, `modalStepBranchS4KeyedOrdered`, or
      `modalExpandBranchesS4Keyed` — insertion was strictly additive (verified via
      `git diff --stat`, additions-only).
- [x] Ran `lake build Cslib.Logics.Modal.Tableau.LoopChecking` (866 jobs, exit 0), then
      `lake build Cslib` (3313 jobs, exit 0).
- [x] Ran `lake lint`: zero `docBlame` findings anywhere in the output, and zero hits on any of
      the five new declaration names. *(Deviation, not addressed: the transcribed
      `modalApplyOneS4KeyedSt_proj`/`modalApplyOneS4KeyedSt_eq` proofs carry the three
      plan-recorded "solved tactic hazards" verbatim, which trigger two pre-existing-style
      `linter.flexible`/`linter.unusedSimpArgs` build-time warnings (not `lake lint` environment
      findings, not one of the 7 prevention categories, and not gated by this plan's Testing &
      Validation checklist). Per the plan's own instruction ("Transcribe the asset; do not
      re-derive"), these were left as-is rather than risking the recorded hazards by rewriting.)*

**Timing**: 1.2 hours

**Depends on**: 3

**Verification Tier**: full

**Scope Hypothesis**: Asserts the asset transcribes to roughly **+100 lines** (an ~18-line
definition plus ~80 lines of proof) across **5 new declarations** in exactly **one** file, with
**zero** existing declarations modified. Confirm by diffing `wc -l` before and after and by
`git diff --stat`, which must show `LoopChecking.lean` as the only changed file with additions
only in the inserted region. If any existing declaration shows as modified, the insertion point
was wrong — revert and re-place.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` - five new declarations inserted after
  `modalExpandBranchesS4Keyed`.

**Verification** (all confirmed):
- `lake build Cslib` exits 0. Confirmed: "Build completed successfully (3313 jobs)".
- Sorry census in `Cslib/Logics/Modal/Tableau/` is still exactly 1. Confirmed:
  `FrameSoundness.lean:1251` only.
- `lake lint` reports no `docBlame` for the five new declarations. Confirmed: 0 `docBlame` hits
  in the entire `lake lint` output.
- `git diff --stat` shows additions only; no existing declaration body altered. Confirmed:
  `Cslib/Logics/Modal/Tableau/LoopChecking.lean | 157 +++++++++++++++++++++++++++` — one file,
  157 insertions, 0 deletions. (The plan's Scope Hypothesis estimated ~100 lines; actual is 157,
  a materially different figure reported honestly here per the hypothesis's own instruction —
  driven by the added section-header docstring and the more verbose real-prose theorem
  docstrings replacing the terse EXPERIMENT labels, not by any extra code.)
- `grep -n "EXPERIMENT" Cslib/Logics/Modal/Tableau/LoopChecking.lean` returns nothing. Confirmed.

**Solved tactic hazards — transcribe, do not re-derive**:
1. In `modalApplyOneS4KeyedSt_eq`, after `cases s <;> cases f` the `{sign := …}.sign` projections
   must be discharged with a bare `dsimp only` **before** `split`. Without it, `split` targets the
   wrong `match` and `rfl` fails with a cross-arm mismatch (the `.neg, □φ` arm being offered for a
   `.pos, ◇` formula).
2. In `modalStepBranchGenSt_eq_S4Keyed`, use `rw [modalApplyOneS4KeyedSt_eq]` and **not**
   `simp only [modalApplyOneS4KeyedSt_eq]`. `simp` normalises
   `branches.map (fun _ => e ++ [sf])` into `List.replicate branches.length (e ++ [sf])` on one
   side only, and the goal will not close. `rw` followed by a bare `rfl` closes it.
3. In `modalExpandBranchesGenSt_eq_S4Keyed`, the `fuel = 0` base case needs a trailing `rfl`
   after `simp only [modalExpandBranchesGenSt, modalExpandBranchesS4Keyed]`.

---

### Phase 5: Entry-point corollary and `Saturation.lean` note retirement [COMPLETED]

**Goal**: Close the ladder story end-to-end by tying `modalTableauS4Keyed` to
`modalExpandBranchesGenSt`, and retire the now-stale "separate, later task, out of scope here"
note that pointed at exactly this work.

**Tasks**:
- [x] Added a corollary `modalTableauS4Keyed_eq_modalExpandBranchesGenSt` immediately after
      `def modalTableauS4Keyed` (found post-Phase-2/3/4 at `:8067-8071`, not the stale pre-Phase-2
      `:8346` estimate) stating that `modalTableauS4Keyed φ` equals
      `modalExpandBranchesGenSt (modalApplyOneS4KeyedSt φ) [[⟨.neg, φ, 0⟩]] [[]] [Accessibility.empty] [[(0, (∅ : Finset (Sign × Proposition Atom)))]] (modalFuelS4 φ)`.
      Confirmed the exact initial-`keyss` argument against `modalTableauS4Keyed`'s own body
      (`unfold`ed via `lean_goal` before writing the proof) rather than assuming the plan's shape
      blind — it matched exactly. Closes by `unfold modalTableauS4Keyed; rw
      [modalExpandBranchesGenSt_eq_S4Keyed]` alone (the trailing `rw` auto-discharges via `rfl`
      once the `let`-bound `initialBranch` zeta-reduces to the literal singleton list, so no
      separate `rfl` line was needed).
- [x] Gave the corollary a real docstring explaining that the S4 entry point cannot route through
      `modalTableauGenSt` because that hardwires K's `modalFuel φ`, whereas the S4 keyed loop
      needs `modalFuelS4 φ` for its pigeonhole world bound `modalWorldBoundS4`.
- [x] Confirmed no fuel parameter was added to `modalTableauGenSt` and `modalTableauGen_eq_St`
      was not touched.
- [x] Updated the note in `Saturation.lean` (found at `:502-505`, matching the plan's estimate) to
      state that the ladder now has `modalExpandBranchesS4Keyed` as a landed consumer via
      `modalExpandBranchesGenSt_eq_S4Keyed` (instantiated at `modalApplyOneS4KeyedSt`, threading
      `keyss : List σ` with `σ := List (WorldIndex × Finset (Sign × Proposition Atom))`), and
      that the KeyedOrdered driver remains unmigrated because `modalStepBranchGenSt` abstracts
      over the rule and not the traversal, while the ordered driver's minting gate depends on a
      global, traversal-level property of the branch.
- [x] Ran `lake build Cslib`: exit 0, "Build completed successfully (3313 jobs)".

**Timing**: 0.7 hours

**Depends on**: 4

**Verification Tier**: full

**Scope Hypothesis**: Asserts **1 new declaration** in `LoopChecking.lean` and **1 prose paragraph
edit** in `Saturation.lean` — exactly two files. Confirm via `git diff --name-only` for this
phase's commit. If the corollary does not close by `rw` + `rfl`, do not escalate to a bespoke
proof: re-check the initial-argument shape against `modalTableauS4Keyed`'s body first, since a
mismatch there is the likely cause.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` - entry-point corollary after `modalTableauS4Keyed`.
- `Cslib/Logics/Modal/Tableau/Saturation.lean` - retire the stale "separate, later task" note.

**Verification** (all confirmed):
- `lake build Cslib` exits 0. Confirmed: "Build completed successfully (3313 jobs)".
- Sorry census in `Cslib/Logics/Modal/Tableau/` is still exactly 1. Confirmed:
  `FrameSoundness.lean:1251` only.
- `grep -n "separate, later task, out of scope here" Cslib/Logics/Modal/Tableau/Saturation.lean`
  returns nothing. Confirmed.
- `lake lint` reports no `docBlame` on the new corollary. Confirmed: 0 `docBlame` hits in the
  entire `lake lint` output, and zero hits on `modalTableauS4Keyed_eq_modalExpandBranchesGenSt`.
- `git diff --name-only` for this phase's commit shows exactly the two declared files
  (`LoopChecking.lean`, `Saturation.lean`), matching the Scope Hypothesis.

---

### Phase 6: Full CI gate and scope-exclusion record [COMPLETED]

**Goal**: Run the complete CSLib verification pipeline against the Phase 1 baseline and record the
two forced scope exclusions so a future reader does not re-attempt them blind.

**Tasks**:
- [x] Ran `lake build Cslib`; confirmed exit 0 (3313 jobs).
- [x] Ran the sorry census; confirmed the count is still exactly 1 and the single hit is
      `FrameSoundness.lean:1251`.
- [x] Ran `lake exe checkInitImports`; confirmed exit 0.
- [x] Ran `lake lint`; confirmed no findings in any of the three modified files
      (`LoopChecking.lean`, `FrameCompleteness.lean`, `Saturation.lean`) — 145 total findings
      repo-wide, all in files this task did not touch (e.g. `FmpMeasure.lean`,
      `FrameSoundness.lean`'s pre-existing `unusedArguments` findings). *(Note: Phase 1's task
      list did not itself run a full `lake lint`, only `lint-style`/`shake`, so there is no
      Phase-1-captured absolute count to diff against; "no new findings" is verified instead by
      confirming zero findings land in the three files this task edited.)*
- [x] Ran `lake exe lint-style`; confirmed exit 0.
- [x] Ran `lake shake --add-public --keep-implied --keep-prefix`; confirmed **no Modal/Tableau
      findings** and the count is still **9** (identical file set to the Phase 1 baseline:
      `TimeM.lean`, `MultiTape/Deterministic.lean`, `StackTape.lean`, `Relation/Defs.lean`,
      `SingleTape/NonDeterministic.lean`, `Relation/Confluence.lean`, `Control/Monad/Free.lean`,
      `CCS/Basic.lean`, `CombinatoryLogic/Defs.lean`). Gated on the finding count, not exit code —
      exit 1 is the expected, correct outcome.
- [x] Ran `lake test`; confirmed pass (9378 jobs, including
      `CslibTests.S4LoopGuardRegression`).
- [x] Recorded the net `wc -l` delta across the three in-scope files against the Phase 1 baseline:
      `LoopChecking.lean` 11761 -> 11500 (**-261**), `FrameCompleteness.lean` 8266 -> 8264
      (**-2**), `Saturation.lean` 755 -> 762 (**+7**) — **net -256 lines** across the three files.
      This is a materially different figure from the plan's ~330-line hypothesis (~437 removed in
      Phases 2-3 vs. an actual combined removal/addition profile of -438 in Phase 2, ~0 net in
      Phase 3, +157 in Phase 4, +25 in Phase 5), reported honestly here rather than restated as
      the hypothesis — the whole-payoff `outDegEq` removal (Phase 2) still delivered the bulk of
      the reduction; Phase 4's bridge transcription (real prose docstrings replacing terse
      EXPERIMENT labels) simply cost more lines than the plan's terse ~100-line estimate.
- [x] Recorded in this summary (see Phase 6 notes below) that the **KeyedOrdered migration** was
      excluded as structurally impossible against the current ladder, with the reason
      (`modalStepBranchGenSt` abstracts over the rule, not the traversal; the ordered driver's
      minting gate is a global property of the branch), and recommends a follow-up task for the
      stepper-parameterised rung.
- [x] Recorded in this summary that the **destructive redefinition** of the bespoke drivers was
      excluded as net +80 lines across 40 re-verified proof sites, per the research measurement,
      and that it would require explicit user sign-off.

**Timing**: 0.5 hours

**Depends on**: 5

**Verification Tier**: full

**Scope Hypothesis**: Asserts the net line delta across the three files is a reduction of roughly
**330 lines** (~437 removed in Phases 2-3, ~105 added in Phases 4-5). Confirm by `wc -l` against
the Phase 1 baseline. A materially different figure is not itself a failure, but it must be
reported honestly in the summary rather than restated as the hypothesis.

**Files to modify**:
- None (verification and recording only).

**Verification** (all confirmed):
- All seven gate commands run, with results recorded against the Phase 1 baseline. Confirmed.
- Both scope exclusions recorded with their reasons. Confirmed (see summary artifact).

---

## Testing & Validation

- [x] `lake build Cslib` exits 0. Confirmed (3313 jobs).
- [x] `grep -rn "^\s*sorry\s*$\|:= sorry\|<;> sorry\|exact sorry" Cslib/Logics/Modal/Tableau/`
      returns exactly 1 hit, at `FrameSoundness.lean:1251`. **Zero-debt: no new `sorry` may be
      introduced.** Confirmed — Phases 2-3 were pure deletion of already-proved material, and
      every Phase 4/5 proof was already compiled in the asset or closes by `rw`+auto-`rfl`.
- [x] `lake exe checkInitImports` exits 0. Confirmed.
- [x] `lake exe lint-style` exits 0. Confirmed.
- [x] `lake lint` shows no new findings, in particular no `docBlame` on any of the six new
      declarations. Confirmed — zero findings land in any of the three files this task touched.
- [x] `lake shake --add-public --keep-implied --keep-prefix`: **no Modal/Tableau findings AND
      count stays 9**. Confirmed (identical 9-file finding set to the Phase 1 baseline). Not
      gated on exit 0 (exit 1 is expected).
- [x] `lake test` passes. Confirmed (9378 jobs).
- [x] No vacuous definitions (`def X := True`, `theorem X := trivial`) anywhere in the diff.
      Confirmed via `git diff 9a3b2370 HEAD -- Cslib/` grepped for the vacuous patterns: zero
      hits.
- [x] `grep -rn "\.outDegEq\|outDegEq" Cslib/Logics/Modal/Tableau/LoopChecking.lean` returns
      nothing; `ModalPotentialInv.outDegEq` in `FmpMeasure.lean` is untouched. Confirmed —
      `git diff 9a3b2370 HEAD -- Cslib/Logics/Modal/Tableau/FmpMeasure.lean` is empty.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — `S4LoopInv.outDegEq` and three orphaned lemmas
  removed; five bridge declarations plus one entry-point corollary added; four docstrings updated.
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — positional constructor arity reduced by
  one, matching bullet deleted.
- `Cslib/Logics/Modal/Tableau/Saturation.lean` — stale "separate, later task" note retired.
- `specs/564_tableau_s4keyed_migration_st_ladder/summaries/01_*-summary.md` — execution summary
  including the gate table, the net line delta, and both recorded scope exclusions.
- Recommendation (not an artifact of this task): a follow-up task for the stepper-parameterised
  rung in `Saturation.lean` that would enable the KeyedOrdered migration.

## Rollback/Contingency

Each phase commits separately (Phase 2 as a single atomic batch), so rollback is per-phase via
`git revert` of that phase's commit — no cross-phase entanglement exists because Phases 2-3 and
Phases 4-5 touch disjoint declarations.

- **Phase 2 fails mid-batch**: the tree is expected to be red between the field removal and the
  last site edit. Do not commit. If the batch cannot be brought green, `git checkout` the two
  files back to the Phase 1 commit (take a `bash .claude/scripts/git-snapshot.sh 564` first if any
  unrelated uncommitted work exists) and mark the phase `[BLOCKED]` with the failing site named.
- **Phase 4 fails**: the bridge is purely additive, so deleting the inserted region restores the
  Phase 3 state exactly. If a transcribed proof does not compile, re-check the three recorded
  tactic hazards before altering the proof — the asset compiled clean against this tree, so a
  failure most likely means a hazard was transcribed away.
- **Phase 5 fails**: revert the corollary only; the Phase 4 bridge stands on its own and the
  `Saturation.lean` note edit can land independently.
- **Any phase introduces a `sorry`**: this is a hard stop, not a contingency. Revert the phase and
  mark it `[BLOCKED]`.
- **Half-1 succeeds, Half-2 fails**: this is an acceptable partial outcome. The `outDegEq` removal
  is the whole line-count payoff and is independently valuable; the task may close as
  `[PARTIAL]` with Phases 4-6 outstanding rather than reverting Phases 2-3.
