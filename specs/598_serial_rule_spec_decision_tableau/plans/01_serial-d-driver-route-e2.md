# Implementation Plan: Serial (D) Driver via Route E2

- **Task**: 598 - serial_rule_spec_decision_tableau
- **Status**: [IMPLEMENTING]
- **Effort**: 12 hours
- **Dependencies**: None
- **Research Inputs**: `specs/598_serial_rule_spec_decision_tableau/reports/01_serial-rule-spec-decision.md`
- **Artifacts**: plans/01_serial-d-driver-route-e2.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Research machine-checked that the task's original premise is false: D's seriality rule does not
have to mint at the box-positive shape, so `RuleApplicationSpec.boxPosNotExpanding` (F9) needs no
weakening and `RuleApplicationSpecSerial` must not be built. This plan implements the research's
recommended **Route E2** instead: a dual-persistent D rule (`T(□ψ)@w ⊢ T(◇ψ)@w`,
`F(◇ψ)@w ⊢ F(□ψ)@w`), a `modalDualAugment` universe transformer that closes the one genuinely
failing field (F2 `outputsSubsetUniverse`), and an **additive** `RuleApplicationSpecAt` sibling in
`GenericDriver.lean` whose F2 is fixed at a single `φ0`. The existing `RuleApplicationSpec` and all
seven of its discharge sites (K, T, B, TB, Five, Kb5'', S5w) stay untouched.

Definition of done for the in-scope deliverable: `Cslib/Logics/Modal/Tableau/DDriver.lean` exists
and builds, carrying `modalApplyOneD`, its twelve field discharges bundled as a
`RuleApplicationSpecAt (modalDualAugment φ) modalApplyOneD` witness, the
`modalStepBranchD`/`modalExpandBranchesD`/`modalTableauD` triple with its `_eq` bridges, and
`modalExpandBranchesD_hintikka` — with **zero `sorry` and zero new axioms**, the acceptance bar
carried over verbatim from the task.

### Research Integration

Binding findings from the research report, all of which this plan is built on rather than
re-deriving:

- **Route E2 is the decision.** Routes A (`RuleApplicationSpecSerial`) and E1 (in-place
  `modalSubfmls` dual closure) are both rejected — A reaches into the potential/measure core
  (`isMintingShaped`, `outDeg`, `modalWorldBound`, `modalFuel`) and is not additive; E1 carries an
  unbounded audit risk across 412 `modalSubfmls` references in 15 files.
- **Six of twelve fields are already machine-checked** in the prototype, including both fields the
  task assumed were unsatisfiable (F9 `boxPosNotExpanding`, F10 `diaNegNotExpanding`).
- **F2 is the only genuine failure**, and it fails for a universe reason
  (`◇ψ ∉ modalSubfmls (□ψ)`), not a rule-shape reason.
- **`modalSubfmlsDual_length_le` is machine-checked**: the dual-closed subformula list keeps the
  same `2 * modalComplexity φ + 1` bound, so `modalWorldBound` and `modalFuel` need no constant
  change and every downstream bound only loosens.
- **`--hard` is not warranted** (research §5): this is a bounded, T-shaped port, not a
  divergence-prone task.

**Preserved asset — do not redo.** `specs/598_serial_rule_spec_decision_tableau/prototype/DSerialPrototype.lean`
is a 351-line file that compiles at HEAD `ad19c80d` with zero errors, zero `sorry`, and
`#print axioms` reporting only `propext` / `Classical.choice` / `Quot.sound`. Phases 1, 4, and 8
**lift** from it rather than re-deriving. Any phase that finds itself re-proving a lemma the
prototype already contains has taken a wrong turn.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context and no ROADMAP.md was loaded. The task's
own stated downstream value is unblocking five of the eight remaining modal-cube corners (D, DB,
D4, D5, D45); research risk #3 notes that the DB/D4/D5/D45 claim rests on an established but
unmeasured composition pattern.

## Goals & Non-Goals

**Goals**:
- Land `modalApplyOneD` and its agreement lemma in `FrameRules.lean`, lifted from the prototype.
- Land the additive `RuleApplicationSpecCoreAt` / `RuleApplicationSpecAt` /
  `RuleApplicationSpec.toAt` trio in `GenericDriver.lean`, leaving `RuleApplicationSpec` and its
  seven discharge sites byte-identical.
- Land `modalDualAugment` with its dual-closure, membership, depth-preservation, and
  entry-measure lemmas.
- Land `DDriver.lean` with all twelve field discharges, the driver triple, the `_eq` bridges, and
  `modalExpandBranchesD_hintikka`.
- Hold zero `sorry` and zero new axioms across every phase, verified per phase, not only at the
  end.

**Non-Goals**:
- `RuleApplicationSpecSerial` and `modalLoopGen_eBoxOnlyNeg_serial` — refuted by research; building
  them is now an error, not an alternative.
- Any weakening of F9 / F10 / `isMintingShaped` / `outDeg` / `modalPotential` /
  `modalWorldBound` / `modalFuel`.
- Any edit to `modalSubfmls` itself (that is Route E1, rejected).
- The `Decidable` instance `instDecidableDValid`, `modalTableauD_sound`, `modalTableauD_complete`,
  `serialGen`, and `extractModelD` — see "Out-of-Scope Follow-Up" below.
- DB / D4 / D5 / D45 corners.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The F2 hypothesis narrowing cascades past the 5 sites research measured — `modalStepHintikka_preserves_inv` and `modalExpandBranchesGen_hintikka` take a full `RuleApplicationSpec`, so D's `…At`-only witness may force their signatures to narrow too | High — would turn a 10-line edit into a `CompletenessLoop.lean` refactor | Medium | `RuleApplicationSpec.toAt` exists precisely so every *existing* caller is unaffected. Phase 3 narrows only what D needs. **Hard stop**: if the cascade exceeds the enumerated sites, stop the phase, record the measured site list, and report — do not widen the refactor to make it fit |
| F3-F7 are argued from T's transported proof shape, not machine-checked (research risk #1). `rankStep` is the one with genuine content: it needs `modalDepth (◇ψ) ≤ rank w` where T needed the easier `modalDepth ψ ≤ rank w` | High — `rankStep` is 108 lines in T | Medium | `modalDepth_diamond_eq_box` is `rfl` and machine-checked; `modalApplyOneD_boxPos_snd` / `_diaNeg_snd` are machine-checked and are exactly what F5/F6 turn on. Phase 6 isolates `rankStep` so a stall there does not block phase 7 |
| `modalDualAugment`'s entry-measure lemma is new (research risk #2): `modalExpMeasure_entry_le_fuel` is stated for `[F(φ)@0]` at `modalUniverse φ`, D needs it at `modalUniverse φ⁺` | Medium | Medium | Proof route is the existing `modalWork U b e ≤ 2\|U\|` then `3 ^ (2\|U\|) ≤ modalFuel` chain, re-run at `φ⁺`; `modalSubfmlsDual_length_le` (machine-checked) guarantees the constant survives. Phase 4 owns it in isolation |
| Two of the plan's phases require files outside the declared `file_scope` | High — silent scope creep | Certain (already identified) | Phase 3 declares its two extra files in the phase body and requires the implementer to record the widening; the soundness/completeness work is excluded entirely into a follow-up section. Neither is done silently |
| `DDriver.lean` is written by six consecutive phases; parallel execution would collide | Medium | Low | The wave table serializes every `DDriver.lean` phase — see the territory note under Dependency Analysis |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 4 | -- |
| 2 | 3, 5 | 1, 2, 4 |
| 3 | 6 | 3, 5 |
| 4 | 7 | 6 |
| 5 | 8 | 7 |
| 6 | 9 | 8 |

Phases within the same wave can execute in parallel.

**Territory note**: phases 4, 5, 6, 7, 8, and 9 all write `Cslib/Logics/Modal/Tableau/DDriver.lean`.
The dependency chain above already serializes 5 -> 6 -> 7 -> 8 -> 9, and phase 4 is the file's
creator, so no two `DDriver.lean` phases ever share a wave. Phase 1 owns `FrameRules.lean`, phase 2
owns `GenericDriver.lean`, and phase 3 owns `FmpMeasure.lean` + `CompletenessLoop.lean` (plus a
second, additive touch of `GenericDriver.lean` after phase 2 has closed). Wave 1's three phases have
disjoint file ownership and are genuinely parallel-safe.

---

### Phase 1: D Rules in FrameRules.lean [COMPLETED]

**Goal**: `modalApplyOneD` and its agreement lemma exist in `FrameRules.lean` and the module builds.

**Tasks**:
- [ ] Read the rule block of `specs/598_serial_rule_spec_decision_tableau/prototype/DSerialPrototype.lean`
      and lift `modalDBoxDual` and `modalDDiaNegDual` verbatim into `FrameRules.lean`, placed
      alongside the existing T and 4 helpers
- [ ] Lift `modalApplyOneD`, merging the two dual arms into K's persistent output at the
      box-positive and diamond-negative shapes exactly as `modalApplyOneT` merges `modalTBoxSelf`
      (`FrameRules.lean:85-108` is the structural model)
- [ ] Add `modalApplyOneD_eq_of_not_boxPos_diaNeg`, mirroring
      `modalApplyOneT_eq_of_not_boxPos_diaNeg` (`FrameRules.lean:113-122`)
- [ ] Add module-doc prose for the D block matching the surrounding T/4 documentation density

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: research estimates this block at ~60 lines, measured from the prototype's
compiling rule block. Confirm at implementation time with `git diff --stat` on `FrameRules.lean`;
a result materially over ~80 lines means something was re-derived rather than lifted, and the
prototype should be re-read before continuing.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameRules.lean` - additive: two dual helpers, `modalApplyOneD`, one
  agreement lemma. No existing declaration changes.

**Verification**:
- `lake env lean Cslib/Logics/Modal/Tableau/FrameRules.lean` is clean
- No `sorry` in the diff; `#print axioms modalApplyOneD_eq_of_not_boxPos_diaNeg` reports only
  `propext` / `Classical.choice` / `Quot.sound`
- `git diff` shows no modification to any pre-existing declaration in the file

---

### Phase 2: Additive `RuleApplicationSpecAt` Sibling [COMPLETED]

**Goal**: `GenericDriver.lean` carries the `…At` structures and the `toAt` projection, with
`RuleApplicationSpec` and its seven discharge sites untouched.

**Tasks**:
- [ ] Add `RuleApplicationSpecCoreAt (φ0) (apply)` — identical to `RuleApplicationSpecCore` except
      `outputsSubsetUniverse` is fixed at the structure's `φ0` rather than universally quantified
- [ ] Add `RuleApplicationSpecAt (φ0) (apply)` — the same narrowing applied to
      `RuleApplicationSpec` (`GenericDriver.lean:194-203` is the field being narrowed)
- [ ] Add `RuleApplicationSpec.toAt : RuleApplicationSpec apply → ∀ φ0, RuleApplicationSpecAt φ0 apply`,
      a one-line `{ spec with outputsSubsetUniverse := spec.outputsSubsetUniverse φ0 }`
- [ ] Add the analogous `RuleApplicationSpecCore.toAt` if the core structure is separately
      consumed
- [ ] Document in the module docstring that the `…At` family is the additive weakening used by
      rules whose outputs are only universe-closed at a dual-closed `φ0`

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: research estimates ~120 lines for the sibling structures, projection, and
re-stated wrappers, and asserts that `RuleApplicationSpec`'s **seven** discharge sites (K
`GenericDriver.lean:355`, T `TDriver.lean:742`, B `BDriver.lean:774`, TB `TBDriver.lean:845`, Five
`FiveSimplification.lean:1277`, Kb5'' `FiveSimplification.lean:2587`, S5w `S5Simplification.lean:2320`)
stay untouched. Confirm the count at implementation time with
`grep -rn "RuleApplicationSpec (Atom" Cslib/Logics/Modal/Tableau/` before editing, and confirm
untouched with `git diff` after. Note the re-stated `_at` wrapper deferred to phase 3 is part of
the same ~120-line estimate.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/GenericDriver.lean` - purely additive: two structures, one or two
  projections, docstring prose.

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.GenericDriver` is clean
- `git diff Cslib/Logics/Modal/Tableau/GenericDriver.lean` contains no deletion or modification of
  any `RuleApplicationSpec` field
- Full `lake build` still green: the seven downstream discharge sites are unaffected

---

### Phase 3: F2 Hypothesis Narrowing [COMPLETED]

**Goal**: `modalExpMeasure_step_lt_gen` accepts the narrowed `hOutputsSubsetUniverse`, all
consumption sites pass, and the `…At` wrapper in `GenericDriver.lean` exists — with the full build
green and no other diff.

> **SCOPE DECISION REQUIRED — this phase edits two files outside the declared `file_scope`.**
> The task's `file_scope` is exactly `GenericDriver.lean`, `FrameRules.lean`, `DDriver.lean`. This
> phase additionally requires:
> - `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` (the lemma's own hypothesis, at
>   `modalExpMeasure_step_lt_gen`; research anchors it near `:3165-3174`, applied once near `:3245`)
> - `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` (the enumerated consumption sites)
>
> This was **not** flagged by the delegation, which reported phases 1-5 as in-scope; it was found
> by re-reading the two files at HEAD. The edit is mechanically forced: D can only ever produce a
> `RuleApplicationSpecAt` witness, so without the narrowing the generic measure chain is
> unreachable from D and phases 5-9 cannot close. Total measured edit is ~10 lines.
>
> **Recommendation: widen `file_scope` to include these two files** rather than spawning a
> successor — the alternative blocks two thirds of this plan for a ten-line change. The implementer
> MUST record the widening explicitly (add both paths to the task's `file_scope` in
> `specs/state.json`, and name the widening in the implementation summary). Proceeding without
> recording it is the silent scope creep this block exists to prevent.

**Tasks**:
- [ ] Narrow the raw `hOutputsSubsetUniverse` parameter of `modalExpMeasure_step_lt_gen` from
      `∀ φ0, …` to the lemma's own already-bound `φ0`
- [ ] Fix the single interior application (research measured exactly one; the body change is
      deleting one argument)
- [ ] Update the enumerated consumption sites to pass `… φ0`: `CompletenessLoop.lean` (research
      anchors `:458`, `:984`, `:1347`, `:1644`) and `GenericDriver.lean` (`:548`)
- [ ] Add the `…At` sibling of `modalStepBranchGen_expMeasure_step_lt` in `GenericDriver.lean`,
      taking `RuleApplicationSpecAt φ0 apply` instead of `RuleApplicationSpec apply`
- [ ] If the narrowing cascades into `modalStepHintikka_preserves_inv` or
      `modalExpandBranchesGen_hintikka` signatures beyond the enumerated sites: **stop**, record
      the measured site list and the cascade shape, and report rather than absorbing the refactor
- [ ] Record the `file_scope` widening in `specs/state.json` and in the phase's commit message

**Timing**: 1 hour

**Depends on**: 2

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: research asserts **five** consumption sites and **one** interior application,
totalling ~10 lines. Both counts are hypotheses. Confirm before editing with
`grep -rn "outputsSubsetUniverse" Cslib/Logics/Modal/Tableau/` and
`grep -rn "modalExpMeasure_step_lt_gen" Cslib/Logics/Modal/Tableau/`; record the actual counts in
the summary. Note that the `:458` and `:984` sites apply `spec.outputsSubsetUniverse` /
`hcore.outputsSubsetUniverse` directly rather than calling the narrowed lemma, so their
inclusion in the five is itself worth confirming.

**Commit-mode rationale**: the signature change and its call sites are red in every intermediate
state — a partially-updated call-site set does not build. The declared batch is exactly the file
set named in the SCOPE DECISION block plus `GenericDriver.lean`. It is declared here in advance,
and must not be widened at implementation time.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` - **outside file_scope** - narrow one hypothesis,
  drop one argument at its single interior application
- `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` - **outside file_scope** - pass `φ0` at the
  enumerated sites
- `Cslib/Logics/Modal/Tableau/GenericDriver.lean` - pass `φ0` at `:548`; add the `…At` wrapper
- `specs/state.json` - record the `file_scope` widening

**Verification**:
- Full `lake build` green with no diff outside the four files above
- `git diff --stat` total under ~30 changed lines across the three Lean files; materially more
  means the cascade hit and the stop condition applies
- Zero `sorry` introduced

---

### Phase 4: `modalDualAugment` and Its Lemmas [COMPLETED]

**Goal**: `DDriver.lean` exists carrying `modalDualAugment` and the four lemmas D's universe
argument needs.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Tableau/DDriver.lean` with header, copyright/authors block, and
      module docstring matching `TDriver.lean:13-60`'s density and structure
- [ ] Define `modalDualAugment φ` — `φ` conjoined with `◇ψ` for each `□ψ ∈ modalSubfmls φ` and
      `□ψ` for each `◇ψ ∈ modalSubfmls φ`
- [ ] Prove `φ ∈ modalSubfmls (modalDualAugment φ)` so the initial branch `[F(φ)@0]` lies in
      `modalUniverse φ⁺`
- [ ] Prove dual-closure in both directions, lifting the proof shape of the prototype's
      `modalSubfmlsDual_box_dual` / `_dia_dual`; one round suffices, since the added duals' own
      subformulas are already present
- [ ] Prove `modalDepth (modalDualAugment φ) = modalDepth φ`
- [ ] Prove the entry-measure variant: `modalExpMeasure_entry_le_fuel` (`FmpMeasure.lean:214`)
      re-stated for branch `[F(φ)@0]` at `modalUniverse φ⁺`, via the existing
      `modalWork U b e ≤ 2|U|` then `3 ^ (2|U|) ≤ modalFuel` chain at `φ⁺`

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: research estimates ~110 lines for the definition plus four lemmas, and
asserts that one round of dual-augmentation suffices for closure. Confirm the one-round claim by
actually proving both closure directions — if a second round turns out to be needed, that is a
design finding to report, not a silent extra iteration to add.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/DDriver.lean` - new file (creator)

**Verification**:
- `lake env lean Cslib/Logics/Modal/Tableau/DDriver.lean` clean
- Zero `sorry`; `#print axioms` on each new lemma reports only the three standard axioms
- The `modalSubfmlsDual_length_le` bound (`2 * modalComplexity φ + 1`) is preserved — no new
  `modalWorldBound` or `modalFuel` constant appears anywhere in the diff

---

### Phase 5: D Driver Triple and Shape Lemmas [COMPLETED]

**Goal**: The `modalStepBranchD` / `modalExpandBranchesD` / `modalTableauD` triple and the
box-positive / diamond-negative shape lemmas exist and build.

**Tasks**:
- [ ] Add the driver instantiation triple, mirroring `TDriver.lean:61-86`, instantiated at
      `φ0 := modalDualAugment φ` while the tableau itself still starts from `F(φ)@0`
- [ ] Port the shape-lemma block mirroring `TDriver.lean:87-247`: the `acc`-equality lemmas, the
      `modalDBoxDual` / `modalDDiaNegDual` case and non-membership lemmas, and the four
      `modalApplyOneD_boxPos_fst` / `_boxPos_snd` / `_diamondNeg_fst` / `_diamondNeg_snd` lemmas
- [ ] Lift `modalApplyOneD_boxPos_snd` and `modalApplyOneD_diaNeg_snd` from the prototype — both
      are machine-checked there and are what F5/F6 turn on in phase 7
- [ ] Add the `not_shape_of_not_or` helper if D's discharges need it (T has it at `:254`)

**Timing**: 1.5 hours

**Depends on**: 1, 2, 4

**Verification Tier**: local

**Scope Hypothesis**: estimated ~200 lines by proportion to `TDriver.lean:61-247` (187 lines).
Confirm with `git diff --stat`; a result far above ~260 lines suggests D's shape lemmas are not in
fact structurally parallel to T's, which would be a finding worth recording since the whole cost
estimate rests on that parallelism.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/DDriver.lean` - append the triple and shape-lemma sections

**Verification**:
- Module builds clean; zero `sorry`
- Each of the four `_fst`/`_snd` lemmas is stated at the same shape as its `modalApplyOneT_`
  counterpart (diff the two statement blocks side by side)

---

### Phase 6: Field Discharges F1-F4 [NOT STARTED]

**Goal**: `freshLocal`, `outputsSubsetUniverse` (at `φ0 := φ⁺`), `persistentFresh`, and `rankStep`
are discharged for `modalApplyOneD`.

**Tasks**:
- [ ] Lift `modalApplyOneD_freshLocal` from the prototype (machine-checked there)
- [ ] Prove `modalApplyOneD_outputsSubsetUniverse_at` at the fixed `φ0 = modalDualAugment φ`, using
      phase 4's dual-closure lemmas. This is the field that fails at plain `φ0` — the prototype's
      `modalApplyOneD_outputsSubsetUniverse_fails` is the counterexample it must route around, not
      a lemma to port
- [ ] Prove `modalApplyOneD_persistentFresh`: the dual arms are `b.any`-guarded and the
      `.notApplicable` guard forces nonemptiness; T's proof shape at the corresponding site
      transports
- [ ] Prove `modalApplyOneD_rankStep`, mirroring `TDriver.lean:376-483`. The only genuinely new
      content is `modalDepth (◇ψ) ≤ rank w` where T needed `modalDepth ψ ≤ rank w`; close it with
      `modalDepth_diamond_eq_box` (`rfl`, machine-checked in the prototype)
- [ ] If `rankStep` stalls past its time box, land F1-F3 green and commit before continuing —
      phase 7 does not depend on `rankStep`

**Timing**: 2 hours

**Depends on**: 3, 5

**Verification Tier**: local

**Scope Hypothesis**: estimated ~280 lines by proportion to `TDriver.lean:266-483` (217 lines),
with `rankStep` alone accounting for ~108 of T's lines. Research classifies F3 and F4 as
"dischargeable, argued not proved" — treat both estimates as hypotheses and record the actual line
counts, since research risk #1 turns specifically on whether `rankStep`'s plumbing replays.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/DDriver.lean` - append the F1-F4 discharge section

**Verification**:
- Module builds clean; zero `sorry` — a `sorry` parked in `rankStep` is not an acceptable phase
  close, since the acceptance bar is zero `sorry`
- `#print axioms` on each of the four lemmas reports only the three standard axioms
- `modalApplyOneD_outputsSubsetUniverse_at` is stated at a fixed `φ0`, never `∀ φ0` — the whole
  point of the `…At` sibling

---

### Phase 7: Field Discharges F5-F7 [NOT STARTED]

**Goal**: `outDegStep`, `knownWorldsStep`, and `branchingLength` are discharged for
`modalApplyOneD`.

**Tasks**:
- [ ] Prove `modalApplyOneD_outDegStep`, mirroring `TDriver.lean:484-532`. D never touches `acc` at
      the two shapes — phase 5's `_boxPos_snd` / `_diaNeg_snd` lemmas are exactly this fact — so
      K's proof transports
- [ ] Prove `modalApplyOneD_knownWorldsStep`, mirroring `TDriver.lean:533-620`, on the same
      `acc`-unchanged grounds: the outputs sit at the *source* world, already known
- [ ] Prove `modalApplyOneD_branchingLength`: D never produces `.branching` at the two shapes
- [ ] Confirm no `isMintingShaped`, `outDeg`, `modalPotential`, `modalWorldBound`, or `modalFuel`
      definition was touched — Route A's failure mode, explicitly out of scope

**Timing**: 1.5 hours

**Depends on**: 6

**Verification Tier**: local

**Scope Hypothesis**: estimated ~200 lines by proportion to `TDriver.lean:484-620` (137 lines) plus
`branchingLength`. All three fields are research-classified "dischargeable, argued not proved";
confirm the transport actually holds rather than assuming it, and record any field that needed
genuinely new content.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/DDriver.lean` - append the F5-F7 discharge section

**Verification**:
- Module builds clean; zero `sorry`
- `git diff` touches no file other than `DDriver.lean`
- `grep -n "isMintingShaped\|outDeg\|modalPotential" ` over the diff shows uses only, no
  definition changes

---

### Phase 8: F8-F12 and the `RuleApplicationSpecAt` Bundle [NOT STARTED]

**Goal**: The remaining five Hintikka/saturation fields are discharged and bundled into a single
`RuleApplicationSpecAt (modalDualAugment φ) modalApplyOneD` witness.

**Tasks**:
- [ ] Lift `modalApplyOneD_localShapeInvariance` (F8) from the prototype — machine-checked
- [ ] Lift `modalApplyOneD_boxPosNotExpanding` (F9) from the prototype — machine-checked, 18 lines,
      and the field the task assumed was unsatisfiable
- [ ] Lift `modalApplyOneD_diaNegNotExpanding` (F10) from the prototype — machine-checked, 18 lines
- [ ] Lift `modalApplyOneD_boxNegWitness` (F11') and `modalApplyOneD_diaPosWitness` (F12') from the
      prototype — both machine-checked
- [ ] Assemble `modalApplyOneD_specAt : RuleApplicationSpecAt (modalDualAugment φ) modalApplyOneD`,
      mirroring the bundle shape of `modalApplyOneT_spec` (`TDriver.lean:740-757`)

**Timing**: 1.5 hours

**Depends on**: 7

**Verification Tier**: local

**Scope Hypothesis**: estimated ~180 lines by proportion to `TDriver.lean:621-757` (137 lines).
Five of the five field lemmas here are machine-checked in the prototype, so this phase should be
dominated by lifting, not proving — a line count far above the estimate, or significant new proof
work, means the prototype was not actually reused and should be re-read.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/DDriver.lean` - append the F8-F12 section and the spec bundle

**Verification**:
- Module builds clean; zero `sorry`
- `modalApplyOneD_specAt` elaborates with every field populated and no `sorry` placeholder
- `#print axioms modalApplyOneD_specAt` reports only `propext` / `Classical.choice` / `Quot.sound`

---

### Phase 9: Bridges, Hintikka, and Final Gate [NOT STARTED]

**Goal**: The `_eq` bridges and `modalExpandBranchesD_hintikka` land, and the whole in-scope
deliverable passes the full gate.

**Tasks**:
- [ ] Add `modalStepBranchD_eq`, `modalExpandBranchesD_eq`, and `modalTableauD_eq`, mirroring
      `TDriver.lean:758-791`
- [ ] Add `modalExpandBranchesD_hintikka`, mirroring `TDriver.lean:792-806`, consuming the phase-3
      `…At` wrapper and phase 8's `modalApplyOneD_specAt`
- [ ] Run the full repository gate set
- [ ] Confirm the acceptance bar repo-wide: zero `sorry` and zero new axioms introduced by this
      task's whole diff
- [ ] Write the implementation summary, naming the phase-3 `file_scope` widening and the
      out-of-scope follow-up explicitly

**Timing**: 1 hour

**Depends on**: 8

**Verification Tier**: full

**Scope Hypothesis**: estimated ~90 lines by proportion to `TDriver.lean:758-806` (49 lines).
Cumulative in-scope estimate across phases 1-9 is ~1,150 lines minus the soundness/completeness
arm; report the measured total against that estimate in the summary, since the whole Route E2 cost
case rests on it.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/DDriver.lean` - append the bridges and Hintikka sections
- `specs/598_serial_rule_spec_decision_tableau/summaries/01_*-summary.md` - implementation summary

**Verification**:
- Full `lake build` green
- `grep -rn "sorry" Cslib/Logics/Modal/Tableau/DDriver.lean` returns nothing
- `#print axioms modalExpandBranchesD_hintikka` reports only the three standard axioms
- `DDriver.lean` mirrors `TDriver.lean` section-for-section (compare the two files' section
  headers)

---

## Out-of-Scope Follow-Up: The `Decidable` Instance

Research §5 phase 6 — the soundness/completeness arm that actually produces
`instDecidableDValid` — is **excluded from this plan** and is not delivered by phases 1-9.

**Files it requires, both outside the declared `file_scope`**:
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`

**Work it comprises** (research §3.2, §3.3, §5):
- `dFC := fun r => Relation.Serial r`, plugged into the existing frame-relativised chain
  (`branchSatisfiableIn FC` / `frameValid FC`); the `hAgree` / `hBoxPos` / `hDiaNeg` triple has the
  same shape as T's
- `serialGen r := fun a b => r a b ∨ ((¬ ∃ c, r a c) ∧ a = b)` and its unconditional
  `Relation.Serial` instance — free, exactly as `Std.Symm` is free off `Relation.SymmGen` for B
  (`FrameCompleteness.lean:432-446`)
- `extractModelD` via `extractModelWith` (`FrameCompleteness.lean:87`), the Strategy-B
  closure-at-extraction the whole cube already uses
- The two new-content Hintikka bridges (box-positive and diamond-negative arms)
- `modalTableauD_sound`, `modalTableauD_complete`, `instDecidableDValid`

Scope is comparable to T's arm in `FrameCompleteness.lean`.

**Choice required before this work proceeds** — this is a decision for the user or orchestrator,
not for the implementing agent:

1. **Widen `file_scope`** to add `FrameSoundness.lean` and `FrameCompleteness.lean`, and append
   these phases to this plan; or
2. **Spawn a successor task** carrying the soundness/completeness arm, depending on this task, with
   `file_scope` set to those two files plus `DDriver.lean`.

Option 2 is the better default: this arm is a coherent, separately-verifiable deliverable of its
own, and the task's stated deliverable ("a measured decision report plus the D prototype, not a
full corner") is already met by phases 1-9. This is a recommendation, not a decision made here.

Note the asymmetry with phase 3, which *is* included: phase 3's out-of-scope edit is ten
mechanically-forced lines without which two thirds of this plan cannot build, whereas this arm is
a large, cleanly separable body of work.

## Testing & Validation

- [ ] `lake build` green at the end of every phase, not only at the end of the task
- [ ] Zero `sorry` in `DDriver.lean` and in every file this task's diff touches
- [ ] Zero new axioms: `#print axioms` on each new top-level theorem reports only `propext`,
      `Classical.choice`, `Quot.sound`
- [ ] `RuleApplicationSpec` is byte-identical to HEAD, and all seven of its discharge sites still
      elaborate untouched
- [ ] No definition change to `modalSubfmls`, `isMintingShaped`, `outDeg`, `modalPotential`,
      `modalWorldBound`, or `modalFuel`
- [ ] `modalApplyOneD_specAt` elaborates as a complete `RuleApplicationSpecAt` witness
- [ ] The phase-3 `file_scope` widening is recorded in `specs/state.json` and named in the summary

## Artifacts & Outputs

- `Cslib/Logics/Modal/Tableau/DDriver.lean` (new, ~1,000 lines)
- `Cslib/Logics/Modal/Tableau/FrameRules.lean` (additive, ~60 lines)
- `Cslib/Logics/Modal/Tableau/GenericDriver.lean` (additive, ~120 lines)
- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` (~5 lines, out of declared scope — see phase 3)
- `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` (~5 lines, out of declared scope — see phase 3)
- `specs/598_serial_rule_spec_decision_tableau/summaries/01_serial-d-driver-summary.md`
- `specs/state.json` (phase-3 `file_scope` widening record)

## Rollback/Contingency

Every phase is additive except phase 3, so rollback is per-phase `git revert` of that phase's
commit in reverse dependency order (9 -> 8 -> 7 -> 6 -> 5 -> 3 -> 4/2/1).

- **Phases 1, 2, 4-9**: additive only. Reverting any one leaves the pre-existing cube (K, T, B, TB,
  Five, Kb5'', S5w) untouched and building, because nothing outside `DDriver.lean` depends on them.
- **Phase 3**: the only phase that mutates an existing signature. It is `atomic-batch` precisely so
  its revert is a single commit. Reverting it forces reverting phases 5-9 as well, since D's
  measure chain depends on the narrowing.
- **If `rankStep` (phase 6) proves unreachable**: this refutes research risk #1's transport
  argument and is a genuine finding. Stop, keep phases 1-5 committed and green, and report — do not
  park a `sorry`, which would breach the task's stated acceptance bar.
- **If the phase-3 cascade exceeds the enumerated sites**: stop before editing further, keep
  phases 1, 2, 4 committed, and report the measured cascade. A `CompletenessLoop.lean` refactor is
  outside both the declared `file_scope` and Route E2's additivity claim, and would justify
  re-opening the route decision rather than absorbing the cost silently.
