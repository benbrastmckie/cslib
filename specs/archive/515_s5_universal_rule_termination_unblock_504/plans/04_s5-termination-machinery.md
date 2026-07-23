# Implementation Plan: S5 Witness-Reuse Rule + Linear World Budget (v3)

- **Task**: 515 - s5_universal_rule_termination_unblock_504
- **Status**: [NOT STARTED]
- **Effort**: 25 hours (15 phases; see per-phase timings -- this is a deliberately pessimistic figure, see "Budget realism" below)
- **Dependencies**: Task 514 (literature grounding); Task 504 (parent; `modalApplyOneS5`, `extractModelS5*`, `modalTruthLemmaS5` landed CI-green). Task 511 (S4 keyed-guard sibling) is **decoupled by this revision** -- see Goals & Non-Goals.
- **Research Inputs**:
  - reports/03_s5-infrastructure-deep-research.md (**the authority for this revision**; 29-agent deep research, mechanized against the repo)
  - reports/01_s5-termination-implementation-blueprint.md (superseded on R7, D2-adjacent findings retained)
  - summaries/01_s5-termination-machinery-summary.md (v1 implementation record)
  - plans/02_s5-termination-machinery.md (superseded by this file)
- **Artifacts**: plans/04_s5-termination-machinery.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/git-workflow.md
  - .claude/rules/plan-format-enforcement.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Plan v2 pursued a keyed loop-checking termination chain (birth keys, pigeonhole, a 12-field
`S5LoopInv`) mirrored from S4, instantiated at a bespoke S5 universe. It landed Phases 1-7
sorry-free and CI-green and then blocked at Phase 8 on the Hintikka lift. Deep research
(`reports/03_s5-infrastructure-deep-research.md`) has since established that plan v2 is
**architecturally invalid, not merely over budget**: its two offered routes to close Phase 8 are a
**false statement** (R7 fuel domination) and a **cost sink** (a keyed driver that can consume
neither the measure engine nor the landed generic lift), and its measurement substrate
(`modalUniverseS5`/`modalWorldBoundS5`) **breaks the fuel arithmetic** it depends on.

This v3 replaces that architecture. **Bound MINTING, not re-firing.** Replace the two
world-*minting* arms of `modalApplyOneS5` (`T(◇φ)@w`, `F(□φ)@w`) with a guard-less witness-reuse
test: if any known world already carries `⟨s,φ,w'⟩`, add edge `w→w'` and emit `.linear [⟨s,φ,w'⟩]`;
mint fresh only when no witness exists on the branch. Leave the S5 universal-propagation arms
(`T(□φ)`, `F(◇φ)`) **completely untouched** -- they are already correct and already self-limiting.
Keep the generic driver **unmodified** and retarget the entire termination stack at K's **own**
`modalUniverse`/`modalWorldBound`/`modalFuel`, bounding worlds by a monotone tag-injection argument
(each mint permanently consumes a distinct `(sign, subformula)` tag) -- **linear**, not exponential.
Split `RuleApplicationSpec` so the Hintikka machinery no longer sees the three fields S5 cannot
discharge.

**Definition of done**: `modalTableauS5` re-based on the witness rule; `modalTableauS5_sound` and
`modalTableauS5_complete` both sorry-free; `instDecidableS5Valid : Decidable (s5Valid φ)`; the R7
refutation landed as a theorem; ~2,000 lines of dead code deleted; the 5/KB5 impossibility recorded
and the false docstrings corrected. Zero `sorry`, zero new axioms, full CSLib CI at every milestone.

### Research Integration

Newly integrated this revision: **`reports/03_s5-infrastructure-deep-research.md`** (56KB). Its §5
lemma-level build plan drives the phase list below; its §6 drives the deletion accounting; its §7
drives Risks & Mitigations; its §8 (Rejected Alternatives) is the standing do-not-re-attempt record.

Four findings invalidate plan v2. **Each was independently re-verified against this repo by the
orchestrator before this plan was written** -- they are not taken on the research agent's word:

1. **R7 (fuel domination) is REFUTED BY EXECUTION, not merely unproven.**
   `modalExpandBranchesGen modalApplyOneS5` on `[T(□◇p)@0]` yields `maxWorld` = 5/10/20/40 at fuel
   10/20/40/80 -- exactly `fuel/2`, no fixpoint. The unguarded S5 expansion is **unbounded** on a
   formula with a **one-world** S5 model. Plan v2's Phase 8 offered exactly two routes to close the
   Hintikka lift; this one is a **false statement**. It is therefore landed as a **theorem** in
   Phase 3, beside `modalApplyOneS5_rankStep_not_dischargeable`, so no future dispatch re-attempts it.
2. **`modalUniverseS5`/`modalWorldBoundS5` BREAK the fuel arithmetic and must be DELETED.**
   `modalFuel` does not dominate the entry measure at `modalUniverseS5`: it fails at `atom` (19 > 8),
   `□p` (135 > 120), `p ∧ q` (779 > 120). The advertised escape hatch
   `modalWorldBoundS5 φ ≤ modalWorldBound φ` is **false** (`atom` 4 vs 1; `□p` 16 vs 9); it holds
   only at `□◇p` -- the single formula the prior dossier was built on. `modalFuel` is calibrated
   *razor-thin* against K's own universe (margin of exactly **1** at `atom p` and `p ∧ q`), so the
   looseness sits **in the exponent**. The whole termination stack retargets at K's own universe,
   where `modalExpMeasure_entry_le_fuel` (`FmpMeasure.lean:208`) applies **verbatim**.
3. **No φ₀-parametrized rule can ever work.** `modalExpMeasure_step_lt_gen`'s
   `hOutputsSubsetUniverse` (`FmpMeasure.lean:3241`) binds `φ0` **universally inside the hypothesis**
   (verified by reading the signature). This kills static pre-allocation outright, and kills the
   `modalApplyOneS5a φ₀` / `modalApplyOneS5g phi0` shapes. The witness rule is plain
   `RuleApply Atom` and discharges the field uniformly. *(This also explains why the landed
   `modalApplyOneS5g phi0` precedent never reached the measure layer.)*
4. **5/KB5 is NOT deliverable by ANY S5 tableau.** Verified from the definitions:
   `s5FC = Std.Refl r ∧ Relation.RightEuclidean r` (`FrameSoundness.lean:1273`) but
   `fiveFC = Relation.RightEuclidean r` **alone** (:1283) and
   `kb5FC = Std.Symm r ∧ Relation.RightEuclidean r` (:1291) -- **strictly larger** frame classes.
   `□p → p` separates them, so `fiveValid ⊊ s5Valid`. See "Scope correction" below.

**The re-firing "crux" does not exist.** `.persistent` returns `[expanded]` **unchanged**
(`Saturation.lean:141`), so boxes are never retired and re-fire automatically; `Saturation.lean:39`
states this as design intent. Re-firing is the divergence **engine** of the shipped rule *and* the
mechanism that makes the fix complete: `modalS5BoxAll` filters formulas already on `b` and returns
`.notApplicable` when `allNew.isEmpty`, so **applicable ⟺ some known world lacks the formula** --
bound the world set and the box saturates **by itself**. No stratification, no firing-order
discipline, no fairness. The report proves these impossible (§8 item 2): the strata do not
stratify, because *firing boxes creates world-creating formulas*. Any phase proposing them solves a
non-problem.

Empirical validation of the recommended rule, executed against the **real** driver: an exhaustive
**3,963-formula** corpus (depth 2 over `{p,q,⊥}` under `□,◇,→,∧,∨`) differentially against an exact
S5 oracle -- **0 mismatches, 0 fuel-instability, 0 world-bound violations** (1,057 valid /
2,906 invalid, non-vacuous). `□◇p` saturates at **2 worlds**, stable across fuel 20→2000.

### Prior Plan Reference

This v3 supersedes `plans/02_s5-termination-machinery.md` (which superseded `plans/01_*.md`).
**No phase of v2 is carried forward as `[COMPLETED]`.** v2's Phases 1-7 landed CI-green and are
committed, but v3 re-architects beneath them: most of that work is deleted in Phase 14 (see
"Preserved-Assets Accounting"). This is intentional and is the honest sticker price of the
recommendation. v2's *findings* survive in full: `modalApplyOneS5_rankStep_not_dischargeable`
(the rank route is dead) is **kept** as landed documentation, and v2's "recommended next dispatch
item 1" (the `accTargetsKnown` top-loop generalization) survives verbatim as Phase 5.

### Budget realism

Plan v2 budgeted its Phase 8 at **3 hours**; it proved to be several phases and ultimately
`[BLOCKED]`. This plan does not repeat that error. Every phase below is sized to **one agent run**
(~100-500 lines of output) and the aggregate is deliberately pessimistic. Where the report supplies
concrete Lean declarations they are named inline; where a phase is a port of an existing proof its
source `file:line` and line count are given. Phase 12 (the ~310-line double induction) carries an
explicit authorization to split across two dispatches rather than being compressed.

The research report recommends **13** phases (0-12). This plan has **15** (0-14). The three
deviations, all justified above: (a) Phase 3 lands the R7 refutation as a theorem plus the
docstring/scope corrections (report §6 "Add a sibling" + §7 scope corrections, unphased there);
(b) Phase 8 is an explicit scratch-probe **gate** for R1 (report R1: "Probe it in scratch BEFORE
committing to Phase 6+"); (c) the report's Phase 10 (`accTargetsKnown`) is promoted to Phase 5,
early and off the critical path, because **every route needs it**.

## Scope correction (READ THIS FIRST -- contradicts the task description)

**The 5/KB5 deliverable is dropped as mathematically impossible via the S5 tableau.**

The task description's stated deliverable -- *"5/KB5 validity + completeness via `Satisfies.five`
(Basic.lean) and `Cslib/Foundations/Relation/Euclidean.lean` RightEuclidean API (Phase 7
completion)"* -- **cannot be delivered by any S5 tableau**, and plan v2's Phase 9 was therefore
pursuing an impossibility. Verified from the definitions in `FrameSoundness.lean`:

| Frame class | Definition | file:line |
|---|---|---|
| `s5FC` | `Std.Refl r ∧ Relation.RightEuclidean r` | :1273 |
| `fiveFC` | `Relation.RightEuclidean r` (**reflexivity absent**) | :1283 |
| `kb5FC` | `Std.Symm r ∧ Relation.RightEuclidean r` (**reflexivity absent**) | :1291 |

`fiveFC` and `kb5FC` are **strictly larger** frame classes than `s5FC`. `□p → p` is `s5Valid` but
not `fiveValid` (a non-reflexive right-Euclidean frame refutes it). Hence `fiveValid ⊊ s5Valid`,
and a sound+complete decision procedure for `s5Valid` **does not compose into one for `fiveValid`**:
the S5 tableau's closure is the wrong side of a strict inclusion. This is a property of the
*mathematics*, not of any tableau engineering.

**In-scope consequence (Phase 3)**: `FrameCompleteness.lean:571-580` currently frames this as a mere
**scheduling** dependency -- *"Such a completeness/decidability result needs `modalTableauS5_complete`
(Phase 4) and `modalTableauS5_sound` (Phase 5) as its proof engine, and both are transitively blocked
by Phase 2"*. **That docstring is wrong on the mathematics** and appears to have misled the last
planner into plan v2's Phase 9. Correcting it to state the frame-class inclusion obstruction is an
**in-scope task of this plan** (Phase 3), so it does not mislead the next one.

**ACTION REQUIRED FROM THE USER**: the task description itself needs amending to drop the
"Phase 7 completion" 5/KB5 deliverable. This plan cannot deliver it and no successor plan can
either. The genuinely independent fragment that *is* landed and CI-green from task 504 --
`extractModelS5_rightEuclidean` (`RightEuclidean (extractModelS5 b acc).r` holds unconditionally,
since every equivalence relation is right-Euclidean) -- stays landed and untouched. Pure-K5 /
pure-5 remains out of scope for the independent reason already recorded in-file (no Mathlib
"Euclidean closure" operator analogous to `Relation.EqvGen`); the report independently corroborates
that gap as a **real mathematical obstruction** (OLP §fil.9), so that half of the note is correct
and is retained.

**Second, smaller correction**: *"against `Cube.S5`"* is a docstring gesture, not a theorem. No Lean
theorem connects `s5Valid` to `Cube.S5` -- and none connects `kValid` to `Cube.K` either, so this is
precedent-consistent rather than an S5 regression. The real deliverable is `Decidable (s5Valid φ)`.

## Goals & Non-Goals

**Goals**:
- Land the guard-less witness-reuse rule `modalApplyOneS5w : RuleApply Atom` (plain, **not**
  φ₀-parametrized) intercepting exactly the two minting shapes; leave the universal-propagation arms
  untouched.
- Land `hintikka_congr` early -- it ports the entire landed countermodel half of S5 completeness
  with **zero edits** to `FrameCompleteness.lean`.
- Land the linear a-priori world budget: `modalOps_lt_worldBound` + the `usedTags` monotone-injection
  counting crux, replacing the birth-key pigeonhole. Retarget at K's own
  `modalUniverse`/`modalWorldBound`/`modalFuel`, reused **verbatim**.
- Split `RuleApplicationSpec` into `RuleApplicationSpecCore` (+ 3 S5-impossible fields), with the
  witness-world obligations weakened to existential form. K/T/B keep their exact names and statements.
- Re-derive the Hintikka lift parametrically over an auxiliary step-preserved predicate `Aux`, with
  a hard **regression gate**: `modalExpandBranchesGen_hintikka` keeps its exact existing name and
  statement.
- Land `modalTableauS5_sound` (statement unchanged) and `modalTableauS5_complete`, then
  `instDecidableS5Valid : Decidable (s5Valid φ)`.
- Land the **R7 refutation as a theorem**; correct the false docstrings and the 5/KB5 scope note.
- Delete ~2,000 lines of dead code, unsentimentally (see accounting below).
- Zero `sorry`, zero new axioms; full CSLib CI at every milestone; incremental commit at each green
  milestone; narrow `git add` (concurrent sessions active).

**Non-Goals**:
- **5/KB5 validity + completeness** -- dropped as mathematically impossible via the S5 tableau (see
  Scope correction). Only the docstring correction is in scope.
- Pure-K5 / pure-5 (Euclidean-without-equivalence) completeness -- out of scope, independently.
- Any `RuleApplicationSpec modalApplyOneS5` witness (proven false, kept as landed documentation).
- **Any stratification / firing-order / fairness / round-robin discipline** -- provably impossible
  (report §8 item 2). Do not phase it.
- **Any re-firing machinery** -- the crux does not exist (`.persistent` never retires the box).
- Any φ₀-parametrized rule -- type-level impossible (report §8 item 3).
- Filtration / semantic FMP as the primary route -- category error (report §8 item 9). Retained only
  as the R1 fallback (`[PARTIAL]`, deliverable 4 only).
- Tightening `modalFuel` -- scope creep; sufficiency, not tightness, is the requirement.
- **Task 511 (S4) coordination.** v2 coupled 515 to 511 via a shared keyed guard. v3 **decouples**
  them: the keyed guard is retired here, so there is no shared artifact and no sequencing
  constraint. 511 is unaffected by this plan and this plan does not owe S4 anything.
- Editing K/T/B rule declarations, `Saturation.lean`'s driver, or `FmpMeasure.lean`'s measure engine.
  The `RuleApplicationSpec` **structure** is split (Phase 9) but K/T/B's instantiations keep their
  shape via `extends`.

## Preserved-Assets Accounting

The task description says *"REUSE the CI-green Phase 1/3 assets already landed and committed by task
504: S5Simplification.lean and FrameCompleteness.lean."* This plan reuses **`FrameCompleteness.lean`
in full and verbatim** (better than v2 managed), but **deletes roughly 2,000 of
`S5Simplification.lean`'s 3,041 lines** (file length verified). That deletion is counter-intuitive
and is justified below so the next implementer does not try to rescue it.

### Reused VERBATIM (zero edits)

| Asset | file:line | Note |
|---|---|---|
| `modalTruthLemmaS5` | FrameCompleteness.lean:2048 | ports via `hintikka_congr` (Phase 2) |
| `modalOpenBranchS5_countermodel` | FrameCompleteness.lean:2288 | via `hintikka_congr` + Phase 5's `hTgt` |
| `hintikkaS5_box_pos` / `_diamond_neg` | :1956 / :1995 | shapes the witness rule does not touch |
| `eqvGen_mem_modalKnownWorlds_iff`, `extractModelS5*` | :1934, :499-531 | loop-back edges inert under `EqvGen` |
| `extractModelS5_rightEuclidean` | FrameCompleteness.lean | landed task-504 asset; unaffected by the 5/KB5 drop |
| `modalS5BoxAll` / `modalS5DiaNegAll` + `_mem` | S5Simplification.lean:216-291 | **untouched -- correct as they stand** |
| `modalApplyOneS5` | S5Simplification.lean:300 | called for all 12 non-mint arms **and** the mint `none` branch |
| `modalApplyOne_diamondPos_witness` / `_boxNeg_witness` | Rules.lean | discharge the `none` arm |
| `modalExpMeasure` / `modalWork` / `_step_lt_gen` | FmpMeasure.lean:192/197/3231 | **spec-free -- VERIFIED** |
| `modalUniverse` / `modalWorldBound` / `modalExpMeasure_entry_le_fuel` | FmpMeasure.lean:149/144/208 | **K's own -- verbatim** |
| `modalFuel` | Saturation.lean:98 | **unchanged, no re-derivation** |
| `modalExpandBranchesGen` / `modalStepBranchGen` / `modalTableauGen` | Saturation.lean:122/201/363 | **generic driver UNMODIFIED** |
| `accReachableInv_related_s5` | FrameSoundness.lean:1381 | the reuse-soundness engine (R1's mitigation) |
| `modalApplyOneS5_fresh_local` | FrameSoundness.lean:~1326 | stays reusable (witness rule is *defeq* to `modalApplyOneS5` on all 12 non-mint arms) |
| `signedSubfmls` + `signedSubfmls_card_le` | LoopChecking.lean:290/298 | the card bound |
| `modalApplyOneS5_rankStep_not_dischargeable` | S5Simplification.lean:2995 | **KEPT** as landed documentation of the dead rank route |

### DELETED (Phase 14) -- ~2,000 CI-green, sorry-free, committed lines

**These die on COST and on CORRECTNESS-OF-SUBSTRATE, not because they contain bugs.** Do not rescue
them.

| Asset | file:line | Why it dies |
|---|---|---|
| `modalWorldBoundS5`, `modalUniverseS5` + membership/length lemmas | :60-204 | **Must** die: `modalFuel` does **not** dominate the entry measure at this universe (`atom` 19 > 8, `□p` 135 > 120, `p∧q` 779 > 120 -- VERIFIED by execution). Keeping them **breaks the fuel**. The escape hatch `modalWorldBoundS5 ≤ modalWorldBound` is **false**. |
| `blockingWorldS5`, `successorBirthContentS5`, `modalApplyOneS5g` | :888-1051 | The **unkeyed** guard provably **never fires** (`= none` at every mint): birth content is scanned trigger-world-**locally**, but S5's universal box broadcasts **globally**, so live sets are permanently a strict superset of birth content. The S4 birth-content abstraction is sound only because in S4 a world inherits at birth everything it will ever have; **S5 violates that premise**. Additionally `modalApplyOneS5g` emits `.linear []` (:987), which **breaks `freshLocal`'s right disjunct** (needs a cons). |
| `blockingWorldS5Keyed`, `modalStepBranchS5gKeyed` | :1424-1549 | The keyed guard **genuinely works** (0/700 differential errors) -- but **no driver runs it**, and one cannot be added cheaply. See the decisive cost fact below. |
| `S5LoopInv` (12 fields) + ~11 `modalStepBranchS5g_preserves_*` | :1566-2723 | Invariants of a stepper **no driver runs**; and it carries **none** of `ModalLoopInvGen`'s five Hintikka-forcing fields, so it could not close the lift even if a driver existed. |
| `modalKnownWorlds_length_le_worldBoundS5`, `S5LoopInv.worldBound` | :2724-2830 | The birth-key **pigeonhole**. Replaced by `modalOps_lt_worldBound` -- a monotone injection: no powerset, no rank, no potential, no birth keys. |
| `modalApplyOneS5_snd_eq` + the acc-invariance chain | :340-351, :398 | Becomes **false** (the reuse arm adds an edge where K adds none). Must be restated, not preserved. |
| Docstrings at :40-45 and :1071-1073 | | **Factually false.** *"`modalFuel` is sufficient here too"* is refuted by execution. Delete, do not preserve. |

**The decisive cost fact -- why the keyed assets die even though the keyed stepper works.** This is
*not* "the guard fails" (that was the **unkeyed** guard -- a different function; the prior dossier's
apparent contradiction resolves because two angles measured `blockingWorldS5` and two measured
`blockingWorldS5Keyed`, and **both measurements are true**). It is:
**`modalExpMeasure_step_lt_gen` is stated for `modalStepBranchGen`** [VERIFIED]. The keyed stepper
threads `keys` and has a **different shape**, so a keyed driver could consume neither the measure
engine **nor** `modalExpandBranchesGen_hintikka` -- the single most expensive landed asset -- and
would have to re-derive both against `FmpMeasure.lean`'s 3,392 lines. The keyed route's
"~1,900 preserved lines" are **inputs to work that must still be written from scratch**. It also
grows **quadratically** (⌊n²/4⌋+1 on alternating `□◇` chains) and has an unresolved
`keysTotal`-at-initialization gap (the driver starts `keys = []` while world 0 is already known).
The witness route keeps the generic driver and *re-instantiates* that induction. **That is the whole
ballgame.**

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|---|---|---|---|
| **R1 (TOP RISK) -- `modalTableauS5_sound` re-proof.** `modalTableauS5_sound` (`FrameSoundness.lean:2379`) is stated for the unguarded rule. The statement stays **identical**, but the proof must be re-run against the witness rule. This is the largest un-costed item in the prior effort and is **un-mechanized**. | H | M | The new case is the reuse edge `w→w'` to an **existing** `w'` carrying `⟨s,φ,w'⟩` -- structurally **easier** than the landed mint case, because the world-assignment `f` is **not extended** (no mint), so the only obligation is `m.r (f w) (f w')` for an existing `w'`. **The decisive reuse**: `accReachableInv_related_s5` (`FrameSoundness.lean:1381`) -- **already landed** -- states exactly that two known worlds, both reachable from 0, are related in any model whose relation is an equivalence relation. **MITIGATION IS A GATE: Phase 8 probes this in scratch BEFORE Phase 9**, exactly as `hintikka_congr` and `diaPosWitness'` were probed in the research session. **Kill condition**: if the re-proof exceeds **~400 lines**, stop and re-litigate the fork (fallback 2 below). |
| **R2 -- Phase 0 tag closure.** If `(s,ψ) ∈ mintTags φ₀` is not derivable from `S5wTagInv` under the `neg φ = φ.imp .bot` encoding, the counting argument fails and the linear bound with it. | H | L | **30-minute kill test. Phase 0. Runs FIRST, before any investment.** `Proposition` has 7 constructors -- `atom, bot, imp, and, or, box, diamond` -- with no primitive negation (`Basic.lean:72-88`) [VERIFIED]. **Kill**: if it fails, fallback 1 (obtain the world bound another way -- a phase, not a redesign). |
| **R3 -- `Aux` parametrization lands on the K/T/B surface.** Phase 10 changes `ModalLoopInvGen`'s shape; dropping `rank` is an **arity change** to the structure K/T/B share, not a field swap. | H | M | `extends` + the **Phase 12 regression gate**: `modalExpandBranchesGen_hintikka` must keep its **exact existing name and statement** (`TDriver.lean:911` / `BDriver.lean:871` consume it **by name** with `∃ rank, ModalLoopInvGen …` in the hypothesis), re-derived from the parametric lift at `Aux := (∃ rank, …)`. **Kill**: if that re-derivation does not go through, **STOP at Phase 12, before any further S5-specific work is wasted** -- the factoring is wrong. |
| **R4 -- un-enumerated `modalApplyOneS5_snd_eq` consumers.** The lemma becomes **false** under the witness rule. | M | L | Blast radius is smaller than feared: `FrameSoundness.lean:1326` is inside `modalApplyOneS5_fresh_local`, which stays reusable; every other site (`S5Simplification.lean:1720/1868/1943/1953/2017/2025/2083`, and :398) lives in the S5g/keyed machinery this plan retires anyway. **Run `lean_references` on `modalApplyOneS5_snd_eq` before Phase 13** to confirm. **Kill**: if a consumer genuinely needs the **unconditional** form and is load-bearing for the countermodel half, the "ports free" claim is falsified -- re-scope. (Judged unlikely: `hintikka_congr` bypasses that lemma entirely. INFERRED.) |
| **R5 -- correctness is validated, not proved.** 3,963 formulas / 0 mismatches / 0 instability is strong evidence, **not a proof**. Depth 2, two atoms. | M | L | The soundness+completeness theorems are the proof; the corpus is the safety net. **Falsifiers**: any formula with `maxWorld > modalOps φ` under `modalApplyOneS5w`; any super-linear world growth. Land the corpus oracle as a `#eval`-backed regression test in `CslibTests` (Phase 14) -- route-independent and the cheapest correctness net available. |
| **R6 -- guard-less arm is non-negotiable.** Adding an `if acc.hasEdge w w' then (.notApplicable, acc)` guard makes `.notApplicable` **reachable on a mint shape**, which **inverts** the `exfalso` conjunct-3/4 discharge (`CompletenessLoop.lean:1049-1060`) from a refutation into a proof obligation. | H | L | Documented as a hard constraint in Phase 1 and Phase 9. Guard-less costs at most one duplicate edge per (formula, world) and is measure-inert. Do not "optimize" it. |
| **R7 (retired) -- fuel domination.** | -- | -- | **REFUTED BY EXECUTION.** Not a risk; a **settled false statement**, landed as a theorem in Phase 3. `maxWorld = fuel/2` exactly, no fixpoint. Do not spend another cycle here. |
| **R8 -- the `birth` trap.** A `birth` function must **NOT** be defined concretely as "the least world carrying the pair": S5's universal box can later add `⟨s,φ,w''⟩` at a **smaller** world, so that formulation is **not step-preserved**. | H | M | The `usedTags`-cardinality formulation (Phase 7) sidesteps this entirely by **never naming a witness world**. This trap is real and cost a prior design; it is called out inline in Phase 7. |
| **R9 -- scope realism.** Landing all 15 phases sorry-free in one task is optimistic; v2's precedent is a `[BLOCKED]` capstone. | M | M | Two hard gates (Phase 0, Phase 8) and one regression gate (Phase 12) fail **cheap and early**, before investment. Each phase commits independently at green. If a phase resists, mark `[BLOCKED]` with the exact `lean_goal` open state -- never a `sorry`. |

**Fallbacks (in order)**:
1. **If R2 fails but the rule is sound**: keep the rule; obtain the world bound another way. This is a
   phase, not a redesign.
2. **If R1 fails**: the **atom-quotient semantic FMP** route (`Decidable (s5Valid φ)` via enumerating
   quotient models over `Fin k → Bool`) is **pre-authorized** by plan v2's Phase 8 blocked branch and
   was compiled sorry-free and axiom-clean in the research session. It delivers **deliverable (4)
   only** -- not `modalTableauS5_complete`, and **not** 5/KB5 (its `qTransfer` needs reflexivity,
   which `fiveFC`/`kb5FC` lack). Legitimate as a documented `[PARTIAL]`, **not** as the primary route.
3. **If R3 fails**: stop at Phase 12. Phases 0-8 (rule, congruence, refutation, budget,
   `accTargetsKnown`, tag invariant, counting crux) remain landed, green, and independently valuable.

## Testing & Validation

Run the full CSLib CI pipeline at **every** phase milestone (zero-debt contract) before committing:

- [ ] `lake build` -- full project green (baseline: 3239/3239 jobs)
- [ ] `lake exe checkInitImports` -- clean
- [ ] `lake exe lint-style` -- clean
- [ ] `lake lint` -- 0 new errors on task-touched files (1 pre-existing unrelated `unusedArguments`
      error in `PrimeExclusion.lean`, and a pre-existing `sorry` in
      `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:118` from task 317, both predate
      this task; do not action)
- [ ] `lake test` -- `CslibTests` suite exit 0
- [ ] `lake shake --add-public --keep-implied --keep-prefix` -- no NEW suggestions for task-touched files
- [ ] `grep -c 'sorry' <touched files>` -- 0 (prose mentions excepted)
- [ ] `grep -c '^axiom ' <touched files>` -- 0 new axioms
- [ ] `lean_verify` on each phase's headline declaration -- axioms limited to
      `propext` / `Classical.choice` / `Quot.sound`
- [ ] **Regression gate (Phases 9-12)**: `TDriver.lean` and `BDriver.lean` compile **unmodified**;
      `modalExpandBranchesGen_hintikka` retains its exact name and statement.

Per-milestone commit discipline: **narrow `git add`** -- only the specific `.lean` file(s) touched by
the phase, plus this plan and state files. **Never `git add -A` / `git commit -am`** (concurrent
sessions are active on this repo). Commit message: `task 515 phase {P}: {name}`.

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 0, 3, 4, 5 | -- |
| 2 | 1, 6 | 0, 4 |
| 3 | 2, 7, 8 | 1, 6 |
| 4 | 9, 13 | 2, 8 |
| 5 | 10 | 7, 9 |
| 6 | 11 | 10 |
| 7 | 12 | 11 |
| 8 | 14 | 3, 5, 12, 13 |

Phases within the same wave can execute in parallel. **Phase 0 gates everything.** **Phase 8 (R1
scratch probe) gates Phase 9 onward.** **Phase 12 carries the K/T/B regression gate: if it fails,
stop.** Phases 3, 4, 5 are independent of the rule and can start immediately in parallel with the
kill test. Phase 13 (soundness) forks after Phase 8 and runs parallel to the 9→10→11→12 lift chain.

Ambient context for every Lean phase: `S5Simplification.lean:54-56`
(`namespace Cslib.Logic.Modal.Tableau`, `open Cslib.Logic.Tableau Cslib.Logic.Modal`) and the file's
`variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]`. **No `Fintype Atom` is needed
anywhere.**

### Phase 0: Kill test -- `modalSubfmls` tag closure under the `neg` encoding [NOT STARTED]

**Goal**: Cheaply falsify the entire design before any investment. Verify `modalSubfmls` closure
survives the `neg φ = φ.imp .bot` encoding, so that `(s,ψ) ∈ mintTags φ₀` is derivable from the tag
invariant in the mint case. **This is the single load-bearing step of the counting argument.**

**Tasks**:
- [ ] In scratch only (`lean_run_code` / `lean_multi_attempt`; **no `.lean` file edited**), confirm
      that for `φ₀` containing `◇ψ` (resp. `□ψ`), the pair `(.pos, ψ)` (resp. `(.neg, ψ)`) is
      reachable in `signedSubfmls φ₀` / `modalSubfmls φ₀` under the encoding
      `neg φ = φ.imp .bot`. `Proposition` has 7 constructors -- `atom, bot, imp, and, or, box,
      diamond` -- with **no primitive negation** (`Basic.lean:72-88`) [VERIFIED].
- [ ] Record the result in the phase's completion note (pass -> proceed; fail -> invoke fallback 1
      and re-plan the world bound, keeping the rule).

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**: none (scratch probe only)

**Verification**: a scratch snippet demonstrating the derivation, or a documented counterexample.

**Blocked-branch**: if closure fails, **do not proceed to Phase 6/7**. The rule (Phases 1-2) and the
refutation (Phase 3) remain independently valuable and should still land. Invoke fallback 1.

---

### Phase 1: The witness-reuse rule + the free bridges [NOT STARTED]

**Goal**: Land the rule. All four declarations below **already compiled sorry-free in the research
session**; this phase transcribes and CI-greens them.

**Tasks**:
- [ ] Land `witnessWorldS5`:
      ```lean
      def witnessWorldS5 (b : List (SignedFormula (Proposition Atom) WorldIndex))
          (s : Sign) (φ : Proposition Atom) : Option WorldIndex :=
        (modalKnownWorlds b).find? (fun w' => b.any (· == (⟨s, φ, w'⟩ : SignedFormula _ _)))
      ```
- [ ] Land `modalApplyOneS5w : RuleApply Atom` (**plain, NOT φ₀-parametrized** -- see report §8 item
      3; `hOutputsSubsetUniverse` at `FmpMeasure.lean:3241` binds `φ0` universally **inside** the
      hypothesis, so a φ₀-parametrized rule can never discharge it):
      ```lean
      /-- GUARD-LESS. Always `.linear [witness]` on a hit -- never `.notApplicable`, never `.linear []`. -/
      def modalApplyOneS5w : RuleApply Atom := fun sf b acc =>
        match sf.sign, sf.formula with
        | .pos, .diamond φ =>
          (match witnessWorldS5 b .pos φ with
           | some w' => (.linear [⟨.pos, φ, w'⟩], acc.addEdge sf.label w')
           | none => modalApplyOneS5 sf b acc)
        | .neg, .box φ =>
          (match witnessWorldS5 b .neg φ with
           | some w' => (.linear [⟨.neg, φ, w'⟩], acc.addEdge sf.label w')
           | none => modalApplyOneS5 sf b acc)
        | _, _ => modalApplyOneS5 sf b acc
      ```
- [ ] Land `witnessWorldS5_mem (h : witnessWorldS5 b s φ = some w') : ⟨s, φ, w'⟩ ∈ b`.
      **Compiled in research** (2 lines: `have := List.find?_some h; simpa using (List.any_eq_true.mp this)`;
      axioms `[propext, Quot.sound]`).
- [ ] Land the two `rfl` bridges -- **compiled in research**, axioms `[propext]`:
      `modalApplyOneS5w_boxPos_eq`, `modalApplyOneS5w_diaNeg_eq`.
- [ ] Land `modalApplyOneS5w_eq_of_not_mint_shape (h : ¬mint-shaped sf) : modalApplyOneS5w sf b acc = modalApplyOneS5 sf b acc`.

**Three design constraints, EACH LOAD-BEARING -- do not "optimize" any of them**:
- **`.linear [witness]`, not `.linear []`** -- the cons is required for `freshLocal`'s right disjunct
  (`.linear (wsf :: rest) ∧ .snd = acc.addEdge sf.label wsf.label`). Note `wsf` is bound only as the
  **head of the linear output**; nothing requires `wsf.label = modalNextWorld b`, despite the
  docstring saying "fresh" [VERIFIED, `GenericDriver.lean:181-190`]. The landed `modalApplyOneS5g`
  emits `.linear []` (`S5Simplification.lean:987`) and **breaks this shape** -- a genuine correction
  over the landed code.
- **`.linear [witness]`, not `.persistent []`** -- `.persistent` with an empty payload returns `some`
  with `b` **and** `expanded` unchanged (`Saturation.lean:141`): an instant infinite loop.
- **No `hasEdge` guard** (R6) -- see Phase 9.

**Timing**: 1 hour

**Depends on**: 0

**Files to modify**: `Cslib/Logics/Modal/Tableau/S5Simplification.lean`

**Verification**: full CI green; `lean_verify` on `witnessWorldS5_mem` and both bridges.

---

### Phase 2: The Hintikka congruence bridge [NOT STARTED]

**Goal**: Land `hintikka_congr`. **This is the single highest-value declaration in the plan** -- it
ports the entire landed countermodel half of S5 completeness **verbatim, with zero edits to
`FrameCompleteness.lean`**. Land it early and the whole plan de-risks.

**Tasks**:
- [ ] Land:
      ```lean
      theorem hintikka_congr (b) (acc) :
          modalHintikkaSetGen modalApplyOneS5w b acc ↔ modalHintikkaSetGen modalApplyOneS5 b acc
      ```
      **COMPILED IN RESEARCH, sorry-free, `#print axioms` = `[propext]`**, by:
      ```lean
      unfold modalHintikkaSetGen
      constructor <;> · rintro ⟨h1, h2, h3, h4⟩
                        refine ⟨h1, ?_, h3, h4⟩
                        intro sf hsf
                        have h := h2 sf hsf
                        rcases hs : sf.sign with _ | _ <;>
                          rcases hf : sf.formula with _|_|_|_|_|ψ|ψ <;> simp_all [modalApplyOneS5w]
      ```
- [ ] Record **why it works** in the docstring [VERIFIED by reading `Saturation.lean:460-480`]:
      conjunct 2 binds `let (result, _) := apply sf b acc` but then returns **literal `True`** at
      `| .neg, .box _` and `| .pos, .diamond _` -- `result` is **unused at exactly the two shapes the
      witness rule intercepts**. Conjuncts 1/3/4 name no rule function at all.
- [ ] Confirm this supersedes the two `rfl` bridges as the porting mechanism: the bridges alone are
      defeated by the 8 rewrites through `modalApplyOneS5_eq_of_not_boxPos_diaNeg` at
      `FrameCompleteness.lean:2096-2181`.

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**: `Cslib/Logics/Modal/Tableau/S5Simplification.lean`

**Verification**: full CI green; `lean_verify` on `hintikka_congr` (expect `[propext]`);
`FrameCompleteness.lean` **unmodified**.

---

### Phase 3: Land the R7 refutation as a theorem + correct the false docstrings and the 5/KB5 scope note [NOT STARTED]

**Goal**: Convert *"Phase 8 blocked"* into *"the Phase 8 target was refutable"* -- a landable,
sorry-free result -- and correct the three factually false pieces of documentation that misled the
last planner. **Independent of the rule; can start immediately.**

**Tasks**:
- [ ] Land a **sibling** to `modalApplyOneS5_rankStep_not_dischargeable` (`S5Simplification.lean:2995`),
      in the same `decide`-backed idiom, refuting the Phase 8 goal for `modalApplyOneS5`: exhibit
      `[T(□◇p)@0]` and show `modalExpandBranchesGen modalApplyOneS5` yields `maxWorld = fuel/2` with
      no fixpoint, hence `modalHintikkaSetGen modalApplyOneS5 bR aR` is **false at every fuel value**.
      Suggested name: `modalApplyOneS5_hintikka_not_reachable` (or
      `modalApplyOneS5_expansion_unbounded`). Mechanism to record in the docstring: `T(□◇p)@0` is
      `.persistent` so it never retires; it re-fires at the newest world `w`, emitting `T(◇p)@w`;
      that fresh signed formula is `.linear`, fires **once**, and mints `w+1`; the box re-fires
      there; repeat. The supply of trigger formulas never runs out because **each new world
      manufactures a new one**. This is the honest disposition of the
      `FrameCompleteness.lean:2245-2273` scope note (whose route (b) is this false statement).
- [ ] **Delete** the false docstring at `S5Simplification.lean:1071-1073`: *"S5 never mints a world
      outside the K `diamondPos`/`boxNeg` arms, so `modalFuel` is sufficient here too"*. The first
      half is **true** (and is precisely why the fix is local to minting); the second half is
      **false** by execution. Rewrite, do not preserve.
- [ ] **Correct** the docstring at `S5Simplification.lean:40-45` (*"`modalApplyOneS5` never mints a
      world"*).
- [ ] **Correct `FrameCompleteness.lean:571-580`** -- the 5/KB5 note. It currently frames the gap as
      a **scheduling** dependency (*"needs `modalTableauS5_complete` … as its proof engine"*). Replace
      with the **frame-class inclusion obstruction**: `s5FC = Std.Refl r ∧ RightEuclidean r` (:1273)
      but `fiveFC = RightEuclidean r` alone (:1283) and `kb5FC = Std.Symm r ∧ RightEuclidean r`
      (:1291) are **strictly larger** frame classes; `□p → p` separates them; hence
      `fiveValid ⊊ s5Valid` and **no S5 tableau can decide `fiveValid`**, regardless of whether
      `modalTableauS5_complete` exists. **Retain** the note's second half (pure-K5/pure-5 out of
      scope for want of a Mathlib "Euclidean closure" operator) -- that half is correct and is
      independently corroborated (OLP §fil.9) as a real mathematical obstruction.
- [ ] Add BibKey docstring traceability for the refutation: **Gore1999** (`references.bib:987`),
      **TR p.48** -- *"it can lead to an infinite chain A ∈ w, ◇A ∈ w, ◇◇A ∈ w, … so this system
      cannot give a decision procedure for S5 either."* **Cite by TR pagination (TR pp.1-106), NOT
      the Handbook's pp.297-396 -- they do not map.**

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**: `Cslib/Logics/Modal/Tableau/S5Simplification.lean`,
`Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (docstring only)

**Verification**: full CI green; the refutation theorem closes sorry-free; no docstring in either
file asserts fuel sufficiency for the unguarded S5 expansion or frames 5/KB5 as a scheduling issue.

---

### Phase 4: The linear budget arithmetic [NOT STARTED]

**Goal**: Land the arithmetic that lets `modalUniverse` / `modalWorldBound` / `modalExpMeasure` /
`modalExpMeasure_entry_le_fuel` / `modalFuel` be reused **verbatim at K's own universe**, and lets
`modalWorldBoundS5`/`modalUniverseS5` be **deleted** rather than parametrized. It single-handedly
retires the `(universe, worldBound)`-parametrization blocker. **Independent of the rule.**

**Tasks**:
- [ ] Land `def modalOps : Proposition Atom → Nat` -- **modal-operator OCCURRENCES**.
- [ ] Land `lemma modalOps_le_complexity (φ) : modalOps φ ≤ modalComplexity φ`.
- [ ] Land `lemma modalOps_lt_worldBound (φ) : modalOps φ < modalWorldBound φ`.
      **PROVED sorry-free in research** (`#print axioms` = `[propext, Classical.choice, Quot.sound]`),
      via `modalWorldBound φ = (2c+1)^(c+1) ≥ (2c+1)^1 = 2c+1 > c ≥ modalOps φ`.
      **The `c = 0` case is the tight one** (`0 < 1 = 1^1`) -- and the *naive* `2 * |modalSubfmls φ|`
      budget **fails** there (2 > 1). **Counting modal-operator occurrences rather than subformulas
      is load-bearing, not cosmetic.**
- [ ] Land `def mintTags (φ₀) : Finset (Sign × Proposition Atom)` -- `◇ψ ↦ (pos,ψ)`; `□ψ ↦ (neg,ψ)`.
- [ ] Land `lemma mintTags_card_le_modalOps (φ₀) : (mintTags φ₀).card ≤ modalOps φ₀`.

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**: `Cslib/Logics/Modal/Tableau/S5Simplification.lean`

**Verification**: full CI green; `lean_verify` on `modalOps_lt_worldBound`.

---

### Phase 5: `accTargetsKnown` top-loop generalization [NOT STARTED]

**Goal**: Close a genuinely missing generic lemma that **every route needs**. This survives verbatim
from plan v2's "recommended next dispatch, item 1" and from the repo's own scope note. Promoted here
(from the report's Phase 10) because it is early, cheap, off the critical path, and unblocks
`modalOpenBranchS5_countermodel`'s `hTgt` argument. **Independent of the rule.**

**Tasks**:
- [ ] Land `theorem modalExpandBranchesGen_openBranch_accTargetsKnown`. `grep` for
      `openBranch_accTargetsKnown` returns **zero hits** across `Cslib/` [VERIFIED]; the repo's own
      scope note (`FrameCompleteness.lean:2250-2253`) says it is *"not yet built"* and prescribes the
      fix.
- [ ] Route: **generalize `modalExpandBranchesGen_openBranch_accSourcesKnown`'s double induction**
      (`BDriver.lean:1065-1205`) over an arbitrary step-preserved per-`(branch, acc)` predicate `P`
      -- **its body is already predicate-agnostic** -- then instantiate at **both**
      `accSourcesKnown` and `accTargetsKnown`. ~60-line clone.
- [ ] Confirm zero regression to B: `modalExpandBranchesGen_openBranch_accSourcesKnown` keeps its
      exact name and statement (re-derived from the generalized form).
- [ ] Note: the step-level fact is already generic and S5-ready
      (`modalStepBranch_preserves_accTargetsKnown_gen`); **only the top-loop propagation is missing**.
      `modalOpenBranchS5_countermodel` **REQUIRES** this as its `hTgt` argument -- several candidate
      designs listed that theorem under "reuses" while never supplying its hypothesis.

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**: `Cslib/Logics/Modal/Tableau/BDriver.lean` (generalization + re-derivation)

**Verification**: full CI green; `BDriver.lean`'s existing consumers compile unmodified; the new
theorem closes sorry-free.

---

### Phase 6: The tag invariant (no world hypothesis -- breaks the circularity) [NOT STARTED]

**Goal**: Land the tag-only branch invariant. **It deliberately carries NO world-bound hypothesis**
-- this is necessary, not an oversight.

**Tasks**:
- [ ] Land:
      ```lean
      def S5wTagInv (φ₀) (b) : Prop := ∀ x ∈ b, (x.sign, x.formula) ∈ signedSubfmls φ₀
      def usedTags (φ₀) (b) : Finset (Sign × Proposition Atom) :=
        (mintTags φ₀).filter (fun p => b.any (fun x => x.sign == p.1 && x.formula == p.2))
      lemma usedTags_mono (h : ∀ x ∈ b, x ∈ b') : usedTags φ₀ b ⊆ usedTags φ₀ b'
      theorem modalApplyOneS5w_outputs_tags (hb : S5wTagInv φ₀ b) (hsf : sf ∈ b) : ...
      ```
- [ ] Record **why `S5wTagInv` carries no world hypothesis**: the landed
      `modalApplyOneS5_outputs_subset` (`S5Simplification.lean:1330`) takes
      `modalMaxWorld b < modalWorldBoundS5 φ₀` as an **input**, so it **cannot be used to prove the
      world bound**. The tag-only invariant breaks that circularity. (That landed lemma is part of
      the Phase 14 deletion set anyway.)
- [ ] Consume Phase 0's tag-closure result for the mint case.

**Timing**: 1.5 hours

**Depends on**: 0, 4

**Files to modify**: `Cslib/Logics/Modal/Tableau/S5Simplification.lean`

**Verification**: full CI green; all four declarations close sorry-free.

---

### Phase 7: The counting crux [NOT STARTED]

**Goal**: The load-bearing new proof. Land the linear a-priori world budget, replacing the birth-key
pigeonhole entirely.

**Tasks**:
- [ ] Land:
      ```lean
      def S5wWorldInv (φ₀) (b) : Prop := modalMaxWorld b ≤ (usedTags φ₀ b).card

      theorem modalStepBranchS5w_preserves_worldInv
          (hT : S5wTagInv φ₀ b) (hW : S5wWorldInv φ₀ b)
          (h : modalStepBranchGen modalApplyOneS5w b e acc = some (bs, es, acc')) :
          ∀ b' ∈ bs, S5wTagInv φ₀ b' ∧ S5wWorldInv φ₀ b'

      theorem modalMaxWorld_lt_worldBound_of_S5w (hT) (hW) : modalMaxWorld b < modalWorldBound φ₀
      ```
- [ ] **The argument** (record in the docstring): a mint fires only when
      `witnessWorldS5 b s ψ = none`, which is **equivalent** to `(s,ψ) ∉ usedTags φ₀ b` (any
      `⟨s,ψ,w''⟩ ∈ b` puts `w''` in `modalKnownWorlds b`, `Branch.lean:89`, so `find?` cannot miss
      it). The mint **emits its own witness** at `w' = modalNextWorld b = modalMaxWorld b + 1`
      (`Rules.lean:125`, `Branch.lean:99`). So `modalMaxWorld` grows by 1 while `usedTags` gains
      `(s,ψ)` -- and since `b` only ever **grows**, that tag is **used forever after**, so it can
      never mint again. Mints inject into `mintTags`. Every non-mint arm leaves `modalMaxWorld`
      unchanged and `usedTags` monotone. Chain:
      `modalMaxWorld b ≤ (usedTags φ₀ b).card ≤ (mintTags φ₀).card ≤ modalOps φ₀ < modalWorldBound φ₀`.
- [ ] Confirm `modalMaxWorld_lt_worldBound_of_S5w` is the **drop-in replacement** for
      `modalMaxWorld_lt_worldBound_of_phiBound` (`CompletenessLoop.lean:775-776`) -- same conclusion,
      at K's own bound, with **no rank, no potential, no pigeonhole, no powerset, no birth keys**.
      That scalar is **all the rank ever buys** (report §2.3).

> **TRAP THE IMPLEMENTER MUST NOT STEP IN (R8 -- this is real and cost a prior design)**: a `birth`
> function must **NOT** be defined concretely as "the least world carrying the pair". S5's universal
> box can later add `⟨s,φ,w''⟩` at a **smaller** world, so that formulation is **not step-preserved**.
> The `usedTags`-cardinality formulation above sidesteps this entirely by **never naming a witness
> world**. Do not reintroduce a `birth` function.

**Timing**: 2 hours

**Depends on**: 1, 6

**Files to modify**: `Cslib/Logics/Modal/Tableau/S5Simplification.lean`

**Verification**: full CI green; `lean_verify` on `modalMaxWorld_lt_worldBound_of_S5w`. Empirical
cross-check: **0 violations of `maxWorld ≤ modalOps φ` across all 3,963 corpus formulas** at
saturation on every branch (research session).

**Blocked-branch**: if the counting crux resists, mark `[BLOCKED]` with the exact open goal and
invoke fallback 1 (keep the rule, obtain the bound another way). No `sorry`.

---

### Phase 8: R1 scratch probe -- soundness re-proof feasibility [NOT STARTED]

**Goal**: **GATE.** Falsify or confirm the top risk (R1) in scratch **before** committing to the
spec split and the lift refactor (Phases 9-12). The report is explicit: *"Probe it in scratch BEFORE
committing to Phase 6+, exactly as `hintikka_congr` and `diaPosWitness'` were probed this session."*
This phase writes **no** production Lean.

**Tasks**:
- [ ] In scratch (`lean_run_code` / `lean_multi_attempt`; **no `.lean` file edited**), probe the new
      soundness case: the reuse edge `w→w'` to an **existing** `w'` carrying `⟨s,φ,w'⟩`. Confirm the
      world-assignment `f` is **not extended** (no mint), so the only obligation is `m.r (f w) (f w')`.
- [ ] Confirm `accReachableInv_related_s5` (`FrameSoundness.lean:1381`, **landed**) discharges it:
      it states that two known worlds, both reachable from 0, are related in **any** model whose
      relation is an equivalence relation. That is exactly the obligation.
- [ ] Run `lean_references` on `modalApplyOneS5_snd_eq` (`S5Simplification.lean:340-351`) to
      **enumerate its real consumers** (R4). Expected: `FrameSoundness.lean:1326` (inside
      `modalApplyOneS5_fresh_local`, which stays reusable) plus S5g/keyed sites
      (`S5Simplification.lean:1720/1868/1943/1953/2017/2025/2083`, :398) that Phase 14 retires anyway.
- [ ] Estimate the re-proof size. **KILL CONDITION: if the probe indicates > ~400 lines, STOP and
      re-litigate the fork** -- invoke fallback 2 (atom-quotient semantic FMP, `[PARTIAL]`,
      deliverable 4 only).

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**: none (scratch probe only)

**Verification**: a written go/no-go with the `lean_references` output and a line estimate, recorded
in the phase completion note and the handoff JSON.

**Blocked-branch**: a no-go here is **cheap and valuable** -- it saves Phases 9-13. Record the
finding, land Phases 0-7 green, and pivot to fallback 2 as a documented `[PARTIAL]`.

---

### Phase 9: Spec split + the one-token weakening [NOT STARTED]

**Goal**: Split `RuleApplicationSpec` so the Hintikka machinery no longer sees the three fields S5
cannot discharge. **Drop THREE fields, not one.**

**Tasks**:
- [ ] Land:
      ```lean
      structure RuleApplicationSpecCore (apply : RuleApply Atom) : Prop where
        freshLocal, outputsSubsetUniverse, persistentFresh, branchingLength,
        localShapeInvariance, boxPosNotExpanding, diaNegNotExpanding,
        boxNegWitness', diaPosWitness'          -- witness world EXISTENTIAL, not `modalNextWorld b`

      structure RuleApplicationSpec (apply) extends RuleApplicationSpecCore apply : Prop where
        rankStep, outDegStep, knownWorldsStep   -- the three fields S5 cannot discharge

      theorem RuleApplicationSpec.toCore (spec : RuleApplicationSpec apply) : RuleApplicationSpecCore apply
      theorem modalApplyOneS5w_specCore : RuleApplicationSpecCore (modalApplyOneS5w (Atom := Atom))
      ```
- [ ] Justify dropping **three** fields, not one (report §2.3, all VERIFIED by reading): for any rule
      that adds an edge to an **existing** world, three fields fail --
      `rankStep` (`GenericDriver.lean:213`, the landed S5 counterexample);
      `knownWorldsStep` (`GenericDriver.lean:245`, a **strict dichotomy**: either `.snd = acc` or
      `.snd = acc.addEdge sf.label (modalNextWorld b)` -- the reuse arm satisfies **neither**);
      and `rankEdge` inside `ModalPotentialInv` (`FmpMeasure.lean:2326`) -- irreparably false, since
      the saturated `□◇p` branch has a **reflexive** edge `(1,1)`, forcing `rank 1 + 1 = rank 1`.
      All three are confined to the potential/measure path; `modalStepBranchGen_knownWorlds` has
      **zero** consumers in the Tableau directory.
- [ ] The structural fact that makes this work [VERIFIED]: the spec-field usage of the five
      Hintikka-forcing lemmas (`CompletenessLoop.lean:233-760`) is
      `3 boxNegWitness, 3 boxPosNotExpanding, 3 diaNegNotExpanding, 3 diaPosWitness, 8 freshLocal,
      1 localShapeInvariance, 1 outputsSubsetUniverse` -- **no `rankStep`, no `knownWorldsStep`, no
      `outDegStep`**. Also: `modalExpMeasure_step_lt_gen` (`FmpMeasure.lean:3231`) takes `apply` plus
      **three raw hypotheses** and a raw `hW : modalMaxWorld bh < modalWorldBound φ0`, mentioning
      **neither `RuleApplicationSpec` nor `rankStep`** [VERIFIED from the full signature]. **The
      measure layer never needed the rank.**
- [ ] Land `diaPosWitness'` for the witness rule. **COMPILED IN RESEARCH** sorry-free (axioms
      `[propext, Quot.sound]`), delegating the `none` arm to `modalApplyOne_diamondPos_witness`:
      ```lean
      cases h : witnessWorldS5 b .pos ψ with
      | some w' => exact ⟨w', [], by simp [modalApplyOneS5w, h], by simp [modalApplyOneS5w, h]⟩
      | none => obtain ⟨hsnd, rest, hfst⟩ := modalApplyOne_diamondPos_witness b acc ψ w
                exact ⟨modalNextWorld b, rest, by simp [...], by simp [...]⟩
      ```
- [ ] Land `boxNegWitness'` symmetrically (via `modalApplyOne_boxNeg_witness`).
- [ ] K/T/B adapters: they instantiate via `where` syntax (`GenericDriver.lean:335`,
      `TDriver.lean:847`, `BDriver.lean:821`), so `extends` keeps those blocks compiling; discharge
      the existential form with `w' := modalNextWorld b` via a 3-line adapter each. **K/T/B pay
      nothing.**

> **R6 -- WHY THE REUSE ARM MUST BE GUARD-LESS** [VERIFIED by reading `CompletenessLoop.lean:1049-1060`]:
> the conjunct-3/4 saturated-leaf discharge is an **`exfalso`** that derives a contradiction *from*
> `.notApplicable`:
> ```lean
> · exfalso
>   obtain ⟨-, rest, hlin⟩ := spec.diaPosWitness bR aR ψ' w
>   rw [hlin] at hna; simp at hna
> ```
> It consumes the **`.linear` shape**, not the witness world. A `hasEdge` guard makes
> `.notApplicable` **reachable** and **inverts this proof from a refutation into a proof obligation**.
> Guard-less keeps both `exfalso` proofs byte-identical.

**Timing**: 2.5 hours

**Depends on**: 2, 8

**Files to modify**: `Cslib/Logics/Modal/Tableau/GenericDriver.lean` (the structure split -- the one
authorized edit to this file), `Cslib/Logics/Modal/Tableau/S5Simplification.lean`
(`modalApplyOneS5w_specCore`), plus 3-line adapters in `TDriver.lean` / `BDriver.lean` if required.

**Verification**: full CI green; **K/T/B compile with their existing `where` blocks**; `lean_verify`
on `modalApplyOneS5w_specCore`.

---

### Phase 10: Rank-free loop invariant with the `Aux` parametrization [NOT STARTED]

**Goal**: Land the rank-free Hintikka loop invariant. **This is real work, not a rename.**

**Tasks**:
- [ ] Land:
      ```lean
      structure ModalLoopInvHintikka (apply) (φ0) (b e) (acc) : Prop where
        bClosure, eClosure, eNodup, accFresh, accKnown        -- from ModalPotentialInv, rank-free
        worldBound : modalMaxWorld b < modalWorldBound φ0     -- replaces potentialInv + phiBound
        hintikkaInv, eBoxOnlyNeg, eBoxNegWitness, eDiamondOnlyPos, eDiamondPosWitness
      ```
- [ ] **The honest hazard, and the fix.** A **bare** `worldBound` scalar is **NOT step-preserved**
      (`n < WB` says nothing about `n+1 < WB`), and K re-establishes `phiBound` only via an exact
      conservation identity (`CompletenessLoop.lean:812`). The fix is **not** a bare field -- it is
      to parametrize over an auxiliary step-preserved predicate:
      ```lean
      (Aux : List (SignedFormula (Proposition Atom) WorldIndex) → Accessibility → Prop)
      (auxStep : Aux is preserved by modalStepBranchGen apply)
      (auxBound : Aux b acc → modalMaxWorld b < modalWorldBound φ0)
      ```
      K instantiates `Aux := fun b _ => ∃ rank, ModalPotentialInv φ0 b e acc rank ∧ phiBound`;
      S5w instantiates `Aux := fun b _ => S5wTagInv φ₀ b ∧ S5wWorldInv φ₀ b` (Phases 6-7).
      **This is the correction that makes the factoring actually inductive.**
- [ ] Note for sizing (R3): `ModalLoopInvGen` really has **7** fields and is parametrized by
      `(rank : WorldIndex → Nat)` -- `potentialInv, phiBound, hintikkaInv, eBoxOnlyNeg,
      eBoxNegWitness, eDiamondOnlyPos, eDiamondPosWitness` [VERIFIED]. The flat field list
      (`bClosure`, `eClosure`, `accFresh`, `accKnown`, `outDegEq`) that several designs asserted lives
      **inside `ModalPotentialInv`**, not in `ModalLoopInvGen`. **Dropping `rank` is an ARITY CHANGE
      to the structure K/T/B share, not a field swap.** Budget accordingly.
- [ ] `hintikkaInv` is **cheap** for the witness rule: `modalHintikkaClauseGen` returns literal `True`
      at `| .box _` and `| .diamond _` (`Completeness.lean`, VERIFIED), so all mint shapes are trivial.

**Timing**: 2 hours

**Depends on**: 7, 9

**Files to modify**: `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean`

**Verification**: full CI green; the structure typechecks; both `Aux` instantiations elaborate.

---

### Phase 11: Step preservation [NOT STARTED]

**Goal**: Port `modalStepGen_preserves_invariant` to the rank-free invariant with `Aux` threaded.

**Tasks**:
- [ ] Land:
      ```lean
      lemma modalStepHintikka_preserves_inv (hs : RuleApplicationSpecCore apply) ... :
        (∀ p ∈ newBs.zip newExps, ModalLoopInvHintikka ... p.1 p.2 newAcc) ∧ measure-drop
      ```
- [ ] Port of `modalStepGen_preserves_invariant` (`CompletenessLoop.lean:761-845`) **minus the two
      `potential_step` lines**, with `Aux` threaded.
- [ ] Consume `modalExpMeasure_step_lt_gen` (`FmpMeasure.lean:3231`) directly for the measure drop:
      it needs only `apply` + three raw hypotheses + `hW : modalMaxWorld bh < modalWorldBound φ0`
      -- supplied by `auxBound` at S5w's instantiation via
      `modalMaxWorld_lt_worldBound_of_S5w` (Phase 7). **No rank.**

**Timing**: 2 hours

**Depends on**: 10

**Files to modify**: `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean`

**Verification**: full CI green; the port closes sorry-free at both `Aux` instantiations.

---

### Phase 12: The parametric Hintikka lift + the K/T/B REGRESSION GATE [NOT STARTED]

**Goal**: The big one. Re-derive the lift parametrically and **prove the factoring correct by
re-deriving K's own theorem from it, unchanged**. ~310 lines, a **double induction**.

**AUTHORIZED TO SPLIT ACROSS TWO DISPATCHES** (12a: the parametric lift; 12b: the K re-derivation +
regression gate). Do **not** compress this into one run if the first does not close -- plan v2's
Phase 8 failed exactly by being budgeted as one unit.

**Tasks**:
- [ ] (12a) Land:
      ```lean
      theorem modalExpandBranchesHintikka (hs : RuleApplicationSpecCore apply) (hAux …) … :
        modalExpandBranchesGen apply branches expandedSets accs fuel = .openBranch bR aR →
        modalHintikkaSetGen apply bR aR
      ```
      Port of `modalExpandBranchesGen_hintikka` (`CompletenessLoop.lean:876-1185`, ~310 lines, a
      double induction).
- [ ] (12b) **REGRESSION GATE -- non-negotiable**: re-derive
      ```lean
      theorem modalExpandBranchesGen_hintikka (…)   -- K-facing name/statement UNCHANGED
      ```
      from the parametric lift at `Aux := (∃ rank, …)`. `TDriver.lean:911` and `BDriver.lean:871`
      consume it **by name** with `∃ rank, ModalLoopInvGen …` in the hypothesis. Both files must
      compile **unmodified**.
- [ ] **KILL (R3)**: if the re-derivation does not go through, **STOP HERE**. The factoring is wrong.
      Do **not** proceed to Phase 14; do **not** attempt S5-specific patches. Phases 0-8, 13 remain
      green and landed. Record the exact failing goal.

**Timing**: 3 hours (may require two dispatches)

**Depends on**: 11

**Files to modify**: `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean`

**Verification**: full CI green; **`TDriver.lean` and `BDriver.lean` unmodified and compiling**;
`modalExpandBranchesGen_hintikka` retains its exact name and statement; `lean_verify` on both
theorems.

**Blocked-branch**: `[BLOCKED]` with the exact `lean_goal` open state at the failing induction step.
No `sorry`. Do not weaken the K-facing statement to make the gate pass -- that defeats its purpose.

---

### Phase 13: Soundness re-proof -- `modalTableauS5_sound` [NOT STARTED]

**Goal**: Re-prove S5 soundness against the witness rule. **Statement unchanged.** This is R1, the
top risk, and the largest un-costed item of the prior effort. **Forks after Phase 8's probe and runs
parallel to the 9→12 lift chain.**

**Tasks**:
- [ ] Land `theorem modalTableauS5_sound (φ) (h : modalTableauS5 φ = .closed) : s5Valid φ` --
      **STATEMENT UNCHANGED** from `FrameSoundness.lean:2379`.
- [ ] The new case is the reuse edge `w→w'` to an **existing** `w'` carrying `⟨s,φ,w'⟩`.
      Structurally **easier** than the landed mint case: the world-assignment `f` is **not extended**
      (no mint), so the only obligation is `m.r (f w) (f w')` for an existing `w'`.
- [ ] **The decisive reuse**: `accReachableInv_related_s5` (`FrameSoundness.lean:1381`) -- **landed** --
      states that two known worlds, both reachable from 0, are related in **any** model whose relation
      is an equivalence relation. That is exactly the obligation. Consume the Phase 8 probe's findings
      verbatim.
- [ ] **Known breakage**: restate `modalApplyOneS5_snd_eq` (`S5Simplification.lean:340-351`,
      *"accessibility output is unconditionally identical to K's"*) -- it becomes **false** under the
      witness rule. Use Phase 8's `lean_references` enumeration (R4) to fix each real consumer.
      `modalApplyOneS5_fresh_local` (`FrameSoundness.lean:~1326`) stays reusable -- the witness rule
      is **defeq** to `modalApplyOneS5` on all 12 non-mint arms.
- [ ] Reuse the landed `S5SoundInv`, `modalStepBranchS5_preserves_satIn`,
      `modalExpandBranchesS5_closed_unsatIn`, `modalS5BoxAll_soundIn`, `modalS5DiaNegAll_soundIn`,
      `accReachableInv` (+`_initial`), `modalStepBranchS5_preserves_accReachableInv`,
      `reachable_imp_related_s5` (all `FrameSoundness.lean`, landed CI-green by v2's Phase 7)
      wherever the witness rule is defeq to `modalApplyOneS5`.
- [ ] **KILL CONDITION**: if the re-proof exceeds **~400 lines**, stop and re-litigate the fork
      (fallback 2).

**Timing**: 3 hours

**Depends on**: 8 (and 1)

**Files to modify**: `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`,
`Cslib/Logics/Modal/Tableau/S5Simplification.lean` (restating `modalApplyOneS5_snd_eq`)

**Verification**: full CI green; `lean_verify` on `modalTableauS5_sound` (expect
`propext`/`Classical.choice`/`Quot.sound` only); **zero edits to any K/T/B/S4 declaration**.

**Blocked-branch**: `[BLOCKED]` with the exact open goal + the measured line count. Invoke fallback 2
(atom-quotient semantic FMP -> `Decidable (s5Valid φ)` only, documented `[PARTIAL]`). No `sorry`.

---

### Phase 14: Assembly, demolition, CI, regression test [NOT STARTED]

**Goal**: Re-base the shipped surface on the witness rule, deliver the capstone, and demolish the
dead code.

**Tasks**:
- [ ] Re-base the surface (**one line**):
      ```lean
      def modalTableauS5 (φ) : ModalTableauResult Atom := modalTableauGen modalApplyOneS5w φ
      ```
- [ ] Land `theorem modalTableauS5_complete (φ) (h : s5Valid φ) : modalTableauS5 φ = .closed`, from
      the Phase 12 lift + `hintikka_congr` (Phase 2) + `modalOpenBranchS5_countermodel` (landed) +
      Phase 5's `hTgt`.
- [ ] Land `instance instDecidableS5Valid (φ) : Decidable (s5Valid φ)`, mirroring `instDecidableTValid`
      (`FrameCompleteness.lean:1281`).
- [ ] **DEMOLITION** -- delete the ~2,000 dead lines per the Preserved-Assets Accounting table above:
      `modalWorldBoundS5`/`modalUniverseS5` + lemmas (:60-204); `blockingWorldS5`,
      `successorBirthContentS5`, `modalApplyOneS5g` (:888-1051); `blockingWorldS5Keyed`,
      `modalStepBranchS5gKeyed` (:1424-1549); `S5LoopInv` + the ~11 `modalStepBranchS5g_preserves_*`
      (:1566-2723); `modalKnownWorlds_length_le_worldBoundS5`, `S5LoopInv.worldBound` (:2724-2830).
      **KEEP** `modalApplyOneS5_rankStep_not_dischargeable` (:2995) and the Phase 3 refutation sibling.
- [ ] Confirm the Phase 3 docstring corrections survived the demolition (:40-45, :1071-1073,
      `FrameCompleteness.lean:571-580`).
- [ ] Land a `#eval`-backed **regression test** in `CslibTests`: the exact S5 oracle from the research
      session (3,963-formula corpus, depth 2 over `{p,q,⊥}`). **The cheapest correctness net available
      and route-independent** (R5).
- [ ] BibKey docstrings: **Gore1999** (`references.bib:987`, **cite by TR pagination**) for the
      divergence prediction (TR p.48) and the linear model graph (TR pp.44-45, `|W| = 1 + m`);
      **Blackburn2001** (`references.bib:65`) §6.6 p.382 for the `m+1` selection-of-points bound and
      S5's NP-completeness. *(Note: Blackburn Ex. 6.6.4 is left as an exercise -- it attests the
      architecture, it is not formalizable as-is. Do not cite Ladner 1977: the local PDF is a
      919-byte HTML error page.)*
- [ ] Full CI: `lake build` / `test` / `checkInitImports` / `lint-style` / `shake`.

**Timing**: 2 hours

**Depends on**: 3, 5, 12, 13

**Files to modify**: `Cslib/Logics/Modal/Tableau/S5Simplification.lean`,
`Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`, `CslibTests/`

**Verification**: full CI green; `lean_verify` on `modalTableauS5_complete` and
`instDecidableS5Valid`; `instDecidableS5Valid` typechecks **and evaluates**; no
`RuleApplicationSpec modalApplyOneS5` witness reintroduced; no rank axiom; `S5Simplification.lean`
down to ~1,000 lines.

---

## Artifacts & Outputs

Expected sorry-free, axiom-free Lean outputs (per phase):

- **P0**: scratch probe result (no file output); go/no-go recorded in the phase note.
- **P1**: `witnessWorldS5`, `modalApplyOneS5w`, `witnessWorldS5_mem`, `modalApplyOneS5w_boxPos_eq`,
  `modalApplyOneS5w_diaNeg_eq`, `modalApplyOneS5w_eq_of_not_mint_shape` (`S5Simplification.lean`).
- **P2**: `hintikka_congr` (`S5Simplification.lean`).
- **P3**: the R7-refutation sibling theorem (`S5Simplification.lean`); corrected docstrings at
  `S5Simplification.lean:40-45`, `:1071-1073`, and `FrameCompleteness.lean:571-580`.
- **P4**: `modalOps`, `modalOps_le_complexity`, `modalOps_lt_worldBound`, `mintTags`,
  `mintTags_card_le_modalOps` (`S5Simplification.lean`).
- **P5**: `modalExpandBranchesGen_openBranch_accTargetsKnown` + the generalized double induction
  (`BDriver.lean`).
- **P6**: `S5wTagInv`, `usedTags`, `usedTags_mono`, `modalApplyOneS5w_outputs_tags`
  (`S5Simplification.lean`).
- **P7**: `S5wWorldInv`, `modalStepBranchS5w_preserves_worldInv`, `modalMaxWorld_lt_worldBound_of_S5w`
  (`S5Simplification.lean`).
- **P8**: R1 go/no-go + `lean_references` enumeration of `modalApplyOneS5_snd_eq` (no file output).
- **P9**: `RuleApplicationSpecCore`, split `RuleApplicationSpec`, `RuleApplicationSpec.toCore`
  (`GenericDriver.lean`); `modalApplyOneS5w_specCore` incl. `diaPosWitness'`/`boxNegWitness'`
  (`S5Simplification.lean`); K/T/B adapters.
- **P10**: `ModalLoopInvHintikka` + the `Aux`/`auxStep`/`auxBound` parametrization
  (`CompletenessLoop.lean`).
- **P11**: `modalStepHintikka_preserves_inv` (`CompletenessLoop.lean`).
- **P12**: `modalExpandBranchesHintikka`; `modalExpandBranchesGen_hintikka` re-derived with its
  **exact existing name and statement** (`CompletenessLoop.lean`).
- **P13**: `modalTableauS5_sound` (statement unchanged) + restated `modalApplyOneS5_snd_eq`
  (`FrameSoundness.lean`, `S5Simplification.lean`).
- **P14**: re-based `modalTableauS5`, `modalTableauS5_complete`, `instDecidableS5Valid`
  (`FrameCompleteness.lean`); ~2,000 deleted lines (`S5Simplification.lean`); `#eval` regression test
  (`CslibTests/`).
- Implementation summary at `specs/515_*/summaries/04_*-summary.md` on completion, with an honest
  per-phase status ledger (including any `[BLOCKED]`-with-open-goal entries) **and an explicit note
  that the 5/KB5 deliverable was dropped as mathematically impossible**.

## Rollback/Contingency

- **Per-phase revert**: each phase commits narrowly and independently; a failing phase is reverted
  with `git revert` of that phase's single commit without disturbing earlier green phases. Never
  `git reset --hard` without a `git-snapshot.sh` snapshot and explicit user request.
- **Zero-debt contract**: no phase lands a `sorry`, a re-added rank axiom, a
  `RuleApplicationSpec modalApplyOneS5` witness, or a weakened K-facing
  `modalExpandBranchesGen_hintikka` statement. If a sub-piece cannot close sorry-free, its phase is
  marked `[BLOCKED]` with the exact `lean_goal` open state, earlier green phases are preserved, and
  downstream phases are transitively `[BLOCKED]`.
- **Three cheap gates, in order**: Phase 0 (30-min kill test, gates everything); Phase 8 (R1 scratch
  probe, gates 9-13); Phase 12b (K/T/B regression gate -- if the re-derivation fails, **stop**, the
  factoring is wrong). Each fails **before** the expensive work it guards.
- **Demolition is LAST (Phase 14)**: the ~2,000 dead lines are deleted only after the replacement
  chain is green. If the plan lands `[PARTIAL]`, the dead code stays -- harmless, and the deletion is
  a clean follow-up. **Never delete ahead of the replacement.**
- **Fallback 1 (R2 fails)**: keep the rule; obtain the world bound another way. A phase, not a
  redesign.
- **Fallback 2 (R1 fails), pre-authorized**: atom-quotient semantic FMP -- `Decidable (s5Valid φ)` via
  enumerating quotient models over `Fin k → Bool`; compiled sorry-free and axiom-clean in the research
  session. Delivers **deliverable (4) only** -- not `modalTableauS5_complete`, and **not** 5/KB5 (its
  `qTransfer` needs reflexivity, which `fiveFC`/`kb5FC` lack). A documented `[PARTIAL]`, never the
  primary route.
- **Fallback 3 (R3 fails)**: stop at Phase 12. Phases 0-8 and 13 remain landed, green, and
  independently valuable (the rule, the congruence bridge, the refutation, the linear budget,
  `accTargetsKnown`, and possibly soundness).
- **Escalation**: if the lift and both fallbacks resist within budget, land the task `[PARTIAL]` with
  the rule + congruence + refutation + budget + soundness green and the lift `[BLOCKED]`-with-open-goal.
- **Task description amendment (USER ACTION)**: the 5/KB5 "Phase 7 completion" deliverable must be
  struck from the task description. It is mathematically impossible via the S5 tableau. This plan
  cannot deliver it and no successor plan can either.

## Rejected Alternatives (standing do-not-re-attempt record)

Recorded here, not only in the report, so a future dispatch does not re-attempt a dead end -- exactly
as the rank measure was. Full argument at `reports/03_s5-infrastructure-deep-research.md` §8.

1. **Fuel domination (R7)** -- *false statement*. `maxWorld = fuel/2`, unbounded [VERIFIED]. Landed as
   a theorem in Phase 3.
2. **Firing-order / stratification / "create all worlds then fire boxes" / fairness** -- *provably
   impossible*. Divergence is a property of the rule set's **closure**, not its **schedule**. A fair
   schedule forces `T(◇p)@w_max` onto the branch -> the minting arm answers with a new world ->
   divergence. An unfair schedule loses Hintikka conjunct 2. **The strata do not stratify**: firing
   boxes *creates* world-creating formulas. (Also pre-emptively kills the Massacci π-before-ν
   ordering route.)
3. **Static pre-allocation / any φ₀-parametrized rule** -- *type-level impossibility*.
   `hOutputsSubsetUniverse` binds `φ0` universally **inside** the hypothesis
   (`FmpMeasure.lean:3241`) [VERIFIED].
4. **Keyed driver over `modalStepBranchS5gKeyed`** -- *rejected on cost, not correctness*.
   `modalExpMeasure_step_lt_gen` is stated for `modalStepBranchGen` [VERIFIED], so a keyed driver can
   consume neither the measure engine nor `modalExpandBranchesGen_hintikka`. Also quadratic
   (⌊n²/4⌋+1 on `□◇` chains).
5. **The unkeyed guard `modalApplyOneS5g` / `blockingWorldS5`** -- *structurally dead*. `= none` at
   **every** mint. S5's universal box injects formulas post-birth; the S4 birth-content abstraction
   assumes a world inherits at birth everything it will ever have. **S5 violates that premise.**
6. **Keeping `modalUniverseS5`/`modalWorldBoundS5`** -- *breaks the fuel*. `entryWorkS5 > fuelExp` at
   `atom`/`□p`/`p∧q` [VERIFIED]; the escape hatch `modalWorldBoundS5 ≤ modalWorldBound` is **false**
   [VERIFIED].
7. **`.linear []` on the reuse arm** -- breaks `freshLocal`'s right disjunct (needs a cons). The
   landed `modalApplyOneS5g` makes exactly this mistake (:987).
8. **A `hasEdge` guard on the reuse arm** -- inverts the `exfalso` conjunct-3/4 discharge
   (`CompletenessLoop.lean:1049-1060`) from a refutation into a proof obligation.
9. **Filtration / semantic FMP as the route to Phase 8** -- *category error*. Filtration is purely
   **semantic**; it cannot produce `modalHintikkaSetGen`. The naive form is **false for S5**:
   filtration preserves reflexivity but **not** transitivity or symmetry (Blackburn2001 pp.79-81).
10. **Doczkal-Smolka-style pruning** -- *no fixpoint*. S5's universal relation makes the box condition
    **global** on the state set, so shrinking `T` makes boxes easier and diamonds harder
    simultaneously -- neither monotone nor antitone.
11. **Tightening `modalFuel`** -- *scope creep*. Sufficiency, not tightness, is the requirement.
