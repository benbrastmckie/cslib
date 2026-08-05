# Implementation Plan: Reformulated S4 Redirect-Sound Invariant for the Keyed Ordered Driver (v7)

- **Task**: 553 - s4_loop_guard_soundness_reachability_restriction
- **Status**: [IMPLEMENTING]
- **Effort**: 39.5 hours total — 18 hours already landed (Phases 1 through 7.2), 21.5 hours
  remaining (Phases 7.3 through 10)
- **Dependencies**: 535 (keyed completeness inputs, landed), 557/561-563 (refactor programme,
  landed), 587 (canonical-witness restriction probe, completed)
- **Research Inputs**:
  - `specs/553_.../reports/06_mint-blocked-redirect-verdict.md` (**primary, new**: the NO-GO on the
    literal per-step statement, the `S4RedirectSoundInv` reformulation in §3, the arm-by-arm
    cross-check in §3.4, the literature grounding in §4, the zero-termination-impact finding in §5,
    and the P1/P2/P3 preconditions in §6)
  - `specs/553_.../summaries/07_p1-p2-mint-blocked-probe-verdict.md` (**primary, new**: the
    PROCEED verdict, P1 proven not merely probed, P2 kill criterion not triggered, and the
    explicit punch list of four remaining items)
  - `specs/587_canonical_witness_restriction_probe/reports/01_canonical-witness-restriction-probe.md`
    (superseded as a route input by the Phase 1 Verdict below; retained for provenance)
  - `specs/553_.../reports/05_gate-a-canonical-witness-blocker-analysis.md` (blocker record)
  - Prior reports 01-04 under `specs/553_.../reports/` (falsified routes; not re-argued)
- **Artifacts**: `plans/08_reformulated-s4-redirect-sound-inv.md` (this file)
- **Standards**:
  - `.claude/context/formats/plan-format.md`
  - `.claude/rules/artifact-formats.md`
  - `.claude/rules/state-management.md`
  - `.claude/rules/plan-compliance.md`
  - `.claude/rules/cslib.md`
  - `.claude/rules/lean4.md`
  - `.claude/rules/no-task-references-in-deliverables.md`
- **Type**: cslib
- **Lean Intent**: true
- **Plan version**: 7 (supersedes `plans/07_canonical-witness-truth-lemma.md`, v6)

---

## Overview

**This is the seventh plan version.** It supersedes v6 (`plans/07_canonical-witness-truth-lemma.md`),
which remains on disk as the authoritative record of Phases 1-6's original task lists and of the
first four Phase 7 dispatches. v6's Phases 1-6 are `[COMPLETED]` and are carried forward here
unchanged in status and substance; v6's Phase 7 was `[IN PROGRESS]` with four of five case-split
arms landed and the fifth (mint-blocked redirect) declared an open architectural question.

That open question has now been answered. The targeted research dispatch
(`reports/06_mint-blocked-redirect-verdict.md`) returned **NO-GO on the step lemma as stated,
CONDITIONAL GO on a reformulated conserved predicate** (`S4RedirectSoundInv`, report §3), and the
follow-on P1/P2 probe (`summaries/07_p1-p2-mint-blocked-probe-verdict.md`) returned **PROCEED**:
P1 was not merely probed but fully proven for the box-negative-blocked shape, and P2 — the named
kill criterion — does not trigger anywhere in the rule set. This plan folds that verdict in.

**The core reformulation, in one sentence**: the soundness induction stops requiring the model to
realize redirect edges, and instead carries the syntactic fact that a redirect edge never transmits
anything the branch does not already contain — restoring on the proof side the soundness/completeness
separation that Massacci-style blocking has natively (report §4), while leaving the driver, the
guard, the `keys` bookkeeping, and every termination lemma **definitionally untouched** (report §5).

**Definition of done**: a sorry-free step-preservation theorem for
`modalStepBranchS4KeyedOrdered` over `S4RedirectSoundInv`, its terminal closed-branch payoff, and
the fuel-induction wrapper, with the sorry census in `Cslib/Logics/Modal/Tableau/` still exactly 1
at every phase boundary and scoped CI green at every commit.

**Scope constraint** (unchanged from v6): file scope is
`Cslib/Logics/Modal/Tableau/{FrameSoundness,FrameCompleteness,LoopChecking}.lean` plus
`CslibTests/S4LoopGuardRegression.lean` plus this task's `specs/` directory. `Rules.lean`,
`Saturation.lean`, `Branch.lean`, `SoundnessStep.lean`, `FrameRules.lean`, `TDriver.lean` and
everything under `Cslib/Logics/Modal/Metalogic/**` are **read-only in every phase**.

**This plan does no refactoring and changes no definition on the driver/termination track.**

### Research Integration

| New finding | Source | How this plan uses it |
|---|---|---|
| The literal per-step statement (model realizes the redirect edge) is not closable from any invariant initializable at an arbitrary countermodel; both known route families are exhausted for structural reasons | report 06 §2 | Phase 7.1 is closed `[COMPLETED WITH EXCLUSIONS]` with the mint-blocked arm recorded as a reasoned exclusion. **No phase re-attempts it.** See Non-Goals. |
| `S4RedirectSoundInv` (four conjuncts (a)-(d)) is the reformulated conserved predicate | report 06 §3.2 | Landed verbatim (transcribed to file vocabulary) in `FrameCompleteness.lean:5141`. Phase 7.2 records it; every later phase consumes it. |
| Under the new predicate the mint-blocked arm closes with **no model construction at all** | report 06 §3.3 | Proven for the box-negative shape (`S4RedirectSoundInv_boxNeg_blocked`, `FrameCompleteness.lean:5178`). Phase 7.3 writes the diamond-positive mirror. |
| The four landed arms need **re-wrapping, not re-proving** | report 06 §3.4; summary 07 item 2-3 | Phases 7.5-7.7. Each phase names the landed lemma it re-wraps and forbids re-deriving its semantic core. |
| Conjunct (d) is the honest crux; it imports the ordered driver's scheduling discipline into the invariant | report 06 §3.5 | Phase 7.4 (the antitone family) exists solely to make (d) preservable at non-mint steps. |
| P2 (antitone applicability) passes: every rule layer filters its own output against `b`; nothing re-fires on data it produced | summary 07 "P2 — PASS" table | Phase 7.4 formalizes it. **The probe verified the premise by reading `Rules.lean`/`FrameRules.lean`/`Branch.lean`; it did not write the lemma family.** Phase 7.4 is that work, not a restatement of a landed fact. |
| P3 ("mint seed covers the 4-payload") was **not attempted** | summary 07 "P3 — not attempted" | Phase 7.6 owns it. It is not assumed discharged. |
| Only the **box-negative-blocked** shape was proven; the diamond-positive dual was not written | summary 07 "Scope note (honest, not elided)" | Phase 7.3, explicitly. |
| Termination impact of the reformulation is **zero**; guard-narrowing alternatives are confirmed dangerous | report 06 §5 | Recorded in Non-Goals and Risks. No phase touches `blockingWorldS4Keyed` or any termination lemma. |
| If (d) proves unpreservable, the fallback is driver-level provenance (`Reds`/`accWithReds`), not a guard change | report 06 §7 | Rollback/Contingency. Not the plan of record. |

### What changed relative to v6, precisely

- **v6's Phase 7 is replaced** by decimal sub-phases 7.1-7.8 plus new Phases 8-10. v6's Phase 7 was
  a single unbounded phase that ran four dispatches without closing; its own Scope Hypothesis
  instructed a split if the real work exceeded one phase. This is that split.
- **v6's Phase 7 target changes**: the conserved predicate is `S4RedirectSoundInv`, not
  `branchSatisfiableIn s4FC`. The five case-split arms survive as *statements to re-wrap*.
- **v6's Phases 1-6 are unchanged**, in status and in what they landed. In particular
  `branchSatisfiableIn_s4FC_addEdge_of_blocked` (v6's Phase 6 capstone) stays landed and stays
  consumed by the **completeness** track; report 06 §3.1 is explicit that it is a terminal,
  fully-saturated-branch construction and is correct where it lives.
- **The `#### Phase 7 Progress Record` chain in v6 is not duplicated here.** v6's four progress
  records (first through fourth dispatch) remain the authoritative narrative for that work; this
  plan's Phase 7.1 summarizes their outcome and points at them.

### Architectural constraint carried forward (still binding)

From v6's Overview, re-verified this planning run and unchanged: `FrameSoundness.lean` does not
import `LoopChecking.lean`; `FrameCompleteness.lean` imports both `LoopChecking.lean` and
`FrameSoundness.lean`. `FrameCompleteness.lean` is therefore the **only in-scope file that sees
every ingredient**, and all new soundness content for the keyed ordered driver lands there.
Additionally (fourth-dispatch discovery, re-verified): `LoopChecking.lean` does **not** import
`TDriver.lean`, so any lemma needing `modalApplyOneT_*` facts cannot live there.

A phase that finds itself wanting to add a `LoopChecking` import to `FrameSoundness.lean`, or a
`TDriver` import to `LoopChecking.lean`, has taken a wrong turn and must stop and record it.

### Roadmap Alignment

`specs/ROADMAP.md` was consulted read-only. This plan advances the same two entries v6 named:
"S4 keyed loop-check guard soundness" (`ROADMAP.md:156`, naming
`branchSatisfiableIn_s4FC_ancestor_redirect`) and "S4 (reflexive-transitive) loop-checking
termination bound + decidability" (`ROADMAP.md:153`). This plan does **not** remove the standing
sorry (see Non-Goals) and does not write to `ROADMAP.md`.

---

## Goals & Non-Goals

**Goals**:

- Complete the mint-blocked arm under `S4RedirectSoundInv` by writing the diamond-positive mirror
  of the proven box-negative theorem (Phase 7.3).
- Formalize the antitone-applicability lemma family that conjunct (d) needs at non-mint steps
  (Phase 7.4).
- Re-wrap the four landed case-split arms against `S4RedirectSoundInv`, reusing their semantic
  cores verbatim (Phases 7.5-7.7).
- Assemble the five arms into a single step-preservation theorem over
  `modalStepBranchS4KeyedOrdered`, threading the ghost edge list `Er` (Phase 7.8).
- Establish the terminal payoff — a closed branch contradicts the weakened predicate (Phase 8).
- Land the fuel-induction wrapper and initialization, and decide the end-to-end capstone scope
  question v6 left open (Phase 9).
- Extend the regression corpus and close out with the full CSLib CI gate (Phase 10).

**Non-Goals**:

- **Removing or altering the standing `sorry` at
  `Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1251` (`branchSatisfiableIn_s4FC_ancestor_redirect`).**
  Retained by explicit user decision. The sorry census over `Cslib/Logics/Modal/Tableau/` is
  **exactly 1** at every phase boundary — verified as of this planning run.
- **Re-attempting `branchSatisfiableIn_s4FC_addEdge_of_blocked` as a per-step lemma.** Report 06
  §2.2 and §8 close this: it needs `modalHintikkaSetS4` conjuncts 3/4, which are *false* at typical
  mint-ready states, and the rebuild is false-as-a-uniform-construction, not merely out of reach.
- **Ambient-model surgery** (closure-extension, generated sub-relation) at step time. Report 06
  §2.2-2.3, grounded in ChagrovZakharyaschev1997 Theorem 5.51's containment pattern.
- **Any invariant of the form "the model satisfies X at `f wBlock`" as a substitute for the edge.**
  Valuations cannot force relations (report 06 §2.1).
- **Forward-cone extension of the free transfers.** Refuted by Decision Gate B; §3's absorption is
  strictly one-hop and needs nothing more.
- **Touching `blockingWorldS4Keyed`, `modalApplyOneS4Keyed`, `modalStepBranchS4KeyedOrdered`,
  `keys`, `acc`, fuel, or any termination lemma definitionally.** Report 06 §5: the reformulation
  is entirely in which proposition the soundness induction conserves. Narrowing the guard
  (ancestor-only, live-set) destroys `keysDistinct` and the world bound; it is not on the table.
- **Re-deriving `accPinnedBy`, `branchSatisfiablePinnedIn`, or
  `branchSatisfiablePinnedIn_redirect_mechanical`.** Preserved verbatim in `FrameSoundness.lean`.
- **Re-running or re-proposing the FrameCompleteness / modal tableau refactor programme.** Landed.
- **Building a parallel `...Boxed` invariant or driver family.** Stale framing from v5.
- **Any task-number citation inside a `.lean` file** (`.claude/rules/no-task-references-in-deliverables.md`).
  Cite declaration names and source labels (`report §3.2`-style references are fine).

---

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Conjunct (d) is not preservable at a **primary-scan** (non-mint) step, where `hmint` is unavailable — the P1 theorem discharged (d) using settledness, which only holds at mint steps | Terminal for the reformulation as stated; falls back to report §7 | M | Phase 7.4 is exactly this, isolated ahead of every arm restatement, and Phase 7.5's Kill Criteria terminate the route rather than weakening (d) silently. P2's reading-level PASS (summary 07) is strong evidence but is **not** a Lean proof. |
| The antitone family is larger than the ~10 mechanical lemmas report §6 priced | Adds a phase's worth of work | M | Phase 7.4 carries a Scope Hypothesis with an explicit confirm-or-stop instruction and a split trigger at 15 lemmas. |
| Re-wrapping an arm turns out to need its semantic core re-proved (not merely re-hypothesised) | Adds real proof mass to 7.5-7.7 | M | Each restatement phase names the landed lemma and its exact hypothesis to weaken. If a core must be re-proved, the phase records it as a finding and stops rather than absorbing it. |
| P3 ("mint seed covers the 4-payload") fails — some `modalFourBoxProp` output at the fresh mint world is not in the mint payload | Mint-unblocked arms need genuine new content | L-M | Phase 7.6 owns P3 as its **first** task, before any restatement work, so a failure is cheap. Report §6 rates it "expected free"; summary 07 confirms it was never tested. |
| The dispatcher theorem cannot be assembled because the five arms have incompatible shapes (some `RuleResultSat`-flavored, some `branchSatisfiableIn`-flavored) | Phase 7.8 stalls | M | Phases 7.5-7.7 are required to land every arm in **one uniform shape** stated in Phase 7.8's target, written out before those phases dispatch. |
| Phase 9's fuel-induction wrapper turns out to require an end-to-end `modalTableauS4KeyedOrdered_sound` capstone comparable in size to the S5 Bespoke Fuel-Induction Assembly (`FrameSoundness.lean:2453-3320`) | 4h estimate is low by a factor | M | v6 flagged this and never decided it. Phase 9 decides it explicitly in its first task and splits into 9.1/9.2 if the capstone is in scope, rather than running unbounded. |
| Line anchors quoted from v6, the report, or the summary have drifted | Wasted dispatch time | M | Every phase re-locates declarations by `grep -n '^def\|^lemma\|^theorem\|^structure\|^abbrev'`. Line numbers in this plan are as-of this planning run and are convenience anchors only, never authority. |
| An implementer treats P2's reading-level PASS as a landed Lean fact | Silent false progress; (d) unproven at non-mint steps | M | Stated explicitly in Research Integration, in Phase 7.4's Goal, and in Phase 7.2's honest-gaps list. |
| Base rate: six routes failed at this obligation before the reformulation | -- | -- | Unlike all six, this route has **no open mathematical question at its center** (summary 07's closing sentence): every remaining piece is "re-wrap a landed lemma under the new predicate", plus one mechanical lemma family. That is a genuine change in kind, but it is a claim to be tested by Phases 7.4-7.5, not assumed. |

---

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |
| 5 | 6 | 5 |
| 6 | 7.1 | 6 |
| 7 | 7.2 | 7.1 |
| 8 | 7.3, 7.4, 8 | 7.2 |
| 9 | 7.5, 7.6, 7.7 | 7.4 |
| 10 | 7.8 | 7.3, 7.5, 7.6, 7.7 |
| 11 | 9 | 7.8, 8 |
| 12 | 10 | 9 |

Phases within the same wave can execute in parallel. Waves 1-7 are already complete. **Wave 8
(Phases 7.3, 7.4, 8) is now complete** — all three closed sorry-free and committed; Phase 7.4's
kill gate returned outcome (i), a clean PASS. **The live frontier is now wave 9** (Phases 7.5,
7.6, 7.7), which may now dispatch since Phase 7.4 has returned a passing outcome. Wave 10 (Phase
7.8) remains blocked on wave 9 completing in full.

---

### Phase 1: GATE 0 — canonical-witness truth-lemma micro-probe [COMPLETED]

- **Goal:** Decide, before any construction, whether the truth lemma's box-positive
  semantic-to-syntactic direction is obtainable at the canonical model, and at what price.
- **Depends on:** none
- **Timing:** 2.5 hours (one dispatch) — spent
- **Verification Tier:** local
- **Completed:** 2026-08-05

#### Phase 1 Verdict (carried forward from v6, unchanged)

**Outcome (i): Gate 0 PASSED on the cheap branch.** Sub-probe 0.A (`reflTransGen_addEdge_iff`,
`FrameCompleteness.lean`) closed sorry-free on the first attempt. `lean_verify` on all three
landed declarations (`reflTransGen_addEdge_iff`, `hasEdge_addEdge_mono_gate0`,
`hasEdge_addEdge_self_gate0`) reported axioms exactly `{propext, Classical.choice, Quot.sound}`.

The identity showed `extractModelS4 b (acc.addEdge src wBlock)` is definitionally the
redirect-extended canonical model, collapsing the entire agreement-lemma workstream and re-scoping
v6's Phases 3-6 onto `modalHintikkaSetS4` preservation under `addEdge`. Sub-probe 0.B was not
attempted, per outcome (i)'s own unconditional text.

**Consumed downstream by the reformulation**: `hasEdge_addEdge_self_gate0` and
`hasEdge_addEdge_mono_gate0` are the exact lemmas conjunct (a) of `S4RedirectSoundInv` is
discharged with (summary 07, "What closed each conjunct" (a)). Gate 0's material is not stranded
by the reformulation.

The full original task list, outcome table, and re-scope record are in
`plans/07_canonical-witness-truth-lemma.md` `### Phase 1` and its `#### Phase 1 Verdict`.

---

### Phase 2: GATE B — `modalS4Saturated` at a settled ordered-stepper state [COMPLETED]

- **Goal:** Determine whether `modalS4Saturated φ₀ b acc` is available at a settled
  ordered-stepper state where `modalNonMintCandidates φ₀ keys b e acc = []`.
- **Depends on:** 1
- **Timing:** 3 hours (one dispatch) — spent
- **Verification Tier:** local
- **Completed:** 2026-08-05

#### Phase 2 Verdict (carried forward from v6, unchanged)

**Outcome (i): Gate B PASSED at its cheapest.** `modalS4Saturated_of_ordered_settled`
(`LoopChecking.lean:9250`) closed sorry-free from `hsettled` + `hHI` alone, with no additional
invariant field. The apparent `sf ∈ e` gap does not arise because `S4KeyedHintikkaInv.eBoxOnlyNeg`
/ `eDiamondOnlyPos` force any box/diamond-shaped member of `e` to be one of the two minting
shapes. Both `_wrapped` bridges (`hintikkaS4_box_pos_reflTransGen_wrapped`,
`hintikkaS4_dia_neg_reflTransGen_wrapped`) also landed sorry-free.

**Consumed downstream by the reformulation**: `modalS4Saturated_of_ordered_settled` is what
supplies `hSat` to `S4RedirectSoundInv_boxNeg_blocked` at the real driver call site (the landed
theorem's own docstring says so), and is a hypothesis Phase 7.8's dispatcher must discharge from
mint-readiness. Gate B's material is load-bearing under the reformulation, not stranded.

Full task list and outcome table: `plans/07_canonical-witness-truth-lemma.md` `### Phase 2`.

---

### Phase 3: `modalHintikkaSetS4` preservation under `addEdge` — mechanical conjuncts [COMPLETED]

- **Goal:** (Re-scoped by the Phase 1 Verdict.) State and discharge the three mechanically
  transferring conjuncts of `modalHintikkaSetS4` under `acc.addEdge src wBlock`.
- **Depends on:** 1
- **Timing:** 2 hours — spent
- **Verification Tier:** local
- **Completed:** 2026-08-05

**Landed, sorry-free**: `modalHintikkaSetS4_addEdge_of_saturated` (`FrameCompleteness.lean`),
discharging 3 of `modalHintikkaSetS4`'s 4 conjuncts from `hSatExt` as a hypothesis. The original
(pre-re-scope) canonical-witness task list and the interim Progress Record are in
`plans/07_canonical-witness-truth-lemma.md` `### Phase 3`; they are superseded and must not be
re-executed.

---

### Phase 4: Saturation transfer under `addEdge`, box-positive layer [COMPLETED]

- **Goal:** (Re-scoped by the Phase 1 Verdict.) Discharge the bare-saturation conjunct at
  `acc.addEdge src wBlock` for the box-positive shape.
- **Depends on:** 2, 3
- **Timing:** 2.5 hours — spent
- **Verification Tier:** local
- **Completed:** 2026-08-05

Landed as part of the folded Phases 3-6 completion record in v6 — see Phase 6 below for the
consolidated declaration list. Key items owned by this phase:
`successorsOf_addEdge_of_ne`/`successorsOf_addEdge_self`, `modalApplyOneS4_boxPos_fst_eq`,
`modalApplyOne_fst_eq_of_not_boxPos_diaNeg`, `modalApplyOneS4_fst_congr_successorsOf`
(all `LoopChecking.lean`).

---

### Phase 5: Saturation transfer under `addEdge`, diamond-negative layer and assembly [COMPLETED]

- **Goal:** (Re-scoped by the Phase 1 Verdict.) The diamond-negative dual, plus assembly into an
  unconditional saturation-transfer lemma.
- **Depends on:** 4
- **Timing:** 2.5 hours — spent
- **Verification Tier:** local
- **Completed:** 2026-08-05

Landed: `modalApplyOneS4_diaNeg_fst_eq`, `mem_signedSubfmls_of_formula_s4loop`, and the hard
content `modalS4Saturated_addEdge_of_blocked` (`LoopChecking.lean`) — unconditional, no remaining
hypothesis. **This lemma is load-bearing under the reformulation**: it is what gives conjunct (d)
of `S4RedirectSoundInv` saturation at the *extended* accessibility for free (summary 07, "What
closed each conjunct" (d)).

---

### Phase 6: Redirect-preservation capstone and probe-lemma supersession [COMPLETED]

- **Goal:** (Re-scoped by the Phase 1 Verdict.) Discharge the redirect-preservation obligation at
  the canonical witness, and remove the superseded canonical-witness probe lemma.
- **Depends on:** 5
- **Timing:** 2.5 hours — spent
- **Verification Tier:** interface
- **Completed:** 2026-08-05

**Landed, sorry-free**:

1. `modalHintikkaSetS4_addEdge_of_blocked` (`FrameCompleteness.lean`) — `modalHintikkaSetS4`
   preservation under the keyed redirect, unconditionally.
2. `branchSatisfiableIn_s4FC_addEdge_of_blocked` (`FrameCompleteness.lean:4358` as of this
   planning run) — the capstone, via `modalTruthLemmaS4` at the extended accessibility with
   `extractModelS4 b (acc.addEdge src wBlock)` as witness.
3. `canonicalWitnessRestrictionProbe_agreementConditional` removed from `FrameSoundness.lean`
   (zero code dependents; one docstring cross-reference repointed).

**Disposition under the reformulation (new, decided here)**: item 2 is **kept, and stays where it
is**. Report 06 §3.1 and §2.2 establish that it is a correct *terminal, fully-saturated-branch*
construction consumed by the **completeness** track — it is not wrong, it is simply not a per-step
lemma. No phase in this plan removes it, weakens it, or re-attempts it as a step lemma.

Full declaration list and verification record: `plans/07_canonical-witness-truth-lemma.md`
`#### Phase 3-6 Completion Record`.

---

### Phase 7.1: Five-arm case lemmas against the pre-reformulation statement [COMPLETED WITH EXCLUSIONS]

- **Goal:** Close each arm of the keyed ordered driver's per-step case split against the
  *unweakened* `branchSatisfiableIn s4FC` / `RuleResultSat` statement.
- **Depends on:** 6
- **Timing:** four dispatches — spent
- **Verification Tier:** local
- **Completed:** 2026-08-05

**Landed, sorry-free** (all `FrameCompleteness.lean`, line anchors as of this planning run):

| Arm | Declaration | Line |
|---|---|---|
| Propositional / non-modal | `modalApplyOneS4Keyed_notBoxDia_sat` | 4495 |
| Mint, unblocked (box-negative) | `modalApplyOneS4Keyed_boxNeg_mint_sat` | 4521 |
| Mint, unblocked (diamond-positive) | `modalApplyOneS4Keyed_diaPos_mint_sat` | 4633 |
| 4-rule, box-positive (`T(□ψ)@w`) | `modalApplyOneS4Keyed_boxPos_sat` | 4897 |
| 4-rule, diamond-negative (`F(◇ψ)@w`) | `modalApplyOneS4Keyed_diaNeg_sat` | 4914 |

Supporting: `boxPlusExtraS4_sat`, `modalApplyOneS4Rules_boxPos_soundIn`/`_diaNeg_soundIn`,
`modalApplyOneT_boxPos_eq`/`_diaNeg_eq` (`FrameCompleteness.lean`); six de-privatizations plus
`modalApplyOneS4Rules_boxPos_snd_eq_acc`/`_diaNeg_snd_eq_acc` (`LoopChecking.lean`); the Phase 7
layering-note module comment.

**Verified on disk this planning run**: all five arm declarations exist at the lines above; working
tree clean; sorry census over `Cslib/Logics/Modal/Tableau/` exactly 1 (`FrameSoundness.lean:1251`).

#### Reasoned Exclusions

| Item | Reason | Evidence |
|------|--------|----------|
| The mint-blocked (redirect) arm, as a preservation lemma for the unweakened `branchSatisfiableIn s4FC` statement | Not closable from any invariant initializable at an arbitrary countermodel. The rebuild-canonical route needs `modalHintikkaSetS4` conjuncts 3/4, which are *false* at typical mint-ready states (settledness gives only non-minting exhaustion; sibling mint shapes may be unwitnessed). The extend-ambient route fails because `wBlock` is chosen by a purely syntactic key comparison with no semantic tie to an arbitrary model. Both are structural exhaustions, not lemma-chaining gaps. | `reports/06_mint-blocked-redirect-verdict.md` §1 (verified code state), §2 (the two-route impossibility argument), §2.3 (the ChagrovZakharyaschev1997 Thm 5.51 containment diagnosis), §8 (do-not-re-attempt list); `handoffs/plan07-phase7-handoff-20260805c.md` and `...d.md` (the two burned implementation dispatches); `plans/07_canonical-witness-truth-lemma.md` "Correction to the previously-catalogued mint-blocked route" |
| The single dispatcher theorem over `modalStepBranchS4KeyedOrdered`, at this statement | Cannot typecheck as a total function over all cases while one arm is unprovable. Superseded rather than abandoned: Phase 7.8 assembles it under `S4RedirectSoundInv`. | `handoffs/plan07-phase7-handoff-20260805d.md` "Updated case-split table" and "What remains" |
| The regression-corpus row and the full CI gate, at this statement | Both were blocked on the dispatcher theorem this phase could not assemble. Carried forward to Phase 10, not dropped. | Same handoff, "What remains" |

**Nothing landed in this phase is discarded.** Report 06 §3.4 is explicit that the four landed arms
need *re-wrapping, not re-proving*; Phases 7.5-7.7 name each one and reuse its semantic core.

---

### Phase 7.2: P1/P2 probe — `S4RedirectSoundInv` and the mint-blocked box-negative arm [COMPLETED]

- **Goal:** Test report 06 §6's two cheap-to-check preconditions before committing to the
  reformulated route: P1 (the mint-blocked arm closes under the new predicate) and P2 (the kill
  criterion — is any rule not output-filtered against `b`).
- **Depends on:** 7.1
- **Timing:** one dispatch — spent
- **Verification Tier:** local
- **Completed:** 2026-08-05

**Verdict: both PASS. PROCEED with the reformulated Phase 7.**

**Landed, sorry-free** (verified present on disk this planning run):

| Declaration | File:line | Role |
|---|---|---|
| `S4RedirectSoundInv` | `FrameCompleteness.lean:5141` | The reformulated conserved predicate, conjuncts (a)-(d), transcribed from report §3.2 against this file's vocabulary (`s4FC`, `sfSat`, `Accessibility.hasEdge`/`addEdge`, `modalMintShape`, `outDeg`) |
| `modalApplyOneS4Rules_boxPos_notApplicable_of_saturated` | `FrameCompleteness.lean:4957` | Under `modalS4Saturated`, a box-positive persistent shape is **unconditionally** `.notApplicable` — every candidate output from all three layers is filtered against `b` |
| `modalApplyOneS4Rules_diaNeg_notApplicable_of_saturated` | `FrameCompleteness.lean:5040` | Diamond-negative dual |
| `S4RedirectSoundInv_boxNeg_blocked` | `FrameCompleteness.lean:5178` | **The mint-blocked (box-negative) arm, proven.** (a) mechanical; (b) the *identical* model witness, no surgery; (c) via `blockedRedirect_boxed_{boxPos,diaNeg}_mem` composed with the T-self bridges `hintikkaS4_{box_pos,dia_neg}_self`; (d) via `modalS4Saturated_addEdge_of_blocked` plus the two new lemmas |

Also: `modalUniverseS4_mem_formula` and `mem_signedSubfmls_of_formula_s4loop` widened from
`private` to public in `LoopChecking.lean` (no proof content touched).

`#print axioms` on all three new theorems/lemmas: exactly `{propext, Classical.choice, Quot.sound}`.
Full `lake build` green (3313/3313); `checkInitImports` and `lint-style` clean; sorry census
exactly 1.

#### Honest gaps this phase did NOT close (do not treat as landed)

1. **Only the box-negative-blocked shape is proven.** `S4RedirectSoundInv_diaPos_blocked` does not
   exist. Summary 07 flags this explicitly as "a real, flagged gap, not assumed-free". → Phase 7.3.
2. **P2 passed as a *reading-level* check.** The probe read `Rules.lean:85,152-161`,
   `FrameRules.lean:62-75,133-148`, and `Branch.lean:196-201` and confirmed every layer filters its
   output against `b`. It did **not** write the antitone-applicability lemma family report §6
   priced at ~10 mechanical lemmas. → Phase 7.4.
3. **P3 was not attempted.** "Mint seed covers the 4-payload" is untested. → Phase 7.6.
4. **The four Phase 7.1 arms are still stated against the old, unweakened hypotheses.** → Phases
   7.5-7.7.
5. **(d) was discharged using `hmint` (mint-readiness).** That hypothesis is available at a mint
   step and **not** at a primary-scan step. Nothing in this phase establishes (d)-preservation at a
   non-mint step. → Phase 7.4, and this is the plan's single largest remaining risk.

---

### Phase 7.3: `S4RedirectSoundInv_diaPos_blocked` — the mirror-image mint-blocked companion [COMPLETED]

- **Goal:** Close the diamond-positive mint-blocked arm (`T(◇φ)@src` blocked, guard call
  `blockingWorldS4Keyed φ₀ b keys .pos φ src`), completing the mint-blocked case under
  `S4RedirectSoundInv`.
- **Depends on:** 7.2
- **Timing:** 1.5 hours (one dispatch)
- **Verification Tier:** local
- **Commit Mode:** per-substep
- **Scope Hypothesis:** This phase asserts the diamond-positive arm is a *literal mirror* of
  `S4RedirectSoundInv_boxNeg_blocked` — same four conjunct discharges, same two new
  `notApplicable_of_saturated` lemmas, same `blockedRedirect_boxed_{boxPos,diaNeg}_mem` /
  `hintikkaS4_{box_pos,dia_neg}_self` composition, the only delta being
  `modalS4Saturated_addEdge_of_blocked` called at `s := .pos` — and estimates roughly 60 lines
  appended to `FrameCompleteness.lean`, no other file touched. This is summary 07's own
  characterization ("the exact mirror-image argument"), **not a verified fact of this codebase**.
  Confirm by transcription: if the mirror does not go through, that is a real asymmetry between the
  two mint shapes and must be recorded as a finding, not absorbed — the box/diamond asymmetry has
  been a route killer in this task before. Confirm the file count against `git diff --stat`.
- **Owns:** `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (appended after
  `S4RedirectSoundInv_boxNeg_blocked`).

- **Tasks:**
  - [x] Re-locate `S4RedirectSoundInv_boxNeg_blocked`, `modalS4Saturated_addEdge_of_blocked`,
        `blockedRedirect_boxed_boxPos_mem`/`_diaNeg_mem`, `hintikkaS4_box_pos_self`/
        `hintikkaS4_dia_neg_self`, `modalApplyOneS4Rules_{boxPos,diaNeg}_notApplicable_of_saturated`
        by grep. Do not trust the line numbers in this plan.
  - [x] Transcribe `S4RedirectSoundInv_boxNeg_blocked` to the diamond-positive shape as
        `S4RedirectSoundInv_diaPos_blocked`, with `hblock : blockingWorldS4Keyed φ₀ b keys .pos φ
        src = some wBlock`. The (c) discharge is unchanged — conjunct (c) quantifies over *both*
        payload shapes at the new edge regardless of which mint shape triggered the block, so the
        same two `blockedRedirect_boxed_*_mem` calls appear in both theorems.
  - [x] Confirm `modalS4Saturated_addEdge_of_blocked` accepts `s := .pos` with no additional
        hypothesis. If it does not, stop and record why. *(Confirmed: the lemma is stated over a
        general `s : Sign` parameter; `.pos` requires nothing extra.)*
  - [x] `#print axioms` (direct, not `lean_verify` — the fourth dispatch and the probe both
        recorded a spurious `sorryAx` from `lean_verify`'s source scan on these declarations);
        require exactly `propext`, `Classical.choice`, `Quot.sound`. *(Confirmed via `lake env
        lean` on a standalone `#print axioms` snippet.)*
  - [x] Scoped `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness`; `lake exe lint-style`;
        sorry census exactly 1. *(All green.)*

- **Done when:** `S4RedirectSoundInv_diaPos_blocked` is sorry-free and committed, or the phase is
  `[BLOCKED]` with the exact `lean_goal` and no `sorry` committed; census exactly 1; scoped build
  and `lint-style` clean.

#### Phase 7.3 Verdict

The mirror held literally, with no box/diamond asymmetry: `S4RedirectSoundInv_diaPos_blocked` is
`S4RedirectSoundInv_boxNeg_blocked`'s transcription at `hblock : blockingWorldS4Keyed φ₀ b keys
.pos φ src = some wBlock`, same four-conjunct discharge, same lemma calls (including the (c)
discharge, which correctly stays symmetric — conjunct (c) quantifies over both payload shapes
regardless of which mint shape triggered the block). Landed in `FrameCompleteness.lean` (grep for
the declaration name; no line anchor kept here per plan convention). Delta from the Scope
Hypothesis's ~60-line estimate: 118 lines including the docstring (the docstring plus the full
duplicated (d)-discharge case split account for the difference; no new lemma was needed).
`#print axioms`: exactly `propext`, `Classical.choice`, `Quot.sound`. Scoped build and
`lake exe lint-style` both clean. Sorry census unchanged at exactly 1
(`FrameSoundness.lean:1251`).

---

### Phase 7.4: Antitone-applicability lemma family (P2 formalized) [COMPLETED]

- **Goal:** Formalize the lemma family that makes conjunct (d) of `S4RedirectSoundInv` preservable
  at a **primary-scan (non-mint) step**, where mint-readiness is unavailable. P2's PASS in summary
  07 is a reading-level verification of the *premise*; this phase is the Lean content. **This is
  the plan's kill gate.**
- **Depends on:** 7.2
- **Timing:** 3 hours (one dispatch; one-dispatch attempt budget, per the gate discipline this task
  has used successfully at Gate 0 and Gate B)
- **Verification Tier:** local
- **Commit Mode:** per-substep
- **Scope Hypothesis:** This phase asserts a family of roughly 10 mechanical lemmas (report §6, P2)
  landing in `FrameCompleteness.lean`, no other file touched. Both the count and the file are
  hypotheses. Confirm by counting the landed declarations and `git diff --stat` at phase close.
  **Split trigger**: if the family exceeds 15 lemmas or requires touching a second file, stop,
  record the real shape, and split the remainder into `7.4.x` rather than running unbounded — v6's
  single unbounded Phase 7 ran four dispatches for exactly this reason.
- **Owns:** `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`, new section appended after the
  Probe P1 section.

**Why this is a genuine gate.** `S4RedirectSoundInv_boxNeg_blocked` discharged (d) from `hmint`
(`modalNonMintCandidates φ₀ keys b e acc = []`) via `modalNonMintCandidates_eq_nil_iff`
(`LoopChecking.lean:1237`). `modalStepBranchS4KeyedOrdered` (`LoopChecking.lean:1439`) reaches its
mint fallback **only** when the primary candidate scan returns `none`
(`modalStepBranchS4KeyedOrdered_cases`, `:1456`). At a primary-scan step the candidate list is
non-empty by construction, so `hmint` is false and (d) must be re-established a different way:
by showing that appending `nf` to `b` cannot turn a `.notApplicable` rule application into an
applicable one.

- **Tasks:**
  - [x] Re-locate `modalNonMintCandidates`, `modalNonMintCandidates_eq_nil_iff`,
        `modalStepBranchS4KeyedOrdered`, `modalStepBranchS4KeyedOrdered_cases`,
        `modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box`, `modalMintShape`, and `outDeg`
        (`FmpMeasure.lean:768`) by grep.
  - [x] Land the **branch-growth** half, per rule class, in this order (cheapest first, banking a
        green commit each):
        1. Propositional / non-mint-non-modal: `tryAllPropRules` takes only `sf` and depends on
           neither `b` nor `acc` (`Rules.lean:85`, confirmed by the probe). Applicability here is
           *literally invariant* under branch growth, which is stronger than antitone — state it
           that way rather than proving the weaker form. *(Landed as
           `modalApplyOne_fst_eq_of_not_box_diamond`, full `.fst` equality over any two branches
           `b1 b2`, stronger than the antitone form as instructed.)*
        2. K box-positive persistent (`boxPropagation`, `Branch.lean:196-201`) and the K
           diamond-negative inline arm (`Rules.lean:152-161`): both `filterMap`-filter each
           candidate against `b` via `b.any (· == sf)`. The antitone step is
           `(nf ++ b).any p = nf.any p || b.any p` (`List.any_append`). *(Landed as the generic
           `filterMap_any_guard_isEmpty_growth`, instantiated per shape.)*
        3. T self-propagation (`modalTBoxSelf`/`modalTDiaNegSelf`, `FrameRules.lean:62-75`) and
           the S4 4-rule (`modalFourBoxProp`/`modalFourDiaNegProp`, `FrameRules.lean:133-148`):
           same shape. *(T self landed as `modalTSelf_isEmpty_growth`; the 4-rule helpers reuse
           `filterMap_any_guard_isEmpty_growth` since they share the same
           `filterMap`-over-successors shape.)*
        4. The merge step: `++` followed by `.filter (fun x => !kForms.any (·==x))` only ever
           *removes* elements, never introduces one absent from a filtered source. *(Discharged
           inline inside `modalApplyOneS4Rules_boxPos_notApplicable_growth`/`_diaNeg_...` by
           case-splitting on each layer's `isEmpty` boolean and using `if_pos`/`if_neg` to collapse
           the nested K/T/4-rule match, rather than as a separate named lemma — the three-way
           `by_cases` split IS the merge-step argument.)*
  - [x] Land the **edge-growth** half for the two mint arms (`acc → acc.addEdge w w'`). **No new
        lemma was needed** — confirmed by inspection rather than by writing new code, exactly as
        the task anticipated: (a) the two persistent modal shapes are covered by the already-landed
        `modalApplyOneS4Rules_{boxPos,diaNeg}_notApplicable_of_saturated` (Phase 7.2), which give
        UNCONDITIONAL `.notApplicable` under `modalS4Saturated` at whatever accessibility is
        supplied — Phases 7.2/7.3 already call these directly at `acc.addEdge src wBlock`, so
        edge-growth for these two shapes is already exercised, not merely available; (b) every
        other shape's `.fst` is proven fully **acc-independent** by the already-landed
        `modalApplyOne_fst_eq_of_not_boxPos_diaNeg`/`modalApplyOneS4_fst_eq_of_not_boxPos_diaNeg`
        (`LoopChecking.lean:9747,9767`), so edge growth is vacuously antitone there; (c) the two
        mint shapes themselves are always `.linear` (never `.notApplicable`) regardless of `acc`,
        the same fact `modalApplyOneS4Keyed_notApplicable_growth`'s vacuous mint-shape case uses.
        Every shape is covered; nothing was left needing a genuine new edge-growth lemma.
  - [x] Assemble a single consumable statement, shaped to what Phases 7.5-7.7 need:
        ```
        (modalApplyOneS4Keyed φ₀ keys sf b acc).1 = .notApplicable →
          (modalApplyOneS4Keyed φ₀ keys sf (nf ++ b) acc).1 = .notApplicable
        ```
        plus the edge-growth variant. Name it and state in its docstring exactly which rule classes
        are covered by which sub-lemma. *(Landed as `modalApplyOneS4Keyed_notApplicable_growth`,
        stated fully generally over every signed-formula shape — not restricted to non-mint
        candidates — with the two mint shapes closed vacuously. The edge-growth variant is the
        reuse recorded above, not a new statement.)*
  - [x] `#print axioms` on every landed declaration; require exactly `propext`, `Classical.choice`,
        `Quot.sound`. *(Confirmed via `lake env lean`; every declaration's axiom set is a subset of
        `{propext, Classical.choice, Quot.sound}`.)*
  - [x] Record a `#### Phase 7.4 Verdict` subsection in this file.

- **Kill criteria and outcomes** (decided now, not under pressure):

| Outcome | Verdict |
|---|---|
| (i) The whole family closes sorry-free within the dispatch | Gate **PASSES**. Phases 7.5-7.7 dispatch. |
| (ii) The family closes for every class except one **nameable** shape, and that shape's failure mode is written out verbatim with its `lean_goal` | **Route survives conditionally.** Record which arm restatement now owes a workaround and stop at recording it. Do not begin the workaround in this phase. |
| (iii) Some rule is found **not** output-filtered — it can re-fire on data it already produced | **Conjunct (d) is unpreservable as stated.** This is report §6's named kill criterion. Do **not** weaken (d) silently to a reachability-style predicate inside a dispatch. Record the rule and the concrete re-fire, mark this phase `[BLOCKED]`, and escalate to the report §7 fallback decision (driver-level provenance, `Reds`/`accWithReds`) as a **user decision**, per the Terminal Condition. |
| (iv) Neither closes nor is refuted within this one dispatch | **Revert the incomplete family**, keep any sub-lemma that landed sorry-free (they stand on their own), record the exact `lean_goal`, and re-plan the split rather than requesting an open-ended second dispatch. Do **not** commit a `sorry`. |
| (v) Reading constraint on any passing outcome | A pass licenses the arm restatements to *consume* the family. It does not license assuming P3, does not license the dispatcher assembly before 7.3/7.5-7.7 return, and does not validate the Phase 9 capstone scope question. |

- **Done when:** the family (or outcome (ii)'s recorded remainder) is sorry-free and committed; a
  `#### Phase 7.4 Verdict` subsection exists; census exactly 1; scoped build and `lint-style` clean.

#### Phase 7.4 Verdict

**Outcome (i): the whole family closes sorry-free within the dispatch. Gate PASSES.** Six new
declarations landed in `FrameCompleteness.lean`, all in the new `## Phase 7.4:
Antitone-Applicability Lemma Family (P2 Formalized)` section appended after the Probe P1
material:

| Declaration | Role |
|---|---|
| `filterMap_any_guard_isEmpty_growth` | Generic branch-growth antitone fact for the `filterMap`-over-successors shape shared by `boxPropagation`, the inline diamond-negative K arm, and the two 4-rule helpers `modalFourBoxProp`/`modalFourDiaNegProp` |
| `modalTSelf_isEmpty_growth` | Same fact for the single-element T self-propagation guard (`modalTBoxSelf`/`modalTDiaNegSelf`) |
| `modalApplyOneS4Rules_boxPos_notApplicable_growth` | Assembles the K/T/4-rule three-layer argument for the box-positive shape, via the already-landed nested-match unfolding `modalApplyOneS4_boxPos_fst_eq` |
| `modalApplyOneS4Rules_diaNeg_notApplicable_growth` | Dual, via `modalApplyOneS4_diaNeg_fst_eq` |
| `modalApplyOne_fst_eq_of_not_box_diamond` | Full `.fst`-equality (strictly stronger than antitone) for every non-box/non-diamond formula shape, independent of `b` entirely |
| `modalApplyOneS4Keyed_notApplicable_growth` | **The assembled target.** Fully general over every signed-formula shape (not restricted to non-mint candidates); the two mint shapes close vacuously since `modalApplyOneS4Keyed` never returns `.notApplicable` there |

**Six lemmas, not the estimated ten** — under the Scope Hypothesis's 15-lemma split trigger, and
fewer than estimated because the file already carried strong reusable infrastructure: the
nested-match unfoldings `modalApplyOneS4_boxPos_fst_eq`/`_diaNeg_fst_eq` (which would otherwise
have needed re-deriving), the direct reduction lemmas
`modalApplyOneS4Keyed_boxPos_eq_S4Rules`/`_diaNeg_eq_S4Rules`, and
`modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box`. File count matches the Scope Hypothesis: only
`FrameCompleteness.lean` touched (`git diff --stat`: 243 lines added, against a ~250-line
estimate).

**Edge-growth half: no new lemma needed**, confirmed by inspection rather than authored — see the
task-level note above for the three-part covering argument (persistent shapes via the Phase 7.2
saturated-implies-`.notApplicable` lemmas already exercised at `acc.addEdge`; every other shape
via the already-landed acc-independence lemmas; mint shapes vacuously). This is itself informative
for P2: it confirms the reformulation's conjunct (d) needs no additional edge-side machinery
beyond what Phase 7.2 already landed.

`#print axioms` on all six: every one reports a subset of `{propext, Classical.choice,
Quot.sound}` (checked via `lake env lean`, not `lean_verify`, per this task's standing note about
`lean_verify`'s spurious `sorryAx` on this file cluster). Scoped `lake build
Cslib.Logics.Modal.Tableau.FrameCompleteness` and `lake exe lint-style` both clean, no warnings.
`lake exe checkInitImports` clean. Sorry census over `Cslib/Logics/Modal/Tableau/` unchanged at
exactly 1 (`FrameSoundness.lean:1251`).

**Reading constraint (outcome (v), honored):** this pass licenses Phases 7.5-7.7 to *consume*
`modalApplyOneS4Keyed_notApplicable_growth` for conjunct (d) at primary-scan steps. It does
**not** license assuming P3 (Phase 7.6's own first task), does not license dispatching Phase 7.8
before 7.3/7.5-7.7 return, and does not touch the Phase 9 capstone scope question.

---

### Phase 7.5: Propositional / non-mint arm restated against `S4RedirectSoundInv` [COMPLETED]

- **Goal:** Re-wrap `modalApplyOneS4Keyed_notBoxDia_sat` into an `S4RedirectSoundInv`-preservation
  arm, discharging conjuncts (a)-(d) at a primary-scan step.
- **Depends on:** 7.4
- **Timing:** 1.5 hours
- **Verification Tier:** local
- **Commit Mode:** per-substep
- **Scope Hypothesis:** This phase asserts that `modalApplyOneS4Keyed_notBoxDia_sat`'s semantic core
  is reusable **verbatim** — verified this planning run by reading its signature
  (`FrameCompleteness.lean:4495`): it takes `hsf : sfSat m f ⟨s, φ, w⟩` and **no** edge-realization
  hypothesis at all, so weakening (b)'s edge conjunct cannot affect it. It further asserts roughly
  80 lines in `FrameCompleteness.lean`, no other file. Confirm the line estimate and file set
  against `git diff --stat`; if the semantic core turns out to need re-proving rather than
  re-hypothesising, stop and record it — that would falsify report §3.4 row 1 and is a finding, not
  an absorbable cost.
- **Owns:** `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`.

- **Tasks:**
  - [x] Land the small bridging fact `acc.hasEdge u v = true → outDeg acc u ≠ 0` (locate `outDeg`
        in `FmpMeasure.lean:768`; it is `(acc.successorsOf u).length`). Conjunct (a) plus this fact
        is what shows a world with `outDeg acc u₀ = 0` is not the source of any ghost edge.
        *(Landed as `outDeg_ne_zero_of_hasEdge`.)*
  - [x] State the arm: from `S4RedirectSoundInv φ₀ b e acc keys Er` and a primary-scan step firing
        a non-mint-shaped `sf` at label `u₀`, conclude
        `S4RedirectSoundInv φ₀ (nf ++ b) (sf :: e) acc keys Er` (`Er` unchanged — a non-mint step
        creates no edge, so `acc' = acc`; confirm this against `modalApplyOneS4Keyed_notBoxDia_sat`'s
        own `.snd = acc` conclusion, which is already part of that lemma's statement). *(Landed as
        `S4RedirectSoundInv_notBoxDia_step`, stated existentially over `nf` with an explicit
        match-shaped selector against `(modalApplyOneS4Keyed φ₀ keys sf b acc).1` — covers
        `.linear`/`.persistent`/`.branching` uniformly, since `tryAllPropRules` (the only rule
        family reachable once box/diamond are excluded) can return any of the three; `acc`/`Er`
        held fixed as the plan specifies.)*
  - [x] Discharge (a): unchanged (`acc' = acc`, `Er' = Er`).
  - [x] Discharge (b): reuse `modalApplyOneS4Keyed_notBoxDia_sat` verbatim on the same `(m, f)` from
        the old (b); the disjunction is untouched because `acc' = acc`.
  - [x] Discharge (c): the only new formulas are in `nf`, all at label `u₀`. By the candidate
        predicate, `sf` is non-mint, not expanded, and applicable at `(b, acc)`; by (d) at the old
        state, an applicable non-mint non-expanded formula forces `outDeg acc u₀ = 0`; by the
        bridging fact plus (a), `u₀` is therefore not `p.1` for any `p ∈ Er`. Hence no ghost edge's
        source gains a formula and (c) is inherited. **This is the load-bearing step of the whole
        reformulation's (c)-stability argument (report §3.4 row 1, §3.5); write it out explicitly
        rather than letting a tactic close it opaquely.** *(Landed exactly this way; the label-
        preservation half needed a new supporting lemma `tryAllPropRules_output_label_eq`, not
        anticipated by name in the plan but consistent with its "load-bearing step" description.)*
  - [x] Discharge (d): consume Phase 7.4's branch-growth antitone lemma. Every formula that was
        `.notApplicable` at `b` stays `.notApplicable` at `nf ++ b`; the fired `sf` moves into `e`.
  - [x] `#print axioms`; scoped build; `lint-style`; census exactly 1.

- **Done when:** the arm is sorry-free and committed, or the phase is `[BLOCKED]` with the exact
  `lean_goal`; census exactly 1; scoped build and `lint-style` clean.

#### Phase 7.5 Verdict

Landed sorry-free in `FrameCompleteness.lean`: `outDeg_ne_zero_of_hasEdge` (bridging fact),
`tryAllPropRules_output_label_eq` (new supporting lemma — every `tryAllPropRules` output shares
its input's label, needed to make the (c)/(d) load-bearing argument generic over which of
`.linear`/`.branching`/`.persistent` the propositional rule actually returns), and
`S4RedirectSoundInv_notBoxDia_step` (the arm). The arm is stated existentially over the produced
`nf` with a match-shaped selector against `(modalApplyOneS4Keyed φ₀ keys sf b acc).1`, covering
all three non-`.notApplicable` result shapes uniformly — the plan's own prose named only `nf`
without settling whether propositional rules ever branch; they do (`andNeg`/`orPos`/`impPos`),
so the existential/selector shape is the honest generalization, not a deviation from the plan's
intent. Delta from the ~80-line estimate: 261 lines including two module docstrings and the new
supporting lemma (`git diff --stat`: `FrameCompleteness.lean` only, purely additive, no existing
declaration touched). `#print axioms` via `lake env lean` on all three new declarations: subsets
of `{propext, Classical.choice, Quot.sound}`. Scoped `lake build
Cslib.Logics.Modal.Tableau.FrameCompleteness`, `lake exe checkInitImports`, and `lake exe
lint-style` all clean. Sorry census over `Cslib/Logics/Modal/Tableau/` unchanged at exactly 1
(`FrameSoundness.lean:1251`). One cosmetic note: `tryAllPropRules_output_label_eq`'s proof
triggers the Lean core `linter.flexible` info/warning (a `simp_all`-then-`rcases` sequence on the
same goal) — not an error, not one of the seven `lake lint` prevention categories this task
tracks, and does not block the build; left as-is rather than spending further budget chasing a
cosmetic linter note.

---

### Phase 7.6: Mint-unblocked arms restated, and P3 [IN PROGRESS]

- **Goal:** Re-wrap `modalApplyOneS4Keyed_boxNeg_mint_sat` and `modalApplyOneS4Keyed_diaPos_mint_sat`
  against `S4RedirectSoundInv`, and settle P3 ("mint seed covers the 4-payload"), which summary 07
  records as **not attempted**.
- **Depends on:** 7.4
- **Timing:** 3 hours
- **Verification Tier:** local
- **Commit Mode:** per-substep
- **Scope Hypothesis:** This phase asserts these two arms are the *most* work of the three
  restatement phases, because (unlike the other three landed arms) their conclusions are
  `branchSatisfiableIn`-shaped existentials over a model
  (`... ∧ branchSatisfiableIn s4FC (nf ++ b) (acc.addEdge w (modalNextWorld b))`, verified this
  planning run at `FrameCompleteness.lean:4521` and `:4633`), not fixed-model `RuleResultSat`
  statements — so the restatement must thread the *same* extended `(m, f')` through conjunct (b)
  rather than re-introducing an existential. It estimates roughly 200 lines in
  `FrameCompleteness.lean`, no other file. Both the shape claim and the line estimate are
  hypotheses; confirm against `git diff --stat` and against the landed lemmas' actual statements
  before relying on either.
- **Owns:** `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`.

- **Tasks:**
  - [x] **P3 first, before any restatement work** (report §6 rates it "expected free"; if it is not
        free, that changes this phase's shape and should be discovered cheaply). State and attempt:
        every `modalFourBoxProp` / `modalFourDiaNegProp` output at the fresh mint world
        `modalNextWorld b` is already in `modalApplyOneS4KeyedMint`'s payload. Route: unfold
        `boxPlusExtraS4` (the BOXED transmission of every `T(□ψ)@w`/`F(◇ψ)@w` already on the
        branch, retargeted to the fresh witness) and compare against the 4-rule's `filterMap` over
        `(acc.addEdge w (modalNextWorld b)).successorsOf w`. Consult
        `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv`'s machinery first — report §6 notes
        this may already be implicit there. **If P3 fails, record the concrete counterexample output
        and stop**; do not attempt to patch the mint payload (that would be a driver-definition
        change, out of scope). *(P3 is TRUE and is genuinely load-bearing, contrary to the "expected
        free" framing — see the Progress Record below for the full mechanism and the two landed
        lemmas `modalApplyOneS4Rules_{boxPos,diaNeg}_layers_eq_nil_of_saturated`.)*
  - [ ] Restate the box-negative mint arm. Reuse the landed pointwise-extension construction
        `f' := fun n => if n = w' then ww else f n` and `boxPlusExtraS4_sat` **verbatim** — report
        §3.4 row 2 is explicit that the new mint edge is realized by construction, so (b) is
        *strictly easier* under the weakened conjunct, and old ghost edges are now exempt.
  - [ ] Discharge (a): `Er' = Er`; the old ghost edges remain recorded under `acc.addEdge` via
        `hasEdge_addEdge_mono_gate0`.
  - [ ] Discharge (c): new formulas land only at the fresh label `modalNextWorld b`. By
        `accFreshInv` (`SoundnessStep.lean:392`) every recorded edge's endpoints are `< modalNextWorld b`,
        so the fresh label is neither a source nor a target of any ghost edge, and (c) is inherited.
        Confirm `accFreshInv` is available as a hypothesis at this call site — the landed arms
        already take it (`hInv : accFreshInv b acc`), so it is threaded, but confirm rather than
        assume it survives to the invariant level.
  - [ ] Discharge (d): consume Phase 7.4's edge-growth half plus mint-readiness (a mint arm *does*
        have `hmint` available, unlike Phase 7.5 — use it, exactly as
        `S4RedirectSoundInv_boxNeg_blocked` does).
  - [ ] Restate the diamond-positive mint arm as the direct dual. **If the box half closes and the
        diamond half does not (or vice versa)**, do not proceed on one half alone: record the
        asymmetry as a route-relevant finding.
  - [ ] `#print axioms`; scoped build; `lint-style`; census exactly 1.

- **Done when:** both mint-unblocked arms are sorry-free and committed under `S4RedirectSoundInv`,
  P3 is either proven or recorded as failed with a concrete counterexample; census exactly 1;
  scoped build and `lint-style` clean.

#### Phase 7.6 Progress Record (first dispatch, incomplete — continuation required)

**P3 landed, and it is a real finding, not a formality.** Contrary to report §6's "expected free"
framing, P3 is genuinely load-bearing: after a mint step fires from world `w` (minting fresh `w'`
with edge `w→w'`), a DIFFERENT, unrelated persistent formula already on the branch at the SAME
world `w` (e.g. some other `T(□ψ'')@w`) picks up a genuinely NEW candidate from the K-rule
(`boxPropagation`) and the 4-rule (`modalFourBoxProp`), because both scan `acc.successorsOf w`,
which now includes `w'`. Nothing makes that new candidate `∈ b` (b hasn't changed) — it is only
present in `nf` (the mint payload itself), via `boxProps`/`boxPlusExtraS4`'s own construction,
which happens to duplicate exactly what the K-rule/4-rule would independently compute for the
fresh successor. Landed, sorry-free, in `FrameCompleteness.lean`:

- `modalApplyOneS4Rules_boxPos_layers_eq_nil_of_saturated` /
  `_diaNeg_layers_eq_nil_of_saturated`: under `modalS4Saturated`, each of the THREE per-layer
  candidate lists (K, T-self, 4-rule) is *individually* empty — not merely that their packaged
  `.fst` value is `.notApplicable`. Proven by reusing the exact internal `hK`/`htR` decomposition
  `modalApplyOneS4Rules_{boxPos,diaNeg}_notApplicable_of_saturated` (Phase 7.2) already performs,
  stopping one step earlier to expose each layer.
- `boxPropagation_addEdge_of_ne` / `modalFourBoxProp_addEdge_of_ne` /
  `modalFourDiaNegProp_addEdge_of_ne`: at any world other than the redirect source, `addEdge`
  leaves `successorsOf` (hence these two rule layers) unchanged.
- `modalApplyOneS4Rules_{boxPos,diaNeg}_fst_addEdge_of_ne`: the assembled acc-independence fact
  off the redirect source, combining the above with `modalApplyOneS4_boxPos_fst_eq`/
  `_diaNeg_fst_eq` (the unconditional closed-form reduction already landed, `LoopChecking.lean`).

Together these give conjunct (d)'s "other-world" case (a persistent formula NOT at the minting
world `w`) for free via acc-independence plus Phase 7.4's branch-growth lemma. The "same-world"
case (a persistent formula AT `w`) is P3 proper and is NOT yet assembled into a single lemma —
see "What remains" below for the exact closing argument, worked out but not yet written as Lean.

**What remains (worked out, not yet written):**

1. **The box-negative mint arm's conjunct (d), same-world sub-case.** For
   `⟨.pos, .box ψ'', w⟩ ∈ b` (b old, any `ψ''`, possibly unrelated to the minting formula's own
   `ψ`), show `(modalApplyOneS4Rules ⟨.pos,.box ψ'',w⟩ (nf++b) (acc.addEdge w w')).fst =
   .notApplicable` directly (not via a growth-lemma chain, since the intermediate state
   `(b, acc.addEdge w w')` is genuinely NOT notApplicable — the K-layer picks up a real new
   candidate there that only `nf` compensates for). Route: `successorsOf_addEdge_self` gives
   `(acc.addEdge w w').successorsOf w = w' :: acc.successorsOf w`; for the `w'` slot, `(ψ'', w) ∈
   boxPositivesOf b` (since `⟨.pos,.box ψ'',w⟩ ∈ b`, by `boxPositivesOf`'s own `filterMap`, easy
   forward direction — `mem_boxPositivesOf`, `Support/KnownWorlds.lean:150`, is only the
   INVERSE direction and does not directly apply; write the forward direction inline, it is a
   one-line `filterMap` membership fact), so `⟨.pos,ψ'',w'⟩ ∈ boxProps ⊆ nf` (K-layer
   compensation) and `⟨.pos,.box ψ'',w'⟩ ∈ boxPlusExtraS4 b w ⊆ nf` (4-rule compensation) — both
   unconditionally, since `w'` is fresh so neither formula could already be filtered out as
   "already in `b`". For the OLD-successor slots, `modalApplyOneS4Rules_boxPos_layers_eq_nil_of_saturated`
   (landed) gives `boxPropagation b acc ψ'' w = []` / `modalFourBoxProp b acc ψ'' w = []`
   directly, i.e. every old successor already has its content in `b ⊆ nf++b`. Assemble via
   `modalApplyOneS4_boxPos_fst_eq`'s unconditional closed form (all three layers empty ⟹ the
   whole nested if-chain collapses to `.notApplicable` by `simp`). Dual argument for
   diamond-negative same-world, using `modalApplyOneS4Rules_diaNeg_layers_eq_nil_of_saturated`.
2. **Conjunct (d)'s "everything else" case** (propositional/atomic, `modalMintShape=false` and
   not box-positive/diamond-negative): acc-independent AND b-independent via
   `modalApplyOne_fst_eq_of_not_box_diamond` (Phase 7.4) plus
   `modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box` (used already in Phase 7.5) — should be the
   cheapest sub-case, mirroring Phase 7.5's own propositional discharge.
3. **`outDeg (acc.addEdge w w') w' = 0`** (needed for the `sf' ∈ nf` case of (d), and nowhere
   proven yet as a standalone fact): via freshness (`accFreshInv`/`hInv`) ruling out any OLD edge
   sourced at `w'` (irreflexivity contradiction if one existed, since `hInv` would give `w' <
   w'`), plus `successorsOf_addEdge_of_ne` ruling out the new edge contributing to `w'`'s own
   OUT-successors (the new edge's source is `w`, not `w'`, since `w ≠ w'` by
   `modalNextWorld_gt`).
4. **Conjunct (b)'s weakened edge clause**: CANNOT reuse `modalApplyOneS4Keyed_boxNeg_mint_sat`
   as a black box — its `hacc` hypothesis is the UNCONDITIONAL `∀u v, acc.hasEdge u v → m.r (f u)
   (f v)`, which the weakened invariant does not supply for ghost-edge sources. The fix (worked
   out, not yet written into a landed theorem) is to re-derive the SAME construction
   (`f' := fun n => if n = w' then ww else f n`, same `boxProps`/`diaNegProps`/`boxPlusExtraS4_sat`
   satisfaction argument, which is UNCHANGED since it never touches `hacc`) with the edge clause
   generalized to `∀u v, acc.hasEdge u v → (u,v) ∈ Er ∨ m.r (f u)(f v)`, concluding `(u,v) ∈ Er ∨
   m.r (f' u)(f' v)` — a case split on `hacc u v hedge` inserted at the one call site
   (`modalApplyOneS4Keyed_boxNeg_mint_sat`, `FrameCompleteness.lean` line ~4566-4567 as of this
   dispatch) where the original calls `hacc u v hedge` directly.
5. **Conjunct (a) and (c)**: straightforward, same shape as Phase 7.5's discharge
   (`hasEdge_addEdge_mono_gate0` for (a); `mintGroup_label_eq_freshWorld` +
   `boxPlusExtraS4_label_eq_freshWorld` — both already landed, give every `nf`-formula's label
   `= w'`, combined with `accFreshInv` giving every ghost-edge endpoint `< w'` hence `≠ w'` — for
   (c)). Not yet written but no open question remains.
6. **The diamond-positive mint arm**: the direct dual of the box-negative arm above, once that
   one is landed and its shape confirmed. Per the plan's own instruction, do NOT proceed on one
   half alone if the other fails — but nothing found this dispatch suggests a box/diamond
   asymmetry (P3's two lemmas are already proven as a symmetric pair).

**Landed and committed this dispatch** (3 commits, all sorry-free, axioms exactly `{propext,
Classical.choice, Quot.sound}`, sorry census held at exactly 1 throughout):
`modalApplyOneS4Rules_{boxPos,diaNeg}_layers_eq_nil_of_saturated` (P3),
`boxPropagation_addEdge_of_ne`, `modalFourBoxProp_addEdge_of_ne`,
`modalFourDiaNegProp_addEdge_of_ne`, `modalApplyOneS4Rules_{boxPos,diaNeg}_fst_addEdge_of_ne`.

**Why this dispatch stopped here rather than pushing through:** the remaining assembly (items
1-6 above) is real, bounded, and now fully designed, but writing and verifying it — plus its
diamond-positive mirror, plus all of Phase 7.7 — was judged to exceed what could be completed
soundly in the turns remaining. Per this task's own standing discipline (never commit a
`sorry`, stop at a clean boundary rather than rush), this is recorded as an honest partial
rather than a rushed or unsound landing.

---

### Phase 7.7: 4-rule arms restated with the ghost-edge disjunction [NOT STARTED]

- **Goal:** Re-wrap `modalApplyOneS4Keyed_boxPos_sat` and `modalApplyOneS4Keyed_diaNeg_sat` against
  the weakened conjunct (b), replacing the blanket edge-realization hypothesis with the
  `(w, w') ∈ Er ∨ m.r (f w) (f w')` disjunction.
- **Depends on:** 7.4
- **Timing:** 2.5 hours
- **Verification Tier:** local
- **Commit Mode:** per-substep
- **Scope Hypothesis:** This phase asserts that the only hypothesis needing change in each landed
  arm is `hacc : ∀ u v, acc.hasEdge u v → m.r (f u) (f v)` — verified this planning run by reading
  both signatures (`FrameCompleteness.lean:4897`, `:4914`): each takes exactly
  `(hFC, hacc, hb, hmem)` and delegates to `modalApplyOneS4Rules_{boxPos,diaNeg}_soundIn`, so the
  disjunction must be pushed down into those two `_soundIn` lemmas, not merely into the arm
  wrappers. It estimates roughly 150 lines in `FrameCompleteness.lean`, no other file. Confirm
  against `git diff --stat`; **if the disjunction cannot be pushed into `_soundIn` without
  re-proving its one-hop `IsTrans` core, record that** — it would mean report §3.4 row 4's
  "restated, not re-proved" characterization is wrong for this arm.
- **Owns:** `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`.

- **Tasks:**
  - [ ] Re-locate `modalApplyOneS4Rules_boxPos_soundIn`/`_diaNeg_soundIn` and read how each
        consumes `hacc` (both go through one hop of `hFC.2 : IsTrans` off a recorded successor
        edge). Identify the exact use sites.
  - [ ] Restate each `_soundIn` with the disjunctive edge hypothesis. Per report §3.4 row 4, split
        per successor:
        - successor reached by a **non-ghost** edge → the landed one-hop `IsTrans` proof applies
          unchanged;
        - successor reached by a **ghost** edge (`(w, w') ∈ Er`) → the rule's output at that
          successor is already `∈ b` by conjunct (c), so its satisfaction comes free from (b)'s
          satisfaction clause, and the `filterMap`'s own dedup against `b` means it never even
          appears in the output list. **Prefer the dedup route if it closes** — it avoids needing
          the satisfaction argument at all — but confirm which one actually applies rather than
          assuming.
  - [ ] Note and confirm the simplification the probe's two `notApplicable_of_saturated` lemmas may
        offer: at a state where `modalS4Saturated` holds, these two shapes are unconditionally
        `.notApplicable` and the arm is vacuous. **Do not rely on this as the whole argument** —
        `modalS4Saturated` is available at settled/mint states via
        `modalS4Saturated_of_ordered_settled`, but a 4-rule shape can also fire at a *primary-scan*
        step where it is not available. Record explicitly which of the two routes each restated arm
        actually takes.
  - [ ] Discharge (a), (c), (d) for these arms: `acc' = acc` (both landed arms conclude
        `.snd = acc`), `Er' = Er`, new formulas land at successors — for a ghost successor already
        present (so no new formula at any redirect source), for a non-ghost successor covered by
        the same `outDeg` argument as Phase 7.5. (d) consumes Phase 7.4's branch-growth half.
  - [ ] `#print axioms`; scoped build; `lint-style`; census exactly 1.

- **Done when:** both 4-rule arms are sorry-free and committed under `S4RedirectSoundInv`; census
  exactly 1; scoped build and `lint-style` clean.

---

### Phase 7.8: The dispatcher theorem over `modalStepBranchS4KeyedOrdered` [NOT STARTED]

- **Goal:** Assemble the five arms into a single step-preservation theorem: if
  `S4RedirectSoundInv φ₀ b e acc keys Er` and `modalStepBranchS4KeyedOrdered` fires producing
  `(newBs, newExps, newAcc, keys')`, then for the selected branch
  `∃ Er' ⊇ Er, S4RedirectSoundInv φ₀ b' e' newAcc keys' Er'` (report §3.2's step-lemma shape).
- **Depends on:** 7.3, 7.5, 7.6, 7.7
- **Timing:** 3 hours
- **Verification Tier:** local
- **Commit Mode:** atomic-batch
- **Scope Hypothesis:** This phase asserts the case split mirrors
  `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv`'s shape exactly
  (`by_cases hmint : (neg,box) ∨ (pos,diamond)`, sub-split on `blockingWorldS4Keyed`), threaded
  through `modalStepBranchS4KeyedOrdered_cases` (`LoopChecking.lean:1456`) — which splits into
  (1) a primary-candidate-scan hit and (2) the settled fallback. It estimates roughly 250 lines in
  `FrameCompleteness.lean`, no other file. Confirm against `git diff --stat`. `atomic-batch` is
  declared because a dispatcher theorem is not green until every arm is wired; intermediate
  per-arm states will not typecheck.
- **Owns:** `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`.

- **Tasks:**
  - [ ] Write the target theorem statement out **first**, before wiring any arm, and confirm each of
        the five landed arms' conclusions is directly consumable by it. If any arm's shape does not
        fit, that is a Phase 7.5-7.7 defect to record and repair there, not to paper over here.
  - [ ] Thread the branch of `modalStepBranchS4KeyedOrdered_cases`:
        - **primary-scan hit**: the selected `sf` is non-mint by the candidate predicate → Phase
          7.5's arm, or a 4-rule shape → Phase 7.7's arm.
        - **settled fallback**: `modalNonMintCandidates = []` gives `hmint`; sub-split on
          `blockingWorldS4Keyed` into blocked (Phases 7.2/7.3) and unblocked (Phase 7.6).
  - [ ] Discharge `modalS4Saturated φ₀ b acc` where the blocked arms require it, from `hmint` plus
        `S4KeyedHintikkaInv` via `modalS4Saturated_of_ordered_settled` (`LoopChecking.lean:9250`).
        Record which additional invariants (`S4LoopInv.bClosure`, `S4LoopInv.keyLowerBd`,
        `S4KeyedHintikkaInv`) the dispatcher must carry alongside `S4RedirectSoundInv` — the blocked
        arms take `hUniv`/`hkL` directly, so the dispatcher's hypothesis list is not just the
        invariant.
  - [ ] Handle the `.branching` result shape (multiple `newBs`): the conclusion must be
        per-selected-branch, matching how the existing S5/Five assemblies state theirs.
  - [ ] `#print axioms`; scoped build; `lint-style`; census exactly 1.

- **Done when:** the dispatcher theorem is sorry-free and committed as one atomic commit; census
  exactly 1; scoped build and `lint-style` clean.

---

### Phase 8: Terminal payoff — closed-branch contradiction under the weakened predicate [COMPLETED]

- **Goal:** Establish that a classically closed branch contradicts `S4RedirectSoundInv`, so the
  weakening of conjunct (b) costs nothing at the terminal step of the soundness argument.
- **Depends on:** 7.2
- **Timing:** 1 hour
- **Verification Tier:** local
- **Commit Mode:** per-substep
- **Scope Hypothesis:** This phase asserts the proof is mechanical because the edge conjunct is
  never consumed downstream — **verified this planning run**: `modalClosed_unsatIn`
  (`FrameSoundness.lean:141`) destructures `⟨W, m, f, _, hedges, hb⟩` and calls `modalClosed_unsat`
  (`SoundnessStep.lean:92`), whose own proof destructures `⟨W, m, f, _, hb⟩` — discarding the edge
  conjunct with `_`. It estimates roughly 25 lines in `FrameCompleteness.lean`, no other file.
  Confirm against `git diff --stat`.
- **Owns:** `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`.

- **Tasks:**
  - [x] State `S4RedirectSoundInv φ₀ b e acc keys Er → isModalClosed b = false` (or the
        `¬ (isModalClosed b = true)` form matching `modalClosed_unsatIn`'s idiom). *(Landed as
        `S4RedirectSoundInv_not_isModalClosed`, the `isModalClosed b = false` form.)*
  - [x] Prove it by extracting conjunct (b)'s satisfaction clause and feeding `modalClosed_unsat`
        directly — conjunct (b)'s existential already supplies `⟨W, m, f, hb⟩`; the edge component
        is not needed. Do **not** route through `branchSatisfiableIn`, which cannot be reconstructed
        from the weakened conjunct. *(Landed via the `Accessibility.empty` vacuous-edge-witness
        idiom already used elsewhere in this file cluster — see the module comment for the exact
        mechanism: `modalClosed_unsat`'s own proof discards its edge-realization hypothesis, so a
        vacuously-true one at the empty accessibility suffices, reusing conjunct (b)'s `(W,m,f,hb)`
        untouched. No route through `branchSatisfiableIn` was attempted.)*
  - [x] `#print axioms`; scoped build; `lint-style`; census exactly 1. *(All green — axioms exactly
        `propext`, `Classical.choice`, `Quot.sound`; scoped build, `lint-style`, and
        `checkInitImports` all clean; sorry census unchanged at exactly 1.)*

- **Done when:** the terminal payoff lemma is sorry-free and committed; census exactly 1; scoped
  build and `lint-style` clean.

#### Phase 8 Verdict

Landed `S4RedirectSoundInv_not_isModalClosed` in `FrameCompleteness.lean` (34 lines, against the
~25-line estimate — module comment plus docstring account for the difference; no other file
touched, matching the Scope Hypothesis). The proof is exactly the Scope Hypothesis's predicted
shape: mechanical, because `modalClosed_unsat`'s own proof body destructures its
`branchSatisfiable` hypothesis as `⟨W, m, f, _, hb⟩`, discarding the edge-realization clause and
never touching it again. Rather than reconstructing a genuine edge witness from
`S4RedirectSoundInv`'s weakened conjunct (b) — which would reintroduce exactly the obligation
this task's whole reformulation exists to avoid — the proof supplies the edge slot with an
unconditionally vacuous witness at `Accessibility.empty` (no recorded edge, so the implication
`acc'.hasEdge w w' → m.r (f w) (f w')` holds for free) and reuses conjunct (b)'s `(W, m, f, hb)`
verbatim. `isModalClosed b` does not mention `acc` at all, so `hclosed` transfers to the
`Accessibility.empty` call site with no adjustment. This is the same idiom already used at
`Soundness.lean:363` and three call sites in `FrameSoundness.lean` (941, 3274, 4456/4464) — not a
novel technique, a documented existing pattern applied here.

`#print axioms`: exactly `propext`, `Classical.choice`, `Quot.sound`. Scoped build, `lake exe
lint-style`, and `lake exe checkInitImports` all clean, no warnings. `git diff --stat` confirms
purely additive (`git diff | grep '^-[^-]'` returns nothing — no existing declaration touched, in
particular none of the preserved declarations in the Testing & Validation checklist). Sorry
census over `Cslib/Logics/Modal/Tableau/` unchanged at exactly 1 (`FrameSoundness.lean:1251`).

---

### Phase 9: Fuel-induction wrapper, initialization, and the capstone scope decision [NOT STARTED]

- **Goal:** Wrap the step theorem in the fuel induction, establish initialization, and **decide
  explicitly** the scope question v6 left open across four dispatches: whether an end-to-end
  `modalTableauS4KeyedOrdered_sound`-shaped capstone is in scope for this task.
- **Depends on:** 7.8, 8
- **Timing:** 4 hours (see split trigger below)
- **Verification Tier:** interface
- **Commit Mode:** per-substep
- **Scope Hypothesis:** This phase asserts the fuel wrapper can mirror the existing
  `modalExpandBranchesGen_closed_unsatIn` (`FrameSoundness.lean:740`) /
  `modalStepBranchS5Gen_preserves_satIn` (`:2491`) assembly shape, and estimates roughly 250 lines
  in `FrameCompleteness.lean`. **Both are hypotheses, and the second is known-shaky**: the S5
  Bespoke Fuel-Induction Assembly spans `FrameSoundness.lean:2453-3320` (~870 lines). **Split
  trigger, mandatory**: the phase's first task is the scope decision; if the end-to-end capstone is
  judged in scope, split into `9.1` (fuel wrapper + initialization) and `9.2` (capstone) and record
  the split here before continuing. Do not run this phase unbounded.
- **Owns:** `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`.

- **Tasks:**
  - [ ] **Scope decision, first.** Read `modalExpandBranchesGen_closed_unsatIn` and the S5 bespoke
        assembly. Decide and record in a `#### Phase 9 Scope Decision` subsection whether this
        task's definition of done requires only the fuel wrapper or also the end-to-end capstone.
        If the capstone is in scope, split per the trigger above. This decision was deferred four
        times in v6; it is not deferrable again.
  - [ ] Establish initialization: at `(b = [F(φ₀)@0], e = [], acc = ∅, keys = [(0, ∅)])` with
        `Er = []`, conjuncts (a), (c), (d) are vacuous ((d) because `acc = ∅` makes every
        `outDeg acc _ = 0`), and (b) is exactly "some S4 countermodel of `φ₀` satisfies the branch"
        — the standard soundness hypothesis (report §3.2, "Initialization").
  - [ ] Thread the fuel induction, consuming Phase 7.8's step theorem and Phase 8's terminal payoff.
        The ghost list `Er` grows monotonically across steps; carry the `∃ Er' ⊇ Er` existential
        through the induction.
  - [ ] Record a module comment naming what the result does and does **not** say: it establishes
        soundness of the keyed ordered driver via a predicate that quarantines redirect edges from
        semantic edge-realization. It does **not** remove or discharge the standing sorry at
        `FrameSoundness.lean:1251`, whose statement is the *unweakened* per-step form this task
        established is not provable. No task numbers in the comment.
  - [ ] `#print axioms`; scoped builds of every touched module; `lint-style`; census exactly 1.

- **Done when:** the scope decision is recorded; the fuel wrapper and initialization are sorry-free
  and committed; census exactly 1; scoped builds and `lint-style` clean.

---

### Phase 10: Regression corpus, full CI gate, and close-out [NOT STARTED]

- **Goal:** Extend the regression corpus with a permanent witness row, run the full CSLib CI
  pipeline, and close the task out.
- **Depends on:** 9
- **Timing:** 2 hours
- **Verification Tier:** full
- **Commit Mode:** per-substep
- **Scope Hypothesis:** This phase asserts a file set of `CslibTests/S4LoopGuardRegression.lean`
  only (no `Cslib/` source change), and asserts every pre-existing row in that file stays
  unchanged — including the ordered-driver `"OPEN"` row on the counterexample formula, and the
  historical `"CLOSED"` KNOWN-UNSOUND row the file's own docstring documents. Confirm against
  `git diff` at phase close: any hunk touching an existing `#guard_msgs` row is a defect, not a
  fix.
- **Owns:** `CslibTests/S4LoopGuardRegression.lean`.

- **Tasks:**
  - [ ] Add one permanent witness row for the step-preservation result. Keep every existing row
        byte-identical.
  - [ ] Run the full CSLib CI order (`.claude/rules/cslib.md`): `lake exe cache get`, `lake build`
        (whole library), `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`,
        `lake test`, `lake exe mk_all --module` (expected no-op — no new files), and
        `lake shake --add-public --keep-implied --keep-prefix`. `lake test`, `lake shake`, and
        `mk_all` were deferred across every prior Phase 7 dispatch and have not been run since; run
        them here and record the result rather than assuming.
  - [ ] Final sorry census: exactly 1 (`FrameSoundness.lean:1251`).
  - [ ] Write `summaries/08_reformulated-s4-redirect-sound-inv-summary.md`.

- **Done when:** the regression file is green with one new row and no changed row; the full CI order
  has been run and its results recorded; census exactly 1; the summary artifact exists.

---

## Terminal Condition

**The one remaining kill gate in this plan is Phase 7.4 outcome (iii)**: some rule in the S4 rule
set is not output-filtered against `b` and can re-fire on data it already produced, making conjunct
(d) unpreservable.

On that outcome:

1. Write the verdict into the `#### Phase 7.4 Verdict` subsection with the concrete rule and the
   concrete re-fire, not a prose assertion.
2. Update `reports/05_gate-a-canonical-witness-blocker-analysis.md` with a pointer to the new
   verdict.
3. Set the task to `[BLOCKED]` and escalate for a **user decision** between:
   (a) report 06 §7's fallback — driver-level provenance, recording redirect edges in a separate
   accumulator (`Reds`/`accWithReds`, retained at `LoopChecking.lean:9330-9346`), with soundness
   conserving `branchSatisfiableIn s4FC b acc` over the mint-only `acc` and completeness consuming
   `accWithReds acc red`. This is a **definition change with ripple through Phases 1-6's landed
   statements**, which is why it is the fallback and not the recommendation. It is still **not** a
   guard change and still has zero termination impact.
   (b) accepting that the keyed S4 guard's soundness obligation stays open with the standing
   documented `sorry`.
4. In an orchestrated dispatch, record this as a `state_updates_pending` entry in
   `.orchestrator-handoff.json` rather than editing `specs/state.json` directly.

**What is different from v6's Terminal Condition**: v6 expected a gate to fire, on a base rate of
six failed routes. That base rate applied to routes with an open mathematical question at their
center. This route has none — report 06 §2 *proves* the old statement unprovable rather than
failing to prove it, and P1 is landed, machine-checked, sorry-free. The remaining risk is
engineering (does the antitone family close), not mathematical. That is a genuine change in kind,
and it is why this plan carries one kill gate rather than two.

---

## Testing & Validation

- [ ] **Sorry census, at every phase boundary.** Run the **bare-tactic** grep — not a
      prose-matching grep, which returns false positives from docstrings:
      ```bash
      grep -rn '^\s*sorry\s*$\|[^a-zA-Z_]sorry\s*$' Cslib/Logics/Modal/Tableau/ --include='*.lean'
      ```
      It MUST return **exactly one** line, `FrameSoundness.lean:1251:    sorry`. Any other count
      fails the phase, including 0 (which would mean the standing sorry was removed in violation of
      the standing user decision). Verified as exactly 1 at this plan's authoring.
- [ ] **`#print axioms` (direct, via `lake env lean`) on every new declaration**; permitted axioms
      are exactly `propext`, `Classical.choice`, `Quot.sound`. Prefer this over `lean_verify`: the
      fourth Phase 7 dispatch and the P1/P2 probe both recorded a spurious `sorryAx` from
      `lean_verify`'s source-scan heuristic on declarations in this file cluster.
- [ ] Scoped `lake build` of each touched module at every phase boundary.
- [ ] `lake exe lint-style` clean at every phase boundary.
- [ ] Full `lake build`, `lake lint`, `lake test`, `lake shake`, `lake exe mk_all --module` at
      Phase 10.
- [ ] `CslibTests/S4LoopGuardRegression.lean` green, with every pre-existing row unchanged.
- [ ] **Preserved-declaration check** at every phase boundary: `git diff` shows no hunk touching
      `accPinnedBy`, `branchSatisfiablePinnedIn`, `branchSatisfiablePinnedIn_redirect_mechanical`,
      `branchSatisfiableIn_s4FC_ancestor_redirect` or its module comment,
      `branchSatisfiableIn_s4FC_addEdge_of_blocked`, `blockingWorldS4Keyed`,
      `modalApplyOneS4Keyed`, `modalStepBranchS4KeyedOrdered`, or any termination lemma
      (`keysDistinct`, `modalKnownWorlds_length_le_worldBoundS4`, `modalWorldBoundS4`).
- [ ] **No task-number citations in any `.lean` file** touched by this plan.

---

## Artifacts & Outputs

- `specs/553_.../plans/08_reformulated-s4-redirect-sound-inv.md` (this file), with
  `#### Phase 7.4 Verdict` and `#### Phase 9 Scope Decision` subsections appended by their
  respective dispatches.
- `specs/553_.../summaries/08_reformulated-s4-redirect-sound-inv-summary.md` (on completion or on
  terminal-condition escalation).
- New sorry-free declarations in `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`:
  `S4RedirectSoundInv_diaPos_blocked`, the antitone-applicability family, the five restated arms,
  the dispatcher theorem, the terminal-payoff lemma, and the fuel-induction wrapper.
- One new regression row in `CslibTests/S4LoopGuardRegression.lean`.
- **No new declarations in `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` or
  `LoopChecking.lean`** are anticipated. If a phase finds it needs one, that is a scope-hypothesis
  violation to record, not a silent addition.

---

## Rollback/Contingency

- **Per-gate (Phase 7.4)**: the append-then-revert-unless-sorry-free contract. Gate material is
  appended in a delimited section. If the family does not close within its one dispatch, revert the
  incomplete portion, keep whatever landed sorry-free, and record the exact `lean_goal`. **Never
  commit a `sorry` at a gate** — that is the exact failure this task suffered twice.
- **Per-phase (Phases 7.3, 7.5-7.8, 8-10)**: work is committed per green sub-step (Phase 7.8 is
  declared `atomic-batch` and is one commit), so rollback is a revert of the last commit. A
  strategic-sorry skeleton remains a legitimate mid-phase recovery move in these **non-gate**
  phases and must be discharged before the phase is marked `[COMPLETED]`.
- **Whole-plan**: every phase after 7.2 is additive to `FrameCompleteness.lean` plus one regression
  row. Reverting this plan entirely means removing those appended sections and the regression row.
  No landed declaration outside this plan's own additions is modified, so no prior result — in
  particular no Phase 1-7.2 result and no completeness-track result — is at risk.
- **On the report §7 fallback**: it is a *definition* change (a separate redirect-edge accumulator)
  with ripple through Phases 1-6's landed statements. It is not attempted by any phase in this plan
  and must not be started without the user decision named in the Terminal Condition.
- **On terminal condition**: see the Terminal Condition section. Do not invent an eighth route.
