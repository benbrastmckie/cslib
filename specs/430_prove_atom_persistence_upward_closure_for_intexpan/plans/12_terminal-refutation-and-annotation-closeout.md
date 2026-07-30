# Implementation Plan: Task #430 — TERMINAL REFUTATION and Annotation Close-Out

- **Task**: 430 - prove_atom_persistence_upward_closure_for_intexpan
- **Status**: [COMPLETED] — Phase 15 (the only live phase) is complete; Phases 1-9 preserved
  COMPLETED, Phase 10 and Phases 11-14 COMPLETED WITH EXCLUSIONS. ODP-1 remains OPEN as a decision
  point requiring machine-checked confirmation or explicit human sign-off — it is not a scheduled
  phase and does not block this plan's completion; see ODP-1 above for what would resolve it.
- **Effort**: Phases 1-9 complete and committed (spent). Phase 10 and Phases 11-14 **terminally
  excluded** — zero further effort authorized. Phase 15 (annotation-and-docstring close-out) ~1
  dispatch. ODP-1 is a decision point, not a work item, and carries no budget.
- **Dependencies**: None blocking. Task 317's Route (a) frame plumbing has landed. Task 585 (DP-2)
  has retired its sorry — DP-2 remains that task's territory and must not be touched. The Phase 3/4
  coordination with task 574's settled work is discharged and does not recur below.
- **Research Inputs**:
  - `reports/11_gap1-fixpoint-completeness.md` (**newly integrated — the decisive artifact of this
    revision**; two-part verdict: Gap 1 **PROVABLE**, the residual beta arm **REFUTED**, overall
    task verdict **REFUTED**)
  - `scratch/BetaSplitRefutation.lean` (**newly integrated** — the machine-verified counterexample;
    `lake env lean` zero errors, zero sorries; independently re-verified by the orchestrator, see
    "The refutation" below)
  - `scratch/Gap1FixpointProbe.lean` (**newly integrated** — 272 loop iterations across 7
    candidates, `nonGenuine = 0`)
  - `handoffs/10_origin-tracing-scoping-and-new-blocker.md` (**newly integrated** — the blocker that
    prompted report 11; its source-scoping (sources 1-5) is preserved, its recommended option (2)
    was executed and returned a refutation)
  - `.orchestrator-handoff.json` (**newly integrated** — structured form of report 11's verdict,
    including both `unverified_claims`)
  - `handoffs/04_gate-b2-verdict.md` (Gate B2 PASS — now **SUPERSEDED by its own supersession
    clause**; see below)
  - `handoffs/07_post-reuse-closure-verdict.md` (Phase 9 COLLAPSED)
  - `handoffs/09_forestcomparable-export-phase10-continuation.md` (the landed `ForestComparable`
    export)
  - `reports/05_phase5-blocker-research.md` (the `tractable_large` verdict — now superseded on its
    load-bearing claim; §4's beta-split risk is the mechanism that in fact refuted the statement)
  - `handoffs/01_gate-a-variant-selection.md`, `handoffs/02_gate-b-verdict.md`,
    `handoffs/03_phase5-investigation-and-partial-progress.md`,
    `handoffs/05_phase7-complete-phase8-handoff.md`,
    `handoffs/06_phase8-complete-phase9-handoff.md`,
    `handoffs/08_phase9-collapsed-phase10-handoff.md`
  - `reports/01_atom-persistence-upward-closure.md`, `reports/02_team-research.md`,
    `reports/03_falsification-spike.md`
  - `specs/317_propositional_tableau_completeness/reports/17_timp-continuation-options.md`
  - `specs/574_tableau_calculus_repair_ancestor_blocking/reports/01_phase6-blocker-resolution.md`
    (the in-repo quotient refutation)
- **Artifacts**: plans/12_terminal-refutation-and-annotation-closeout.md (this file). Supersedes
  plans/06_gate-b2-then-origin-tracing-export.md, which is preserved unmodified for history (and is
  where Phases 1-9's full per-phase detail lives). plans/04 remains preserved beneath it.
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; cslib.md;
  lean4.md
- **Type**: cslib
- **Lean Intent**: true

## VERDICT: TERMINAL REFUTATION

**The statement this task exists to prove is FALSE.** Positive-formula persistence along
`intAccessPreorder` over the **augmented** edge list — the statement in the task description, the
statement Phases 7-13 were built to establish — is refuted by a machine-verified counterexample
against the real `intuitionisticTableau` **and** the real `minimalTableau`.

This is not a proof-route failure. It is a refutation of the statement itself.

### The refutation

- **Evidence**: `reports/11_gap1-fixpoint-completeness.md` §3, and the compiled artifact
  `specs/430_prove_atom_persistence_upward_closure_for_intexpan/scratch/BetaSplitRefutation.lean`.
- **Counterexample**: `phiRef1 = ((pr ∨ ps) ∧ ((ps → (ps → pr)) → pb)) → pr`, built by a
  **closure-asymmetry recipe** that *forces* the two beta-splits apart rather than hoping they
  diverge by accident. World `1`'s `T(pr)` child closes immediately against `F(pr)@1`, forcing world
  `1` onto `ps`; the `genCopies` copy `T(pr ∨ ps)@2` is a *distinct* `ISF` entry that splits
  independently **after** the loop-back edge `(1,2)` is recorded, and its `T(pr)@2` child does not
  close because reuse suppressed creation of any `F(pr)`-carrying world below `2`. Worlds `1` and
  `2` are preorder-**equivalent** in the augmented frame yet disagree on `pr`.
- **Why Gate B2 missed it**: Gate B2 planted disjunctions into reuse-heavy formulas and hoped for
  accidental divergence. The closure-asymmetry recipe removes the accident. Gate B2's own candidate
  family had no member of this shape. Report 11 §3.1.

### Independent re-verification (orchestrator, this revision cycle)

The decisive part was independently re-verified by compiling `scratch/BetaSplitRefutation.lean`
directly. Recorded here so it is not re-litigated:

| Check | Result |
|---|---|
| Compile | exit 0, **zero errors, zero sorries** |
| `branchesAgree` | **`true`** — the recreated loop returns exactly the branch the real `intuitionisticTableau` returns |
| `minBranchesAgree` | **`true`** — likewise for the real `minimalTableau` |
| Violation | `some (2, 1, 2)` at the **real** fuel `intFuelExt phiRef1` |
| `decisiveFacts` | **`(true, false)`** — `intExtractValuation b 2 pr` holds, `intExtractValuation b 1 pr` does not |
| `fimpWitnesses` | **`[1]`** — world `1` is the unique world on `b` carrying `T(ps)` and `F(pr)` |
| Candidate spread | 3 of 4 refute (`phiRef1`, `phiRef3`, `phiRef4`); `phiRef2` yields `none` |

The refutation reproduces under `isMinimallyClosed`, so DP-4's calculus is hit **independently**,
not merely by inheritance.

### Why the pre-existing terminal authorization applies, scoped by mechanism

Plan 06's Risks table (row 1) named this exact shape and pre-authorized the outcome:

> "If realizable, the statement is **FALSE** and all three sorries are permanently deferred" …
> "Refutation ⇒ terminal deferral per Rollback/Contingency, **NOT** escalation."

**That authorization is scoped by MECHANISM, not by which phase discovered the mechanism.** It
therefore fires here even though Phase 5 (Gate B2) itself recorded a PASS. Two independent grounds,
recorded explicitly so a later reader does not re-open the question:

1. **The mechanism matches exactly.** Plan 06's risk row describes "independent disjunction splits
   at `w` and at the reused ancestor `x` leav[ing] the two preorder-equivalent worlds disagreeing on
   atoms, with no mechanism to invalidate the recorded loop-back edge." That is, verbatim, what
   `phiRef1` realizes. The refutation was found by a sharper construction *inside the same search
   space*, not by a different mechanism.
2. **Gate B2's PASS contains its own supersession clause.** `handoffs/04_gate-b2-verdict.md` states
   verbatim: *"If either phase discovers a genuine obstruction traceable to this exact mechanism,
   that discovery supersedes this PASS and the plan's Rollback/Contingency for a later-phase failure
   applies."* Report 11 §6 invokes this clause and answers the deferral-scope question directly: the
   pre-authorized deferral **applies directly and needs no extension**.

Gate B2's PASS is therefore **SUPERSEDED**, not contradicted. Its method was sound; its candidate
family was insufficient, and it said so ("residual risk explicitly carried forward, not
exhaustively refuted").

### What is NOT authorized by this verdict

- **No escalation to the quotient / blocking-frame route.** It remains **PROHIBITED**. It is refuted
  twice over (in-repo non-monotonicity of `intBlockRep` under branch growth; published
  nontransitivity of interval filtration relations) and a refutation of the augmented-frame route is
  not new evidence in its favour. See Reasoned Exclusions.
- **No successor persistence route of any kind.** Do not propose one. Do not propose a weakened
  persistence statement, a restricted frame, a different preorder, or a "persistence modulo X"
  variant as a way to keep the build-out alive. The obstruction is in the calculus's frame
  construction (see below), not in the choice of proof route, so no re-routing reaches it.

## Overview

The goal of plans 04 and 06 — prove positive-formula persistence along the augmented accessibility
relation and use it to discharge DP-3, DP-4 and DP-5 at once — is **terminally unreachable**. This
revision converts the plan from a build-out into a close-out.

**What changed in this revision**, driven by `reports/11_gap1-fixpoint-completeness.md`:

1. **Gap 1 is PROVABLE — and the STOP-gate note claiming otherwise is STALE.** The blocker handoff
   10 escalated (does `applyPersistenceFixpoint` reach a genuine fixpoint before every rule step?)
   is not open. `applyAllTImpRules` is purely additive, so the length-equality exit **is** genuine
   fixpoint-ness (`applyAllTImpRules_eq_self_of_length_eq`, `Scheme.lean:5335`); the only
   non-genuine exit is `fuel = 0`; and the fuel-sufficiency lemma
   `applyPersistenceFixpoint_genuine_of_count_le_fuel` is **already landed sorry-free** at
   `Scheme.lean:5386`, stated for **arbitrary** `b` and **arbitrary** `fuel`. Both its hypotheses
   (`IAllUniv`, `IAllFuel`) are already in scope at *every* arm of the `key` induction, including
   the reuse arm (`case6`: `hUnivP_head` at `Scheme.lean:7173`, `hFuel_bh_eH` at `:7180`).
   Empirically: `scratch/Gap1FixpointProbe.lean` records `nonGenuine = 0` across **272 loop
   iterations** over 7 candidates. The Gap-1 STOP-gate note at **`Scheme.lean:553-573`** — *"This
   measure has not been built"* — is therefore **stale** and directly contradicts the section header
   at `Scheme.lean:5094-5098` ("Closes GAP 1 of the `sat_timp` STOP-gate above"). Correcting it is
   Phase 15's task, warranted independently of everything else here.
2. **Granting Gap 1 unblocks nothing.** It does not merely reduce the residual obligation — it
   *eliminates* origin tracing, the `ForestComparable` case split, and handoff 10's non-terminating
   recursion, because the reuse-containment invariant strengthens for free from the single world `l`
   to **all raw ancestors of `l`**: `Q'(b) := ∀ y, isAccessible E y l → ∀ χ, T(χ)@y ∈ b → T(χ)@x ∈
   b`. Four of the five content-adding arms then close (copy-from-ancestor, cross-world T-imp,
   alpha, mint-payload/initial-content — the last vacuously). **Exactly one arm survives: beta.**
   And that arm is refuted. **Phase 10's remaining task list was therefore unnecessary work
   independent of the refutation**, and is now moot twice over.
3. **The defect is calculus-level, in a frame construction — not in a proof.**
   `intFImpReuseWitnessAnc?` checks `Sfor`-containment **at reuse time**, and the recorded loop-back
   edge is **never re-validated**. Subsequent independent beta-splits at the two now-equated worlds
   break the equation the edge asserts. **Termination (task 574's concern) is unaffected**;
   countermodel *soundness* is not. Any repair would have to make the loop-check re-validatable, or
   robust to post-reuse beta-splits (e.g. expanding a disjunction at most once per equivalence
   class, or refusing reuse when either world carries an unexpanded positive disjunction). **Both
   are calculus-level changes and both are out of this task's scope.**

**Structure of what remains.** One annotation-and-docstring dispatch (Phase 15) and one open
decision point (ODP-1) that is explicitly *not* scheduled work. Nothing else. Phases 10-14 are
closed with reasoned exclusions.

### Superseded verification criterion

The task description's verification criterion — *"`grep -n sorry` on both `Completeness.lean` files
returns no bare `sorry`; DP-5 closed"* — is **unachievable and is hereby superseded**. It presumed a
true statement. The replacement criterion is in Testing & Validation: the sorries must be *honestly
and accurately annotated*, not removed. A dispatch that makes the `sorry` tokens disappear by
routing them through a false premise, or by weakening a statement, is executing this plan
incorrectly.

### Research Integration

Newly integrated in this revision:

- **`reports/11_gap1-fixpoint-completeness.md`** — the decisive artifact. Findings consumed: the
  Gap-1 provability verdict and the staleness of the `Scheme.lean:553-573` note (§1 → Phase 15 task
  2); the `Q'` interval-strengthening and the one-surviving-arm table (§2 → the exclusion record for
  Phases 10-14); the machine-verified beta refutation (§3 → the VERDICT section above); the
  self-loop secondary finding (§4 → Phase 15 task 4); the do-not-re-derive list (§5); the per-sorry
  disposition table and the deferral-scope answer (§6 → Phase 15 tasks 1 and 3, and ODP-1); the
  recommended-next-dispatch shape (§7 → Phase 15 as a whole).
- **`scratch/BetaSplitRefutation.lean`** — evidence, not conjecture, and independently
  re-verified this cycle (table above). **Do not delete.** It is the durable anchor Phase 15's
  annotations must cite.
- **`scratch/Gap1FixpointProbe.lean`** — the empirical Gap-1 confirmation. **Do not delete.**
- **`handoffs/10_origin-tracing-scoping-and-new-blocker.md`** — its source enumeration (the five
  ways positive content can be added, `Rules.lean:250-283`) is **preserved and reused** by report
  11 §2's arm table and must not be re-derived. Its recommended option (2) — a Gate-B2-style probe
  of the concrete scenario, before investing in the lemma — was executed and returned the
  refutation. Recording that the cheap probe was run *first*, as recommended, and that it saved the
  large investment.

**Every `[UNVERIFIED]` marker carried by report 11 is preserved verbatim below.** There are exactly
two, and neither is load-bearing for the refutation itself:

- **[UNVERIFIED]** (report 11 §1.4) — the six-line `case6` composition that instantiates Gap 1 at
  the reuse arm was **not compiled**. The delegation prohibited `Cslib/` writes and the declarations
  are `private` to `Scheme.lean`, so a scratch file cannot call them. Grounding: the identical
  three-step composition already compiles at `case4` (`Scheme.lean:7011-7017`), both hypotheses are
  present at `case6` under the same names, and `bPers` is the same
  `applyPersistenceFixpoint bh edgesH (f'+1)` term at both arms. Risk of non-compilation low but
  nonzero. **This marker survives into Phase 15's optional task 5.**
- **[UNVERIFIED]** (report 11 §3.3) — the step from `fimpWitnesses = [1]` to *"the whole `∃ edges`
  conjunct of `openBranch_countermodel` is false for this `b`"* is a **proof-level argument, not
  machine-checked**. It assumes `¬IForces` is only obtainable through `truthLemma`'s `IFimpAccess`
  route. Hand-checked support: over the **raw** frame `[(1,0),(2,1)]` upward closure *does* hold,
  but `IForces (intExtractValuation b) 0 phiRef1` is then **true** (the antecedent fails at every
  world, because `pb` is forced nowhere), so the raw frame does not witness the existential either.
  **This marker is the entire content of ODP-1 and is why no `Cslib/` statement change is
  authorized.**

### Preserved from plans 04 and 06 — complete, CI-verified, committed

Phases 1-9 are carried forward as **done**, not re-planned, and are **never** to be discarded,
reverted, or re-derived. Their full per-phase detail lives in plan 06 (and, for Phases 1-4, plan
04), both preserved unmodified. Committed at `e52f2624`, `611e8f9d`, `8f504c77`, `0ef99cd4`,
`d38751ba`, `52f1eb16`, `7f9031c0`, `9442560d`.

Landed assets that remain **correct, useful, and sorry-free** notwithstanding the refutation:

| Asset | Location | Status under the refutation |
|---|---|---|
| V4 generalized `genCopies` copy channel | `Expansion.lean`, `Scheme.lean`, `Soundness.lean` | Landed, CI green, unaffected |
| `applyAllTImpRules_copy_complete_of_fixpoint` | `Scheme.lean` | Sorry-free, axiom-clean, unaffected |
| `applyPersistenceFixpoint_copy_complete` | `Scheme.lean` | Sorry-free, axiom-clean, unaffected |
| `applyPersistenceFixpoint_genuine_of_count_le_fuel` | `Scheme.lean:5386` | Sorry-free; **this is Gap 1's fuel side**, and report 11 §1.2 confirms it general in `b` and `fuel` |
| `applyAllTImpRules_eq_self_of_length_eq` | `Scheme.lean:5335` | Sorry-free; makes the length-equality exit genuine |
| `IPosPersistRaw` + its export (2nd existential) | `Scheme.lean` | Landed; **raw-edge** persistence is true and remains true. The refutation is about the **augmented** frame only |
| `IReuseContain` / `IAllReuseContain` + export (3rd existential) | `Scheme.lean` | Landed; the reuse-time containment fact is true *at reuse time*. Its insufficiency is exactly the defect in §3 above |
| `ForestComparable` export (`par`-linearity, (H1-acc)) | `Scheme.lean` | Landed sorry-free (commit `7f9031c0`); a genuine corollary of `IWorldHist`, correct and reusable |
| `scratch/HvalidShapeRefutation.lean` | scratch | The Phase-6 statement-shape refutation; still valid on its own terms. **Do not delete** |

**Do NOT revert any of the above.** Nothing in the refutation makes any landed, sorry-free lemma
false. The single landed item whose *truth* is in question is Phase 6's added upward-closure
conjunct — and that question is ODP-1, not a scheduled action.

## Goals & Non-Goals

**Goals**:
- Record the terminal refutation prominently and durably, with its evidence and its independent
  re-verification, so it is not re-litigated (this file; Phase 15's `Cslib/` annotations).
- Re-annotate DP-3, DP-4 and DP-5 as **permanently deferred / unprovable-as-stated**, not merely
  unfinished, citing `scratch/BetaSplitRefutation.lean` and `phiRef1` as durable anchors.
- Correct the stale Gap-1 STOP-gate note at `Scheme.lean:553-573`.
- Document the loop-check's post-reuse beta-split defect at `intFImpReuseWitnessAnc?` as a recorded
  **frame-construction** limitation, with the counterexample cited and termination explicitly noted
  as unaffected.
- Record ODP-1 (the Phase-6 conjunct's disposition) as an **open decision point** requiring
  machine-checked confirmation or explicit human sign-off — and record that nothing may be changed
  in landed `Cslib/` code on the strength of an unverified inference.
- Leave the tree green, with the sorry count unchanged and every sorry honestly annotated.

**Non-Goals**:
- Do **not** build out Phase 10's origin-tracing task list. Unnecessary given Gap 1 (report 11 §5
  item 2) and moot given the refutation.
- Do **not** open Phases 11-14. See the exclusion records.
- Do **not** rebuild a quotient / blocking-frame reconstruction under **any** circumstance,
  including as an escalation after this refutation. **PROHIBITED.** See Reasoned Exclusions.
- Do **not** propose, design, or dispatch **any successor persistence route** — no weakened
  statement, no restricted frame, no alternative preorder, no "persistence modulo X". The
  obstruction is in the calculus's frame construction, so no re-routing reaches it.
- Do **not** revert, weaken, or otherwise change Phase 6's landed upward-closure conjunct, or any
  other landed statement, on the strength of the **[UNVERIFIED]** `fimpWitnesses` inference. See
  ODP-1.
- Do **not** attempt a calculus-level repair of the loop-check (re-validatable reuse edges;
  once-per-equivalence-class disjunction expansion; refusing reuse under an unexpanded positive
  disjunction). All are out of this task's scope; Phase 15 documents them as recorded limitations
  only.
- Do **not** touch DP-2 (`intFreshMint_preserves_nw`) — task 585 territory, already retired there.
- Do **not** pursue Route C (containment preorder) or `≤`-on-ℕ upward closure — both empirically
  refuted long before this.
- Do **not** re-open task 574's termination design. Termination is unaffected by this refutation.
- Do **not** delete any `scratch/` artifact. Three of them are now load-bearing evidence.
- Do **not** cite task numbers in any Lean source, docstring, or comment. Durable anchors only
  (lemma names, section headings, file paths, `phiRef1`).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| **A future dispatch reads "REFUTED" as "the proof route failed" and proposes a successor persistence route.** | Critical | Medium | The VERDICT section states the statement itself is false, with machine-verified evidence and independent re-verification. Non-Goals forbid successor routes explicitly. Report 11 §3.3's ghost-witness argument shows no choice of augmented edge list rescues the existential. |
| **The [UNVERIFIED] `fimpWitnesses` inference is acted on as if established**, and Phase 6's landed conjunct is reverted or weakened. | Critical | Medium | **ODP-1** below. No phase authorizes such a change; Phase 15 is annotation-only and its Files-to-modify list forbids statement edits. The marker is preserved verbatim in three places in this plan. |
| **Phase 15's annotation is written as "REFUTED" for the Phase-6 conjunct**, converting an argued inference into an asserted fact in landed source. | High | Medium | Phase 15 task 3 specifies the exact epistemic register: the conjunct's disposition is **UNDECIDED pending ODP-1**, with the argued-but-unverified refutation recorded as such. Report 11's own §6 recommendation ("re-annotate as REFUTED") is deliberately **not** followed at that register — its own §3.3 marks the inference unverified. |
| **The stale Gap-1 note is "corrected" by deleting the STOP-gate entirely**, losing the record that DP-5 is deferred. | Medium | Low | Phase 15 task 2 is scoped to the *staleness* only: the "measure has not been built" claim. The deferral record itself is re-annotated by task 1, not removed. |
| **Someone reverts landed Phase 3/4/7/8 assets as "part of a refuted route".** | High | Low | The preserved-assets table above enumerates them with their status. None is false. Non-Goals and Rollback/Contingency both forbid the revert. |
| **Territory collision on `Scheme.lean`** with a concurrently live 317/574/585 phase. | Medium | Low | Phase 15 is a single dispatch touching three files with comment/docstring edits only; `file_scope` is populated in this task's metadata so the orchestrator's footprint gate can serialize. Small and re-runnable if yielded. |
| **The refutation is read as impugning soundness or termination.** | Medium | Low | Report 11 §6 consequence 2 and the Overview both state it: termination (task 574's concern) is unaffected; `intExpandBranches_closed_unsat` and `Soundness.lean` are untouched and remain sorry-free. `phiRef1` is genuinely *not* intuitionistically valid, so `.openBranch` is the **correct** verdict — the defect is in the countermodel the open branch yields, not in the closure verdict. |

## Open Decision Points

### ODP-1: disposition of Phase 6's landed upward-closure conjunct (`Scheme.lean` ~7884)

**Status: OPEN. Requires machine-checked confirmation OR explicit human sign-off. No `Cslib/`
change is authorized until one of those exists.**

- **What is established (machine-verified)**: for `phiRef1`, upward closure of
  `intExtractValuation b` fails along `intAccessPreorder` over the *reconstructed* augmented edge
  list — `decisiveFacts = (true, false)`, violation `some (2, 1, 2)`, `branchesAgree = true`.
- **What is argued but NOT machine-checked — [UNVERIFIED]** (report 11 §3.3, preserved verbatim):
  *"the step from `fimpWitnesses = [1]` to 'the whole `∃ edges` conjunct of
  `openBranch_countermodel` is false for this `b`' is a proof-level argument, not machine-checked:
  it assumes `¬IForces` is only obtainable through `truthLemma`'s `IFimpAccess` route."* Supporting
  hand-check: over the raw frame `[(1,0),(2,1)]` upward closure *does* hold, but
  `IForces (intExtractValuation b) 0 phiRef1` is then **true**, so the raw frame does not witness
  the existential either.
- **Why this matters**: `openBranch_countermodel`'s conclusion is an **existential over `edges`**.
  The refutation of upward closure at one particular reconstructed witness does not, by itself,
  refute the existential. Closing that inference requires ruling out *every* admissible witness —
  which is exactly the unverified step.
- **Consequence**: report 11 §6 consequence 1 recommends re-annotating the conjunct as REFUTED and
  observes that plan 06's claim that Phase 6 *"remains worth landing even under a Gate B2
  refutation"* is therefore **wrong** (see the correction record below). That correction to the
  *plan's* claim stands. But the *source annotation* may not assert refutation as fact while the
  inference is unverified.
- **What would resolve it** (either suffices):
  1. A machine-checked confirmation that no admissible `edges` witnesses the existential for
     `phiRef1` — e.g. an exhaustive decidable search over admissible edge lists satisfying
     `IExpandedAccessConsistent` for the reused obligation `F(ps → pr)@2`, or a compiled Lean proof
     of the `∃ edges` conjunct's negation at this `b`.
  2. Explicit human sign-off on the argued inference.
- **Explicitly NOT authorized in the meantime**: reverting the conjunct; weakening it; deleting it;
  restating `openBranch_countermodel`'s conclusion over a loop-back-free frame (report 11 §3.3
  notes this breaks `¬IForces`, making it a calculus-level redesign, not a restatement); or
  discharging DP-3/DP-4 through it. **Do not plan, schedule, or authorize any of these.**

### Correction to plan 06's line ~398 claim

Plan 06's Phase 6 body asserted that the phase *"remains worth landing even under a Gate B2
refutation, because it converts an unfillable sorry into an honestly-stated one."* **That claim is
withdrawn.** Report 11 §6 consequence 1 argues the landed conjunct is itself **false** rather than
honestly-deferred, so the conversion the claim describes did not occur: an unfillable sorry was
replaced by a differently-unfillable one, not by an honest deferral. The same withdrawal applies to
the identical claim in plan 06's Planned Strategic Sorries table (Gate B2 row).

**Scope of the withdrawal**: it retracts the *plan's* optimistic claim. It does **not** establish
the conjunct's falsity as fact — that remains ODP-1's **[UNVERIFIED]** inference. The honest state
is: *the conjunct's truth is undecided, its argued disposition is false, and plan 06's confidence
that it was a strict improvement was unwarranted.* Phase 6 itself remains landed and is not
reverted.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |
| 3 | 4 | 3 |
| 4 | 5, 6 | 4 |
| 5 | 7 | 5 |
| 6 | 8 | 7 |
| 7 | 9 | 8 |
| — | 10, 11, 12, 13, 14 | **terminally excluded — no wave** |
| 8 | 15 | 9 (and the report-11 verdict) |
| — | ODP-1 | decision point, not a phase; gated on external confirmation or human sign-off |

Waves 1-7 are complete. Phases 10-14 are closed with reasoned exclusions and are **not** scheduled
in any wave. Phase 15 is the only live phase and is a single sequential dispatch on
`Scheme.lean` + both `Completeness.lean` files.

### Phase 1: Gate A — variant selection probe (V1 vs V4) [COMPLETED]

- **Goal:** Determine by measurement which copy-channel form to reinstate: V1 (self-copy verbatim)
  or V4 (generalize to copy *every* positive formula).
- **Outcome:** **V4 selected.** Control fidelity reproduced against the prior task's recorded
  tables; V4 saturates on `φ0` at `fuel ≥ 120`; all 20 `TableauConformance.lean` propositional rows
  match. Full measurement tables in `handoffs/01_gate-a-variant-selection.md`.
- **Tasks:**
  - [x] Probe harness recreated in `scratch/VariantProbe.lean`; true control reproduced first.
  - [x] V1 and V4 measured on the fuel ladder; conformance rows checked read-only.
  - [x] Decision recorded in `handoffs/01_gate-a-variant-selection.md`.
- **Timing:** ~1 dispatch (spent)
- **Depends on:** none
- **Verification Tier:** local
- **Files modified:** `scratch/VariantProbe.lean`. Zero `Cslib/` writes, confirmed.

### Phase 2: Gate B — persistence prototype (GATING, no algorithm change) [COMPLETED]

- **Goal:** Decide whether positive-formula persistence along the augmented relation is provable at
  all, before any calculus change.
- **Outcome:** **PASS (conditional).** The descendant sub-case closes; the ancestor sub-case was
  carried forward. Verdict in `handoffs/02_gate-b-verdict.md`; prototype in
  `scratch/PersistPrototype.lean`.
- **Recorded limitation, now vindicated:** Gate B analysed only the *copy* argument's
  descendant/ancestor sub-cases and did **not** consider independent beta-split choices at `w`
  versus at the reused ancestor `x`. That is precisely the mechanism that refuted the statement.
  Gate B also did not re-confirm multi-hop composition under `Relation.ReflTransGen`.
- **Tasks:**
  - [x] Single-loop-back-hop prototype built and green in `scratch/`.
  - [x] The `bPers`-vs-final-branch survival question confronted directly.
  - [x] Explicit PASS/FAIL verdict recorded.
- **Timing:** ~1 dispatch (spent)
- **Depends on:** none
- **Verification Tier:** local
- **Files modified:** `scratch/PersistPrototype.lean`. Zero `Cslib/` writes.

### Phase 3: Reinstate the copy channel — V4 generalized `genCopies` [COMPLETED]

- **Goal:** Restore the copy channel in the form Gate A selected, returning the tree to green with
  the channel present.
- **Outcome:** V4's generalized `genCopies` channel landed in `Expansion.lean`, with the
  `rfl`-level pattern-match repairs and proof restructuring in `Scheme.lean` and `Soundness.lean`.
  Full detail, including every recorded deviation from a literal revert, is in plan 04's Phase 3.
- **Verification results (recorded at the time):** `lake build` green; `lake exe checkInitImports`
  clean; `lake lint` zero new warnings in the three touched files; `lake exe lint-style` clean;
  `lake shake` no new findings in touched files; `lake test` green including `TableauConformance`.
  `intExpandBranches_closed_unsat` axiom-clean (`propext`, `Classical.choice`, `Quot.sound`);
  `Soundness.lean` sorry-free.
- **Status under the refutation:** unaffected. The channel is correct and is not reverted.
- **Tasks:**
  - [x] `Expansion.lean`: generalized `genCopies` channel plus docstring.
  - [x] `Scheme.lean`: pattern-match repairs, generalized `applyAllTImpRules_copy_notMem`, new
        shared helper `applyAllTImpRules_eq_self_of_length_eq`.
  - [x] `Soundness.lean`: `applyAllTImpRules_sat` and `freshAbove_applyAllTImpRules` restructured
        for the 3-way append.
  - [x] Axiom-cleanliness and conformance re-verified against the real library.
- **Timing:** ~1 dispatch (spent)
- **Depends on:** 1, 2
- **Verification Tier:** full
- **Commit Mode:** atomic-batch
- **Files modified:** `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`,
  `.../Intuitionistic/Scheme.lean`, `.../Intuitionistic/Soundness.lean`.

### Phase 4: Copy-completeness at a genuine `applyAllTImpRules` fixpoint [COMPLETED]

- **Goal:** Prove that at a genuine `applyAllTImpRules` fixpoint the copy channel has delivered
  every positive formula it owes along the **raw** edges.
- **Outcome:** Two lemmas landed, both **sorry-free and axiom-clean**:
  `applyAllTImpRules_copy_complete_of_fixpoint` and `applyPersistenceFixpoint_copy_complete`.
- **Status under the refutation:** unaffected and **now more valuable than planned** — report 11 §2
  shows these plus Gap 1 are what collapse the residual obligation from four arms to one. They are
  not to be reverted or re-proved.
- **Verification results:** `lake build` green; `checkInitImports` and `lint-style` clean; zero new
  `lake lint` warnings in `Scheme.lean`.
- **Tasks:**
  - [x] Case-split on the same guard `genCopies` itself uses.
  - [x] `applyAllTImpRules_copy_complete_of_fixpoint` stated and proved sorry-free.
  - [x] `applyPersistenceFixpoint_copy_complete` composed and verified.
- **Timing:** ~1 dispatch (spent)
- **Depends on:** 3
- **Verification Tier:** local
- **Files modified:** `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`

### Phase 5: Gate B2 — beta-split refutation probe (GATING) [COMPLETED]

- **Goal:** Determine empirically whether the beta-split shape refutes atom-level persistence along
  the **augmented** relation.
- **Outcome:** **PASS (with residual risk explicitly carried forward, not exhaustively refuted)** —
  and that PASS is now **SUPERSEDED**. Eight `φ0` candidates were tested; three (`phiRS`, `phiRS2`,
  `phiBeta2`) genuinely exercised the mechanism and found zero violations. Full verdict and method
  in `handoffs/04_gate-b2-verdict.md`.
- **Supersession record (this revision):** the PASS was correct about its own candidate family and
  wrong about the statement. `reports/11_gap1-fixpoint-completeness.md` §3 found a violation with a
  **closure-asymmetry** construction (`phiRef1`) that *forces* the two beta-splits apart instead of
  hoping they diverge — a shape absent from Gate B2's family. Gate B2's own closing bullets
  authorize this supersession verbatim: *"If either phase discovers a genuine obstruction traceable
  to this exact mechanism, that discovery supersedes this PASS."* The method was sound; the search
  was insufficient, and the verdict said so.
- **Tasks:** (all complete; see plan 06 Phase 5 for the full task list and its recorded deviations
  — the eight-candidate widening, the fuel-40 compute-budget deviation on the heaviest candidates,
  and the augmented-vs-raw edge-list discipline)
  - [x] Candidate family constructed; reuse events and shared disjunctions confirmed per candidate.
  - [x] Atom-level persistence decided computationally over `intAccessPreorder augEdges`.
  - [x] Explicit verdict recorded in `handoffs/04_gate-b2-verdict.md`, including the supersession
        clause that later fired.
- **Timing:** ~1 dispatch (spent)
- **Depends on:** 4
- **Verification Tier:** local
- **Files modified:** `scratch/BetaSplitProbe.lean`. Zero `Cslib/` writes, confirmed.

### Phase 6: Statement-shape fix — `openBranch_countermodel` and `hvalid` [COMPLETED]

- **Goal:** Close the machine-verified statement-shape defect (`scratch/HvalidShapeRefutation.lean`
  proves both `IValid (p → (q → p))` and the falsity of `hvalid`'s body at `edges=[(1,0)]`,
  `b=[T(p)@0, T(q)@1]`), moving the upward-closure obligation to where `b`'s provenance is in scope.
- **Outcome:** Landed. `openBranch_countermodel`'s conclusion carries the upward-closure conjunct
  (proved by a new, deliberately-deferred `sorry`); `tableau_complete`'s `hvalid` accepts it as a
  hypothesis and its own proof body is sorry-free. Both `Completeness.lean` files' bridge sites
  updated; DP-3/DP-4 re-annotated (still `sorry`, deliberately, to avoid laundering the gap two
  files away). `lake build` green; exactly 4 sorries.
- **Status under the refutation — read carefully:** the statement-shape *diagnosis* stands (the old
  `hvalid` premise really was unfillable, machine-verified). What does **not** stand is plan 06's
  claim that this phase converted an unfillable sorry into an honestly-stated one: report 11 §6
  consequence 1 argues the new conjunct is itself false. That argued disposition rests on an
  **[UNVERIFIED]** inference and is **ODP-1**. Phase 6 is **not reverted**, and no change to its
  landed statement is authorized. See "Correction to plan 06's line ~398 claim" above.
- **Tasks:** (all complete; full task list and the `lean_verify` transitive-`sorryAx` analysis in
  plan 06 Phase 6)
  - [x] `scratch/HvalidShapeRefutation.lean` re-confirmed to compile before any signature edit.
  - [x] Consumers enumerated (`grep -n`): exactly the two `Completeness.lean` bridge sites plus
        `tableau_complete`'s own internal call — matching the Scope Hypothesis, no excess.
  - [x] `openBranch_countermodel`'s conclusion strengthened; `tableau_complete`'s `hvalid` weakened
        and its proof repaired; `tableau_complete` confirmed sorry-free in its own body;
        `Soundness.lean` confirmed untouched.
  - [x] Docstrings updated; DP-3/DP-4 re-annotated rather than laundered.
- **Timing:** ~1 dispatch (spent)
- **Depends on:** 4
- **Verification Tier:** interface
- **Commit Mode:** atomic-batch
- **Files modified:** `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`,
  `.../Intuitionistic/Completeness.lean`, `.../Minimal/Completeness.lean`.

### Phase 7: Export the raw-edge persistence conjunct [COMPLETED]

- **Goal:** Add the **raw-edge** persistence conjunct to `intExpandBranches_openBranch_sat`'s
  conclusion.
- **Outcome:** Landed. `IPosPersistRaw edges b` defined; the conclusion became
  `∃ (edges rawEdges : IEdges), IBranchSaturation Atom b ∧ IFimpAccess edges b ∧
  IPosPersistRaw rawEdges b` — a **second** existential, since `IPosPersistRaw`'s accessibility
  hypothesis is genuinely over the RAW edge list, a necessary refinement recorded at the time. Only
  the substantive terminal case (`case4`) needed new work. `lake build` green; zero new sorries.
- **Status under the refutation:** **unaffected and still true.** Raw-edge persistence is the easy
  half and is not what was refuted — the refutation is about the **augmented** frame. Report 11
  §3.3 confirms upward closure *does* hold over the raw frame for `phiRef1`. Not reverted.
- **Tasks:** (all complete; see plan 06 Phase 7, including the recorded deviation composing via
  `applyPersistenceFixpoint_copy_complete` directly)
  - [x] `IPosPersistRaw` defined and threaded.
  - [x] Terminal return site discharged via the Phase 4 pairing lemma.
  - [x] Other return sites confirmed to need no new work.
  - [x] Conclusion extended and the single destructuring consumer repaired.
- **Timing:** ~1 dispatch (spent)
- **Depends on:** 5
- **Verification Tier:** interface
- **Files modified:** `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`

### Phase 8: Export reuse-time containment as a companion invariant [COMPLETED]

- **Goal:** Thread `posFormulasAt bPers w ⊆ posFormulasAt bPers x` as a monotone planted fact per
  recorded loop-back edge, surviving to the final branch.
- **Outcome:** Landed. Adopted the existential-snapshot encoding
  `IReuseContain (lbH) (b) := ∀ x l, (x, l) ∈ lbH → ∃ bSnap, (∀ y ∈ bSnap, y ∈ b) ∧
  ∀ χ, T(χ)@l ∈ bSnap → T(χ)@x ∈ bSnap`, plus `IAllReuseContain` and its `_append`/`_map_const`
  lemmas, threaded through a **separate** parallel list (`lbSets`/`pendingLB`/`doneLB`). The
  conclusion gained a **third** existential (`lbEdges`). The reuse arm (`case6`) plants via
  `hcontGen` + `IReuseContain_snoc`; all other arms mono-lift via `IReuseContain_mono`. `lake build`
  (3311 jobs) green; `checkInitImports`/`lint-style` clean; `TableauConformance` green; zero new
  sorries.
- **Status under the refutation:** **unaffected and still true** — and it is the precise locus of
  the defect report 11 §6 consequence 2 names: the containment holds **at reuse time** and the
  loop-back edge is never re-validated afterwards. The invariant is correct; what it guarantees is
  simply not enough, and post-reuse beta-splits are why. Not reverted.
- **Tasks:** (all complete; see plan 06 Phase 8 for the full enumeration of all 10 induction cases
  and the recorded encoding deviation)
  - [x] `IReuseContain`/`IAllReuseContain` defined with the existential-snapshot shape.
  - [x] Companion-not-merged pattern followed, on its own parallel list.
  - [x] `IReuseContain_mono` / `_append` / `_map_const` mirrored from the `IWorldHist` family.
  - [x] Threaded through the `key` induction; exactly one planting arm confirmed by enumeration.
  - [x] Branch-append monotonicity confirmed to carry the planted fact to the final branch.
- **Timing:** ~1 dispatch (spent)
- **Depends on:** 7
- **Verification Tier:** interface
- **Files modified:** `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`

### Phase 9: Post-reuse closure lemma — the cheap route first [COMPLETED]

- **Goal:** Prove that no positive formula arrives at `w` after the reuse event without also being
  at `x`, attempting the saturation + copy-completeness route first.
- **Outcome: COLLAPSED** (a planned branch, not a failure). Full analysis in
  `handoffs/07_post-reuse-closure-verdict.md`. The `y ≤ x` descendant sub-case closes cleanly with
  already-landed exports; the `x ≤ y ≤ w` ancestor sub-case remained open because content flows
  forward-only via the copy channel. Zero `Cslib/` writes; `lake build` reconfirmed green with the
  identical 4-sorry set.
- **Status under the refutation — the COLLAPSED verdict is superseded on its diagnosis, not on its
  discipline:** report 11 §2 shows the residual obligation does **not** in fact require origin
  tracing. Granting Gap 1, the containment invariant strengthens from `{l}` to *all raw ancestors of
  `l`* for free (`Q'`), which closes four of the five content-adding arms and eliminates the
  `ForestComparable` case split entirely. The genuinely residual arm was **beta** all along — and it
  is refuted. Phase 9's refusal to force a result, and its zero-`Cslib/`-writes discipline, were
  correct and are what kept the tree clean through this outcome.
- **Tasks:** (all complete; see plan 06 Phase 9)
  - [x] Residual obligation stated precisely (in the verdict handoff, not as landed Lean).
  - [x] Decomposition source discharged via saturation at `x`.
  - [x] `y ≤ x` copy source discharged via `IPosPersistRaw`.
  - [x] `x ≤ y ≤ w` case attacked within budget and recorded as genuinely open.
  - [x] `ForestComparable` export gap identified (subsequently landed sorry-free, commit
        `7f9031c0`; a pure corollary of `IWorldHist`/`IWorldHistCounter`, no new invariant needed).
  - [x] Verdict **COLLAPSED** recorded in `handoffs/07_post-reuse-closure-verdict.md`.
  - [x] Prohibited workarounds honoured: no `sorry`, no vacuous placeholder, no weakened statement.
- **Timing:** ~1 dispatch (spent)
- **Depends on:** 8
- **Verification Tier:** interface
- **Files modified:** none this phase (`ForestComparable` landed in the following dispatch, in
  `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`).

### Phase 10: Fallback — full origin tracing [COMPLETED WITH EXCLUSIONS]

- **Goal (withdrawn):** build the origin-tracing extension — track a traceable point of origin for
  every positive formula's branch presence, and show that origin is raw-accessible to any loop-back
  edge's source.
- **Disposition: TERMINALLY EXCLUDED. No further build-out.** Its prerequisite
  (`ForestComparable` export) landed sorry-free and is kept. Its remaining task list is closed
  unbuilt, on two **independent** grounds — either alone would suffice:
  1. **Unnecessary.** Report 11 §2: granting Gap 1 (which is provable, and whose load-bearing lemma
     is already landed), the reuse-containment invariant strengthens for free from `{l}` to all raw
     ancestors of `l`, which eliminates origin tracing, the `ForestComparable` case split, **and**
     handoff 10's non-terminating recursion. Origin tracing was never needed.
  2. **Moot.** The one arm that survives that strengthening is beta, and beta is refuted.
- **Prior-dispatch findings preserved (do not re-derive):** handoff 10's source enumeration
  (`Rules.lean:250-283`, the five ways positive content is added) and its narrowing of genuine
  self-origination points to mint-payload plus initial content; handoff 10's identification that
  Phase 10's residual case and DP-5's "Gap 1" are the same underlying question — which is what
  routed the escalation to report 11 and produced the refutation.
- **Tasks:** (none executed; closed unbuilt)
  - [x] Prerequisite `ForestComparable` export — **landed sorry-free**, commit `7f9031c0`, retained.
  - [~] Origin-tracing witness extension — **excluded** (see Reasoned Exclusions).
  - [~] (H3) generalization to every positive formula's point of origin — **excluded**.
  - [~] Origin-raw-accessibility via (H1-acc) and `par`-linearity — **excluded**.
  - [~] Phase 9 retry — **excluded**.
- **Timing:** 0 (closed)
- **Depends on:** 9
- **Verification Tier:** prose
- **Files to modify:** none.

#### Reasoned Exclusions

| Item | Reason | Evidence |
|------|--------|----------|
| Origin-tracing witness extension (`IWorldHist` companion invariant tagging every positive entry with a self-origination point) | **Unnecessary AND moot.** Unnecessary: granting Gap 1, the containment invariant strengthens to `Q'(b) := ∀ y, isAccessible E y l → ∀ χ, T(χ)@y ∈ b → T(χ)@x ∈ b`, whose base case is immediate from copy-completeness at a genuine fixpoint composed with the reuse check's own containment conjunct — this closes the copy-from-ancestor arm with **no `ForestComparable` case split at all**. Moot: the surviving beta arm is refuted, so the whole augmented-frame statement is false. Building this would be the exact "duplicated churn" the plan's discipline forbids, on the largest invariant in the plan. | `reports/11_gap1-fixpoint-completeness.md` §2 (the `Q'` strengthening and the five-arm table), §5 item 2 ("Phase 10's remaining task list is therefore unnecessary work, **independent of the refutation**"), §3 (the refutation), §7 ("Do **not** dispatch Phase 10's remaining origin-tracing task list"); `scratch/BetaSplitRefutation.lean` (compiled, zero errors, independently re-verified). |
| (H3) generalization from mint-time `Sfor` to every positive formula's origin | Same two grounds; it exists only to serve the witness extension above. | Same. |
| Origin-raw-accessibility lemma | Same two grounds; consumed only by the excluded retry. | Same. |
| Phase 9 retry with origin tracing in hand | The retry's target — the `x ≤ y ≤ w` residual — is *dissolved* by `Q'` (report 11 §2), not closed by origin tracing; and what remains after dissolution is the refuted beta arm. A retry cannot succeed against a false statement. | `reports/11_gap1-fixpoint-completeness.md` §2, §3; `handoffs/10_origin-tracing-scoping-and-new-blocker.md` (the non-terminating recursion this dissolution removes). |

### Phase 11: Multi-hop composition and augmented-edge export [COMPLETED WITH EXCLUSIONS]

- **Goal (withdrawn):** confirm the single-hop transfer lemma composes under
  `Relation.ReflTransGen`, then export the augmented-edge persistence conjunct
  (`IPosPersist edges b`) in `intExpandBranches_openBranch_sat`'s conclusion.
- **Disposition: TERMINALLY EXCLUDED.** There is no single-hop transfer lemma to compose, because
  the single-hop statement is **false** at `phiRef1`: worlds `1` and `2` are augmented-preorder
  equivalent across **one** recorded loop-back edge `(1,2)` and disagree on `pr`. Composition is
  moot when the base case fails. Exporting `IPosPersist` would export a false invariant.
- **Tasks:** (none executed)
  - [~] Two-hop composition check — **excluded** (single-hop base case refuted).
  - [~] Lift to `intAccessPreorder` via `intAccessPreorder_le_of_isAccessible` — **excluded**.
  - [~] Define and export `IPosPersist edges b` — **excluded** (would export a false invariant).
  - [~] Repair destructuring call sites — **excluded** (no conclusion change occurs).
- **Timing:** 0 (closed)
- **Depends on:** 9, 10
- **Verification Tier:** prose
- **Files to modify:** none.

#### Reasoned Exclusions

| Item | Reason | Evidence |
|------|--------|----------|
| Multi-hop composition check | Moot: the **single-hop** statement it would compose is refuted. The violation at `phiRef1` arises across exactly one recorded loop-back edge. | `reports/11_gap1-fixpoint-completeness.md` §3.2 (loop-back list `[(1,2), (2,2)]`, violation `some (2,1,2)`), §3.3 (direction convention verified against source); `scratch/BetaSplitRefutation.lean`. |
| `IPosPersist edges b` definition and export in `intExpandBranches_openBranch_sat`'s conclusion | The invariant is **false**. Exporting it would require a `sorry` or a weakened statement, both prohibited outright by this plan and its predecessors. | Same, plus `handoffs/04_gate-b2-verdict.md`'s supersession clause and plan 06's Risks row 1 pre-authorization. |
| Any weakened or restricted variant of the augmented-edge export | Excluded as a successor persistence route. The obstruction is in the calculus's frame construction (`intFImpReuseWitnessAnc?` never re-validates the loop-back edge), so no restatement over a different frame or preorder reaches it — report 11 §3.3 shows a loop-back-free frame breaks `¬IForces` instead, making it a calculus-level redesign. | `reports/11_gap1-fixpoint-completeness.md` §3.3, §6 consequence 2. |

### Phase 12: Discharge DP-5 (`truthLemma` T-implication case) [COMPLETED WITH EXCLUSIONS]

- **Goal (withdrawn):** close DP-5 (`Scheme.lean` ~`:731`; re-locate by content) by instantiating
  the exported augmented-edge invariant at `φ = φ'→ψ'` so reflexive `sat_timp` fires at `w'`.
- **Disposition: TERMINALLY EXCLUDED. DP-5 is PERMANENTLY DEFERRED as unprovable-as-stated**, not
  merely unfinished. It consumes the augmented frame, which is refuted. Phase 15 re-annotates it;
  nothing discharges it.
- **Tasks:** (none executed)
  - [~] Consume the augmented-edge persistence conjunct in `truthLemma`'s `imp` case — **excluded**
        (the conjunct does not and cannot exist).
  - [~] Fire `sat_timp` at `w'`; replace the `sorry` — **excluded**.
  - [~] Update STOP-gate docstrings to record the gap as closed — **excluded**; superseded by Phase
        15's re-annotation as *permanently deferred*, which is the opposite update.
- **Timing:** 0 (closed)
- **Depends on:** 11
- **Verification Tier:** prose
- **Files to modify:** none (Phase 15 owns the annotation).

#### Reasoned Exclusions

| Item | Reason | Evidence |
|------|--------|----------|
| Discharging DP-5 | Depends on augmented-frame persistence, which is refuted. Report 11 §6's per-sorry table: DP-5 → *"terminal deferral; depends on the same augmented frame."* | `reports/11_gap1-fixpoint-completeness.md` §6 table; `scratch/BetaSplitRefutation.lean`. |
| Any shape-specific algorithm-level patch for the T-imp case | Previously excluded and still excluded: `truthLemma`'s frame is `intAccessPreorder` over the augmented list, deliberately decoupled from the raw edges, so any raw-edge-filtered copy channel is strictly weaker. The obstruction is at the invariant level. | Plan 06 Reasoned Exclusions ("A T-imp-only or atom-only phase"); task description §"Why this scope". |

### Phase 13: Discharge DP-3 and DP-4 at atom shape [COMPLETED WITH EXCLUSIONS]

- **Goal (withdrawn):** close `Intuitionistic/Completeness.lean` (~`:146`) and
  `Minimal/Completeness.lean` (~`:141`) sorry-free via a shared order-agnostic upward-closure
  corollary parametric in the formula slot.
- **Disposition: TERMINALLY EXCLUDED. DP-3 and DP-4 are PERMANENTLY DEFERRED as
  unprovable-as-stated.** DP-3 would consume a premise whose truth is undecided at best (ODP-1) and
  false at worst; DP-4 is hit **independently** — the refutation reproduces under
  `isMinimallyClosed` (`reportMin phiRef1 realFuel` gives the same violation `some (2,1,2)`, and
  `minBranchesAgree = true` against the real `minimalTableau`), so DP-4 is not merely collateral.
- **Explicitly prohibited here**: discharging DP-3/DP-4 by routing them through Phase 6's landed
  conjunct. That would launder the gap two files away behind a premise whose own status is ODP-1 —
  exactly what Phase 6 deliberately refused to do when the premise was merely deferred, and a
  stronger refusal is warranted now.
- **Tasks:** (none executed)
  - [~] Shared parametric upward-closure corollary — **excluded**.
  - [~] `intExtractValuation_upward_closed` / `minBranchBotForces_upward_closed` specializations —
        **excluded**.
  - [~] `Intuitionistic/Completeness.lean` instantiation and `sorry` replacement — **excluded**.
  - [~] `Minimal/Completeness.lean` instantiation and `sorry` replacement — **excluded**.
  - [~] Rewrite both "Notes on sorry" sections to describe closure — **excluded**; superseded by
        Phase 15's re-annotation as *permanently deferred*.
- **Timing:** 0 (closed)
- **Depends on:** 6, 12
- **Verification Tier:** prose
- **Files to modify:** none (Phase 15 owns the annotation).

#### Reasoned Exclusions

| Item | Reason | Evidence |
|------|--------|----------|
| Discharging DP-3 | Consumes the upward-closure premise from `openBranch_countermodel`, whose disposition is ODP-1 (argued false, **[UNVERIFIED]**) and whose underlying mathematical content is refuted at the reconstructed witness. Report 11 §6 table: *"terminal deferral; consumes a false premise."* | `reports/11_gap1-fixpoint-completeness.md` §6 table, §3.3 (including the preserved `[UNVERIFIED]` marker). |
| Discharging DP-4 | Refuted **independently** under `isMinimallyClosed`, not by inheritance from the intuitionistic case. | `reports/11_gap1-fixpoint-completeness.md` §3.2 (`reportMin`, `minBranchesAgree = true`); `scratch/BetaSplitRefutation.lean`, independently re-verified. |
| Routing DP-3/DP-4 through Phase 6's landed conjunct to make the `sorry` tokens vanish | Gap-laundering. Phase 6 refused this when the premise was honestly deferred; the premise's status is now weaker, not stronger. Prohibited by this plan's replacement verification criterion. | Plan 06 Phase 6, "Why DP-3/DP-4 are deliberately left `sorry`"; Testing & Validation below. |

### Phase 14: CI and final verification [COMPLETED WITH EXCLUSIONS]

- **Goal (withdrawn):** confirm all three sorries are gone with no regressions and full CI green.
- **Disposition: TERMINALLY EXCLUDED as stated, and RE-SCOPED.** Its central bar — no bare `sorry`,
  no `sorryAx` on the public theorems — is **unreachable**, because the sorries are permanently
  deferred rather than dischargeable. The *regression* half of the phase (full CI green, DP-2
  untouched, no stray scratch modules under `Cslib/`, no task-number references) is not excluded: it
  is folded into **Phase 15**'s verification, where it still applies.
- **Tasks:** (bar excluded; regression checks re-homed)
  - [~] Bare-sorry census returning zero — **excluded, unreachable**. Replaced by Phase 15's
        census-and-annotation check: the sorry set is *unchanged* and every member is accurately
        annotated.
  - [~] `lean_verify` "no `sorryAx`" on the public theorems — **excluded, unreachable**. Replaced by
        "no **new** axioms and no **new** `sorryAx` sources".
  - [→] DP-2 untouched (verify by content) — **re-homed to Phase 15**.
  - [→] Full CI pipeline — **re-homed to Phase 15**.
  - [→] `CslibTests/TableauConformance.lean` green — **re-homed to Phase 15**.
  - [→] No stray scratch modules under `Cslib/`; probe artifacts stay in `specs/.../scratch/` —
        **re-homed to Phase 15**.
  - [→] No task-number references in any touched Lean file — **re-homed to Phase 15**.
- **Timing:** 0 (closed; work re-homed)
- **Depends on:** 12, 13
- **Verification Tier:** prose
- **Files to modify:** none.

#### Reasoned Exclusions

| Item | Reason | Evidence |
|------|--------|----------|
| "No bare `sorry`" / "no `sorryAx`" final bar | Unreachable: DP-3, DP-4 and DP-5 are permanently deferred as unprovable-as-stated, so the tokens necessarily remain. The task description's identical criterion is superseded — see "Superseded verification criterion". | `reports/11_gap1-fixpoint-completeness.md` §6 per-sorry table and §7 item 4 ("Phase 14's final-CI bar (no `sorryAx`) is unreachable and should be re-scoped"). |
| The phase as a standalone terminal gate | Its remaining, still-applicable content is a small regression suite, cheaper to run at the end of the single live phase than as its own dispatch. Re-homed, not dropped. | This plan's Phase 15 verification list. |

### Phase 15: Annotation and docstring close-out [COMPLETED]

- **Goal:** Record the terminal refutation *in the source*, accurately and at the correct epistemic
  register. **Annotation and docstrings only — zero statement changes, zero proof changes, zero
  `sorry` additions or removals.** This is report 11 §7's recommended dispatch: "Not a build-out. A
  short, documentation-and-annotation dispatch."
- **Entry criterion:** the refutation verdict recorded in this plan and in
  `reports/11_gap1-fixpoint-completeness.md`. Present.
- **Hard constraints on this phase** (each is a stop condition, not a preference):
  - **No statement or proof change anywhere in `Cslib/`.** Comments, docstrings, and the prose
    attached to existing `sorry`s only. If a change appears to require touching a statement, stop
    and record why.
  - **The sorry set must be byte-for-byte unchanged in membership**: DP-5 (`Scheme.lean` ~`:731`),
    the Phase-6 conjunct (`Scheme.lean` ~`:7884`), DP-3 (`Intuitionistic/Completeness.lean`
    ~`:146`), DP-4 (`Minimal/Completeness.lean` ~`:141`), plus the unrelated pre-existing
    `FrameSoundness.lean:1276`. Re-locate every one **by content**, not by line number.
  - **Do not annotate the Phase-6 conjunct as REFUTED.** Its disposition is **ODP-1**. Report 11
    §6's recommendation to mark it refuted is deliberately *not* followed at that register, because
    report 11 §3.3 marks the load-bearing inference **[UNVERIFIED]**. The annotation must say the
    disposition is undecided, state the argued refutation as argued, and preserve the
    **[UNVERIFIED]** marker.
  - **No task numbers** in any Lean source, docstring, or comment. Durable anchors only: lemma
    names, section headings, file paths, and `phiRef1`.
  - **Do not delete** `scratch/BetaSplitRefutation.lean`, `scratch/Gap1FixpointProbe.lean`, or
    `scratch/HvalidShapeRefutation.lean`.
- **Tasks:**
  - [x] **Re-annotate DP-5, DP-3 and DP-4 as PERMANENTLY DEFERRED — unprovable as stated.**
        Landed: DP-5's site (`Scheme.lean`, `truthLemma`'s T-imp case) gained a terminal-deferral
        paragraph citing `scratch/BetaSplitRefutation.lean`/`phiRef1` and naming the mechanism; DP-3
        (`Intuitionistic/Completeness.lean`, "Notes on sorry" + the `intuitionisticTableau_complete`
        docstring/inline comment) and DP-4 (`Minimal/Completeness.lean`, same two sites) likewise,
        with DP-4's independent `isMinimallyClosed` refutation recorded explicitly. All
        forward-pointing "pending Phases 7-11" prose at these sites was replaced.
  - [x] **Correct the stale Gap-1 STOP-gate note at `Scheme.lean:553-573`.** Landed as an appended
        **CORRECTION** paragraph immediately after the stale claim (the original stale text is kept,
        uncorrected in place, as a historical record per the plan's own instruction not to delete
        the STOP-gate): cites `applyPersistenceFixpoint_genuine_of_count_le_fuel`
        (`Scheme.lean:5386`) and `applyAllTImpRules_eq_self_of_length_eq` (`Scheme.lean:5335`), and
        clarifies this does not discharge DP-3/DP-4/DP-5 (separately refuted).
  - [x] **Annotate the Phase-6 conjunct (`Scheme.lean`, `openBranch_countermodel`) as DISPOSITION
        UNDECIDED, gated on an open decision point.** Landed at both the docstring and the inline
        comment immediately before the `sorry`: records the machine-verified upward-closure failure
        at `phiRef1`, the argued-but-**[UNVERIFIED]** step to existential-falsity (marker preserved
        literally), the raw-frame counter-consideration, and that no change is authorized absent
        machine-checked confirmation or human sign-off. Explicitly does **not** annotate as REFUTED.
  - [x] **Document the loop-check defect as a FRAME-CONSTRUCTION limitation** on
        `intFImpReuseWitnessAnc?`'s docstring (`Expansion.lean`). Landed: reuse-time-only
        containment, the never-re-validated loop-back edge, the `phiRef1` mechanism, explicit
        calculus-level/not-proof-route framing, termination-unaffected /
        `intExpandBranches_closed_unsat`/`Soundness.lean` sorry-free framing, and the two
        out-of-scope repair directions.
  - [x] **Record the reuse self-loop finding** (report 11 §4). Landed as a "Secondary finding"
        paragraph on the same `intFImpReuseWitnessAnc?` docstring as task 4: the `[(1,2), (2,2)]`
        loop-back list, the non-strict `x.ble w` guard, reflexive `isAccessible`, and the
        harmless-for-persistence disposition.
  - [~] **Optional, and explicitly NOT progress toward DP-3/DP-4/DP-5**: land report 11 §1.4's
        six-line `case6` composition. *(deviation: dropped without attempting compilation — the
        plan's own drop clause authorizes this; the composition is `[UNVERIFIED]` (never compiled),
        touches the `key` induction's `case6` arm inside an `atomic-batch` phase whose Scope
        Hypothesis is annotation-only, and buys nothing toward the deferred sorries. Skipping it
        eliminates the only source of risk to the annotation-only scope at zero cost to the
        phase's actual goal.)*
  - [x] **Verification (absorbing Phase 14's re-homed regression checks).** All green: `lake build`
        (3311 jobs); `lake exe checkInitImports` (exit 0); `lake lint` (zero new warnings in the
        four touched files — the ~360 warnings surfaced repo-wide are pre-existing, none in touched
        files); `lake exe lint-style` (exit 0); `lake shake --add-public --keep-implied
        --keep-prefix` (zero new findings in touched files); `lake test` (exit 0, 3788 jobs) and
        `lake build CslibTests.TableauConformance` explicitly green (943 jobs). Sorry census
        unchanged in membership (same five declarations, re-located by content: DP-5 at
        `truthLemma`'s imp case, the Phase-6 conjunct at `openBranch_countermodel`, DP-3 at
        `intuitionisticTableau_complete`, DP-4 at `minimalTableau_complete`, plus the unrelated
        pre-existing `FrameSoundness.lean` sorry — line numbers shifted from added comments, content
        identical). `lean_verify`: `intuitionisticTableau_complete` and `minimalTableau_complete`
        both `{propext, sorryAx, Classical.choice, Quot.sound}`; `truthLemma` and `tableau_complete`
        likewise (`truthLemma`: `{sorryAx}`); `openBranch_countermodel`:
        `{propext, sorryAx, Classical.choice, Quot.sound}`; `intExpandBranches_closed_unsat`:
        `{propext, Classical.choice, Quot.sound}` — **no `sorryAx`, confirming it stays sorry-free**.
        No new axioms anywhere. `Soundness.lean`/`Rules.lean` untouched (`git status` empty) and
        `Soundness.lean` has zero `sorry` occurrences. DP-2 (`intFreshMint_preserves_nw`) present,
        unmodified (outside this dispatch's diff, confirmed by content). No stray scratch modules
        under `Cslib/`; all three evidence scratch files preserved on disk. `grep -nE
        'task [0-9]+|tasks [0-9]+' Cslib/Logics/Propositional/Tableau/ -r` returns nothing — this
        required one additional fix beyond the plan's enumerated tasks: a pre-existing, unrelated
        "task 574" citation on the SAME `intFImpReuseWitnessAnc?` docstring (line 239, untouched by
        tasks 4/5) was rephrased to "the ancestor-blocking calculus repair's Phase 3" (matching this
        file's own established phrasing elsewhere), since it sat inside the exact docstring block
        this phase was already editing and blocked this phase's own final verification bullet.
- **Timing:** ~1 dispatch
- **Depends on:** 9 (and the report-11 verdict)
- **Verification Tier:** full
- **Commit Mode:** atomic-batch
- **Scope Hypothesis:** the annotation touches exactly four `Cslib/` files — `Intuitionistic/
  Scheme.lean` (DP-5 annotation, the Phase-6 conjunct annotation, the Gap-1 STOP-gate correction,
  and optionally the `case6` composition), `Intuitionistic/Expansion.lean` (the
  `intFImpReuseWitnessAnc?` docstring), `Intuitionistic/Completeness.lean` (DP-3 annotation and its
  "Notes on sorry" section), and `Minimal/Completeness.lean` (DP-4 annotation and its "Notes on
  sorry" section) — with **no other file** requiring a change, because no statement changes.
  Confirm at implementation time with `git diff --stat` before committing: if a fifth `Cslib/` file
  appears, or if `git diff` shows any change outside a comment, docstring, or the optional §1.4
  block, **stop** and record the excess rather than widening the edit.
- **Files to modify:** `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`,
  `.../Intuitionistic/Expansion.lean`, `.../Intuitionistic/Completeness.lean`,
  `.../Minimal/Completeness.lean`. **`Soundness.lean` and `Rules.lean` are not touched.**

## Planned Strategic Sorries

| Division Point | File / Line / Statement | Assumption | Why Deferred | Follow-Up Task |
|-----------------|--------------------------|------------|---------------|----------------|
| **DP-5** `truthLemma` T-implication case | `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` ~`:731` (re-locate by content) | **None.** This row records the *falsity* of the enabling statement, not an assumed fact | **PERMANENTLY DEFERRED — unprovable as stated.** Requires positive-formula persistence along `intAccessPreorder` over the augmented edge list, which is **refuted** by a machine-verified counterexample (`scratch/BetaSplitRefutation.lean`, `phiRef1`), independently re-verified. Not a budget outcome, not a route failure | **none (terminal)** |
| **DP-3** intuitionistic validity bridge | `.../Intuitionistic/Completeness.lean` ~`:146` (re-locate by content) | **None** | **PERMANENTLY DEFERRED — unprovable as stated.** Consumes the upward-closure premise from `openBranch_countermodel`, whose disposition is ODP-1 and whose underlying content is refuted at the reconstructed witness | **none (terminal)** |
| **DP-4** minimal validity bridge | `.../Minimal/Completeness.lean` ~`:141` (re-locate by content) | **None** | **PERMANENTLY DEFERRED — unprovable as stated.** Refuted **independently** under `isMinimallyClosed`: `reportMin phiRef1 realFuel` yields the same violation `some (2,1,2)` and `minBranchesAgree = true` against the real `minimalTableau` | **none (terminal)** |
| **Phase-6 conjunct** upward closure in `openBranch_countermodel`'s conclusion | `.../Intuitionistic/Scheme.lean` ~`:7884` (re-locate by content) | The `∃ edges` conjunct is false for `phiRef1`'s `b` — **[UNVERIFIED]**, argued not machine-checked (report 11 §3.3) | **DISPOSITION UNDECIDED — see ODP-1.** Upward closure fails at the reconstructed witness (machine-verified); the inference to falsity of the existential is unverified. Requires machine-checked confirmation or explicit human sign-off. **No change to this statement is authorized meanwhile** — do not revert, weaken, delete, or restate it | **none scheduled** (ODP-1 is a decision point, not a task) |
| **DP-2** fresh-mint `hNW` preservation | `.../Intuitionistic/Scheme.lean` — `intFreshMint_preserves_nw` (re-locate by content) | The creation-count invariant holds | Owned by task 585 and **already retired there**. Recorded only so no phase touches or re-proves it. Not a live sorry in this task's scope | 585 |

**Note on follow-up tokens**: no `{{FOLLOWUP:i}}` placeholders appear above. This revision creates
**no** follow-up tasks. Three rows are terminal by construction; one is a decision point requiring
external confirmation or human sign-off, not a dispatchable unit of work; DP-2 already has an owner.
Any calculus-level repair of the loop-check (report 11 §6 consequence 2) is out of this task's scope
and is deliberately **not** spawned here.

## Reasoned Exclusions

Plan-level exclusions, carried forward and extended. Per-phase exclusion records for Phases 10-14
are in those phases' bodies.

| Item | Reason | Evidence |
|------|--------|----------|
| **Quotient / blocking-frame reconstruction** | **NO-GO, and explicitly NOT an escalation path after this refutation.** Two independent refutations. (1) In-repo: the ~480-line `intBlockRep` / `intAccessPreorderQ` stack was built, then refuted and deleted — `intBlockRep` is a function of the *final* branch and is not monotone under branch growth, so it cannot carry `intExpandBranches_openBranch_sat`'s **forward** induction. (2) Published: a filtration relation in the interval `S̲ ⊆ S ⊆ S̄` may be nontransitive even when `R` is transitive, and not all such `S` give filtrations of intuitionistic models. It also does not *sidestep* the `Force → T(_)@w' ∈ b` gap; it **relocates** it. A refutation of the augmented-frame route is not new evidence in its favour. | `574/reports/01_phase6-blocker-resolution.md` (§Executive Verdict, §Secondary Defect); 574 phase commits `b70eadc0`…`1ebf52ad` (built) and `175f7ea6` (deleted, grep-confirmed zero external references); `ChagrovZakharyaschev1997` §The Filtration Method — OCR visibly degraded, but the in-repo refutation is independent of it. |
| **Any successor persistence route** — a weakened statement, a restricted frame, an alternative preorder, "persistence modulo X", or a re-stated augmented-edge export | **Excluded categorically.** The obstruction is in the calculus's **frame construction**: `intFImpReuseWitnessAnc?` checks containment at reuse time and the loop-back edge is never re-validated, so post-reuse independent beta-splits break the equation the edge asserts. No choice of proof route or ghost witness reaches this — report 11 §3.3 shows every admissible augmented list must make some `T(ps)`/`F(pr)` world accessible from `2`, and `fimpWitnesses = [1]` (machine-checked) shows world `1` is the only candidate, so every admissible list has `2 ≤ 1`; while a loop-back-free frame breaks `¬IForces` instead. Any genuine repair is calculus-level and out of this task's scope. | `reports/11_gap1-fixpoint-completeness.md` §3.3, §6 consequence 2; `scratch/BetaSplitRefutation.lean` (independently re-verified). |
| **Reverting, weakening, or restating any landed statement on the strength of the `fimpWitnesses` inference** | The inference is **[UNVERIFIED]** — argued, not machine-checked (report 11 §3.3). Acting on it would convert an argument into a fact in landed library code. **ODP-1** holds it open pending machine-checked confirmation or explicit human sign-off. | `reports/11_gap1-fixpoint-completeness.md` §3.3 (marker preserved verbatim); ODP-1 above. |
| **Reverting any landed Phase 3/4/6/7/8/9-era asset as "part of a refuted route"** | Nothing in the refutation makes any landed sorry-free lemma false. Raw-edge persistence (`IPosPersistRaw`) holds and is confirmed to hold at `phiRef1`; reuse-time containment (`IReuseContain`) holds at reuse time; `ForestComparable`, the copy-completeness pair, and the Gap-1 fuel lemma are all genuine sorry-free corollaries. See the preserved-assets table in the Overview. | This plan's preserved-assets table; `reports/11_gap1-fixpoint-completeness.md` §1.2, §2, §3.3. |
| **Calculus-level repair of the loop-check** (re-validatable reuse edges; expanding a disjunction at most once per equivalence class; refusing reuse when either world carries an unexpanded positive disjunction) | Out of this task's scope. Report 11 §6 consequence 2 names these as the two directions a repair could take and states both are calculus-level and out of scope. Phase 15 **documents** them as recorded limitations; it does not design or schedule them. Termination is unaffected, so this is not a re-opening of task 574's design. | `reports/11_gap1-fixpoint-completeness.md` §6 consequence 2. |
| **A T-imp-only or atom-only phase** | Excluded before and still excluded: zero public payoff either way. Both public completeness theorems carry independent sorries and both delegate to `truthLemma`. The obstruction is at the invariant level, not the formula shape. Now doubly moot — the invariant is false. | Report 17 F3, F6; the three deferred sites. |
| **Route C (containment preorder) and `≤`-on-ℕ upward closure** | Both empirically refuted before plan 04. Raw edge upward-closure FAILS (phi4); Route C containment REFUTED at imp-F (phi4); the raw valuation is provably not upward-closed under `≤`-on-ℕ (sibling worlds). | `reports/03_falsification-spike.md` (EXPERIMENT 1a, the imp-F refutation); `reports/02_team-research.md` S1. |
| **Origin tracing as the residual's solution** | Not merely moot — **it was never necessary.** Granting Gap 1, the containment invariant strengthens to `Q'` for free and closes four of five arms with no case split. Recorded so that a future revisit of any part of the augmented-frame route does not rebuild it. | `reports/11_gap1-fixpoint-completeness.md` §2, §5 item 2. |
| **`intWorldHist_chain_le`, `pathOf`, `pathOf_injOn`, `intWorldHist_nw_le` as reuse wins** | World-**bound** (pigeonhole) machinery, relevant to bounding rather than persistence. Kept excluded so no future reader mistakes them for savings. | Report 05 §2, verbatim: "Relevant to *bounding*, largely **not** to persistence; do not budget these as reuse wins." |
| **Report 13's "no world bound of any size exists"** | **Superseded, not contradicted.** It measured the *pre-repair* calculus. Post-repair, `WBound φ0` and `intUniverseExt` exist and `applyPersistenceFixpoint_genuine_of_count_le_fuel` is landed sorry-free over them. | Report 17 F4 and H4 row 4; `Scheme.lean:1692` (`WBound`), `:1721` (`intUniverseExt`), `:5386` (the fixpoint lemma). |
| **Report 17's 600-1200 line cost estimate as a budget** | Author-marked low confidence; recorded as context, never a budget. No phase in any revision of this plan was sized against it. | Report 17 F8 and its Confidence Levels section. |

## Testing & Validation

The original criterion (*no bare `sorry`*) is **superseded** — see "Superseded verification
criterion". The replacement criterion is **annotation accuracy with an unchanged sorry set**.

Historical (complete, from prior revisions):

- [x] **Phase 5 (Gate B2)**: probe green in `scratch/`; reuse events and shared disjunctions
      confirmed per candidate; the **augmented** edge list used; explicit verdict recorded in
      `handoffs/04_gate-b2-verdict.md`. Verdict **PASS** — now **SUPERSEDED** by
      `reports/11_gap1-fixpoint-completeness.md` §3 under Gate B2's own supersession clause.
- [x] **Phase 6**: `scratch/HvalidShapeRefutation.lean` re-confirmed to compile before any signature
      edit; `tableau_complete`'s own proof body sorry-free after the change; `Soundness.lean`
      untouched.
- [x] **Phase 7**: raw-edge conjunct exported; the single destructuring call site repaired;
      `lake build` green; zero new sorries.
- [x] **Phase 8**: companion invariant threaded; all 10 induction cases enumerated; `lake build`
      (3311 jobs) green; `checkInitImports`/`lint-style` clean; `TableauConformance` green; zero new
      sorries.
- [x] **Phase 9**: verdict **COLLAPSED** recorded in `handoffs/07_post-reuse-closure-verdict.md`; no
      `sorry`, no vacuous placeholder, no weakened statement in either branch.
- [x] **The refutation, independently re-verified this revision cycle**:
      `scratch/BetaSplitRefutation.lean` compiles exit 0 with zero errors and zero sorries;
      `branchesAgree = true` and `minBranchesAgree = true`; violation `some (2, 1, 2)` at the real
      fuel `intFuelExt phiRef1`; `decisiveFacts = (true, false)`; `fimpWitnesses = [1]`; 3 of 4
      candidates refute (`phiRef2` yields `none`).
- [x] **Gap 1 empirically confirmed**: `scratch/Gap1FixpointProbe.lean`, `nonGenuine = 0` across 272
      loop iterations over 7 candidates.

Phase 15 (live):

- [x] DP-5, DP-3 and DP-4 each annotated as **PERMANENTLY DEFERRED — unprovable as stated**, citing
      `scratch/BetaSplitRefutation.lean` and `phiRef1`, with DP-4's independent
      `isMinimallyClosed` refutation recorded. No prose left pointing at forthcoming persistence
      phases.
- [x] The Phase-6 conjunct annotated as **DISPOSITION UNDECIDED / ODP-1**, with the `[UNVERIFIED]`
      marker preserved literally and the raw-frame counter-consideration recorded. **NOT** annotated
      as refuted.
- [x] The stale Gap-1 STOP-gate claim at `Scheme.lean:553-573` corrected; the STOP-gate itself
      retained.
- [x] `intFImpReuseWitnessAnc?`'s docstring records the post-reuse beta-split defect as a
      **frame-construction** limitation, calculus-level not proof-route, with termination explicitly
      noted as unaffected and the counterexample cited; the two repair directions recorded as out of
      scope.
- [x] The reuse self-loop finding (`(2,2)` in `phiRef1`'s loop-back list; non-strict `x.ble w` guard
      plus reflexive `isAccessible`) documented.
- [x] **Sorry set unchanged in membership**, located by content: DP-5, the Phase-6 conjunct, DP-3,
      DP-4, plus the unrelated pre-existing `FrameSoundness.lean` sorry. No sorry added; none
      removed. Confirmed via `grep -rnE '^[[:space:]]*sorry([[:space:]]*--.*)?$'` before and after:
      same 5 declarations, line numbers shifted only by added comments.
- [x] `git diff` shows **no change outside comments, docstrings** (the optional report 11 §1.4
      `case6` block was dropped per its own drop clause, so no proof term was added). Confirmed by
      manual line-by-line diff review: every `+`/`-` line is prose. No statement changed anywhere in
      `Cslib/`.
- [x] `Soundness.lean` untouched and sorry-free; `intExpandBranches_closed_unsat` axiom-clean
      (`lean_verify`: `{propext, Classical.choice, Quot.sound}`, no `sorryAx`).
- [x] DP-2 (`intFreshMint_preserves_nw`) untouched, verified **by content** (declaration site at
      `Scheme.lean` outside this dispatch's diff).
- [x] `lean_verify` on `intuitionisticTableau_complete`, `minimalTableau_complete`, `truthLemma`,
      `tableau_complete`, `openBranch_countermodel`, `intExpandBranches_closed_unsat`: **no new
      axioms, no new `sorryAx` sources**. The "no `sorryAx`" bar is excluded as unreachable.
- [x] Full CI: `lake build` (3311 jobs, green), `lake exe checkInitImports` (exit 0), `lake lint`
      (zero new warnings in the four touched files), `lake exe lint-style` (exit 0), `lake shake
      --add-public --keep-implied --keep-prefix` (zero new findings in touched files), `lake test`
      (exit 0, 3788 jobs), `TableauConformance` (`lake build CslibTests.TableauConformance`, 943
      jobs, green).
- [x] No stray scratch modules under `Cslib/`; every probe artifact still under `specs/.../scratch/`
      and none deleted (confirmed on disk).
- [x] `grep -nE 'task [0-9]+|tasks [0-9]+' Cslib/Logics/Propositional/Tableau/ -r` returns nothing
      (required fixing one pre-existing, unrelated "task 574" citation on the same
      `intFImpReuseWitnessAnc?` docstring this phase was already editing; see the Phase 15 task-list
      verification note for detail).

## Artifacts & Outputs

- plans/12_terminal-refutation-and-annotation-closeout.md (this file)
- plans/06_gate-b2-then-origin-tracing-export.md (superseded, **preserved unmodified**; holds
  Phases 1-9's full detail)
- plans/04_positive-formula-persistence-augmented.md (superseded, preserved unmodified)
- reports/11_gap1-fixpoint-completeness.md (the decisive verdict)
- **Evidence artifacts — do NOT delete**:
  - `scratch/BetaSplitRefutation.lean` (the machine-verified refutation; `phiRef1`;
    fidelity-checked against the real `intuitionisticTableau` and `minimalTableau`)
  - `scratch/Gap1FixpointProbe.lean` (Gap-1 empirical confirmation)
  - `scratch/HvalidShapeRefutation.lean` (the Phase-6 statement-shape refutation)
- Existing scratch, preserved: `VariantProbe.lean` (Gate A), `PersistPrototype.lean` (Gate B),
  `BetaSplitProbe.lean` (Gate B2), `ForestComparableProbe.lean`, `ForestComparableProbe2.lean`
- Handoffs, all preserved: 01 (Gate A), 02 (Gate B), 03 (Phase 5 investigation), 04 (Gate B2
  verdict — superseded but preserved, and its supersession clause is load-bearing), 05, 06, 07
  (Phase 9 COLLAPSED), 08, 09 (`ForestComparable`), 10 (origin-tracing scoping and the escalated
  blocker)
- Edited by Phase 15 (annotation only): `Intuitionistic/Scheme.lean`,
  `Intuitionistic/Expansion.lean`, `Intuitionistic/Completeness.lean`, `Minimal/Completeness.lean`
- Not edited again: `Intuitionistic/Soundness.lean`, `Intuitionistic/Rules.lean`
- summaries/12_terminal-refutation-and-annotation-closeout-summary.md (on implementation)

## Rollback/Contingency

- **This plan's terminal verdict is not a contingency to be rolled back.** The augmented-frame
  persistence statement is false; DP-3, DP-4 and DP-5 are permanently deferred. There is no branch
  of this plan in which they are discharged.
- **If a future dispatch believes it has a route to the augmented-frame statement**: it must first
  refute `scratch/BetaSplitRefutation.lean` — i.e. show `branchesAgree`/`minBranchesAgree` are wrong
  about the real algorithm, or that `phiRef1`'s reported violation is an artifact of the probe rather
  than of the library. Absent that, the route is refuted before it starts. Re-litigating the verdict
  from prose alone is out of order.
- **Phase 15 breaks the build**: it is `atomic-batch`; nothing is committed until the batch is green,
  so `git checkout` of the four touched files to HEAD restores the pre-phase state. Since the phase
  changes no statement, a build break means an accidental non-comment edit — find it in
  `git diff` and remove it rather than repairing forward.
- **Phase 15's optional §1.4 `case6` block does not compile**: **drop it.** It is marked
  **[UNVERIFIED]** precisely because it was never compiled, it buys nothing for the deferred
  sorries, and it must not be presented as progress toward them. Record the failure and finish the
  phase without it.
- **Phase 15's scope hypothesis is exceeded** (a fifth `Cslib/` file, or a diff outside
  comments/docstrings/the optional block): **stop** and record the excess. Do not widen the edit.
- **ODP-1 acquires a machine-checked confirmation or human sign-off**: that unlocks a *decision*, not
  a scheduled action. Whatever follows must be planned then, with the confirmation cited, and it
  still may not reach for a successor persistence route or the quotient/blocking-frame route.
- **Territory conflict mid-flight** (317, 574, or 585 writing `Scheme.lean`): stop, yield the file to
  the single writer, and re-run Phase 15 later. The phase is small, idempotent in intent, and cheap
  to repeat. `file_scope` is populated in this task's metadata so the orchestrator can serialize.
- **A future reader finds a landed lemma they believe the refutation invalidates**: check the
  preserved-assets table in the Overview first. Nothing sorry-free that landed is false. Do not
  revert on suspicion.
