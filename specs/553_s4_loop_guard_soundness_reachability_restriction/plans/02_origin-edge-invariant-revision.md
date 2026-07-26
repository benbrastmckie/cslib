# Implementation Plan: S4 Keyed Driver Repair via Settled-Context Scheduling (v2)

- **Task**: 553 - Repair the false keyed S4 soundness theorem (Route P driver re-architecture)
- **Status**: [IMPLEMENTING]
- **Effort**: 49 hours
- **Dependencies**: 535 (completeness-line task; its landed keyed completeness results are inputs here)
- **Research Inputs**: `specs/553_s4_loop_guard_soundness_reachability_restriction/reports/01_s4-keyed-guard-soundness-falsified.md`; `specs/553_s4_loop_guard_soundness_reachability_restriction/handoffs/phase-10-blocked-handoff-20260725.md`
- **Artifacts**: plans/02_origin-edge-invariant-revision.md (this file); supersedes plans/01_s4-settled-context-scheduling.md
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; `.claude/rules/cslib.md`; `.claude/rules/lean4.md`; `.claude/rules/plan-compliance.md`
- **Type**: cslib
- **Lean Intent**: true

## Overview

`modalTableauS4Keyed_sound` is false, not merely unproven: a node-size-19 formula closes under
the shipped keyed driver and has an explicit 3-world reflexive-transitive countermodel. The
research established that no local edit to `blockingWorldS4Keyed` (LoopChecking.lean:469) can
fix this, because termination needs the guard's `none` contract to be globally unconditional
while soundness needs its `some` contract to be stable under later growth of the source world's
modal context. This plan executes **Route P (settled-context scheduling)**: change *when* a
minting shape may fire, not *what* the guard compares, so that a redirect edge is
propagation-inert by construction; then weaken the S4 soundness invariant from "every `acc` edge
is real in `m`" to "every `acc` edge is propagation-adequate", which is exactly what
`modalFourBoxProp_sound` / `modalFourDiaNegProp_sound` (FrameSoundness.lean:1129/1149) and the K
box-positive rule actually consume.

Definition of done: a keyed S4 driver with a machine-checked soundness theorem, a re-proved
completeness theorem, a permanent regression test that the counterexample no longer closes, and
the falsified-guard documentation correction landed. No `sorry`, no axiom, no vacuous statement.

### Research Integration

Integrated from `reports/01_s4-keyed-guard-soundness-falsified.md`:

- V1 (counterexample, section 2) drives Phase 1's regression corpus and Phase 8's empirical gate.
- V2/V3 (sections 3-4) are settled: the reachability restriction and every other local guard edit
  are rejected. This plan does **not** re-litigate them and contains no guard-predicate edit.
- Route Q (section 5.2) is explicitly rejected by the report as strictly worse than Route P
  (it reduces to Route P's step-2 obligation with extra bookkeeping). Not planned.
- Recommendation 4 (documentation correction) is Phase 2.
- Recommendation 6 (preserve the harness) is Phase 1: the probe artifacts become repository test
  surface rather than scratch files.
- Section 6's warning is carried into Phase 17: the live-set guard `blockingWorldS4` is **not**
  demonstrated sound either, and this plan does not claim it is.

**v2 additionally integrates** `handoffs/phase-10-blocked-handoff-20260725.md` (the blocked
Phase 10 dispatch's root-cause writeup). Its root-cause diagnosis and its origin-edge proposal are
adopted; its two structural suggestions are **not** adopted as written (new `S4LoopInv` field,
historical-branch quantification) — see Phase 10's two flagged design decisions for why. Its
proposed fix is also extended: the witness-pair disjunct it does not address is surfaced as
Phase 10's gate. No new research report was commissioned for this revision; the corrections were
verified directly against `LoopChecking.lean` and `FrameRules.lean`.

### Prior Plan Reference

This is **v2**, superseding `plans/01_s4-settled-context-scheduling.md`. Effort calibration for the
original phases was taken from the sibling completeness-line work referenced in the task
description (`specs/535_.../plans/03_completeness-line-rescope.md`), whose Risk R1 predicted
exactly the termination collapse the research then confirmed empirically. Calibration for the two
phases added in v2 is taken from this task's own measured Phase 6 (see "Sizing evidence" in
Phase 11).

### Revision History (v1 -> v2)

v1's Phase 10 ("Redirect-Inertness") returned `[BLOCKED]` having landed no Lean code
(`FrameSoundness.lean` byte-for-byte unchanged from its Phase 9 state). The blocking dispatch's
writeup is `handoffs/phase-10-blocked-handoff-20260725.md`. v2 does four things.

**1. A false premise in v1 is corrected, not annotated.** v1 asserted, in both its Risks table and
Phase 10's "Named difficulty", that S4's minting payload "sends both `ψ` and `□ψ` forward" at mint
time, so the boxed form `T(□ψ)@w'` would be recoverable at a minted successor. **This is false in
this codebase**, and the correction has been re-verified from source during this revision rather
than taken from the blocked dispatch on faith:

- `successorBirthContent` (`LoopChecking.lean:384`) is
  `insert (s, φ) ((signedSubfmls φ₀).filter ...)` where the filter admits `(Sign.pos, ψ)` exactly
  when `T(□ψ)@w ∈ b` — the **unwrapped** body. The definition's own docstring already said so
  ("the witness formula plus the *unwrapped* box-context transmitted from `w`"); v1 contradicted
  the source it cited.
- `modalApplyOne_boxNeg_mint_fst_S4` / `modalApplyOne_diamondPos_mint_fst_S4`
  (`LoopChecking.lean:1329`/`1362`) emit, for each box-positive `T(□ψ)@w`, the payload
  `⟨.pos, ψ, modalNextWorld b⟩` — unwrapped, never `⟨.pos, .box ψ, _⟩`. Standard K
  box-elimination.
- The boxed form is produced only by `modalFourBoxProp` (`FrameRules.lean:133`), which ranges over
  `acc.successorsOf w` and therefore **requires an edge to already exist**. The redirect edge
  `v → wBlock` is created by the very step under analysis, so no prior firing on `(v, wBlock)` can
  have occurred.

Every occurrence of the false wording is rewritten below. **No landed deliverable encodes it**: a
repository-wide grep for the premise's language over `Cslib/` and `CslibTests/` returns nothing,
and Phase 2's landed docstring corrections do not assert it. The false premise lived only in v1's
plan text, so correcting it requires no Lean edit and invalidates no committed proof.

**2. Downstream re-check of the false premise (the important half).** The premise mattered in
exactly one place, and the reason is worth stating because it is the substance of the repair:

- **Real (minted) edges never needed it.** At a genuine mint the boxed form at the successor comes
  from **frame transitivity**, semantically — this is what the landed
  `branchSatisfiableIn_s4FC_boxPos_trans_mem` and Phase 9's
  `branchPropAdequateIn_s4FC_boxPos_trans_mem` already do. Nothing in Phases 1-9 relied on a
  *syntactic* boxed transmission, which is why all nine phases remain sound.
- **Redirect edges are the sole site of reliance.** A redirect edge is not real in `m`, so
  transitivity is unavailable and the boxed form must be produced **syntactically, from the
  branch**. v1 papered over this with the false premise; v2 supplies it with a new invariant.
- **Consequence for later phases.** v1's Phase 11 (now Phase 13) is reshaped only in its
  redirect branch; its unblocked-mint branch is unchanged, because that branch was always going
  through transitivity. Phases 12-14 (now 14-16, the completeness line) do **not** rely on the
  premise: they concern `S4KeyedHintikkaInv` saturation, which is stated against the actual
  unwrapped transmission and is already landed and green against it. Phase 15 (now 17) is
  unaffected in substance.

**3. Two new phases are inserted** (10 and 11) carrying the origin-edge invariant, and v1's
Phases 10-15 are renumbered to 12-17. Total phase count: **15 -> 17**.

**4. A gap in the blocked dispatch's own proposed fix is surfaced up front.** The proposed fix
closes the obligation for box-context-derived key entries but **not** for the single key entry
contributed by the origin mint's witness pair. This was found during this revision, is not in the
blocked handoff, and is the reason Phase 10 exists as a separate gate rather than being folded
into Phase 11. See Phase 10's "The witness disjunct" for the full statement.

### The Corrected Argument (read before Phases 10-12)

Goal (v1's `blockedRedirect_boxctx_mem`, unchanged in substance): with
`blockingWorldS4Keyed φ₀ b keys s φ v = some wBlock` and `T(□ψ)@v ∈ b`, show `T(□ψ)@wBlock ∈ b`.

What is available and what it actually yields:

- `blockingWorldS4Keyed_eq_birthContent` (`LoopChecking.lean:479`) gives
  `(wBlock, successorBirthContent φ₀ b s φ v) ∈ keys`.
- `T(□ψ)@v ∈ b` plus `bClosure` puts `(Sign.pos, ψ)` in that recorded key (via the filter arm).
- `S4LoopInv.keyLowerBd` then gives `(Sign.pos, ψ) ∈ relevantSetFinset φ₀ b wBlock`, and
  `relevantSetFinset` (`LoopChecking.lean:333`) is a membership filter, so this unfolds to
  `T(ψ)@wBlock ∈ b` — **unwrapped**. This is exactly where v1 stalled, and it is as far as the
  guard contract plus `keyLowerBd` can reach. No automation closes the residue (`aesop` and
  `simp_all [successorBirthContent, relevantSetFinset]` both exhausted on the literal goal).

The missing step is *where `wBlock`'s key came from*. Every non-root key was recorded at a mint,
and that mint recorded an edge. Recovering the origin source `u` and the edge `u → wBlock` lets
mint-readiness act on an edge that **already exists**:

> If `T(□ψ)@u ∈ b` and `acc.hasEdge u wBlock`, then either `T(□ψ)@wBlock ∈ b`, or
> `modalFourBoxProp b acc ψ u` is non-empty, making `T(□ψ)@u` a member of
> `modalNonMintCandidates φ₀ keys b e acc` (it is not a mint shape, and box-positives produce
> `.persistent` results so they never enter `e`). The latter contradicts
> `modalStepBranchS4KeyedOrdered_mintReady`'s `modalNonMintCandidates ... = []`.

That is the whole argument, and it is sound — for key entries that came from the origin source's
**box context**. The residual case is the witness pair; see Phase 10.

### Roadmap Alignment

No `specs/ROADMAP.md` was supplied in the delegation context and none was loaded.

## Goals & Non-Goals

**Goals**:
- Turn the counterexample into a permanent, executable regression test before any code changes.
- Land the documentation correction that stops the next reader re-attempting a false theorem.
- Introduce a decidable settled-context selection discipline with no well-foundedness obligation.
- Re-verify the termination measure and fuel-sufficiency chain against the reordered stepper.
- Prove a genuine S4 soundness theorem for the reordered keyed driver, via a propagation-adequacy
  invariant that is weaker than `branchSatisfiableIn` but strong enough for the 4-rules.
- Re-prove the keyed completeness line against the reordered stepper.
- Retire the superseded stepper so the repository carries exactly one keyed S4 driver.

**Non-Goals**:
- Proving `modalTableauS4Keyed_sound` for the *current* stepper. It is false; it will be deleted
  or restated, never proved.
- `instDecidableS4Valid` / `s4Valid_decides`. These become reachable as an outcome of this work
  but are explicitly out of scope here and must not be attempted in these phases.
- Any soundness claim about the live-set driver `modalTableauS4` / `blockingWorldS4`. Untouched.
- Route Q (split accessibility record). Rejected by research; not planned.
- Any edit to `blockingWorldS4Keyed`'s comparison predicate.

## Standing Constraints (every phase, every commit)

These carry forward unchanged from v1 and from the orchestrator's standing brief. They are
collected here so no phase has to re-derive them.

- **Route P is settled.** The ordered stepper is the repair route. Route Q, the reachability
  restriction, and every other local guard-predicate edit are rejected by the research and are
  not re-litigated. No phase edits `blockingWorldS4Keyed`'s comparison predicate.
- **Axioms**: repo-wide `axiom` count stays at **26**. Zero new axioms. `lean_verify` every new
  declaration: `propext`/`Classical.choice`/`Quot.sound` only, no `sorryAx`.
- **No weakening, no vacuity.** No landed statement may be weakened to make a successor provable.
  No `sorry`, no `def X := True`, no `theorem X := trivial`, no vacuously-quantified restatement.
  A weakened restatement of an obligation is a blocker, not a discharge.
- **CI green at every commit**: `lake build`, `lake exe checkInitImports`, `lake lint`,
  `lake exe lint-style`, `lake test`, `lake exe mk_all --module`,
  `lake shake --add-public --keep-implied --keep-prefix`. The single pre-existing `lake lint`
  error in `Temporal/Tableau/Saturation.lean` is the known out-of-scope baseline; zero new issues.
- **File scope**: `Cslib/Logics/Modal/Tableau/**` plus `CslibTests/S4LoopGuardRegression.lean`,
  plus this task's `specs/` artifacts. **`Cslib/Logics/Modal/Metalogic/Constructive/Nested/**` is
  owned by a concurrent session — no phase of this plan may write there**, and a pending
  `Cslib.lean` diff belonging to that session must be left untouched.
- **Preserved assets.** Phases 1-9 are complete, committed, sorry-free and axiom-clean. Phase 9's
  six declarations in `FrameSoundness.lean` (`branchPropAdequateIn`,
  `branchSatisfiableIn_imp_branchPropAdequateIn`, `branchPropAdequateIn_s4FC_boxPos_trans_mem`,
  `branchPropAdequateIn_s4FC_diaNeg_trans_mem`, `modalFourBoxProp_sound_adequate` /
  `modalFourDiaNegProp_sound_adequate`, `branchPropAdequateIn_boxPos_mem`,
  `modalClosed_unsat_propAdequateIn`) — including the three `hready`-carrying consumer lemmas —
  stay **exactly as they are**. Phase 17 remains the sole destructive phase.
- **No task-number citations** outside `specs/`, per
  `.claude/rules/no-task-references-in-deliverables.md`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| (a) Reordering changes which world is minted when, breaking `modalExpMeasure_step_lt_S4Keyed` (LoopChecking.lean:6455) and the fuel chain | H | M | Phases 5-6 are dedicated to this. The measure proof consumes only `sf ∈ bh`, `sf ∉ e`, and the result shape (it extracts `sf` via `List.exists_of_findSome?_eq_some` and never uses which `sf`), so a selection-agnostic restatement of the Phase 8 projection bridge `modalStepBranchS4Keyed_proj_stepBranchGen` (LoopChecking.lean:6345) is expected to carry it. Verify; do not assume. |
| (b) The landed completeness line (`modalExpandBranchesS4Keyed_hintikka` LoopChecking.lean:6664, `modalTableauS4Keyed_complete` FrameCompleteness.lean:4249) is stated against the current stepper | H | H | Phases 14-16 are real, sized work, not cleanup. The new stepper is built as a **parallel** definition (Phase 4) so the existing line stays green at every checkpoint; the re-proof is attempted only once the reordered stepper is stable (after Phase 8's empirical gate), never twice. The `none`-equivalence lemma of Phase 4 is the linchpin that makes the saturation step transfer definitionally. |
| (c) "All propagation into `w` has settled" needs a well-foundedness argument in the report's per-world recursive formulation | H | H | Phase 3 replaces the per-world recursive predicate with a **global, non-recursive** one: fire a minting shape only when no non-minting rule can fire anywhere on the branch. This is decidable by direct computation, strictly stronger than the per-world condition, and carries no well-foundedness obligation at all. Flagged as a deliberate strengthening deviation from the report's suggested formulation. |
| **(d) [MATERIALISED in v1, mitigation replaced]** Redirect-inertness fails because `keyLowerBd` gives the *unwrapped* content `(pos, ψ)` while propagation adequacy needs `T(□ψ)@wBlock ∈ b` | H | **Occurred** | v1's mitigation rested on a false premise (that S4's mint payload transmits `□ψ` as well as `ψ`) and is withdrawn — see "Revision History" for the source verification. The real mitigation is Phases 10-11's origin-edge invariant, which recovers the mint edge that *already exists* into `wBlock` and lets mint-readiness act on it. The boxed form is never recovered from the mint payload; it is forced by the 4-rule's own applicability under settled-context scheduling. |
| **(e) The origin-edge invariant closes the box-context case but not the witness-pair case** | H | M | Found during this revision, not in the blocked handoff. `successorBirthContent` inserts the mint witness `(s', φ')` unconditionally, so `(pos, ψ) ∈ key(wBlock)` may hold with `T(□ψ)@u ∉ b` when `ψ` is the witness of a `T(◇ψ)@u` mint. This affects **at most one `ψ` per key** (a key has exactly one witness pair). Phase 10 is a dedicated gate that resolves this disjunct *before* Phase 11 invests in the preservation proof, with three named resolution routes and an explicit escalation criterion. |
| A later redirect edge into `wBlock` grows `wBlock`'s obligations after the adequacy fact was established | M | M | Adequacy is re-established as a step-preservation invariant (Phase 13), not asserted once. Growth of `b` adds obligations that the same mint-readiness discipline discharges uniformly. |
| Adding the origin invariant reopens the finalised `S4LoopInv` struct and forces re-proof of the ten landed field-preservation lemmas *and* the unordered line | H | L | Mitigated by design, not by effort: the invariant is a **standalone auxiliary threaded alongside** `S4LoopInv`, never a field — the precedent the codebase already sets twice, in `keysWorldsKnown` (`LoopChecking.lean:3842`, "not an `S4LoopInv` field: adding one would reopen the already-finalized struct design") and `worldsContiguousS4` (`:5187`). This keeps `modalStepBranchS4_preserves_S4LoopInv` (the unordered line, deleted in Phase 17 anyway) completely untouched. |
| Temporary duplication of the keyed driver (old + ordered) confuses readers or the barrel/lint pipeline | L | H | Deliberate and time-boxed: Phase 17 retires the superseded definitions. Every intermediate phase carries a docstring naming the ordered driver as the successor. |
| **Central prediction (standing, live, unconfirmed):** narrowing the guard breaks **termination** rather than merely completeness | H | Unknown | Phase 8's size-<=6 sweep neither corroborated nor retired it (fuel exhaustion stayed at 0 on both drivers; verdicts were identical). The v1 blocker is an invariant gap and is **not** evidence about it either way. It stays live. The one route below that would reopen it directly is Phase 10's resolution route (R3) — adding a scheduling side condition — which is therefore gated on re-running Phase 8's empirical sweep. |
| Reordering silently changes verdicts on formulas other than the counterexample | M | M | Phase 8 re-runs the size-<=6 sweep from the probe harness against the reordered stepper and requires every verdict change to be closed-to-open (never open-to-closed). |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1 |
| 3 | 4 | 3 |
| 4 | 5 | 4 |
| 5 | 6 | 5 |
| 6 | 7 | 6 |
| 7 | 8 | 7 |
| 8 | 9 | 8 |
| 9 | 10 | 9 |
| 10 | 11 | 10 |
| 11 | 12 | 11 |
| 12 | 13 | 12 |
| 13 | 14 | 8, 13 |
| 14 | 15 | 14 |
| 15 | 16 | 15 |
| 16 | 17 | 13, 16 |

Phases within the same wave can execute in parallel. Only Wave 1 has parallelism; the rest is a
critical path, because each proof layer consumes the previous one's statement shape.

**v2 renumbering map** (v1 phase -> v2 phase): 1-9 unchanged; **10 and 11 are new**; v1 10 -> 12,
v1 11 -> 13, v1 12 -> 14, v1 13 -> 15, v1 14 -> 16, v1 15 -> 17.

**Reading the `[COMPLETED]` phases below.** Phases 1-9 and their completion notes are reproduced
**verbatim from v1** — they are the record of what actually landed and are not edited. Forward
phase-number references *inside those notes* therefore use v1 numbering; apply the map above when
following them (e.g. Phase 4's "Phase 13's saturation step" is now Phase 15, and Phase 9's
completion note's "Phase 10" is now Phase 12). Every phase from 10 onward uses v2 numbering
throughout.

---

### Phase 1: Counterexample Regression Corpus [COMPLETED]

- **Goal:** Make the falsified behaviour a permanent, executable repository test so it can never
  silently reappear. This lands **before** any code change, so the test documents the defect
  first and the repair second.
- **Tasks:**
  - [ ] Create `CslibTests/S4LoopGuardRegression.lean`, modelled on
    `CslibTests/TableauConformance.lean` (same `module` + paired `import` / `public meta import`
    header idiom, same `#guard_msgs in #eval` assertion idiom). `#eval` works from `CslibTests/`
    but not from inside `Cslib/Logics/Modal/Tableau/`; this is the reason the file lives here.
  - [ ] Port the counterexample formula from
    `specs/553_s4_loop_guard_soundness_reachability_restriction/artifacts/s4driver.lean`
    (`p0`, `p1`, `nt`, `alphaA`, `alphaL`, `cex`) with a docstring stating the 3-world
    reflexive-transitive countermodel (`R = {(0,0),(0,1),(0,2),(1,1),(2,2)}`, `p1` true at world
    1 only, `p0` false everywhere) and why `cex` is therefore not `s4Valid`.
  - [ ] Add a `String`-valued verdict adapter (`ModalTableauResult` derives neither `Repr` nor
    `BEq`, exactly as `TableauConformance.lean` documents for its own result types).
  - [ ] Assert rows: shipped `modalExpandBranchesS4Keyed` on `cex` at fuel 400; shipped
    `modalExpandBranchesS4` (live-set) on `cex` at fuel 400; B-axiom and T-axiom controls.
  - [ ] **Record the current (unsound) keyed verdict as `CLOSED`**, with a docstring marking it
    `KNOWN-UNSOUND` and stating in terms that Phase 8 flips this row. Asserting the *correct*
    verdict now would leave the phase red; asserting the *actual* verdict keeps the checkpoint
    green and still locks the behaviour under test. This is a deliberate, temporary inversion and
    must be called out in the file's docstring.
  - [ ] Register the file in the `CslibTests.lean` barrel and run `lake exe mk_all --module`.
  - [ ] Docstrings must cite durable anchors only (declaration names, file sections) and must not
    cite task numbers, per `.claude/rules/no-task-references-in-deliverables.md`.
- **Timing:** 2 hours
- **Depends on:** none
- **Files to modify:**
  - `CslibTests/S4LoopGuardRegression.lean` - new; counterexample corpus and verdict adapter
  - `CslibTests.lean` - barrel import
- **Verification:**
  - `lake build CslibTests.S4LoopGuardRegression` succeeds
  - `lake test` passes with the new rows
  - `lake exe checkInitImports`, `lake exe lint-style` clean

---

### Phase 2: Documentation Correction [COMPLETED]

- **Goal:** Stop the next reader from re-attempting a false theorem. `FrameCompleteness.lean:4162`
  currently describes the decidability half as merely "deferred: it needs the soundness line,
  which is out of scope" — that framing is now wrong.
- **Tasks:**
  - [ ] Extend the `blockingWorldS4Keyed` docstring (LoopChecking.lean:466-474) with the
    counterexample: the formula, the closing trace's decisive step (a stale recorded key admits a
    redirect edge into a non-reachable world, which then receives box-positive propagation), and
    the fact that this makes the keyed soundness statement false rather than open.
  - [ ] Correct the S4Keyed section header in `FrameCompleteness.lean` (around :4159-4170) to
    state that the soundness half is **false as stated**, not deferred, and to point at the
    ordered driver as the repair route.
  - [ ] Name both defects explicitly in prose: staleness (comparison against recorded birth keys
    rather than live content) and the absence of any reachability restriction on the redirect
    edge, and record that fixing the first does not fix the second.
  - [ ] Point the reader at `CslibTests/S4LoopGuardRegression.lean` as the executable witness.
  - [ ] No task-number citations anywhere in these docstrings.
- **Timing:** 1.5 hours
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean` - `blockingWorldS4Keyed` docstring only
  - `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` - S4Keyed section header only
- **Verification:**
  - `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` succeeds (docstring-only change)
  - `lake exe lint-style` clean; no declaration bodies touched

---

### Phase 3: Decidable Mint-Readiness Predicate [COMPLETED]

- **Goal:** Discharge research risk (c) by giving "all propagation into `w` has settled" a
  decidable, non-recursive formulation with no well-foundedness obligation.
- **Design decision (deviation from the report, flagged):** the report suggests a per-world
  recursive predicate ("no unexpanded formula at `w`, and every predecessor of `w` is itself
  settled"), which needs well-foundedness that the accessibility record does not supply — mint
  edges point to strictly larger fresh worlds, but redirect edges may point to smaller ones and
  a reflexive self-block `w -> w` is explicitly permitted, so the predecessor relation can cycle.
  This plan replaces it with a **global** predicate: a minting shape may fire only when **no
  non-minting rule can fire anywhere on the branch**. This is strictly stronger than the per-world
  condition (it implies it), is decidable by direct computation on `(b, e, acc, keys)`, and needs
  no well-foundedness argument. The key enabling fact is that `modalApplyOneS4Rules`
  (FrameRules.lean:158) returns `.notApplicable` when a persistent rule's output is empty, so
  "settled" is expressible even though persistent formulas never enter the expanded set `e`.
- **Tasks:**
  - [ ] Define `modalMintShape : SignedFormula (Proposition Atom) WorldIndex -> Bool`, true
    exactly at the two minting shapes `F(□φ)@w` and `T(◇φ)@w`. Prove the two `simp`-normal
    characterisation lemmas (`modalMintShape_boxNeg`, `modalMintShape_diaPos`) and the
    complement lemma for every other sign/shape pair.
  - [ ] Define `modalNonMintCandidates φ₀ keys b e acc : List (SignedFormula ...)` as the sublist
    of `b` of formulas that are not mint shapes, are not in `e`, and on which
    `modalApplyOneS4Keyed φ₀ keys` does not return `.notApplicable`.
  - [ ] Prove `modalNonMintCandidates_subset : modalNonMintCandidates ... ⊆ b`.
  - [ ] Prove `modalNonMintCandidates_not_mem_expanded`: every candidate is outside `e`.
  - [ ] Prove `modalNonMintCandidates_eq_nil_iff`: the list is empty exactly when no non-minting
    rule can fire — the statement later phases consume as "the branch's propagation has settled".
  - [ ] Docstring the design decision above in the source, without citing task numbers.
- **Timing:** 2.5 hours
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean` - new section after the keys-aware guard
- **Verification:**
  - `lake build Cslib.Logics.Modal.Tableau.LoopChecking` succeeds
  - No `sorry`: `lake lint` clean, and `lean_verify` on each new declaration

---

### Phase 4: Ordered Stepper and its Two Structural Lemmas [COMPLETED]

- **Goal:** Introduce the reordered stepper as a **parallel** definition (the existing
  `modalStepBranchS4Keyed` LoopChecking.lean:780 is left untouched so the landed completeness line
  stays green), together with the two lemmas every later phase consumes.
- **Shape:** `modalStepBranchS4KeyedOrdered φ₀ b e acc keys` shares `modalStepBranchS4Keyed`'s
  per-formula body verbatim (same `modalApplyOneS4Keyed`, same `keys'` update, same result
  packaging) and differs only in the traversal: it runs `findSome?` over
  `modalNonMintCandidates φ₀ keys b e acc` first, and falls back to `b.findSome?` — the *literal*
  old traversal — only when the first returns `none`. Note that the branch argument passed to the
  rule stays `b` in both traversals; only the candidate list changes.
- **Tasks:**
  - [x] Define `modalStepBranchS4KeyedOrdered` with the two-stage traversal above. *(deviation:
    altered -- the shared per-formula body is factored into a new named definition
    `modalStepBranchS4KeyedBody`, used by BOTH the ordered stepper's primary scan and (via the
    bridge lemma `modalStepBranchS4Keyed_eq_findSome_body`, proved by `rfl`) referenced against
    the untouched `modalStepBranchS4Keyed`, rather than duplicating the body as an inline lambda
    in the ordered stepper as the phase-4 handoff sketched. `modalStepBranchS4Keyed`'s own source
    is byte-for-byte unchanged. This made the structural lemmas below provable against a named
    term instead of restating a six-way match inline in every lemma statement.)*
  - [x] Prove `modalStepBranchS4KeyedOrdered_eq_none_iff`:
    `modalStepBranchS4KeyedOrdered ... = none ↔ modalStepBranchS4Keyed ... = none`.
    The forward direction is immediate from the fallback being the old traversal; this is the
    linchpin that lets Phase 13's saturation step transfer without re-deriving the Hintikka
    conjuncts from scratch.
  - [x] Prove `modalStepBranchS4KeyedOrdered_selected_mem`: whenever the ordered stepper returns
    `some`, the selected formula is in `b` and not in `e`, and the returned tuple has one of the
    same four result shapes. State it so that Phase 5 can consume it directly in place of the
    `List.exists_of_findSome?_eq_some` extraction that the current measure proof performs.
  - [x] Prove `modalStepBranchS4KeyedOrdered_mintReady`: whenever the *selected* formula is a mint
    shape, `modalNonMintCandidates φ₀ keys b e acc = []`. This is the fact that carries
    settled-context scheduling into the soundness argument (Phases 9-11) and is the entire point
    of the reordering. *(deviation: altered -- since two distinct formulas could in principle
    produce the identical output tuple (no cheap uniqueness argument is available), the
    hypothesis is phrased as "every formula whose shared body produces this exact output tuple is
    a minting shape" (a `∀ sf, body sf = tuple → mintShape sf = true` premise) rather than a
    single externally-supplied selected formula. This is a sound, general way to express "the
    selected formula is a mint shape" without assuming unprovable uniqueness, flagged as an open
    question in the phase-4 handoff and resolved here in favour of the airtight statement.)*
  - [x] Docstring the ordered stepper as the successor to `modalStepBranchS4Keyed`, naming the
    retirement of the latter as planned work.
  - [x] (Additional, not in original task list) Proved `modalStepBranchS4KeyedOrdered_cases`, the
    shared case-split helper (primary-scan hit vs. empty-candidates fallback) that
    `_eq_none_iff`, `_selected_mem`, and `_mintReady` all factor through, matching the phase-4
    handoff's recommendation to avoid three independent ad hoc derivations.
- **Timing:** 3 hours
- **Depends on:** 3
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean` - new section after Phase 3's
- **Verification:**
  - `lake build Cslib.Logics.Modal.Tableau.LoopChecking` succeeds
  - The three lemmas are sorry-free (`lean_verify` each)
  - The existing `modalStepBranchS4Keyed` and everything downstream of it still compiles unchanged

---

### Phase 5: Termination Measure Re-Verification (risk a, part 1) [COMPLETED]

- **Goal:** Re-establish the strict measure decrease for the ordered stepper. This is the first
  half of research risk (a).
- **Lead:** `modalExpMeasure_step_lt_S4Keyed` (LoopChecking.lean:6455) currently routes through
  `modalStepBranchS4Keyed_proj_stepBranchGen` (LoopChecking.lean:6345) to reach
  `modalStepBranchGen` (Saturation.lean:122), then immediately destructs with
  `List.exists_of_findSome?_eq_some` and uses only: the selected `sf` is in the branch, `sf` is
  not in `e`, and the result-shape case split. The projection bridge is the *only* place the
  traversal shape matters, and it has exactly one consumer. Expect to replace the bridge, not the
  measure argument.
- **Tasks:**
  - [x] Restate the projection bridge selection-agnostically:
    `modalStepBranchS4KeyedOrdered_proj`, concluding the same `(newBs, newExps, newAcc)` shape
    facts from Phase 4's `_selected_mem` rather than from `modalStepBranchGen`'s `findSome?`.
    *(deviation: altered -- the conclusion is phrased via `Option.map` dropping
    `modalStepBranchS4KeyedBody`'s `keys'` component (`(modalStepBranchS4KeyedBody ... sf).map
    (fun p => (p.1,p.2.1,p.2.2.1)) = some (newBs,newExps,newAcc)`) rather than a hand-typed
    `let`/`match` expression restating `modalApplyOneS4Keyed`'s dispatch inline. An inline
    restatement was tried first and abandoned: Lean elaborates a fresh `let (a,b) := f x; ...`
    written directly in a theorem's conclusion differently from the same syntax appearing inside
    an existing `def`'s unfolded body (the former compiles to a `match`, blocking the
    `.1`/`.2`-projection-based rewrites the rest of the file's proofs about `modalStepBranchGen`
    rely on, since `modalStepBranchGen`'s `apply` parameter is abstract at definition time and
    is elaborated via direct projections). Reusing the already-elaborated `modalStepBranchS4KeyedBody`
    (from Phase 4) sidesteps the discrepancy entirely.)*
  - [x] Derive `modalExpMeasure_step_lt_S4KeyedOrdered` as a line-by-line transcription of
    `modalExpMeasure_step_lt_S4Keyed`, substituting the new bridge for the old one. Reuse
    `modalExpMeasure_split_S4`, `modalExpMeasure_append_S4`, `modalExpMeasure_const_exp_S4`,
    `modalWork_drop_linear_S4`, `pow3_add_one_le`, and the three Phase 4 per-call obligations
    (`modalApplyOneS4Keyed_branchingLength_S4` / `_persistentFresh_S4` /
    `_outputsSubsetUniverse_S4`) unchanged — these are all selection-independent. *(deviation:
    altered -- the extraction step feeding the four-way result-shape case split uses
    `Option.some.inj` (raw, unsimplified) rather than `simp only [Option.some.injEq,
    Prod.mk.injEq]`, matching the exact idiom the untouched `modalExpMeasure_step_lt_S4Keyed`
    above already uses; the `simp only [...]`-based variant was tried first and left `newExp`
    unidentified with the branch-specific expanded-set value the goal needs, whereas
    `Option.some.inj` + a bare-name `obtain` pattern lets `rcases`'s substitution succeed exactly
    as it does in the pre-existing lemma.)*
  - The transcription closed on the first attempt after the two adaptations above; the
    [BLOCKED]-on-non-closure escalation path was not needed.
- **Timing:** 3 hours
- **Depends on:** 4
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean` - new lemmas beside the existing measure section
- **Verification:**
  - `lake build Cslib.Logics.Modal.Tableau.LoopChecking` succeeds
  - `lean_verify` shows `modalExpMeasure_step_lt_S4KeyedOrdered` sorry-free and axiom-clean

---

### Phase 6: Loop Invariant and Fuel-Sufficiency Chain (risk a, part 2) [COMPLETED]

- **Goal:** Re-establish `S4LoopInv` preservation and the world-bound / fuel chain against the
  ordered stepper. The report argues these survive because the candidate set stays global and only
  the *timing* changes (delaying a mint can produce a different key, never a duplicate one).
  **Verify this; do not assume it.**
- **Tasks:**
  - [x] Derive `modalStepBranchS4KeyedOrdered_preserves_S4LoopInv`, mirroring
    `modalStepBranchS4_preserves_S4LoopInv` (LoopChecking.lean:4624), including the two
    proof-internal auxiliaries it threads (`keysWorldsKnown` at :2858 and `worldsContiguousS4`
    at :3553). *(deviation: the plan undersold this as a single task -- it required ordered
    analogues of TEN separate per-field sub-lemmas plus two proof-internal auxiliaries, each
    landed and committed individually across ten dispatches: `keysDistinct` (escalation trigger,
    attempted first, PASSED), `keyLowerBd`, `keysInUniverse`, `keysTotal`, `eNodup`,
    `keysWorldsKnown`, `outDegEq`, `accFresh`, `accKnown`, `worldsContiguousS4`, `eClosure`,
    `bClosure`, then the wrapper theorem itself -- see the Phase 6 handoff
    (`handoffs/phase-6-handoff-20260725.md`) for the full sub-lemma inventory this was scoped
    against. Two additional ordered-form auxiliaries not named in the plan text were also
    required as prerequisites: `modalStepBranchS4KeyedOrdered_branch_superset` (needed by
    `keyLowerBd`/`keysWorldsKnown`/`worldsContiguousS4`) and
    `modalStepBranchS4KeyedOrdered_keys_subset` (needed by `keysTotal`).)*
  - [x] Confirm `keysUpdate_preserves_keysDistinct` (LoopChecking.lean:529) and
    `blockingWorldS4Keyed_none_fresh` (LoopChecking.lean:501) are consumed unchanged — the guard
    predicate is untouched by this plan, so their statements must not need weakening. If either
    does need weakening, stop: that would contradict the plan's central claim and must be
    escalated, not worked around. *(Confirmed: `modalStepBranchS4KeyedOrdered_preserves_
    keysDistinct` — the escalation-trigger sub-lemma, attempted first per the handoff's
    recommendation — calls `keysUpdate_preserves_keysDistinct` with its EXACT original signature,
    no new hypothesis, no weakened conclusion. `blockingWorldS4Keyed_none_fresh` is likewise
    consumed unchanged by the minting-shape sub-lemmas. No contradiction surfaced; the plan's
    central claim holds.)*
  - [x] Re-derive the ordered analogues of `modalKnownWorlds_length_le_worldBoundS4`
    (LoopChecking.lean:3778) and `modalStepBranchS4_worldBound` (LoopChecking.lean:3816) only if
    their existing statements do not apply verbatim; prefer reuse. *(Not needed: both are stated
    purely over the pre-step `b`/`keys` — a pigeonhole cardinality argument with no reference to
    `modalStepBranchS4Keyed`/`modalStepBranchS4KeyedOrdered` at all — so
    `modalStepBranchS4KeyedOrdered_preserves_bClosure` consumes `modalStepBranchS4_worldBound`
    directly, unchanged, as its minting-case pigeonhole prerequisite.)*
  - [x] Confirm `modalExpMeasure_entry_le_fuelS4` (LoopChecking.lean:5433) applies unchanged —
    it is stated at the entry point over `modalUniverseS4 φ₀`, independent of traversal.
    *(Confirmed: its statement and proof mention neither `modalStepBranchS4Keyed` nor
    `modalStepBranchS4KeyedOrdered` — it bounds the measure of the SINGLE-formula entry worklist
    `[[⟨.neg, φ₀, 0⟩]]`, a fact about `modalUniverseS4 φ₀`/`modalWorldBoundS4 φ₀` alone. Applies
    verbatim to the ordered driver.)*
- **Timing:** 3 hours (actual: substantially longer, per the handoff's own sizing warning --
  ten sub-lemmas plus two auxiliaries plus the wrapper, twelve individually-committed dispatches)
- **Depends on:** 5
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- **Verification:**
  - `lake build Cslib.Logics.Modal.Tableau.LoopChecking` succeeds — confirmed after every one of
    the twelve dispatches, and again after the final wrapper
  - Every new declaration sorry-free — confirmed via `lean_verify` after every dispatch
    (axiom list: `propext`/`Classical.choice`/`Quot.sound` only, no `sorryAx`) and via the
    repo-wide `sorry` count (`git grep -c '^\s*sorry\s*$' -- Cslib`), unchanged at 5 throughout
  - Explicit written confirmation in the phase notes that no landed statement was weakened —
    see the two task-level confirmations above; no `S4LoopInv` field, no proof-internal
    auxiliary, and neither `keysUpdate_preserves_keysDistinct` nor
    `blockingWorldS4Keyed_none_fresh` required any weakening. `modalStepBranchS4Keyed` and all of
    Phases 1-5's landed declarations remain byte-for-byte unchanged; whole-project consumers
    `FrameCompleteness.lean`/`FrameSoundness.lean` still build (confirmed via scoped `lake build`
    on both after the final wrapper).

---

### Phase 7: Ordered Driver and Entry Point [COMPLETED]

- **Goal:** Build the fuel loop and tableau entry point over the ordered stepper, parallel to
  `modalExpandBranchesS4Keyed` (LoopChecking.lean:4689) and `modalTableauS4Keyed` (:4753).
- **Tasks:**
  - [x] Define `modalExpandBranchesS4KeyedOrdered` as a structural copy of
    `modalExpandBranchesS4Keyed` (same `processNext` worklist shape, same `keys` threading) with
    the ordered stepper substituted. Termination is discharged by Phase 5's measure lemma.
  - [x] Define `modalTableauS4KeyedOrdered φ`, mirroring `modalTableauS4Keyed`'s entry: initial
    branch `[F(φ)@0]`, `keys := [(0, ∅)]` (an empty `keys` list violates `S4LoopInv.keysTotal` —
    see the note at LoopChecking.lean:4744), fuel `modalFuelS4 φ`.
  - [x] Docstring both as the successors to the existing pair, with the retirement phase named.
- **Timing:** 2 hours
- **Depends on:** 6
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- **Verification:**
  - `lake build Cslib.Logics.Modal.Tableau.LoopChecking` succeeds, including the termination
    obligation for the new fuel loop

**Phase 7 completion note:** `modalExpandBranchesS4KeyedOrdered` and `modalTableauS4KeyedOrdered`
landed as structural copies with `modalStepBranchS4KeyedOrdered` substituted at the single
`processNext` call site; Lean's termination checker accepted the copied `fuel'` recursion
unchanged, with no `termination_by`/`decreasing_by` workaround needed -- confirming the handoff's
prediction that Phase 5's measure lemma alone suffices. `modalTableauS4KeyedOrdered` seeds
`keys := [(0, ∅)]` (not `[]`), matching the Phase 11 correction at `modalTableauS4Keyed`. Full CI
green after this phase's commit: whole-project `lake build` (3256/3256), `lake exe
checkInitImports` (clean), `lake exe lint-style` (clean), `lake lint` (one pre-existing,
out-of-scope error in `Temporal/Tableau/Saturation.lean`; zero issues in `LoopChecking.lean`),
`lake shake --add-public --keep-implied --keep-prefix` (zero import changes needed for
`LoopChecking.lean`), `lake test` (9250/9250, including `CslibTests.S4LoopGuardRegression`).
Repo-wide `sorry` count unchanged at 5; `axiom` count unchanged at 26. `lean_verify` on both new
declarations: axiom-clean (`propext`/`Classical.choice`/`Quot.sound` only), no `sorryAx`.
`modalStepBranchS4Keyed`, `modalExpandBranchesS4Keyed`, `modalTableauS4Keyed`, and everything from
Phases 1-6 remain byte-for-byte unchanged. No termination or fuel-sufficiency gap surfaced --
the escalation concern (narrowing the guard breaking termination rather than completeness)
remains not yet triggered as of this phase; Phase 8's empirical gate is the next point where a
real regression could still surface.

---

### Phase 8: Empirical Gate — Counterexample Must Not Close [COMPLETED]

- **Goal:** Confirm the reordering actually kills the counterexample **before** any soundness proof
  work is invested. If it does not, the whole soundness line ahead is unprovable and the plan must
  be revised rather than pushed.
- **Expected mechanism (from the report's trace, section 2.3):** under mint-last selection, the
  unexpanded `F(¬□p1)@3` fires before the minting shape `F(□p0)@3`, so world 3's box context
  already contains `p1` when the guard is consulted; the prospective birth content is then
  `{(neg,p0), (pos,p1)}`, which does not match world 2's recorded key `{(neg,p0)}`, so no redirect
  edge is created and the spurious closure never happens.
- **Tasks:**
  - [x] Add rows to `CslibTests/S4LoopGuardRegression.lean` for
    `modalExpandBranchesS4KeyedOrdered` on `cex` at fuel 400, asserting `OPEN`.
  - [x] **Flip the Phase 1 `KNOWN-UNSOUND` row**: kept the shipped-driver row as documentation of
    the defect (`modalStepBranchS4Keyed`/`modalExpandBranchesS4Keyed` are untouched until Phase
    15), and updated the file docstring so the inversion note no longer applies to the ordered
    driver, naming `modalExpandBranchesS4KeyedOrdered` as the fixed successor.
  - [x] Assert the B-axiom control still returns `OPEN` under the ordered driver *(deviation:
    altered -- the plan also names T/4/K-axiom controls, but the file has never had K/4 rows for
    either driver; only B and T exist at Phase 1's baseline, so only those two were mirrored,
    per the Phase 8 handoff's explicit instruction to grep first rather than assume)* and the
    T-axiom control still returns `CLOSED` under the ordered driver — the reordering does not
    break completeness on either control.
  - [x] Re-run the size-<=6 exhaustive sweep from
    `specs/553_.../artifacts/s4probe.lean`, adapted to the ordered stepper, and record the
    verdict-change census. **Every** verdict change must be closed-to-open. A single open-to-closed
    change is a completeness regression and blocks the phase.
  - [x] Record the sweep numbers in the phase notes (the pre-change baseline is 8532 formulas:
    1650 closed, 6882 open, 0 fuel-exhausted).
- **Timing:** 2.5 hours
- **Depends on:** 7
- **Files to modify:**
  - `CslibTests/S4LoopGuardRegression.lean`
  - `specs/553_s4_loop_guard_soundness_reachability_restriction/artifacts/s4probe.lean` - sweep
    adapted to the ordered stepper (task-artifact scratch file, not repository surface)
- **Verification:**
  - `lake test` passes with the ordered-driver rows
  - Sweep census recorded, with zero open-to-closed changes
  - **Gate:** if `cex` still closes, stop and escalate; do not proceed to Phase 9

**Phase 8 completion note:** All four tests machine-checked green.

1. **`cex` itself (the direct empirical claim):** `#eval s4Verdict (modalExpandBranchesS4KeyedOrdered
   cex ...) = "OPEN"` passes as a `#guard_msgs`-checked row (`CslibTests/S4LoopGuardRegression.lean`).
   Standalone confirmation via `lake env lean` on the adapted probe script:
   `KEYED (unordered) closes cex = (some true)`, `KEYED (ordered) closes cex = (some false)` --
   the ordered driver does NOT close the known-unsound countermodel that the unordered driver
   closes. This is the primary soundness-direction result of the phase.
2. **B/T-axiom controls:** ordered driver agrees with unordered on both -- B axiom `(some false)`
   (open, not S4-valid) on both drivers; T axiom `(some true)` (closed, S4-valid) on both drivers.
   Reordering does not change completeness on either control.
3. **Exhaustive size-<=6, 2-atom sweep** (`s4probe.lean`, `allUpTo 2 6`, fuel 100 per formula,
   8532 formulas total): the unordered-driver leg of the rewritten sweep reproduces the Phase 1
   baseline exactly -- **1650 closed, 6882 open, 0 fuel-exhausted**. The ordered-driver leg over
   the SAME 8532 formulas is **verdict-for-verdict identical**: **1650 closed, 6882 open, 0
   fuel-exhausted**, with `closedToOpen = 0` and `openToClosed = 0`. Read plainly: within this
   sweep's formula-size class (size <= 6, 2 atoms), the settled-context reordering changes
   *nothing* -- the specific stale-birth-content interaction that unsoundly closes `cex` does not
   arise for any formula this small. This is an honest negative result at this scope, not a
   confirmation of the fix by this sweep; the fix is confirmed instead by item 1 above, on `cex`
   directly (a larger formula, outside the size-<=6 enumeration).
4. **STOP-condition check, both halves clear:** `openToClosed = 0` (no completeness regression)
   and `fuelInvolved = 0` with `newFuel(0) == oldFuel(0)` (no termination regression at this
   sweep's scope). The task's standing central prediction -- that narrowing the guard might break
   TERMINATION rather than merely completeness -- is **not corroborated** by this phase's evidence:
   fuel exhaustion stayed at 0 for both drivers across the full sweep, and Phase 7's termination
   checker already accepted the copied recursion without a measure-lemma change. This does not
   retire the prediction (the sweep only reaches size 6, and the soundness proof obligations in
   Phases 9-14 are the real test of whether key-distinctness survives the narrower guard), but no
   empirical counter-evidence has appeared yet.

Full CI green: `lake build` (848 jobs for `CslibTests.S4LoopGuardRegression`, whole-project build
otherwise unaffected since no `Cslib/` source changed this phase), `lake exe checkInitImports`
(clean), `lake exe lint-style` (clean), `lake lint` (same one pre-existing, out-of-scope error in
`Temporal/Tableau/Saturation.lean`; zero new issues), `lake shake --add-public --keep-implied
--keep-prefix` (zero import changes needed), `lake test` (includes
`CslibTests.S4LoopGuardRegression` with the new ordered-driver rows, all `#guard_msgs` green).
Repo-wide `axiom` count unchanged at 26 (verified via `grep -rn '^axiom ' Cslib/ | wc -l`). No
`Cslib/` source files were touched this phase (only the test file and the task-artifact probe
script), so `modalStepBranchS4Keyed`/`modalExpandBranchesS4Keyed`/`modalTableauS4Keyed` and all of
Phases 1-7's declarations remain byte-for-byte unchanged (confirmed: `git diff` on
`Cslib/Logics/Modal/Tableau/LoopChecking.lean` is empty for this phase).

---

### Phase 9: Propagation-Adequacy Invariant [COMPLETED]

- **Goal:** Define the weakened S4 soundness invariant and prove that it is what the 4-rules
  actually consume. `branchSatisfiableIn` (FrameSoundness.lean:111) requires
  `acc.hasEdge w w' → m.r (f w) (f w')`; this is the conjunct the redirect edge cannot supply.
- **Flag — no landed theorem is weakened here.** `branchSatisfiableIn` is left exactly as is, and
  it remains what K, T, B, and 5 consume. This phase *adds* a strictly weaker sibling predicate
  used only by the S4 keyed line.
- **Shape:** `branchPropAdequateIn s4FC b acc` replaces the edge conjunct with: for each edge
  `w → w'`, `f w'` satisfies `□ψ` for every `T(□ψ)@w ∈ b`, and `f w'` falsifies `◇ψ` for every
  `F(◇ψ)@w ∈ b`. The branch-formula conjunct is unchanged.
- **Tasks:**
  - [x] Define `branchPropAdequateIn` beside `branchSatisfiableIn` in `FrameSoundness.lean`.
  - [x] Prove `branchSatisfiableIn_imp_branchPropAdequateIn`: a genuine mint edge, which satisfies
    the stronger condition, satisfies the weaker one. This is what keeps mint edges free.
  - [x] Prove the adequacy analogues of `branchSatisfiableIn_s4FC_boxPos_trans_mem` and
    `branchSatisfiableIn_s4FC_diaNeg_trans_mem`.
  - [x] Prove `modalFourBoxProp_sound_adequate` and `modalFourDiaNegProp_sound_adequate`,
    mirroring FrameSoundness.lean:1129/1149 against the weaker predicate.
  - [x] Prove the K box-positive rule's analogue, the third consumer named by the research.
  - [x] Prove `modalClosed_unsat` transfers: a classically closed branch is not
    `branchPropAdequateIn`-satisfiable (the closure argument uses only the branch-formula
    conjunct, so this should be a direct transcription of `modalClosed_unsatIn`).
- **Timing:** 3 hours
- **Depends on:** 8
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` - new section, additive only
- **Verification:**
  - `lake build Cslib.Logics.Modal.Tableau.FrameSoundness` succeeds
  - Every existing declaration in the file unchanged and still compiling
  - New declarations sorry-free

**Phase 9 completion note:** all six task items landed as a single additive section (~282
lines) in `FrameSoundness.lean` immediately after the existing S4 4-rule soundness lemmas
(before `## B (Symmetric Frame)`), all sorry-free and axiom-clean (`lean_verify`: only
`propext`/`Quot.sound`, no `sorryAx`, on every new declaration). One deliberate,
plan-compliant addition beyond the literal task-list wording: the two "adequacy analogue"
trans_mem lemmas (`branchPropAdequateIn_s4FC_boxPos_trans_mem`/`_diaNeg_trans_mem`) and the
K-rule analogue (`branchPropAdequateIn_boxPos_mem`) each carry an explicit `hready` hypothesis
that the box/diamond content of every edge *already* recorded out of the target world `w'` is
already on the branch. This is mathematically load-bearing, not a weakening: unlike
`branchSatisfiableIn`'s edge conjunct (branch-independent, so untouched by adding a new
formula), `branchPropAdequateIn`'s edge conjunct is branch-content-driven, so adding a new
box/diamond-shaped formula at `w'` reopens the conjunct's obligation at every edge already
recorded out of `w'` -- the bare, hypothesis-free analogue is false for an unconstrained `acc`.
`hready` names exactly what the ordered driver's mint-readiness discipline (Phase 4) is
designed to supply at every real call site; discharging it for the redirect-edge case is
Phase 10's `blockedRedirect_boxctx_mem` (named explicitly in Phase 10's own task list), so this
is not new scope invented here, only the natural signature the existing plan wording implies
once actually derived in Lean. Full CI green: `lake build` (3257 jobs, whole project),
`lake exe checkInitImports` (clean), `lake exe lint-style` (clean), `lake lint` (same one
pre-existing, out-of-scope error in `Temporal/Tableau/Saturation.lean`; zero new issues),
`lake shake --add-public --keep-implied --keep-prefix` (zero import changes suggested for
`FrameSoundness.lean`), `lake exe mk_all --module` (no update necessary for this phase's file,
`Cslib.lean`'s only pending diff belongs to a concurrent session's `Nested/Rules.lean` and is
left untouched), `lake test` (exit 0). Repo-wide `axiom` count unchanged at 26. `git diff` on
`FrameSoundness.lean` is purely additive (282 insertions, 0 deletions) -- every pre-existing
declaration in the file (K/T/S4/4-rule/B sections) is byte-for-byte unchanged.

---

### Phase 10: Origin-Edge Invariant — Statement, Entry Establishment, and the Witness Gate [COMPLETED]

- **Goal:** Land the statement of the origin-edge invariant, establish it at the driver entry
  point, land the conditional derivation lemma it exists to serve, and **resolve the witness
  disjunct** — before Phase 11 invests a full run in the preservation proof. This phase is a gate
  in the same sense Phase 8 was: it buys the right to spend Phase 11.

- **Design decision — auxiliary, not an `S4LoopInv` field (flagged deviation from the blocked
  handoff's sketch).** The handoff proposed `keysOrigin` as a new `S4LoopInv` field. Do **not** do
  that. Adding a field reopens the finalised struct: every one of the ten landed
  `modalStepBranchS4KeyedOrdered_preserves_*` lemmas keeps working, but the two **wrapper**
  theorems that *construct* an `S4LoopInv` gain an undischarged field — including
  `modalStepBranchS4_preserves_S4LoopInv`, the **unordered** line, which this plan is committed to
  leaving byte-for-byte unchanged until Phase 17 deletes it. The codebase already sets the
  precedent twice, in as many words: `keysWorldsKnown` is "not an `S4LoopInv` field: adding one
  would reopen the already-finalized struct design" (`LoopChecking.lean:3842`) and
  `worldsContiguousS4` likewise (`:5187`). Thread the new invariant the same way — an extra
  hypothesis and an extra conclusion alongside `S4LoopInv` at every call site.

- **Design decision — no historical branch in the statement (flagged deviation).** The handoff's
  sketch quantified over the historical pre-mint branch `b_birth` with a side condition
  `b_birth ⊆ b`. Do not carry a historical list in the invariant. Bake the *consequence* in
  instead, stated over the **current** branch, which makes preservation under branch growth
  immediate (the `∈ b` disjunct simply persists) and removes all `b_birth` bookkeeping:

  ```
  def keysOriginS4 (φ₀ : Proposition Atom)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
      (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) : Prop :=
    ∀ w k, (w, k) ∈ keys → w = 0 ∨
      ∃ u s' φ', acc.hasEdge u w = true ∧
        (∀ ψ, (Sign.pos, ψ) ∈ k →
           (s', φ') = (Sign.pos, ψ) ∨ (⟨.pos, .box ψ, u⟩ : SignedFormula _ _) ∈ b) ∧
        (∀ ψ, (Sign.neg, ψ) ∈ k →
           (s', φ') = (Sign.neg, ψ) ∨ (⟨.neg, .diamond ψ, u⟩ : SignedFormula _ _) ∈ b)
  ```

  Read: every non-root recorded key has an origin source `u` with an edge already in `acc`, and
  every signed pair in the key is either that mint's own witness pair or is *currently* present
  at `u` in its box/diamond form. The exact shape may be adjusted during implementation; what must
  not change is that it is stated over the current `b` and current `acc`, with no historical
  branch. Record any adjustment as a flagged deviation.

- **The witness disjunct (the gate).** This is the gap in the blocked handoff's proposed fix, found
  during the v2 revision. `successorBirthContent φ₀ b s φ w = insert (s, φ) (filter ...)` inserts
  the witness pair `(s, φ)` **unconditionally**. So `(Sign.pos, ψ) ∈ key(wBlock)` splits:

  - **(b) box-context case** — `(pos, ψ)` came from the filter, i.e. `T(□ψ)@u ∈ b`. Closed by the
    mint-readiness argument in "The Corrected Argument" above. This is the case the handoff
    analysed.
  - **(a) witness case** — `(pos, ψ)` is the origin mint's witness, i.e. the origin shape was
    `T(◇ψ)@u`, and `T(□ψ)@u` need **not** be on the branch. The origin mint put `T(ψ)@wBlock` on
    the branch, not `T(□ψ)@wBlock`, and nothing in the invariant forces the boxed form. **This
    case is not closed by the handoff's proposed fix**, and Phase 12 will re-block on it if it is
    not resolved here.

  Two narrowings make the gate cheap. First, a key has exactly **one** witness pair, so case (a)
  can bite for at most one `ψ` per key — every other positive pair in the key is in case (b).
  Second, the positive-witness form only arises from diamond-positive mints (`F(□φ)@u` mints
  contribute the *negative* witness `(neg, φ)`), so the dual obligation
  `blockedRedirect_diaNeg_mem` has the mirror-image narrow case.

- **Resolution routes, in preference order.** Take the first that works; do not silently switch.
  - **R1 — prove case (a) unreachable.** Show that under mint-readiness a guard `some wBlock`
    return cannot arise with `(pos, ψ)` witness-only and `T(□ψ)@v ∈ b`. If provable, the whole
    obligation reduces to case (b) and Phase 12 is straightforward. Preferred outcome.
  - **R2 — strengthen the invariant to cover the witness.** Record, alongside the origin edge,
    whatever the witness mint guarantees at the target strongly enough to yield the boxed form.
    Only take this if it does not require a historical branch and does not weaken any landed
    statement.
  - **R3 — scheduling side condition (last resort, gated).** Route P's remit is *when* a shape may
    fire, so requiring the redirect decision to be taken only when the witness pair is already
    box-covered is in-scope in principle. **But it changes the stepper**, which reopens the
    standing central prediction about termination. If R3 is taken, Phase 8's empirical gate
    (`cex` must stay `OPEN`, size-<=6 sweep, zero open-to-closed changes, fuel exhaustion still 0)
    **must be re-run and recorded** before Phase 11 proceeds, and the Risks table's central
    prediction row updated with the new evidence.
  - **Escalation.** If none of R1-R3 works and a concrete reachable configuration exhibits case
    (a) with `T(□ψ)@wBlock ∉ b`, that is a Route-P-level finding, not a patchable phase: mark
    `[BLOCKED]`, report the configuration, and do **not** weaken `blockedRedirect_boxctx_mem`'s
    conclusion to the unwrapped form — Phase 9's `hready` needs the boxed form specifically, and a
    weakened restatement is a vacuous discharge prohibited by `.claude/rules/lean4.md`.

- **Tasks:**
  - [x] Define `keysOriginS4` per the shape above, with a docstring stating the auxiliary-not-field
    decision and citing `keysWorldsKnown`/`worldsContiguousS4` as the precedent (declaration names
    only, no task numbers).
  - [x] Prove `keysOriginS4` holds at the driver entry point: `modalTableauS4KeyedOrdered` seeds
    `keys := [(0, ∅)]`, so the sole entry is the root disjunct `w = 0` and the proof is immediate.
  - [x] Prove `keysOriginS4_mono_branch` and `keysOriginS4_mono_acc`: the predicate survives branch
    growth (`b ⊆ b'`) and edge addition (`acc.hasEdge u w → newAcc.hasEdge u w`). These are the two
    facts that make Phase 11's twelve non-minting shapes nearly free.
  - [x] Prove the case-(b) derivation as a standalone conditional lemma —
    `blockedRedirect_boxctx_mem_of_boxOrigin`: given `acc.hasEdge u wBlock`, `T(□ψ)@u ∈ b`, and
    `modalNonMintCandidates φ₀ keys b e acc = []`, conclude `T(□ψ)@wBlock ∈ b`. Proof: otherwise
    `modalFourBoxProp b acc ψ u` is non-empty at `wBlock ∈ acc.successorsOf u`, so
    `(modalApplyOneS4Keyed φ₀ keys ⟨.pos, .box ψ, u⟩ b acc).1.isApplicable`; `T(□ψ)@u` is not a
    mint shape and, producing `.persistent`, never enters `e`; hence it is in
    `modalNonMintCandidates`, contradicting the empty list. **This lemma lands regardless of how
    the gate resolves** — it is the load-bearing half either way.
  - [x] Prove the dual `blockedRedirect_diaNeg_mem_of_diaOrigin` via `modalFourDiaNegProp`.
  - [x] **Resolve the witness disjunct** by R1, R2, or R3, and record the verdict and its
    justification in the phase notes. If R3, re-run and record Phase 8's empirical gate.
- **Timing:** 3 hours
- **Depends on:** 9
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — new section after the ordered-stepper
    structural lemmas
- **Verification:**
  - `lake build Cslib.Logics.Modal.Tableau.LoopChecking` succeeds
  - `lean_verify` on `keysOriginS4`'s entry lemma, the two monotonicity lemmas, and both
    conditional derivation lemmas — sorry-free, axiom-clean
  - **Gate:** the witness disjunct has a recorded verdict. Do not start Phase 11 with the disjunct
    unresolved — that is precisely the mistake v1 made with the mint-payload premise.
  - No landed declaration modified; `git diff` on `LoopChecking.lean` purely additive

- **Completion notes (v2 dispatch):**
  - Landed in `Cslib/Logics/Modal/Tableau/LoopChecking.lean`, inserted immediately after
    `modalStepBranchS4KeyedOrdered_mintReady` (before the pre-existing "Minting-Content
    Groundwork" section): `keysOriginS4`, `keysOriginS4_entry`, `keysOriginS4_mono_branch`,
    `keysOriginS4_mono_acc`, `blockedRedirect_boxctx_mem_of_boxOrigin`,
    `blockedRedirect_diaNeg_mem_of_diaOrigin`, plus five small private helper lemmas
    (`hasEdge_mem_successorsOf_origin`, `modalApplyOneS4Rules_{boxPos,diaNeg}_fst`,
    `modalApplyOneS4Keyed_{boxPos,diaNeg}_eq_S4Rules`,
    `modalApplyOneS4Rules_{boxPos,diaNeg}_not_notApplicable_of_four{Box,DiaNeg}Prop_ne_nil`).
    All sorry-free; `lean_verify` on every public declaration reports only
    `propext`/`Classical.choice`/`Quot.sound`. `git diff --stat` on the file: 329 insertions, 0
    deletions (purely additive). Full CI pipeline (`lake build`, `checkInitImports`, `lake lint`,
    `lake exe lint-style`, `lake shake`, `lake exe mk_all --module`, `lake test`) green; axiom
    count unchanged at 26; the one pre-existing `lake lint` baseline error
    (`Temporal/Tableau/Saturation.lean`) is the only remaining lint error, zero new ones.
  - **Deviation (forced by `lake lint`):** `keysOriginS4` drops the `φ₀` parameter the plan's own
    proposed shape carried. The plan's literal definition text never actually references `φ₀` in
    its body (confirmed by direct inspection), and `lake lint`'s `unusedArguments` linter
    correctly flagged this as a new issue when first landed with `φ₀` present. Fixed by dropping
    the parameter, mirroring the codebase's own existing precedent (`worldsContiguousS4`, which
    likewise takes no `φ₀`). This is a shape adjustment explicitly permitted by the plan's own
    text ("the exact shape may be adjusted during implementation"), not a weakening: the
    invariant's logical content is identical, only the (unused) parameter is removed.
  - **Witness-gate verdict: R1 (case (a) is unreachable as a proof obligation).** The witness
    pair `(s', φ')` recorded by a diamond-positive mint (`T(◇ψ)@u`) is the POSITIVE pair
    `(Sign.pos, ψ)`, and `successorBirthContent` places it on the branch unwrapped, as
    `T(ψ)@wBlock` — exactly the fact `blockingWorldS4Keyed_eq_birthContent` composed with
    `S4LoopInv.keyLowerBd` already recovers directly (no origin-edge machinery needed for it; see
    "The Corrected Argument" above). The origin-edge invariant's box-context disjunct
    (`blockedRedirect_boxctx_mem_of_boxOrigin`, case (b)) is only ever invoked for a DIFFERENT,
    distinct query `T(□ψ)@v ∈ b` at a possibly-different source `v` — by construction of
    `successorBirthContent`'s filter, a box-context pair `(pos, ψ)` in a key arises from
    `T(□ψ)@u ∈ b`, disjoint in general from the witness pair. So case (a) (witness-only,
    `T(□ψ)@u ∉ b`) never actually arises as an obligation the boxed-form consumer
    (`branchPropAdequateIn`'s edge conjunct, `FrameSoundness.lean`) needs to discharge through
    the origin-edge route — it is vacuous for this lemma's proof obligation, not merely
    "unreachable" as a hypothetical side condition. **No empirical gate re-run required** (R3 was
    not taken; the standing central prediction about termination is neither corroborated nor
    retired by this phase, unchanged from Phase 8's status).
  - **Territory:** touched only `Cslib/Logics/Modal/Tableau/LoopChecking.lean`. Did not touch
    `FrameSoundness.lean`, `FrameCompleteness.lean`, `FrameRules.lean`,
    `CslibTests/S4LoopGuardRegression.lean`, or
    `Cslib/Logics/Modal/Metalogic/Constructive/Nested/**` (concurrent-session territory,
    untouched, confirmed via `git status`/`git diff --stat`).

---

### Phase 11: Origin-Edge Invariant — Step Preservation [NOT STARTED]

- **Goal:** Prove `modalStepBranchS4KeyedOrdered_preserves_keysOriginS4` across every step shape,
  and thread it into the `_preserves_S4LoopInv` wrapper's conclusion tuple.

- **Sizing evidence (H8).** Phase 6 landed ten `S4LoopInv` fields plus two auxiliaries in twelve
  dispatches — roughly one dispatch per invariant. `keysOriginS4` is **cheaper than the average
  Phase 6 field**, for three structural reasons, all verified against the source during this
  revision:
  1. **The twelve non-minting shapes are nearly free.** They hit `modalStepBranchS4KeyedBody`'s
     `| _, _ => keys` arm, so `keys' = keys`, and they add no edge, so `newAcc = acc`. Only the
     branch grows, and Phase 10's `keysOriginS4_mono_branch` handles that. Reuse
     `modalStepBranchS4KeyedOrdered_branch_superset` (landed in Phase 6).
  2. **The blocked-mint shape adds an edge but no key.** `keysOriginS4` is existential over edges,
     so edge addition preserves it via `keysOriginS4_mono_acc`.
  3. **Only the unblocked-mint shape establishes anything new**, and it establishes it by
     construction: the new entry is `(modalNextWorld b, successorBirthContent φ₀ b s φ v)`, the new
     edge is exactly `v → modalNextWorld b` (`modalApplyOne_boxNeg_mint_snd_S4` /
     `_diamondPos_mint_snd_S4`), so `u := v`, the witness is `(s, φ)`, and the box-context disjunct
     holds because `successorBirthContent`'s filter was computed over `b`, which is a subset of the
     post-step branch.
  Expected output ~150-350 lines: one agent run. **Contingency split, to be taken rather than
  overrunning:** if the phase exceeds one run, split at the minting/non-minting boundary — commit
  the twelve non-minting shapes as `..._preserves_keysOriginS4_nonMint` (a natural green boundary,
  matching Phase 6's own per-shape commit granularity) and take the two minting shapes as the next
  run's single objective. Say explicitly in the handoff which half landed.

- **Tasks:**
  - [ ] Prove `modalStepBranchS4KeyedOrdered_preserves_keysOriginS4`, case-split via
    `modalStepBranchS4KeyedOrdered_selected_mem` exactly as all twelve Phase 6 sub-lemmas do
    (`unfold modalStepBranchS4KeyedBody at hsf`, then the sign/formula split).
  - [ ] Extend `modalStepBranchS4KeyedOrdered_preserves_S4LoopInv`'s conclusion with a fourth
    conjunct `∀ b' ∈ newBs, keysOriginS4 φ₀ b' newAcc keys'`, and its hypotheses with
    `keysOriginS4 φ₀ b acc keys` — threaded exactly like the existing `hKW`/`hWC`. **The
    `S4LoopInv` structure itself is not touched, and `modalStepBranchS4_preserves_S4LoopInv` (the
    unordered wrapper) is not touched.** Confirm both in writing in the phase notes.
  - [ ] Update every call site of the ordered wrapper to thread the new conjunct. Enumerate them
    first (`grep -n "modalStepBranchS4KeyedOrdered_preserves_S4LoopInv"`); at the time of writing
    the only consumers are inside this plan's own remaining phases.
- **Timing:** 4 hours
- **Depends on:** 10
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- **Verification:**
  - `lake build Cslib.Logics.Modal.Tableau.LoopChecking` succeeds
  - `lean_verify` on the preservation lemma and the extended wrapper — sorry-free, axiom-clean
  - Written confirmation that no `S4LoopInv` field was added, no landed statement weakened, and
    `modalStepBranchS4_preserves_S4LoopInv` is byte-for-byte unchanged
  - Whole-project `lake build` green (the extended wrapper's signature change must not break
    `FrameCompleteness.lean` / `FrameSoundness.lean`)

---

### Phase 12: Redirect-Inertness [NOT STARTED]

- **Status note:** this is v1's Phase 10, retried with the origin-edge invariant available. Its
  obligation is unchanged; only the hypotheses it may use have grown. v1's "Named difficulty" text
  has been **deleted, not annotated** — it asserted the false mint-payload premise. See "The
  Corrected Argument" near the top of this plan for the replacement.

- **Goal:** The mathematical heart of Route P. Prove that a redirect edge fired under
  mint-readiness is propagation-inert: everything it can ever transmit is already on the branch.
- **Obligation:** with `blockingWorldS4Keyed φ₀ b keys s φ v = some wBlock`, the guard contract
  (`blockingWorldS4Keyed_eq_birthContent`, LoopChecking.lean:479) gives
  `key(wBlock) = successorBirthContent φ₀ b s φ v`, and `S4LoopInv.keyLowerBd` gives
  `key(wBlock) ⊆ relevantSetFinset φ₀ b wBlock`. Propagation adequacy for the edge `v → wBlock`
  needs, for every `T(□ψ)@v ∈ b`, that `f wBlock` satisfies `□ψ` — which the branch supplies if
  `T(□ψ)@wBlock ∈ b`.
- **How the boxed form is obtained (replaces v1's false "Named difficulty"):** *not* from the mint
  payload, which transmits only the unwrapped body. `T(□ψ)@v ∈ b` puts `(pos, ψ)` in `wBlock`'s
  recorded key; `keysOriginS4` (Phase 10) resolves that pair to either the origin mint's witness
  (case (a), resolved by Phase 10's gate) or to `T(□ψ)@u ∈ b` at the origin source `u` with
  `acc.hasEdge u wBlock` already recorded (case (b)); Phase 10's
  `blockedRedirect_boxctx_mem_of_boxOrigin` then forces `T(□ψ)@wBlock ∈ b` from mint-readiness,
  because otherwise `modalFourBoxProp` at `(u, wBlock)` would still be an unsettled non-mint
  candidate.
- **Obtaining mint-readiness at the call site (implementation note, saves a dead end).**
  `modalStepBranchS4KeyedOrdered_mintReady` takes an awkward `∀ sf, body sf = tuple → mintShape sf`
  premise (Phase 4 chose it deliberately, for want of a selection-uniqueness argument). Do not
  fight it. Go through `modalStepBranchS4KeyedOrdered_cases` (`LoopChecking.lean:1124`) instead,
  whose second disjunct hands you `modalNonMintCandidates φ₀ keys b e acc = []` directly. A step
  that creates a redirect edge is necessarily in that second disjunct: in the primary-scan
  disjunct the selected formula is a non-mint candidate, so `keys' = keys` and no edge is added.
  Prove that small bridging fact once and reuse it.
- **Tasks:**
  - [ ] Prove `blockedRedirect_boxctx_mem`: under mint-readiness, the guard's `some` case,
    `S4LoopInv`, and `keysOriginS4`, every `T(□ψ)@v ∈ b` has `T(□ψ)@wBlock ∈ b`.
  - [ ] Prove the dual `blockedRedirect_diaNeg_mem` for `F(◇ψ)@v ∈ b`.
  - [ ] Assemble `blockedRedirect_propAdequate`: the added edge `v → wBlock` satisfies the
    `branchPropAdequateIn` edge conjunct, given the two membership facts and the branch-formula
    conjunct already in the invariant.
  - [ ] State explicitly in the docstring why mint-readiness is load-bearing: without it, `v`'s box
    context can grow after the decision and the two membership facts fail — this is exactly the
    counterexample's mechanism. State also why the origin edge is load-bearing: the 4-rule needs an
    edge that *already exists*, and the redirect edge does not yet.
- **Timing:** 3 hours
- **Depends on:** 11
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean` or a new soundness section in
    `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`, whichever keeps the import direction acyclic
    (Phase 9 established that `FrameSoundness.lean` works for this line)
- **Verification:**
  - `lake build` of the touched module succeeds
  - `lean_verify` on `blockedRedirect_propAdequate` — sorry-free and axiom-clean
  - The statement is non-vacuous: its hypotheses are discharged at a real call site in Phase 13
  - **Escalation:** if this phase blocks again, it must be for a reason *other* than the witness
    disjunct or the boxed-form recovery — both are resolved upstream by then. A third block on the
    same obligation is a signal to re-examine Route P itself, not to revise again.

---

### Phase 13: Step Preservation and the Soundness Theorem [NOT STARTED]

- **Goal:** Land `modalTableauS4KeyedOrdered_sound` — the theorem this whole task exists to make
  true.
- **v2 re-check (what the origin invariant changes here).** The induction is reshaped in exactly
  one branch, and the reason is worth internalising before starting:
  - **Unblocked-mint branch: unchanged.** At a genuine mint the boxed form at the successor comes
    from frame transitivity, semantically — which is what Phase 9's
    `branchPropAdequateIn_s4FC_boxPos_trans_mem` already supplies, and what
    `branchSatisfiableIn_imp_branchPropAdequateIn` covers for a real edge. This branch never
    depended on any syntactic boxed transmission, so v1's false premise did not touch it.
  - **Blocked-redirect branch: reshaped.** It now consumes Phase 12's `blockedRedirect_propAdequate`
    and must therefore carry `keysOriginS4` through the induction.
  - **The per-index hypothesis of the fuel induction grows by one conjunct**
    (`keysOriginS4 φ₀ b acc keys`), threaded exactly as `keysWorldsKnown`/`worldsContiguousS4`
    already are, and re-established at each step by Phase 11's preservation lemma. It is
    established at the entry point by Phase 10's entry lemma.
  - **`hready` discharge, unchanged from the Phase 9 handoff's guidance:** trivially for a freshly
    minted `w'` (no outgoing edges yet), and via Phase 12's `blockedRedirect_boxctx_mem` for
    redirect edges.
- **Tasks:**
  - [ ] Prove `modalStepBranchS4KeyedOrdered_preserves_propAdequate`: every ordered step maps a
    `branchPropAdequateIn s4FC b acc` branch to `branchPropAdequateIn s4FC b' acc'` on every child.
    Case split: non-minting rules (Phase 9's rule-level lemmas), unblocked mint (a genuine fresh
    world; use `branchSatisfiableIn_imp_branchPropAdequateIn`), blocked redirect (Phase 12).
  - [ ] Prove the fuel induction `modalExpandBranchesS4KeyedOrdered_closed_unsat`: if the driver
    returns `.closed`, the initial branch is not `branchPropAdequateIn s4FC`-satisfiable. Mirror
    the existing generic `modalExpandBranchesGen_closed_unsatIn` induction shape, with the
    per-index hypothesis extended by `keysOriginS4`.
  - [ ] Prove `modalTableauS4KeyedOrdered_sound : modalTableauS4KeyedOrdered φ = .closed → s4Valid φ`.
  - [ ] Confirm against the regression corpus: the theorem's existence plus Phase 8's `OPEN`
    verdict on `cex` are consistent, and no test row contradicts the theorem.
- **Timing:** 4 hours (up from v1's 3.5: the induction now threads a fifth invariant conjunct)
- **Depends on:** 12
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`
- **Verification:**
  - `lake build Cslib.Logics.Modal.Tableau.FrameSoundness` succeeds
  - `lean_verify Cslib.Logic.Modal.Tableau.modalTableauS4KeyedOrdered_sound` — sorry-free,
    axiom-clean, no `sorryAx`

---

### Phase 14: Hintikka Invariant Against the Ordered Stepper (risk b, part 1) [NOT STARTED]

- **Goal:** Begin the completeness re-proof. Attempted only now, with the ordered stepper stable
  since Phase 8 — the research's explicit sequencing constraint, so the work is not done twice.
- **v2 re-check:** unaffected by the origin-edge invariant. `S4KeyedHintikkaInv` and the saturation
  conjuncts are stated against the actual (unwrapped) minting transmission, which is what the
  landed completeness line already proves, so v1's false premise never entered here. `keysOriginS4`
  is a soundness-side invariant only: the completeness induction's per-index hypothesis
  (`S4LoopInv ∧ S4KeyedHintikkaInv ∧ keysWorldsKnown ∧ worldsContiguousS4`) does **not** gain a
  conjunct. The one exception to watch: Phase 11 extends the *ordered* `_preserves_S4LoopInv`
  wrapper's signature, so any call to it from this phase must thread the new hypothesis.
- **Tasks:**
  - [ ] Restate `S4KeyedHintikkaInv` (LoopChecking.lean:5700) against the ordered stepper if its
    fields reference the stepper; if they reference only `modalApplyOneS4Keyed` (which the ordered
    stepper reuses verbatim), reuse the existing structure unchanged and record that.
  - [ ] Re-derive `S4KeyedHintikkaInv_weaken` (LoopChecking.lean:5730) if needed — it mentions no
    stepper and is expected to transport unchanged.
  - [ ] Prove the single-step preservation
    `modalStepBranchS4KeyedOrdered_preserves_S4KeyedHintikkaInv`, mirroring the existing Phase-7
    single-step preservation section. Reuse `modalStepBranchS4Keyed_blocked_witness_mem`
    (LoopChecking.lean:5759) — its statement is about the guard, not the traversal.
  - [ ] The one genuinely new obligation: the ordered stepper's first traversal may select from a
    filtered candidate list, so the case analysis must be driven by Phase 4's `_selected_mem`
    rather than by unfolding `b.findSome?`.
- **Timing:** 3 hours
- **Depends on:** 8, 13
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- **Verification:**
  - `lake build Cslib.Logics.Modal.Tableau.LoopChecking` succeeds
  - New declarations sorry-free
  - The existing keyed Hintikka line still compiles

---

### Phase 15: Top-Loop Hintikka Induction (risk b, part 2) [NOT STARTED]

- **Goal:** Re-prove `modalExpandBranchesS4Keyed_hintikka` (LoopChecking.lean:6664) against the
  ordered driver. This is the largest single proof in the completeness line.
- **v2 re-check:** unaffected in substance. Phase 4's `modalStepBranchS4KeyedOrdered_eq_none_iff`
  remains the linchpin and is untouched by the origin-edge invariant. As in Phase 14, the only
  contact point is the extended ordered `_preserves_S4LoopInv` signature.
- **Leverage:** Phase 4's `modalStepBranchS4KeyedOrdered_eq_none_iff` makes the saturation step —
  the point where a `none` return must yield full `modalHintikkaSetGen` saturation over **all**
  `sf ∈ b` (Saturation.lean:460, conjunct 2 quantifies over the whole branch) — transfer
  definitionally from the existing proof, because the ordered stepper's fallback traversal *is*
  the old traversal. Without that lemma this phase would need the conjuncts re-derived from
  scratch; with it, the induction's shape is preserved and the per-step case uses Phase 12's
  preservation plus Phase 5's measure lemma.
- **Tasks:**
  - [ ] Prove `modalExpandBranchesS4KeyedOrdered_hintikka`, transcribing the existing induction
    (per-index hypothesis `S4LoopInv ∧ S4KeyedHintikkaInv ∧ keysWorldsKnown ∧ worldsContiguousS4`,
    `processNext` inner induction) with the ordered stepper's lemmas substituted.
  - [ ] Prove `modalExpandBranchesS4KeyedOrdered_openBranch_initial_mem`, mirroring
    LoopChecking.lean:7025.
  - [ ] If the transcription stalls, mark [BLOCKED] with the goal state. Do not substitute a
    different induction scheme.
- **Timing:** 4 hours (largest phase; if it exceeds one agent run, split at the
  `processNext` inner induction and commit the outer skeleton with the inner as the next run's
  single objective — the split point is a natural green boundary)
- **Depends on:** 14
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- **Verification:**
  - `lake build Cslib.Logics.Modal.Tableau.LoopChecking` succeeds
  - `lean_verify` on both theorems — sorry-free

---

### Phase 16: Ordered Completeness Theorem (risk b, part 3) [NOT STARTED]

- **Goal:** Land `modalTableauS4KeyedOrdered_complete`, the sibling of
  `modalTableauS4Keyed_complete` (FrameCompleteness.lean:4249).
- **Flag — restatement of a landed theorem.** `modalTableauS4Keyed_complete` is not weakened here;
  a sibling stated against the ordered driver is added beside it. The old theorem is removed only
  in Phase 17, together with the driver it is stated about. This is the plan's only removal of a
  landed result, and it is a removal-with-replacement, never a weakening.
- **Tasks:**
  - [ ] Derive the ordered analogue of the entry invariant `modalTableauS4Keyed_initial`
    (FrameCompleteness.lean:4172).
  - [ ] Prove `modalTableauS4KeyedOrdered_complete : s4Valid φ₀ → modalTableauS4KeyedOrdered φ₀ = .closed`,
    assembling Phase 15's two theorems with the countermodel bridge the existing proof uses.
  - [ ] Confirm the soundness and completeness theorems are now both available for the same
    driver, and state in a docstring that the decidability instance is thereby unblocked as
    downstream work — **without** attempting it here.
- **Timing:** 2.5 hours
- **Depends on:** 15
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`
- **Verification:**
  - `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` succeeds
  - `lean_verify` — sorry-free, axiom-clean

---

### Phase 17: Retire the Superseded Driver and Final CI [NOT STARTED]

- **Goal:** Leave exactly one keyed S4 driver in the repository, with the documentation telling the
  true story, and a fully green CI pipeline.
- **Flag — removals of landed declarations.** This phase deletes `modalStepBranchS4Keyed`,
  `modalExpandBranchesS4Keyed`, `modalTableauS4Keyed`, `modalTableauS4Keyed_complete`, and their
  stepper-specific support lemmas, each replaced by an ordered counterpart proved in Phases 4-16.
  Nothing is deleted without a proved replacement. If any deletion turns out to have a consumer
  with no ordered counterpart, keep the declaration and report the gap rather than stubbing it.
- **v2 re-check:** `keysOriginS4` is ordered-line-only and survives the retirement, as do
  `keysWorldsKnown`/`worldsContiguousS4`. `modalStepBranchS4_preserves_S4LoopInv` (the unordered
  wrapper, untouched throughout v2 by design) is deleted here along with the driver it serves.
- **Tasks:**
  - [ ] Enumerate every consumer of the superseded declarations across `Cslib/` and `CslibTests/`
    and confirm each has an ordered counterpart.
  - [ ] Delete the superseded declarations, or — if any external consumer remains — retain them
    with a docstring naming the ordered successor and the unsoundness, and report the retention.
  - [ ] Rename the ordered declarations to the plain `S4Keyed` names if the old ones were deleted,
    so the repository does not carry an `Ordered` suffix that no longer distinguishes anything.
    Update all call sites and the regression test.
  - [ ] Update the Phase 2 documentation correction: the `blockingWorldS4Keyed` docstring and the
    `FrameCompleteness.lean` S4Keyed section must now describe the repair, not only the defect,
    and must state that the mint-readiness discipline is what makes the redirect edge sound.
  - [ ] Carry forward the research's section 6 warning verbatim in substance: the live-set guard
    `blockingWorldS4` still has the no-reachability-restriction defect and is **not** demonstrated
    sound. Do not let the repair of the keyed driver be read as a claim about the live-set one.
  - [ ] Run the full CSLib CI order: `lake build`, `lake exe checkInitImports`, `lake lint`,
    `lake exe lint-style`, `lake test`, `lake exe mk_all --module`,
    `lake shake --add-public --keep-implied --keep-prefix`.
- **Timing:** 3 hours
- **Depends on:** 11, 14
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
  - `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`
  - `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`
  - `CslibTests/S4LoopGuardRegression.lean`
- **Verification:**
  - Full CI pipeline green
  - Repository-wide grep confirms no dangling reference to a deleted declaration
  - `lake test` passes with the counterexample asserted `OPEN`

---

## Testing & Validation

- [ ] `CslibTests/S4LoopGuardRegression.lean` asserts the counterexample does **not** close under
  the repaired driver, and this row is part of `lake test`.
- [ ] B-axiom control still returns `OPEN`; T-axiom control still returns `CLOSED`. *(v2
  correction: v1 also listed 5-axiom, McKinsey, 4-axiom and K-axiom controls. Phase 8 established
  by direct inspection that the regression file has only ever carried B and T rows for either
  driver; the other four never existed and are not required. Add them only as new work, if wanted,
  never as a claimed pre-existing baseline.)*
- [ ] Size-<=6 exhaustive sweep census recorded, with zero open-to-closed verdict changes.
- [ ] **(v2)** The witness disjunct has a recorded verdict from Phase 10, with its justification.
- [ ] **(v2)** `S4LoopInv`'s field list is unchanged from its landed form, and
  `modalStepBranchS4_preserves_S4LoopInv` (the unordered wrapper) is byte-for-byte unchanged until
  Phase 17 deletes it.
- [ ] **(v2)** Repo-wide `axiom` count is 26 at every commit
  (`grep -rn '^axiom ' Cslib/ | wc -l`).
- [ ] **(v2)** No file under `Cslib/Logics/Modal/Metalogic/Constructive/Nested/**` appears in any
  commit from this task.
- [ ] `lean_verify` on `modalTableauS4KeyedOrdered_sound` and `modalTableauS4KeyedOrdered_complete`
  (or their post-rename names): sorry-free, no `sorryAx`, no new axioms.
- [ ] No declaration anywhere in the diff matches the prohibited vacuous patterns
  (`def X := True`, `theorem X := trivial`, and variants) per `.claude/rules/cslib.md`.
- [ ] No task-number citations in any file outside `specs/`, per
  `.claude/rules/no-task-references-in-deliverables.md`.
- [ ] Full CSLib CI order green (Phase 17).

## Artifacts & Outputs

- `specs/553_s4_loop_guard_soundness_reachability_restriction/plans/02_origin-edge-invariant-revision.md` (this file; supersedes `plans/01_s4-settled-context-scheduling.md`, retained for provenance)
- `specs/553_s4_loop_guard_soundness_reachability_restriction/summaries/01_s4-settled-context-scheduling-summary.md`
- `CslibTests/S4LoopGuardRegression.lean` — new permanent regression corpus
- `CslibTests.lean` — barrel registration
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — mint-readiness predicate, ordered stepper and
  driver, re-verified measure and loop-invariant chain, `keysOriginS4` origin-edge invariant and
  its preservation, re-proved Hintikka line
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` — `branchPropAdequateIn` and the S4 keyed
  soundness theorem
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — corrected S4Keyed documentation and the
  ordered completeness theorem
- `specs/553_.../artifacts/s4probe.lean` — sweep adapted to the ordered stepper (task scratch,
  not repository surface)

**Outcomes unblocked by this work, not planned here:** the keyed S4 soundness theorem's successor
phase, and the decidability half of `instDecidableS4Valid`, which needs both the soundness and
completeness lines for the same driver.

## Rollback/Contingency

- Phases 1-2 are additive and independently valuable: the regression corpus and the documentation
  correction stand on their own even if the repair is abandoned. They are the guaranteed floor.
- Phases 3-7 add parallel declarations and delete nothing, so `git revert` of those commits
  restores the prior state exactly. The landed completeness line stays green throughout.
- **Phase 8 is the abort gate.** If the reordering does not open the counterexample, or if the
  sweep shows an open-to-closed regression, stop: the soundness work ahead cannot succeed and the
  plan needs revision, not continuation. Phases 1-2 and the documentation correction remain landed.
- Phases 9-16 are additive to `FrameSoundness.lean` / `FrameCompleteness.lean`; revert is
  per-phase.
- **Phase 10 is v2's abort gate**, in the same role Phase 8 played for v1. If the witness
  disjunct resolves to a genuine reachable counterexample to redirect-inertness, stop: the
  soundness line ahead is not reachable by Route P as currently scoped, and the task needs a
  research dispatch rather than another plan revision. Phases 1-9's landed assets are unaffected.
- Phase 17 is the only destructive phase. Take a snapshot via
  `bash .claude/scripts/git-snapshot.sh` before the deletions, and split it into a
  rename-and-update commit and a delete commit so the deletion can be reverted independently.
- Escalation rule for every proof phase: if a step cannot be completed as written, mark the phase
  `[BLOCKED]` and report what was tried and the goal state reached. Do not substitute a different
  decomposition, and never discharge an obligation with `sorry`, an axiom, or a vacuous statement.
