# Implementation Plan: Canonical-Witness Truth Lemma for the S4 Keyed Loop Guard (v6)

- **Task**: 553 - s4_loop_guard_soundness_reachability_restriction
- **Status**: [IMPLEMENTING]
- **Effort**: 18 hours (7 phases; two front-loaded kill gates, the first of which can terminate
  the route before any construction is built)
- **Dependencies**: 535 (keyed completeness inputs, landed), 557/561-563 (refactor programme,
  landed), 587 (canonical-witness restriction probe, completed — its verdict report is this
  plan's primary input)
- **Research Inputs**:
  - `specs/587_canonical_witness_restriction_probe/reports/01_canonical-witness-restriction-probe.md`
    (**primary**: the CONDITIONAL GO verdict, the Restriction A/B1 machine-checked results, the
    field-by-field conjunct classification, and the Phase 3 pricing table)
  - `specs/553_.../plans/05_pinned-witness-truth-lemma.md` `#### Phase 1 Verdict` (**reference**:
    the exact stuck goals, the outcome-(iii) escalation, and the effort calibration)
  - `specs/553_.../reports/05_gate-a-canonical-witness-blocker-analysis.md` (blocker record)
  - Prior reports 01-04 under `specs/553_.../reports/` (the four falsified routes; not re-argued)
- **Artifacts**: `plans/07_canonical-witness-truth-lemma.md` (this file)
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
- **Plan version**: 6

---

## Overview

**This is the sixth plan version for this task.** Plans `01` through `05` are versions 1-5; there
is no `06` plan file. The `07` filename prefix comes from the repository's global per-task artifact
sequence, whose current maximum is `summaries/06`, not from a deleted or missing plan. Version 6
supersedes v5 (`plans/05_pinned-witness-truth-lemma.md`, `[BLOCKED]` at its Gate A / Phase 1).

The keyed S4 loop guard licenses a redirect edge `src -> wBlock` into the same `Accessibility`
structure that `branchSatisfiableIn`'s edge conjunct quantifies over. Justifying that edge against
a model is the one obligation on which five successive routes have now died. The completed
canonical-witness restriction probe answered the question v5's Gate A escalated with a **CONDITIONAL
GO**: restricting the witness carrier closes both of v5's machine-checked stuck cases, but only if
the witness is further committed to a **canonical/term model** whose valuation reads branch
membership, rather than left an arbitrary pinned witness. This plan executes that commitment, behind
a front-loaded kill gate that prices the one obstruction the probe explicitly flagged as unpriced
residual risk.

**Definition of done**: the redirect-preservation obligation is discharged at a canonical witness,
sorry-free and standard-axioms-only, wired into the keyed ordered driver's soundness argument, with
the sorry census in `Cslib/Logics/Modal/Tableau/` still exactly 1 at every phase boundary and scoped
CI green at every commit. If Gate 0 (Phase 1) fails, the plan terminates by returning to the blocker
record rather than proposing a seventh route.

**Scope constraint**: file scope is `Cslib/Logics/Modal/Tableau/{FrameSoundness,FrameCompleteness,
LoopChecking}.lean` plus `CslibTests/S4LoopGuardRegression.lean` plus this task's `specs/` directory.
`Rules.lean`, `Saturation.lean`, `Branch.lean`, `SoundnessStep.lean` and everything under
`Cslib/Logics/Modal/Metalogic/**` are **read-only in every phase**.

**This plan does no refactoring.** The modal tableau refactor programme already landed. No file
splitting, no `Boneyard/` moves, no `modalTableauGen` unification.

### Research Integration

The probe report is the authoritative input and its findings are carried as follows.

| Probe finding | How this plan uses it |
|---|---|
| Restriction A (`W := WorldIndex`, `f := id`) does **not** close the obligation; machine-checked stuck at `box.mp.inr` and `diamond.mpr` | **Not retried.** No phase re-proposes a bare carrier fix. The literal reading of v5's Verdict is dead. |
| Restriction B1 (carrier `{w : WorldIndex // w ∈ modalKnownWorlds b}`) closes both cases sorry-free, modulo two assumed hypothesis groups | Phases 3-6 discharge those two groups. B1 is the adopted encoding; B2 (a closure side condition) is not revisited. |
| The semantic-to-syntactic **truth-lemma** direction is not free for an arbitrary pinned witness; it requires a canonical/term model | The central commitment of this plan, and the subject of Gate 0. |
| Three of `branchSatisfiablePinnedIn`'s four conjuncts collapse under the canonical choice; only the branch conjunct re-shapes | Phase 3 discharges the three collapsing conjuncts cheaply; Phases 4-6 own the branch conjunct. |
| `branchSatisfiablePinnedIn_redirect_mechanical` survives verbatim, unconditionally | **No phase re-derives it.** It is a preserved asset. |
| Residual risk: the truth lemma's box/diamond cases may need more from `modalS4Saturated` than Gate B supplies — a seventh obstruction | Phase 1 is exactly the recommended front-loaded Gate 0 against this risk. |

### Prior Plan Reference

v5 is read as a **source of lessons, not a template**. What is carried forward:

- **The kill-gate discipline itself**, including the one-dispatch attempt budget per gate and the
  standing prohibition on committing a `sorry` at a gate. Both v5's Gate A and the probe used it and
  both terminated cheaply as designed. This plan keeps it unchanged.
- **v5's Phase 2 (Decision Gate B)**, which was never executed and whose question — is
  `modalS4Saturated φ₀ b acc` available at a settled ordered-stepper state? — is still open and still
  load-bearing. It reappears here as Phase 2, re-scoped to the current file layout. Its analysis that
  `modalHintikkaClauseGen` matches on the formula alone and so supplies nothing for `T(box ψ)` /
  `F(diamond ψ)` remains valid and is not re-argued.
- **The preserved-asset discipline**: nothing sorry-free and landed is retired.
- **v5's Postmortem Constraints** on what must not be re-proposed (redirect inertness, the
  reachability restriction, ancestor-only blocking, route (2')'s disjunctive edge conjunct, the
  `red` channel, retargeting to `branchPropAdequateIn`, and the box-condition form of `accPinnedBy`
  as a *primitive* invariant). All still binding; see Non-Goals.

What is explicitly **stale in v5 and must not be re-proposed from it**:

- **v5's Phases 5-7 framing** — "land a parallel `S4LoopInvBoxed` / `S4KeyedHintikkaInvBoxed` /
  `...Boxed` driver family beside the landed ones" — is stale. The refactor programme landed
  Mechanism 2 (box-plus birth content) **inline** in the mainline `successorBirthContent`
  (`LoopChecking.lean:525`) and `blockingWorldS4Keyed` (`:655`). There is no parallel `Boxed` family
  to build and none is planned here.
- **v5's Phase 1 sub-step 1.2 route** — an agreement lemma over an arbitrary witness by structural
  induction — is machine-checked dead in two independent forms (v5's own Verdict, and the probe's
  Restriction A). No phase retries it against an arbitrary witness.
- **v5's line anchors throughout.** Every declaration must be re-located by
  `grep -n '^def\|^lemma\|^theorem\|^structure\|^abbrev'`, never by a line number quoted in v5.

### Roadmap Alignment

`specs/ROADMAP.md` was consulted read-only. This plan advances two entries in the "Known sorries and
gaps" section:

- **S4 keyed loop-check guard soundness (1 sorry, the only Modal one)** — the entry naming
  `branchSatisfiableIn_s4FC_ancestor_redirect` directly. Note: this plan does **not** remove that
  sorry (see Non-Goals); it builds the apparatus that a future task would need in order to.
- **S4 (reflexive-transitive) loop-checking termination bound + decidability** — the last classical-cube
  decidability corner, gated behind the same soundness obligation.

No roadmap phases are added: `roadmap_flag` is false for this dispatch, and this plan does not write
to `ROADMAP.md`.

### The architectural finding this plan turns on

The probe report left one design question open: whether to "import `FrameCompleteness.lean` into the
soundness side, or re-state the three-line valuation locally." **Neither option is available, and the
question has a forced answer**, re-derived from the import graph in this planning run:

- `FrameSoundness.lean` imports `Soundness`, `FrameRules`, `S5Simplification`, `FiveSimplification`,
  `Support.Accessibility`, `Support.KnownWorlds`. It does **not** import `LoopChecking.lean`.
- `FrameCompleteness.lean` imports **both** `LoopChecking.lean` and `FrameSoundness.lean`.

Therefore importing `FrameCompleteness` into `FrameSoundness` is an **import cycle**, not a trade-off;
and re-stating the valuation locally in `FrameSoundness` does not help either, because
`modalS4Saturated` and `modalHintikkaSetS4` live in `LoopChecking.lean`, which `FrameSoundness` also
cannot see. `FrameCompleteness.lean` is the **only in-scope file that sees every ingredient** the
canonical-witness construction needs.

**Consequence, binding on Phases 3-7**: `accPinnedBy` and `branchSatisfiablePinnedIn` stay where they
are in `FrameSoundness.lean` (upstream, and visible from `FrameCompleteness`); every new declaration
in this plan that mentions the canonical model, `modalS4Saturated`, or `modalHintikkaSetS4` lands in
`FrameCompleteness.lean`. A phase that finds itself wanting to add a `LoopChecking` import to
`FrameSoundness.lean` has taken a wrong turn and must stop and record it.

### Disposition of the retained probe lemma

`canonicalWitnessRestrictionProbe_agreementConditional` is a landed, sorry-free declaration in
`Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (re-locate by
`grep -n 'canonicalWitnessRestrictionProbe'`, not by line number). Its disposition is decided here so
no phase has to guess:

**It is scaffolding to build on through Phases 1-5, and to be superseded and removed in Phase 6.**

- Through Phases 1-5 it serves as a compile-checked specification of the exact target shape: its two
  assumed hypothesis groups (`hpropBox`/`hpropDia`, and `htruthBoxPos`/`htruthDiaNeg`) are precisely
  the obligations Phases 2 and 4-5 discharge, and its proof body is the forward-chaining skeleton the
  real lemma reuses. Do not modify its statement in those phases.
- In Phase 6, once the real redirect lemma lands with those hypotheses discharged at the canonical
  witness, the probe lemma is **removed** along with its `/-! ### CANONICAL-WITNESS RESTRICTION PROBE
  -- REVERT UNLESS SORRY-FREE -/` section header. Keeping two near-identical agreement lemmas, one of
  them carrying six assumed hypotheses, is exactly the unreviewable duplication CSLib review flags.
- **Unconditionally, in Phase 1**: that section header is stale regardless of any gate outcome — it
  reads as an instruction to revert a declaration that was deliberately retained. Phase 1 retitles it
  and rewrites the surrounding module comment to describe a landed conditional agreement lemma. This
  is a two-minute prose edit and is not gated on the probe's outcome.

---

## Goals & Non-Goals

**Goals**:

- Determine, cheaply and before any construction, whether the truth lemma's box-positive
  semantic-to-syntactic direction is obtainable at the canonical model, and at what price (Phase 1).
- Settle whether `modalS4Saturated` is available at a settled ordered-stepper state — v5's
  never-executed Gate B (Phase 2).
- Commit the witness of `branchSatisfiablePinnedIn` to the canonical/term model, discharging the
  three conjuncts the probe classified as collapsing (Phase 3).
- Prove the canonical-witness truth lemma in both the box-positive and diamond-negative directions
  (Phases 4-5).
- Discharge the redirect-preservation obligation at the canonical witness, superseding the probe
  lemma (Phase 6).
- Wire the result into the keyed ordered driver's soundness argument and extend the regression
  corpus (Phase 7).

**Non-Goals**:

- **Removing or altering the standing `sorry` at `Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1251`
  (`branchSatisfiableIn_s4FC_ancestor_redirect`).** It is retained by explicit user decision. No phase
  touches it, its enclosing declaration, or its module comment. The sorry census over
  `Cslib/Logics/Modal/Tableau/` is **exactly 1** at every phase boundary.
- **Re-running or re-proposing the FrameCompleteness / modal tableau refactor programme.** It landed.
  Its box-plus birth content is inline in `successorBirthContent` and `blockingWorldS4Keyed`.
- **Re-deriving `accPinnedBy`, `branchSatisfiablePinnedIn`, or
  `branchSatisfiablePinnedIn_redirect_mechanical`.** All three are preserved verbatim.
- **Retrying Restriction A, or an agreement lemma over an arbitrary (non-canonical) pinned witness.**
  Both are machine-checked dead.
- **Building a parallel `...Boxed` invariant or driver family.** Stale framing from v5.
- **Retargeting to `branchPropAdequateIn`, or weakening `accPinnedBy` to make a proof close.** Both
  closed by standing decision; a phase that finds a proof hard must record the difficulty, not
  silently substitute a weaker invariant.
- **Proposing a seventh route if Gate 0 fails.** The terminal condition is a return to the blocker
  record.
- **Any task-number citation inside a `.lean` file** (repo rule
  `.claude/rules/no-task-references-in-deliverables.md`). Cite declaration names and source labels.

---

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The converse truth-lemma direction (`Satisfies m w (box ψ) -> T(box ψ)@w ∈ b`) is **false** for a downward-saturated tableau branch, because the branch is not maximal: neither `T(box ψ)@w` nor `F(box ψ)@w` need be present | Terminal — this is the seventh obstruction the probe named | H | Phase 1 is a one-dispatch micro-probe targeting exactly this. Its outcome table has an explicit refutation branch that terminates the plan rather than escalating into further construction. |
| The canonical model is only Hintikka at a **saturated** branch, but the soundness invariant must hold at every intermediate state, where the branch is not saturated | Terminal for the naive "plug in `extractModelS4`" reading | H | Phase 2 (Gate B) is exactly this question and is a kill gate. Phase 1's outcome table explicitly states that a Phase-1 pass does **not** make Gate B moot. |
| The canonical construction must live in `FrameCompleteness.lean`, but the eventual soundness capstone for the keyed ordered driver conventionally belongs on the soundness side | Structural: soundness content lands in a file named for completeness | H (certain, given the import graph) | Recorded as a forced consequence in the Overview. Phase 7 records the resulting layering note for a future refactor task; it does not attempt a file split (out of scope). |
| Gate B needs one additional invariant field, which then needs a preservation proof across the mint shapes | Adds a phase's worth of work not in the estimate | M | Gate B's outcome (ii) requires the field to be written out verbatim and its preservability argued **in the same dispatch**, exactly as v5 specified. Do not proceed past recording it. |
| An implementer treats the probe lemma's six assumed hypotheses as discharged because the lemma is sorry-free | Silent false progress | M | The Disposition subsection above states the assumed groups explicitly, and Phase 6 removes the lemma once the real one lands. |
| Line anchors quoted from v5 or from the probe report have drifted | Wasted dispatch time; wrong edit region | M | Every phase re-locates declarations by `grep -n '^def\|^lemma\|^theorem\|^structure\|^abbrev'`. No phase in this plan quotes a line number as an anchor except the standing sorry, which is verified by grep, not by line. |
| A phase accidentally commits a `sorry` at a gate, standing in for a possibly-false statement | Repeat of the exact failure this task has suffered twice | L | Standing prohibition, restated per gate phase: at a gate, if the proof does not close, **revert** and record the exact `lean_goal`. Never commit the sorry. |
| Base rate: six routes have failed at this one obligation | The expected outcome is that a gate fires | H | The plan is built to reach that verdict cheaply (Phase 1 is 2.5 hours and comes before any construction), not to avoid recording it. |

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
| 6 | 7 | 6 |

Phases within the same wave can execute in parallel. **Phases 3-7 must not be dispatched until
Phase 1 returns a passing outcome, and Phases 4-7 must not be dispatched until Phase 2 returns a
passing outcome.** No construction is scaffolded ahead of a gate verdict.

---

### Phase 1: GATE 0 — canonical-witness truth-lemma micro-probe [COMPLETED]

- **Goal:** Decide, before any construction, whether the truth lemma's box-positive
  semantic-to-syntactic direction is obtainable at the canonical model, and at what price. This is
  the front-loaded gate the probe report's Residual Risk section explicitly recommended.
- **Depends on:** none
- **Timing:** 2.5 hours (one dispatch; the attempt budget is one dispatch by design)
- **Verification Tier:** local
- **Scope Hypothesis:** This phase asserts two sub-probes totalling roughly 100 lines of Lean, all
  appended to `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`, plus one prose edit in
  `FrameSoundness.lean`. Confirm at implementation time by counting the appended lines and the
  touched files against `git diff --stat`; if the real edit region turns out to span a third file,
  stop and record why before continuing.
- **Owns:** `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (new probe section appended at end
  of file, delimited and reverted per the outcome table); `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`
  (the stale-header prose edit only — no declaration in that file is modified).

**Why `FrameCompleteness.lean` and not `FrameSoundness.lean`**: see the Overview's architectural
finding. `FrameSoundness.lean` cannot see `modalHintikkaSetS4`, `modalS4Saturated`, or
`extractModelS4`, and cannot be made to without an import cycle.

- **Tasks:**
  - [ ] **Unconditional prose fix (do this first, it is not gated).** Retitle the
        `/-! ### CANONICAL-WITNESS RESTRICTION PROBE -- REVERT UNLESS SORRY-FREE -/` section header in
        `FrameSoundness.lean` and rewrite the surrounding module comment so it describes a landed
        conditional agreement lemma rather than instructing a reverter. Name the two assumed hypothesis
        groups explicitly in the new comment. No declaration is modified. No task numbers.
  - [ ] **Sub-probe 0.A (mechanical, unconditionally useful, attempt first — it is the cheapest
        possible collapse of the entire priced cost).** State and attempt the `addEdge` /
        `ReflTransGen` decomposition identity:
        ```lean
        lemma reflTransGen_addEdge_iff (acc : Accessibility) (src wBlock x y : WorldIndex) :
            Relation.ReflTransGen (fun a c => (acc.addEdge src wBlock).hasEdge a c = true) x y ↔
              Relation.ReflTransGen (fun a c => acc.hasEdge a c = true) x y ∨
              (Relation.ReflTransGen (fun a c => acc.hasEdge a c = true) x src ∧
               Relation.ReflTransGen (fun a c => acc.hasEdge a c = true) wBlock y)
        ```
        If this closes, then `extractModelS4 b (acc.addEdge src wBlock)` **is** definitionally the
        redirect-extended `extractModelS4 b acc` — the exact relation `r'` that both v5's Gate A and
        the probe's agreement lemmas were built around. That would replace the entire agreement-lemma
        workstream with a `rfl`-adjacent identity plus `modalTruthLemmaS4` applied at the extended
        accessibility. Locate `Accessibility.addEdge` and `hasEdge_addEdge_*` helpers by grep before
        starting; a local re-derivation of the `hasEdge_addEdge` case split may be needed.
  - [ ] **Sub-probe 0.B (the named residual risk).** State and attempt the converse truth-lemma
        direction at the canonical model, from `modalHintikkaSetS4` alone:
        ```lean
        lemma canonicalTruthBoxPos (φ₀ : Proposition Atom)
            (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
            (hH : modalHintikkaSetS4 φ₀ b acc) :
            ∀ ψ w, Satisfies (extractModelS4 b acc) w (.box ψ) →
              (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b
        ```
        **Read the landed `modalTruthLemmaS4` first** (`FrameCompleteness.lean`, locate by grep): it
        supplies only the syntactic-to-semantic direction, `T(φ)@w ∈ b -> Satisfies m w φ` and
        `F(φ)@w ∈ b -> ¬ Satisfies m w φ`. Its second clause contraposes to the goal **only** given a
        decidedness fact. So the concrete route to attempt is: derive the goal from
        `modalTruthLemmaS4` plus
        ```lean
        hdecidedBox : ∀ ψ w, w ∈ modalKnownWorlds b → .box ψ ∈ modalSubfmls φ₀ →
            (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b ∨
            (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b
        ```
        and then **assess `hdecidedBox` itself in the same dispatch**. The honest expectation is that
        it is FALSE: a tableau branch is downward saturated but not maximal, and adds only
        rule-generated formulas, so a branch containing neither polarity of `box ψ` at `w` is
        routine. If it is false, exhibit a concrete such branch rather than asserting the fact.
  - [ ] Run `lean_verify` on every declaration that lands; require only `propext`, `Classical.choice`,
        `Quot.sound`.
  - [ ] Record the verdict in a `#### Phase 1 Verdict` subsection in this file, with the exact
        `lean_goal` state at any stuck point and, for a refutation, the concrete branch exhibited.

- **Kill criteria and outcomes** (decided now, not under pressure):

| Outcome | Verdict |
|---|---|
| (i) **0.A closes sorry-free** | Gate 0 **PASSES on the cheap branch.** The redirect-extended canonical model IS the canonical model of the extended accessibility, so the agreement-lemma workstream collapses and the branch-conjunct obligation reduces to `modalHintikkaSetS4` preservation under `addEdge` (which the landed `blockedRedirect_unwrapped_*_mem` and the wrapped transfers are positioned to supply). **Re-scope Phases 3-6 against this before dispatching them**, and record the re-scope in this plan. **This does NOT make Phase 2 moot** — `modalHintikkaSetS4` is a saturation predicate and is still unavailable at intermediate states; see (vi). |
| (ii) 0.A fails, **0.B closes from `modalHintikkaSetS4` alone** | Gate 0 **PASSES on the expensive branch.** Proceed with the priced truth-lemma programme, Phases 3-6 as written. |
| (iii) 0.A fails, and 0.B needs **exactly one nameable additional hypothesis** whose establishability is argued in the same dispatch | Gate 0 **PASSES CONDITIONALLY.** Write the hypothesis out verbatim, name which phase owes it, and stop at recording it. Do not begin discharging it in this phase. |
| (iv) 0.A fails and 0.B's missing hypothesis is **refuted** — a concrete branch reachable at a blocking decision carries neither `T(box ψ)@w ∈ b` nor `F(box ψ)@w ∈ b` for a relevant `ψ` | **Route (a) is dead.** This is the seventh obstruction the probe named as residual risk, now confirmed. Revert both sub-probes, keep the prose fix, record the branch, and **return to the blocker record** per the Terminal Condition. Do **not** invent an eighth route. |
| (v) Neither sub-probe closes nor is refuted **within this one dispatch** | **Route (a) is dead as planned.** The one-dispatch budget is the same discipline v5's Gate A and the probe both used, and both terminated correctly under it. Revert, keep the prose fix, record the exact `lean_goal`, return to the blocker record. Do **not** request a second dispatch to keep trying, and do **not** commit a `sorry`. |
| (vi) **Reading constraint on any passing outcome** | A pass licenses only what it states. It does not validate Gate B's saturation availability, does not license reordering or softening any later phase's criteria, and does not license scaffolding Phases 3-7 before Phase 2 also returns. |

- **Done when:** the prose fix is committed; each sub-probe is either sorry-free and committed or
  reverted with its `lean_goal` recorded; a `#### Phase 1 Verdict` subsection exists in this file;
  the bare-tactic sorry census over `Cslib/Logics/Modal/Tableau/` returns **exactly 1** line
  (`FrameSoundness.lean:1251`); scoped `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` and
  `lake exe lint-style` clean.

#### Phase 1 Verdict

**Outcome (i): Gate 0 PASSES on the cheap branch.** Sub-probe 0.A (`reflTransGen_addEdge_iff`,
`FrameCompleteness.lean`, locate by grep) closed **sorry-free on the first attempt**, requiring no
retry and no additional hypothesis. `lean_verify` on all three landed declarations
(`reflTransGen_addEdge_iff`, and its two local helpers `hasEdge_addEdge_mono_gate0`,
`hasEdge_addEdge_self_gate0`) reports axioms exactly `{propext, Classical.choice, Quot.sound}`
(the mono helper needs only `propext`). Scoped `lake build
Cslib.Logics.Modal.Tableau.FrameCompleteness` is clean; `lake exe lint-style` is clean; the
bare-tactic sorry census over `Cslib/Logics/Modal/Tableau/` returns exactly one line,
`FrameSoundness.lean:1251`.

**Proof shape.** Forward direction: tail-induction on the `ReflTransGen` witness over the
extended relation, splitting each edge via the public `hasEdge_addEdge_cases`
(`Support/Accessibility.lean`) into "the new edge `src → wBlock`" or "an old `acc` edge", and
routing the disjunction accordingly. Backward direction: `Relation.ReflTransGen.mono` lifts an
`acc`-path into an `(acc.addEdge src wBlock)`-path, and one `.tail`/`.trans` assembly threads
through the new edge for the second disjunct. Neither the private `hasEdge_addEdge_mono_FS`/
`hasEdge_addEdge_self_FS` helpers (`FrameSoundness.lean`, file-private) nor any Hintikka-set or
saturation hypothesis was needed — the identity is purely about `Accessibility`/`ReflTransGen`
and holds for every `acc`, `src`, `wBlock`.

**Sub-probe 0.B was not attempted.** Outcome (i)'s own text is unconditional: 0.A closing alone
passes Gate 0 "on the cheap branch," collapsing the entire agreement-lemma workstream (0.B's
target, `canonicalTruthBoxPos`, and Phases 3-6 as originally scoped) into applying the landed
`modalTruthLemmaS4` at the extended accessibility `acc.addEdge src wBlock` directly, with
`extractModelS4 b acc` unchanged as the witness type. Attempting 0.B in addition would pursue
exactly the workstream this outcome supersedes; the Reading Constraint (outcome (vi)) already
disclaims that a pass "does not license reordering or softening any later phase's criteria," so
this verdict claims only what outcome (i) states.

**Re-scope of Phases 3-6, per outcome (i)'s explicit instruction ("re-scope … before dispatching
them, and record the re-scope in this plan").** The redirect-preservation obligation no longer
needs `accPinnedBy`/`branchSatisfiablePinnedIn`/a canonical (subtype-restricted) witness type at
all. The new target, replacing Phases 3-6 as originally scoped:

- **`extractModelS4 b acc` is the witness at every accessibility state**, original and redirected
  alike — no carrier restriction, no pinning conjunct, no second model type. `s4FC` and the edge
  conjunct come free from `extractModelS4_refl`/`extractModelS4_trans`/
  `extractModelS4_hasEdge_imp_r` regardless of `acc`, exactly as they already do for the
  unredirected case.
- **The single remaining obligation is `modalHintikkaSetS4` preservation under the specific
  `addEdge` the keyed guard performs**: given `modalHintikkaSetS4 φ₀ b acc`, show
  `modalHintikkaSetS4 φ₀ b (acc.addEdge src wBlock)`. Applying `modalTruthLemmaS4` at the
  extended accessibility then gives `branchSatisfiableIn`-shaped satisfiability directly — no
  agreement lemma, no `htruthBoxPos`/`htruthDiaNeg` truth-lemma direction, no
  `hpropBox`/`hpropDia` forward-persistence lemma of the shape the probe lemma assumed.
- **This is not free.** `modalHintikkaSetS4`'s saturation conjunct (`modalS4Saturated`) is
  itself parametrized by `acc` through `acc.successorsOf` inside `modalApplyOneS4`'s box/diamond
  rule outputs, so redirecting `src`'s successor set to include `wBlock` changes what saturation
  demands at `src` (and, via `reflTransGen_addEdge_iff`, at every world with a closure-path
  through `src`). Gate B (Phase 2) is exactly the question of whether `modalS4Saturated` is
  available at the ordered-stepper state where this redirect fires, and is **restated below,
  unchanged in substance**, as the load-bearing question for the re-scoped route too — this
  matches outcome (i)'s own caveat that a Phase 1 pass "does NOT make Phase 2 moot."
- **Re-scoped Phase 3** (was: canonical witness instance and three collapsing conjuncts) becomes:
  state the `modalHintikkaSetS4`-preservation-under-`addEdge` target as a named, un-admitted
  obligation in `FrameCompleteness.lean`, decomposing it into its four `modalHintikkaSetS4`
  conjuncts (`isModalClosed` unchanged; the bare saturation conjunct per the note above; the two
  box-negative/diamond-positive witness conjuncts, which are existentials over `acc.hasEdge`
  successors and need `hasEdge_addEdge_cases`/`hasEdge_addEdge_mono_gate0`-style case splits, not
  a new truth lemma). Confirm which conjuncts collapse mechanically (the two existential-witness
  conjuncts are expected to, by the same case-split `reflTransGen_addEdge_iff`'s proof already
  performs at the single-edge level) before Phase 4 is dispatched.
- **Re-scoped Phases 4-5** (was: canonical truth lemma, box-positive and diamond-negative
  directions) become: discharge the bare-saturation conjunct at `acc.addEdge src wBlock`,
  consuming Gate B's `hintikkaS4_box_pos_reflTransGen_wrapped`/
  `hintikkaS4_dia_neg_reflTransGen_wrapped` bridges (or Gate B's recorded additional field, under
  outcome (ii)) together with `reflTransGen_addEdge_iff` to relate reachability under `acc` and
  under `acc.addEdge src wBlock`. No truth lemma over an arbitrary or canonical witness model is
  proved anywhere in the re-scoped route — the semantic side is handled once, by
  `modalTruthLemmaS4`, applied at whichever accessibility relation is in play.
- **Re-scoped Phase 6** (was: redirect-step re-assembly, supersession of the probe lemma) becomes:
  assemble `modalHintikkaSetS4 φ₀ b (acc.addEdge src wBlock)` from re-scoped Phases 3-5's
  conjuncts, apply `modalTruthLemmaS4` at the extended accessibility to conclude the
  redirect-preservation obligation, and **only then** decide the probe lemma's removal — it is
  disposable regardless of route, since the re-scoped route does not consume it at all (it was
  scaffolding for the now-superseded agreement-lemma workstream). Enumerate dependents by grep
  before removing, exactly as originally planned.
- **Phase 7 (wiring, regression, CI) is unaffected in shape**, though its consumed lemma names
  change to match the re-scoped Phase 6 output.

This re-scope is recorded here per outcome (i)'s instruction; re-scoped Phases 3-6 are executed
as separate dispatches following this record, not rewritten as new phase bodies in this plan
file (the phase headings and task lists below remain the v6 originals for provenance — a reader
executing Phase 3 onward must read this Verdict first and follow the re-scope, not the original
canonical-witness task list, which outcome (i) has superseded).

---

### Phase 2: GATE B — `modalS4Saturated` at a settled ordered-stepper state [COMPLETED]

- **Goal:** Determine whether `modalS4Saturated φ₀ b acc` is available at an **intermediate** state —
  specifically at a settled ordered-stepper state where `modalNonMintCandidates φ₀ keys b e acc = []`
  and a blocked step can fire. This is v5's Phase 2, never executed, re-scoped to the current layout.
- **Depends on:** 1
- **Timing:** 3 hours (one dispatch)
- **Verification Tier:** local
- **Scope Hypothesis:** This phase asserts roughly 200 lines appended to
  `Cslib/Logics/Modal/Tableau/LoopChecking.lean` and no other file touched. Confirm against
  `git diff --stat` at phase close. If the attempt requires adding a field to `S4KeyedHintikkaInv`
  (an existing structure with a landed preservation lemma), the tier rises to `interface` and the
  work is **out of this phase's scope** — record the field per outcome (ii) and stop.
- **Owns:** `Cslib/Logics/Modal/Tableau/LoopChecking.lean`, new section appended at end of file.

**Why this is a genuine gate, and why Phase 1 does not subsume it.** `modalHintikkaClauseGen`
(`Saturation.lean`, read-only) matches on the **formula alone** and returns `True` for `.box _` and
`.diamond _` regardless of sign, whereas `modalS4Saturated` (`LoopChecking.lean`, locate by grep)
matches on `(sign, formula)` and carves out only `(.neg, .box)` and `(.pos, .diamond)`. The landed
`S4KeyedHintikkaInv.hintikkaInv` therefore supplies **nothing** for `T(box ψ)` or `F(diamond ψ)` —
exactly the two shapes the canonical construction consumes. The candidate mechanism is the ordered
stepper's own settledness: at a settled state every non-mint-shaped `sf ∈ b` is either in `e` or has
its rule conclusions already on `b`. **The gap is `sf ∈ e`**: a formula expanded against an older,
smaller `acc`, whose conclusion for a later-added edge may be missing. Closing or refuting that gap is
this phase's entire content. This analysis is carried from v5 and is not re-argued.

- **Tasks:**
  - [ ] Re-locate `modalS4Saturated`, `modalNonMintCandidates`, `S4KeyedHintikkaInv`,
        `hintikkaS4_box_pos_step`, `hintikkaS4_box_pos_reflTransGen`, `hintikkaS4_dia_neg_reflTransGen`
        and `hintikka_congr_S4` by grep. Do not use any line number from v5.
  - [ ] Land `hintikkaS4_box_pos_reflTransGen_wrapped` and `hintikkaS4_dia_neg_reflTransGen_wrapped`:
        the **wrapped**-conclusion variants of the landed `_reflTransGen` bridges, by
        `Relation.ReflTransGen.head_induction_on` carrying `T(box ψ)` rather than unwrapping at the
        base. Each is a short transcription of the landed proof with the `_self` step dropped from the
        `refl` case. **These are unconditionally useful and must land sorry-free regardless of the
        gate's verdict** — they are precisely the `hpropBox`/`hpropDia` shapes the probe lemma assumes.
  - [ ] State and attempt the gate lemma:
        ```lean
        lemma modalS4Saturated_of_ordered_settled (φ₀ : Proposition Atom)
            (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
            (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
            (hsettled : modalNonMintCandidates φ₀ keys b e acc = [])
            (hHI : S4KeyedHintikkaInv φ₀ b e acc keys) :
            modalS4Saturated φ₀ b acc
        ```
        The `sf ∉ e` half goes through `modalNonMintCandidates`'s filter predicate plus
        `hintikka_congr_S4`. The `sf ∈ e` half is the gap.
  - [ ] If the `sf ∈ e` half does not close, **name the exact missing fact** as a candidate additional
        field on the keyed Hintikka invariant, write its statement out verbatim, and assess **in the
        same dispatch** whether it is preservable — noting that the box-plus birth content now inline
        in `successorBirthContent` already emits the wrapped forms at mint time, which is what such a
        field would need. Say so if it holds; say what breaks if not.
  - [ ] `lean_verify` on every landed declaration.
  - [ ] Record a `#### Phase 2 Verdict` subsection in this file.

- **Kill criteria and outcomes:**

| Outcome | Verdict |
|---|---|
| (i) The gate lemma closes from `hsettled` + `hHI` + `hintikka_congr_S4` alone | Gate B **PASSES** at its cheapest. Commit. |
| (ii) It needs exactly **one nameable additional invariant field**, written out verbatim and with its preservability argued in the same dispatch | **Route survives at the cost of one added field.** Record the statement verbatim and name the phase that would owe the preservation proof. Do **not** add the field in this phase — doing so changes an existing structure with a landed preservation lemma and is an `interface`-tier change outside this phase's declared scope. |
| (iii) A concrete reachable settled state is exhibited at which `modalS4Saturated` **fails** | **Route (a) is dead.** The canonical construction's saturation premise is false where it is needed. Record the state and return to the blocker record. |
| (iv) Neither closes nor is refuted within this dispatch, and no nameable field is identified | **Route (a) is dead as planned.** One-dispatch budget. Revert the gate lemma, keep the two `_wrapped` bridges (they stand on their own), record the goal state, return to the blocker record. |

- **Done when:** the two `_wrapped` bridges are sorry-free and committed; the gate lemma is either
  sorry-free and committed or reverted with a recorded verdict; bare-tactic sorry census exactly 1;
  scoped `lake build Cslib.Logics.Modal.Tableau.LoopChecking` and `lake exe lint-style` clean.

#### Phase 2 Verdict

**Outcome (i): Gate B PASSES at its cheapest.** Both `_wrapped` bridges
(`hintikkaS4_box_pos_reflTransGen_wrapped`, `hintikkaS4_dia_neg_reflTransGen_wrapped`) landed
sorry-free as short transcriptions of the existing unwrapped proofs, with the `_self` step
dropped from the `refl` case. The gate lemma `modalS4Saturated_of_ordered_settled` **also closed
sorry-free**, in the same dispatch, from `hsettled` + `hHI` alone (plus a per-shape keyed/unkeyed
congruence argument in the spirit of `hintikka_congr_S4`) -- **no additional invariant field was
needed**, contrary to this phase's own honest prior expectation that outcome (ii) was likely.

**Why the apparent `sf ∈ e` gap does not arise.** `S4KeyedHintikkaInv.hintikkaInv` states its
obligation via `modalHintikkaClauseGen`, which is vacuous (`True`) at **every** box/diamond-shaped
formula regardless of sign -- seemingly supplying nothing for the box-positive/diamond-negative
(T-self/4-rule) shapes a member of `e` might have, which is exactly what `modalS4Saturated`
demands real content for. The resolution: `S4KeyedHintikkaInv.eBoxOnlyNeg`/`eDiamondOnlyPos`
(both already-landed fields) force any box/diamond-shaped member of `e` to be **exactly one of
the two minting shapes** (`.neg,.box`/`.pos,.diamond`) -- a box-shaped `e`-member's sign is forced
`.neg`, a diamond-shaped one's sign is forced `.pos`. Once the two minting shapes are excluded
(the gate lemma's outer case split, mirroring `hnb` in `modalApplyOneS4_eq_of_not_boxNeg_diaPos`'s
style), a member of `e` can therefore **never** be box/diamond-shaped at all, so
`modalHintikkaClauseGen`'s vacuity never actually applies to the cases that matter, and
`hintikkaInv` supplies genuine content there -- exactly matching `modalS4Saturated`'s own
requirement once the keyed/unkeyed apply congruence (`modalApplyOneS4Keyed φ₀ keys sf b acc =
modalApplyOneS4 φ₀ sf b acc` for non-mint-shaped `sf`, the same fact `hintikka_congr_S4` and
`S4KeyedHintikkaInv_weaken` already lean on) is applied.

**Verification**: `lean_verify` on `hintikkaS4_box_pos_reflTransGen_wrapped`,
`hintikkaS4_dia_neg_reflTransGen_wrapped`, and `modalS4Saturated_of_ordered_settled` all report
axioms exactly `{propext, Classical.choice, Quot.sound}`. Scoped `lake build
Cslib.Logics.Modal.Tableau.LoopChecking` is clean (no warnings); `lake exe lint-style` is clean;
the bare-tactic sorry census over `Cslib/Logics/Modal/Tableau/` returns exactly one line,
`FrameSoundness.lean:1251`.

**Reading constraint honored**: this pass licenses the re-scoped Phases 3-6 (per the Phase 1
Verdict) to consume `modalS4Saturated_of_ordered_settled` and the two `_wrapped` bridges as
landed facts. It does not itself discharge any part of the `addEdge`-preservation obligation
those phases still own.

---

### Phase 3: Canonical witness instance and the three collapsing conjuncts [COMPLETED]

**Re-scoped per the Phase 1 Verdict (outcome (i)).** This phase now executes the re-scope
recorded there, not the original canonical-witness task list below (which is superseded and left
for provenance only).

#### Phase 3 Progress Record (superseded by the Completion Record below -- kept for provenance)

**Landed, sorry-free** (`FrameCompleteness.lean`, locate by
`grep -n 'modalHintikkaSetS4_addEdge_of_saturated'`):

```lean
lemma modalHintikkaSetS4_addEdge_of_saturated (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (src wBlock : WorldIndex)
    (hH : modalHintikkaSetS4 φ₀ b acc)
    (hSatExt : modalS4Saturated φ₀ b (acc.addEdge src wBlock)) :
    modalHintikkaSetS4 φ₀ b (acc.addEdge src wBlock)
```

This discharges 3 of `modalHintikkaSetS4`'s 4 conjuncts unconditionally (branch-openness
transfers as-is; the box-negative/diamond-positive existential-witness conjuncts transfer via
`hasEdge_addEdge_mono_gate0`, GATE 0's mono helper, reused directly since this lemma lives in the
same file). `lean_verify` reports axioms exactly `{propext, Classical.choice, Quot.sound}`.

**NOT yet discharged -- the single remaining obligation, per the plan's own instruction not to
`sorry` it**: `hSatExt : modalS4Saturated φ₀ b (acc.addEdge src wBlock)` is taken as an assumed
hypothesis above, not derived. Establishing it (for the specific `acc.addEdge src wBlock` the
keyed guard's redirect performs, i.e. under `blockingWorldS4Keyed φ₀ b keys s φ src = some
wBlock`) is re-scoped Phases 4-5's content. Investigation so far, recorded for the next dispatch:

- For `sf` with `sf.label ≠ src`: `(acc.addEdge src wBlock).successorsOf w = acc.successorsOf w`
  for `w ≠ src` (confirmed by unfolding `Accessibility.successorsOf`/`addEdge`: the new edge only
  ever contributes to `src`'s successor list). A "local shape invariance" lemma establishing
  `modalApplyOneS4 φ₀ sf b (acc.addEdge src wBlock) = modalApplyOneS4 φ₀ sf b acc` for
  `sf.label ≠ src` is not yet written but should be a short transcription of
  `modalApplyOneS4Keyed_fst_eq_of_not_box`'s style, keyed off `successorsOf`-invariance rather
  than `b`-invariance.
- For `sf.label = src` and `sf` box-positive/diamond-negative shaped: this is where the new
  successor `wBlock` genuinely adds an obligation. `blockedRedirect_boxed_boxPos_mem`/
  `blockedRedirect_boxed_diaNeg_mem` (`LoopChecking.lean`, already landed, sorry-free) supply
  `T(□χ)@wBlock ∈ b` from `T(□χ)@src ∈ b`, `blockingWorldS4Keyed φ₀ b keys s φ src = some
  wBlock`, `hkL : ∀ w k, (w,k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w` (this is
  `S4LoopInv.keyLowerBd`), and `(Sign.pos, .box χ) ∈ signedSubfmls φ₀`. The last hypothesis is
  available from `S4LoopInv.bClosure` (`∀ x ∈ b, x ∈ modalUniverseS4 φ₀`) via a Finset-membership
  bridge from `modalUniverseS4` to `signedSubfmls` that was not yet located/derived this
  dispatch -- confirm one exists (search `mem_modalUniverseS4`) or derive it directly from
  `modalUniverseS4`'s definition (`LoopChecking.lean:366`).
- Assembling these into a full `modalS4Saturated φ₀ b (acc.addEdge src wBlock)` proof needs one
  more step beyond the per-`χ` transfer: `modalApplyOneS4 φ₀ ⟨.pos,.box ψ,src⟩ b (acc.addEdge src
  wBlock)`'s RESULT is a `.persistent` list merging ALL of `modalTBoxSelf`/`modalFourBoxProp`'s
  content across the (now-extended) successor set, not a single-`χ` fact -- the per-`χ` transfer
  lemmas need to be applied inside a `∀ sf' ∈ newForms, sf' ∈ b`-shaped goal, most likely by
  showing the extended `modalFourBoxProp b (acc.addEdge src wBlock) ψ src`'s membership predicate
  decomposes into "old target" (already covered by `hH`'s saturation at `acc`) or "new target
  `wBlock`" (covered by `blockedRedirect_boxed_boxPos_mem`), mirroring
  `hasEdge_addEdge_cases`'s case split.

#### Phase 3-6 Completion Record (continuation dispatch, folds re-scoped Phases 3-6 into one)

**All four re-scoped phases (3-6) are now COMPLETE, sorry-free, standard-axioms-only
(`propext`, `Classical.choice`, `Quot.sound`, verified both via `lean_verify` and directly via
`lake env lean` + `#print axioms` to rule out the MCP tool's occasional `sorryAx` false
positive).** The previously-open obligation -- `hSatExt : modalS4Saturated φ₀ b (acc.addEdge src
wBlock)`, taken as an explicit hypothesis in the Progress Record above -- is now discharged in
full. Landed declarations, in dependency order:

1. **`successorsOf_addEdge_of_ne`/`successorsOf_addEdge_self`** (`LoopChecking.lean`): the two
   `Accessibility.successorsOf`/`addEdge` case-split facts everything below is built on.
2. **`modalApplyOneS4_boxPos_fst_eq`/`_diaNeg_fst_eq`** (`LoopChecking.lean`): closed forms for
   `modalApplyOneS4`'s `.fst` at the two 4-rule-relevant shapes, isolating every acc-dependent
   subterm as `boxPropagation`/`modalFourBoxProp` (resp. the inline diamond-negative K arm/
   `modalFourDiaNegProp`) applied to that accessibility -- reused by both the congruence lemma
   below and the hard saturation lemma, avoiding re-deriving the T/S4-layer unfolding twice.
3. **`modalApplyOne_fst_eq_of_not_boxPos_diaNeg`/`modalApplyOneS4_fst_eq_of_not_boxPos_diaNeg`/
   `modalApplyOneS4_fst_congr_successorsOf`** (`LoopChecking.lean`): the acc-independence/
   acc-congruence lemmas covering every OTHER shape (non-4-rule-relevant shapes are acc-free
   absolutely; the two guard shapes reduce via the already-landed `modalApplyOneS4_boxNeg_*_eq`/
   `_diaPos_*_eq` lemmas to `modalApplyOne`, which is itself acc-free at those shapes since K's
   mint arms never consult `acc`).
4. **`mem_signedSubfmls_of_formula_s4loop`** (`LoopChecking.lean`, private): the
   `modalSubfmls`-to-`signedSubfmls` bridge needed to supply `blockedRedirect_boxed_boxPos_mem`/
   `_diaNeg_mem`'s `hsf` hypothesis from `S4LoopInv.bClosure`.
5. **`modalS4Saturated_addEdge_of_blocked`** (`LoopChecking.lean`) -- **the hard content**:
   `modalS4Saturated φ₀ b acc → (S4LoopInv.bClosure) → (S4LoopInv.keyLowerBd) →
   (blockingWorldS4Keyed ... = some wBlock) → modalS4Saturated φ₀ b (acc.addEdge src wBlock)`,
   UNCONDITIONALLY (no remaining hypothesis). Proof route, per world/shape: `sf.label ≠ src` is
   invariant via `modalApplyOneS4_fst_congr_successorsOf`; `sf.label = src` non-4-rule-relevant
   shapes are acc-free via `modalApplyOneS4_fst_eq_of_not_boxPos_diaNeg`; `sf.label = src`
   box-positive/diamond-negative shapes are the genuine hard case, closed by combining
   `blockedRedirect_boxed_boxPos_mem`/`_diaNeg_mem` (gives the BOXED fact `T(□χ)@wBlock ∈ b`/
   `F(◇χ)@wBlock ∈ b`) with the already-landed T-self bridges `hintikkaS4_box_pos_self`/
   `hintikkaS4_dia_neg_self` (re-applies `hSat` at the ORIGINAL `acc` to the newly-established
   boxed fact, recovering the UNWRAPPED fact `T(χ)@wBlock ∈ b`/`F(χ)@wBlock ∈ b` -- the T-rule's
   self-propagation arm never consults `acc`, so this works at any accessibility): with both
   facts in hand, `boxPropagation`/`modalFourBoxProp` (resp. the diamond duals) at the extended
   accessibility are shown LITERALLY equal (not just membership-preserving) to their values at
   the original `acc`, since the new `wBlock` branch of each `filterMap` evaluates to `none`.
6. **`modalHintikkaSetS4_addEdge_of_blocked`** (`FrameCompleteness.lean`) -- re-scoped Phases
   3-5's assembly, folded into one: composes `modalHintikkaSetS4_addEdge_of_saturated` (the
   three mechanical conjuncts, previously landed) with `modalS4Saturated_addEdge_of_blocked`
   (item 5) applied to `modalHintikkaSetS4_saturated hH`. `modalHintikkaSetS4` preservation
   under the keyed redirect, UNCONDITIONALLY -- no `modalS4Saturated` hypothesis remains.
7. **`branchSatisfiableIn_s4FC_addEdge_of_blocked`** (`FrameCompleteness.lean`) -- **re-scoped
   Phase 6's capstone**: `branchSatisfiableIn s4FC b (acc.addEdge src wBlock)`, built directly
   from `modalHintikkaSetS4 φ₀ b acc` via item 6 and `modalTruthLemmaS4` applied at the extended
   accessibility with `extractModelS4 b (acc.addEdge src wBlock)` (identity world-assignment) as
   the witness. `s4FC` and the edge conjunct come free from `extractModelS4_refl`/
   `extractModelS4_trans`/`extractModelS4_hasEdge_imp_r`, unconditionally on `acc`, exactly as
   the Phase 1 Verdict predicted. **This is the actual redirect-preservation result** the S4
   keyed loop guard's soundness argument needs -- Phase 7 wires it into the per-step argument.
8. **Phase 6's probe-lemma removal, executed**: `canonicalWitnessRestrictionProbe_
   agreementConditional` and its `/-! ### Canonical-Witness Restriction Conditional Agreement
   Lemma -/` section header are removed from `FrameSoundness.lean` (it was the last declaration
   in the file; `accPinnedBy`/`branchSatisfiablePinnedIn`/`branchSatisfiablePinnedIn_
   redirect_mechanical` are preserved verbatim, per the standing constraint). Dependents
   enumerated by `grep -rn 'canonicalWitnessRestrictionProbe' Cslib/ CslibTests/` before
   removal: zero in actual code (one docstring cross-reference in `LoopChecking.lean`, updated
   to point at the landed replacement instead of removed).

**Verification**: scoped builds of `FrameCompleteness`, `FrameSoundness`, `LoopChecking` are all
clean; `lake exe checkInitImports` and `lake exe lint-style` clean; a full `lake build` (3313
jobs) and `lake test` (including `CslibTests.S4LoopGuardRegression`) both pass; bare-tactic
sorry census over `Cslib/Logics/Modal/Tableau/` returns exactly one line
(`FrameSoundness.lean:1251`, the standing, explicitly-retained sorry).

**What remains**: Phase 7 (wiring item 7's capstone into the keyed ordered driver's actual
per-step soundness argument, extending the regression corpus, and the final full-gate close-out)
is genuinely substantial, separate work -- confirmed by inspecting `modalStepBranchS4KeyedOrdered`
(`LoopChecking.lean`), whose primary-scan/fallback case split (`modalStepBranchS4KeyedOrdered_
cases`) the bespoke step lemma must thread through. Not attempted this dispatch; see the
continuation handoff.

**Do not re-attempt the canonical-witness/pinned-witness apparatus** (original Phase 3's task
list below) -- it is superseded by the Phase 1 Verdict and is not the target.

- **Goal:** Instantiate `branchSatisfiablePinnedIn`'s existential at the canonical choice and
  discharge the three conjuncts the probe classified as collapsing, leaving only the branch conjunct
  outstanding.
- **Depends on:** 1
- **Timing:** 2 hours
- **Verification Tier:** local
- **Scope Hypothesis:** This phase asserts that **three of `branchSatisfiablePinnedIn`'s four
  conjuncts collapse** under the canonical choice (`FC m.r` via `Relation.reflexive_reflTransGen` /
  `Relation.transitive_reflTransGen`; the edge conjunct via `Relation.ReflTransGen.single`; the
  `accPinnedBy` conjunct definitionally, which the probe machine-confirmed in a reverted check). This
  is the probe's classification, not a verified fact of this codebase at this commit. **Confirm each
  of the three independently** by closing it in Lean before relying on it; if any one does not
  collapse as classified, record which and stop rather than absorbing the cost silently. Roughly 120
  lines expected in `FrameCompleteness.lean`.
- **Owns:** `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`, new section appended at end of file.

- **Tasks:**
  - [ ] Re-locate `accPinnedBy`, `branchSatisfiablePinnedIn`, `branchSatisfiablePinnedIn_redirect_mechanical`
        (`FrameSoundness.lean`) and `extractModelS4`, `extractModelS4_r`, `extractModelS4_refl`,
        `extractModelS4_trans`, `extractModelS4_hasEdge_imp_r`, `extractModelWith`
        (`FrameCompleteness.lean`) by grep. **Do not modify any of them.**
  - [ ] Fix the encoding. Per the probe's Restriction B1 decision, the carrier is
        `{w : WorldIndex // w ∈ modalKnownWorlds b}` with `f` the coercion; per the probe's Phase 3
        pricing, the fully canonical choice is `m.r := Relation.ReflTransGen (acc.hasEdge)` and the
        valuation is `extractModelWith`'s clause. Record in the docstring **which of the two the
        implementation takes and why**: B1's subtype carrier discharges `accPinnedBy`'s membership
        hypotheses by typing, while the `WorldIndex` carrier reuses `extractModelS4` verbatim. If the
        two must be bridged, land the bridge here and name it; do not leave the encoding implicit.
  - [ ] Discharge `FC m.r` (`s4FC`): reflexivity and transitivity free off `ReflTransGen`, the same
        route `extractModelS4_refl` / `extractModelS4_trans` already take.
  - [ ] Discharge the edge conjunct via `Relation.ReflTransGen.single` (the landed
        `extractModelS4_hasEdge_imp_r` is the same fact — reuse rather than re-derive).
  - [ ] Discharge the `accPinnedBy` conjunct. The probe machine-confirmed the hypothesis becomes
        definitionally identical to the conclusion under the canonical relation. Confirm; if it is
        `id`, say so in the docstring rather than writing a proof that hides the fact.
  - [ ] State the branch conjunct as the single remaining obligation, as an explicit `def` or lemma
        statement with the canonical model already substituted, so Phases 4-6 have a fixed target.
        **Do not `sorry` it** — state it as a hypothesis of a downstream lemma, not as an admitted fact.
  - [ ] `lean_verify` on every landed declaration.

- **Done when:** the three conjuncts are sorry-free and committed with the canonical witness
  substituted; the branch conjunct is stated as a named, un-admitted obligation; bare-tactic sorry
  census exactly 1; scoped `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` and
  `lake exe lint-style` clean.

---

### Phase 4: Canonical truth lemma, box-positive direction [COMPLETED]

- **Goal:** Prove the box-positive semantic-to-syntactic direction at the canonical model, at the
  price Phase 1 established, discharging the `htruthBoxPos` group the probe lemma assumes.
- **Depends on:** 2, 3
- **Timing:** 2.5 hours
- **Verification Tier:** local
- **Scope Hypothesis:** This phase asserts the box-positive case is separable from the diamond-negative
  case and independently closable, and estimates roughly 150 lines in `FrameCompleteness.lean`.
  Confirm separability by closing the box side without any diamond-side lemma in scope; if the two
  cases turn out to be mutually recursive (a single induction carrying both polarities, as the landed
  `modalTruthLemmaS4` does), merge Phases 4 and 5 into one and record the merge here rather than
  proving half a mutual induction.
- **Owns:** `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`, extending Phase 3's section.

- **Tasks:**
  - [ ] Re-read Phase 1's `#### Phase 1 Verdict` and execute the branch it licensed. Under outcome (i)
        this phase is the `modalHintikkaSetS4`-preservation-under-`addEdge` argument, not a new
        induction. Under outcomes (ii)/(iii) it is the truth-lemma induction proper. **Do not execute a
        branch Phase 1 did not license.**
  - [ ] Consume Phase 2's `hintikkaS4_box_pos_reflTransGen_wrapped` and, if Gate B passed at (i),
        `modalS4Saturated_of_ordered_settled`. If Gate B passed at (ii), the recorded additional field
        is a **hypothesis** of this phase's lemma, not something this phase establishes.
  - [ ] Mirror the landed `modalTruthLemmaS4`'s induction shape (strong recursion on
        `modalComplexity`) rather than inventing a new one — it is the shape the box case is already
        known to close under in this codebase.
  - [ ] Record explicitly, in the docstring, which hypotheses remain assumed and which phase owes each.
  - [ ] `lean_verify`; require only `propext`, `Classical.choice`, `Quot.sound`.

- **Done when:** the box-positive direction is sorry-free and committed, or the phase is recorded as
  `[BLOCKED]` with the exact `lean_goal` and no `sorry` committed; bare-tactic sorry census exactly 1;
  scoped build and `lake exe lint-style` clean.

---

### Phase 5: Canonical truth lemma, diamond-negative direction, and the initial-state branch conjunct [COMPLETED]

- **Goal:** Prove the diamond-negative dual, then assemble the full branch conjunct at the initial
  (pre-redirect) state, closing Phase 3's stated obligation.
- **Depends on:** 4
- **Timing:** 2.5 hours
- **Verification Tier:** local
- **Scope Hypothesis:** This phase asserts the diamond-negative case is the exact dual of Phase 4's
  box-positive case and therefore costs less than it, and estimates roughly 150 lines. Confirm by
  transcription: if the dual does **not** go through by mirroring Phase 4, that is a real asymmetry
  and must be recorded, not absorbed — v5's Gate A outcome (v) treated a box/diamond split as a route
  killer for good reason (a prior report measured 40 counterexamples for a wrapped-only transfer), and
  the same reasoning applies here.
- **Owns:** `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`, extending Phase 3's section.

- **Tasks:**
  - [ ] Prove the diamond-negative direction as the dual of Phase 4, consuming Phase 2's
        `hintikkaS4_dia_neg_reflTransGen_wrapped`.
  - [ ] **If the box half closes and the diamond half does not (or vice versa)**: do not proceed on the
        box half alone, and do not fall back to a wrapped-only transfer. Record the asymmetry and treat
        it as a route-terminating finding, returning to the blocker record.
  - [ ] Assemble the branch conjunct at the initial state, discharging the obligation Phase 3 stated.
        The probe priced this as cheap ("canonical base-case assembly, 1.5h") **conditional on** the
        truth lemma; that conditionality is now met by Phases 4-5.
  - [ ] `lean_verify` on every landed declaration.

- **Done when:** `branchSatisfiablePinnedIn s4FC b acc` is established at the canonical witness,
  sorry-free, for a branch at the relevant state; bare-tactic sorry census exactly 1; scoped build and
  `lake exe lint-style` clean.

---

### Phase 6: Redirect-step re-assembly, and supersession of the probe lemma [COMPLETED]

- **Goal:** Discharge the redirect-preservation obligation at the canonical witness — the obligation
  five routes died on — and remove the now-superseded probe lemma.
- **Depends on:** 5
- **Timing:** 2.5 hours
- **Verification Tier:** interface
- **Commit Mode:** per-substep
- **Scope Hypothesis:** This phase asserts it touches exactly two files
  (`FrameCompleteness.lean` for the new lemma, `FrameSoundness.lean` for the probe-lemma removal) and
  that `branchSatisfiablePinnedIn_redirect_mechanical` requires **no** modification. Confirm the
  latter by building `FrameCompleteness` after the removal and by `git diff` showing no hunk touching
  that declaration. The `interface` tier is taken because removing a public declaration from
  `FrameSoundness.lean` is a visible-signature change for its dependents, even though the expected
  dependent count is zero — enumerate the dependents with
  `grep -rn 'canonicalWitnessRestrictionProbe' Cslib/ CslibTests/` before removing, and build each.
- **Owns:** `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`;
  `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (removal of the probe lemma and its section header
  only — `accPinnedBy`, `branchSatisfiablePinnedIn`, `branchSatisfiablePinnedIn_redirect_mechanical`
  and the standing sorry are all untouched).

- **Tasks:**
  - [ ] State and prove the redirect-preservation lemma at the canonical witness: from
        `branchSatisfiablePinnedIn s4FC b acc` at the canonical witness plus the wrapped transfers and
        the membership facts, conclude `branchSatisfiablePinnedIn s4FC b (acc.addEdge src wBlock)`.
  - [ ] **Reuse `branchSatisfiablePinnedIn_redirect_mechanical` verbatim** for the three mechanical
        conjuncts. The probe report established it is parametric over any witness satisfying them and
        survives unconditionally, with all four proof bullets intact. **Do not re-derive it.**
  - [ ] Supply the branch conjunct from Phases 4-5. Under Phase 1 outcome (i) this is the
        `addEdge`-decomposition route; otherwise it is the agreement-lemma route with the truth-lemma
        hypotheses now discharged.
  - [ ] Enumerate dependents of `canonicalWitnessRestrictionProbe_agreementConditional` by grep;
        confirm zero (or fix them); then remove the lemma and its
        `/-! ### CANONICAL-WITNESS RESTRICTION PROBE ... -/` section header from `FrameSoundness.lean`.
        Record the removal and its rationale in the new lemma's docstring, by declaration name, with
        no task numbers.
  - [ ] `lean_verify` on the new lemma; require only `propext`, `Classical.choice`, `Quot.sound`.

- **Done when:** the redirect-preservation lemma is sorry-free and committed; the probe lemma is
  removed and every dependent builds; bare-tactic sorry census exactly 1; `lake build` of
  `Cslib.Logics.Modal.Tableau.FrameSoundness` **and** `Cslib.Logics.Modal.Tableau.FrameCompleteness`
  and `lake exe lint-style` all clean.

---

### Phase 7: Wire into the soundness argument, regression, and CI [IN PROGRESS]

- **Goal:** Connect the redirect-preservation result to the keyed ordered driver's soundness argument,
  extend the regression corpus, and close out with a full gate run.
- **Depends on:** 6
- **Timing:** 3 hours
- **Verification Tier:** full
- **Scope Hypothesis:** This phase asserts a file set of `FrameCompleteness.lean`,
  `LoopChecking.lean`, and `CslibTests/S4LoopGuardRegression.lean`, and asserts that the wiring does
  **not** require touching `FrameSoundness.lean`. Both are hypotheses. Confirm against
  `git diff --stat` at phase close. The probe priced this workstream at 3-5 hours over 1-2 phases and
  flagged it as the least-specified; if the real work exceeds one phase, split it and record the split
  rather than running an unbounded phase.
- **Owns:** `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`,
  `Cslib/Logics/Modal/Tableau/LoopChecking.lean`, `CslibTests/S4LoopGuardRegression.lean`.

- **Tasks:**
  - [x] Wire the redirect-preservation lemma into the per-step preservation argument for the keyed
        ordered driver. *(deviation: partial — see Phase 7 Progress Record below. The bespoke
        step-preservation lemma is not yet fully assembled; three of its case-split arms are now
        landed sorry-free as standalone case-scoped lemmas (propositional/non-modal, and both
        mint-unblocked shapes), and the exact remaining case-split and reusable ingredients are
        catalogued in the Progress Record, including a correction to the mint-blocked case's
        previously-catalogued "cheapest" route, which does not actually work as a per-step
        argument.)*
  - [x] Record the **layering note** the import graph forces: soundness content for the keyed ordered
        driver now necessarily lives in `FrameCompleteness.lean`, because that is the only file seeing
        both `LoopChecking` and `FrameSoundness`. Write this as a module-comment note naming the
        constraint and the files, with no task numbers. Do **not** attempt a file split — out of scope.
        *(Landed as the "Re-scoped Phase 7" module comment, `FrameCompleteness.lean`.)*
  - [ ] Extend `CslibTests/S4LoopGuardRegression.lean` with a permanent witness row for the
        redirect-preservation result. Keep every existing row unchanged, including the ordered-driver
        `"OPEN"` row on the counterexample formula. *(deviation: deferred — blocked on the step lemma
        this row would witness.)*
  - [ ] Run the full gate set: `lake build` (whole library), `lake exe lint-style`, `lake lint`, and
        the regression test file. *(deviation: deferred to phase close, once the step lemma lands;
        the scoped `FrameCompleteness` build, `lint-style`, and sorry census were run this dispatch
        for the one landed lemma and are clean.)*
  - [ ] Final census check and summary. *(deviation: deferred — phase not yet closed.)*

#### Phase 7 Progress Record (fourth continuation dispatch; phase remains `[IN PROGRESS]`)

**Landed this dispatch (sorry-free, `{propext, Classical.choice, Quot.sound}` only, confirmed by
direct `#print axioms` since `lean_verify`'s source-scan heuristic reports a known spurious
`sorryAx` on these declarations)** — both remaining 4-rule cases catalogued as the single
largest remaining piece by the prior dispatch:

- `modalApplyOneS4Keyed_boxPos_sat` (`FrameCompleteness.lean`) — closes the **4-rule,
  box-positive** case (`T(□φ)@w`). Bridges `modalApplyOneS4Keyed` down to `modalApplyOneS4Rules`
  at this shape via `LoopChecking.lean`'s already-landed (de-privatized this dispatch)
  `modalApplyOneS4Keyed_boxPos_eq_S4Rules` (a direct `rfl`), then discharges the resulting
  obligation with a new `modalApplyOneS4Rules_boxPos_soundIn`. That lemma composes three sound
  layers: K's own `boxPos` arm (`modalApplyOne_boxPos_sound`, pre-existing), the T self-
  propagation layer reused as a **black box** via the already-landed
  `modalApplyOneT_boxPos_soundIn` (feeding it `hFC.1 : reflFC m.r` extracted from `s4FC`'s
  reflexivity conjunct — no need to re-derive the K+T composition), and the 4-rule propagation
  layer (`modalFourBoxProp`) proved directly inline via one hop of `IsTrans` (`hFC.2`) off the
  recorded successor edge, mirroring `branchSatisfiableIn_s4FC_boxPos_trans_mem`'s semantic core
  but re-derived for a FIXED `(m, f)` rather than an existentially-quantified model (the
  `branchSatisfiableIn`-flavored lemmas in `FrameSoundness.lean` cannot be applied as black boxes
  to a caller's specific model, same reasoning the pre-existing `modalApplyOneT_boxPos_soundIn`'s
  own doc comment already states for the T-self layer).
- `modalApplyOneS4Keyed_diaNeg_sat` — direct dual, closes the **4-rule, diamond-negative** case
  (`F(◇φ)@w`), via `modalApplyOneS4Rules_diaNeg_soundIn`.

**Discovery: most of the `.fst`/bridge infrastructure this case needed already existed,
privately, un-connected to `FrameCompleteness.lean`.** The prior Progress Record catalogued this
case as needing new merge-lemma infrastructure from scratch. On inspection, `LoopChecking.lean`
already contained (private, apparently authored in anticipation during an earlier phase but never
wired to `FrameCompleteness.lean`): `modalApplyOneS4Rules_boxPos_fst`/`_diaNeg_fst` (the exact
`.fst` closed form in terms of `modalApplyOneT`'s own result) and
`modalApplyOneS4Keyed_boxPos_eq_S4Rules`/`_diaNeg_eq_S4Rules` (the Keyed→S4Rules bridge, `rfl`).
This dispatch de-privatized exactly these four (plus two small transitively-needed private `.snd`
facts, `modalApplyOneS4Rules_snd_eq` and `modalApplyOne_boxPos_snd_S4`/`_diamondNeg_snd_S4`) and
added two new small companion lemmas (`modalApplyOneS4Rules_boxPos_snd_eq_acc`/
`_diaNeg_snd_eq_acc`) rather than re-deriving the `.fst` closed forms from scratch as the catalogue
suggested. An earlier attempt this dispatch to build fresh, differently-named driver lemmas
directly in `LoopChecking.lean` hit two real obstacles worth recording: (1) name collisions with
this already-existing private infrastructure, and (2) `LoopChecking.lean` does not import
`TDriver.lean`, so a `modalApplyOneT`-level case-split lemma
(`modalApplyOneT_boxPos_eq`/`_diaNeg_eq`, needed as the outer case-split for the K+T+4 merge)
cannot live there — it was placed in `FrameCompleteness.lean` instead, which already imports
`TDriver.lean` per the file's own layering note.

Verification per lemma: scoped `lake build Cslib.Logics.Modal.Tableau.LoopChecking` and
`lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` both clean; `lake exe lint-style` clean
on both files; sorry-free confirmed via direct `#print axioms` on all four new
`FrameCompleteness.lean` declarations (`modalApplyOneS4Rules_boxPos_soundIn`,
`modalApplyOneS4Rules_diaNeg_soundIn`, `modalApplyOneS4Keyed_boxPos_sat`,
`modalApplyOneS4Keyed_diaNeg_sat`). Bare-tactic sorry census over `Cslib/Logics/Modal/Tableau/`
stayed at exactly 1 (`FrameSoundness.lean:1251`, standing, retained) after each commit. A
whole-project `lake build` was re-run this dispatch and is clean. `lake exe checkInitImports` is
clean. Two separate green commits, one per file, per the phase-substep commit convention.

**Updated case-split table**:

| Case | Status |
|------|----|
| Propositional/non-modal | **Landed** (`modalApplyOneS4Keyed_notBoxDia_sat`) |
| Mint, unblocked (box-negative) | **Landed** (`modalApplyOneS4Keyed_boxNeg_mint_sat`) |
| Mint, unblocked (diamond-positive) | **Landed** (`modalApplyOneS4Keyed_diaPos_mint_sat`) |
| 4-rule, box-positive (`T(□φ)@w`) | **Landed this dispatch** (`modalApplyOneS4Keyed_boxPos_sat`) |
| 4-rule, diamond-negative (`F(◇φ)@w`) | **Landed this dispatch** (`modalApplyOneS4Keyed_diaNeg_sat`) |
| Mint, blocked (redirect) | **Still open** — the sole remaining case. Not attempted this dispatch, per explicit out-of-scope instruction; see the third-dispatch Progress Record's "Correction to the previously-catalogued mint-blocked route" below for the full technical dead-end analysis. That analysis is unchanged and still stands. |

**Four of the five case-split arms are now landed sorry-free.** Mint-blocked (redirect) is the
ONLY remaining case, and it blocks assembling a complete dispatcher theorem regardless of how
cheap the other four are — the architectural question raised in the third-dispatch record (does
the induction need a stronger threaded invariant, or does the per-step decomposition need
rethinking at the phase-design level) is unresolved and still needs planning-level or user
attention before further implementation on that specific case. Phase 7 stays `[IN PROGRESS]`, not
`[COMPLETED]` — do not mark it complete while any case is open, regardless of how small the
remainder looks.

**Not yet done, deferred to phase close**: assembling the single dispatcher theorem (blocked on
mint-blocked), extending the regression corpus with an `"OPEN"` counterexample row (also blocked
on the step lemma it would witness), and the full 8-step CI gate (`lake lint` full repo,
`lake test`, `lake shake`, `lake exe mk_all --module`) beyond what this dispatch already ran
(`checkInitImports`, scoped builds, `lint-style`, whole-project `lake build`).

#### Phase 7 Progress Record (third continuation dispatch; phase remains `[IN PROGRESS]`)

**Landed this dispatch (sorry-free, `{propext, Classical.choice, Quot.sound}` only, confirmed by
direct `#print axioms` since `lean_verify`'s source-scan heuristic reports a known spurious
`sorryAx` on these declarations)**, all in `FrameCompleteness.lean`:

- `modalApplyOneS4Keyed_notBoxDia_sat` — closes the **propositional/non-modal** case. At any
  signed formula whose top-level connective is neither `box` nor `diamond`,
  `modalApplyOneS4Keyed` reduces to plain K's `modalApplyOne`
  (`modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box`, un-privatized in `LoopChecking.lean` to
  make the reduction visible across the file boundary the layering note requires), and
  `tryAllPropRules_sat` discharges `RuleResultSat` preservation in one call.
- `modalApplyOneS4Keyed_boxNeg_mint_sat` — closes the **mint-unblocked, box-negative** case
  (`F(□ψ)@w`, `blockingWorldS4Keyed = none`). Mirrors the plain-K box-negative mint arm's
  fresh-witness pointwise extension `f'` verbatim (`FrameSoundness.lean`'s `neg`/`box φ` case,
  ~lines 606-720), with `boxPlusExtraS4_sat` closing the extra chunk.
  `modalApplyOneS4KeyedMint_boxNeg_eq_S4` (already-landed closed form) supplied the exact literal
  payload, avoiding any need to re-derive the K witness-group structure.
- `modalApplyOneS4Keyed_diaPos_mint_sat` — direct dual, closes the **mint-unblocked,
  diamond-positive** case (`T(◇ψ)@w`).

Each is stated as a case-scoped, standalone lemma (not yet wired into a single dispatcher
theorem) — same pattern `boxPlusExtraS4_sat` established: `∃ nf, modalApplyOneS4Keyed φ₀ keys sf
b acc = (RuleResult.linear nf, newAcc) ∧ branchSatisfiableIn s4FC (nf ++ b) newAcc`. Three of the
five-ish case-split arms are now done. Sorry census over `Cslib/Logics/Modal/Tableau/` unchanged
at exactly 1 (the standing, retained `FrameSoundness.lean:1251`). Scoped build and
`lake exe lint-style` clean after each landed lemma; whole-project `lake build` also re-confirmed
clean this dispatch (not run at the end of the prior two dispatches).

**Correction to the previously-catalogued mint-blocked route (discovered this dispatch, not a
speculation)**: the prior Progress Record catalogued mint-blocked (redirect) as the **cheapest**
remaining case, "via `branchSatisfiableIn_s4FC_addEdge_of_blocked` (the Phase 6 capstone)
directly". This does **not** work as a per-step lemma. `branchSatisfiableIn_s4FC_addEdge_of_
blocked` takes `hH : modalHintikkaSetS4 φ₀ b acc` as a hypothesis — the FULL saturated-branch
Hintikka set, whose conjuncts 3/4 require **every** box-negative/diamond-positive-shaped formula
on the ENTIRE branch `b` to already have a witness successor, not just the one currently firing.
It builds an entirely fresh canonical model via `extractModelS4`, discarding whatever ambient
`(W, m, f)` `hsat` supplied — it is a *terminal, fully-saturated-branch* construction (matching
the open-branch countermodel step at the end of a completeness argument), not a per-step
invariant. At an arbitrary settled ordered-stepper state (`modalNonMintCandidates = []`, the
precondition under which a mint-blocked step can fire per `modalStepBranchS4KeyedOrdered_
mintReady`), settledness only guarantees every *non-minting* rule has already fired — it says
nothing about whether *other* mint-shaped formulas on `b` already have witnesses (only the one
formula `modalStepBranchS4KeyedBody` selects is being processed this step; siblings are
processed one at a time by later steps). So `modalHintikkaSetS4 φ₀ b acc` genuinely does not hold
at this point, and the capstone's hypotheses cannot be discharged from `S4LoopInv`/
`S4KeyedHintikkaInv` alone.

A genuine per-step argument (extending the SAME ambient `(W, m, f)`, the way the three landed
cases above do) needs `m.r (f w) (f wBlock)` to hold in that arbitrary model — but `wBlock` is
chosen by `blockingWorldS4Keyed` via a purely **syntactic** comparison (`key(wBlock) ⊆
relevantSetFinset φ₀ b w`, `S4LoopInv.keyLowerBd`), which has no a priori semantic connection to
an arbitrary model that happens to satisfy `b`. Neither route (rebuild-canonical-model,
extend-ambient-model) closes with the invariants currently available to a per-step lemma. This
looks like a genuine open architectural question, not a proof-engineering gap closable by more
lemma-chaining within a dispatch: either (a) the induction needs a STRONGER invariant than plain
`branchSatisfiableIn s4FC b acc` threaded through every step (e.g. carrying enough of
`modalHintikkaSetS4`-style saturation, or a dedicated "redirect edges are already realized"
witness, incrementally), or (b) the mint-blocked case is not provable as a literal per-step
preservation lemma at all and the soundness architecture for the keyed ordered driver needs to be
rethought at the phase-design level (flagged to the user, not silently worked around). **Do not
re-attempt the `branchSatisfiableIn_s4FC_addEdge_of_blocked`-direct route in a future dispatch
without first resolving this** — it is a dead end as stated, confirmed by inspection of both
`modalHintikkaSetS4`'s conjunct 3/4 and `modalNonMintCandidates`'s definition (`LoopChecking.lean`).

**Remaining case-split (updated)**:

| Case | Status |
|------|----|
| Propositional/non-modal | **Landed** (`modalApplyOneS4Keyed_notBoxDia_sat`) |
| Mint, unblocked (box-negative) | **Landed** (`modalApplyOneS4Keyed_boxNeg_mint_sat`) |
| Mint, unblocked (diamond-positive) | **Landed** (`modalApplyOneS4Keyed_diaPos_mint_sat`) |
| Mint, blocked (redirect) | **Open, and harder than previously catalogued** — see correction above. Needs either a stronger threaded invariant or a rethought architecture; not closable by direct reuse of `branchSatisfiableIn_s4FC_addEdge_of_blocked`. |
| 4-rule, box-positive (`T(□φ)@w`) | Open, unchanged from prior catalogue (see below) — still the single largest remaining piece. |
| 4-rule, diamond-negative (`F(◇φ)@w`) | Open, dual of the above. |

**4-rule cases, unchanged from the prior Progress Record (not yet attempted this dispatch)**:
box-positive via `modalApplyOneS4_boxPos_fst_eq` (`LoopChecking.lean:9587`, the exact
three-layer closed form: K's `boxPropagation`, THEN `modalTBoxSelf` dedup-appended, THEN
`modalFourBoxProp` dedup-appended) — needs a not-yet-built merge lemma composing
`modalApplyOne_boxPos_sound` (`SoundnessStep.lean:447`) + `modalTBoxSelf_sound`
(`FrameSoundness.lean:1019`) + `modalFourBoxProp_sound` (`FrameSoundness.lean:1123`), plus a
Keyed→S4 `.fst`-equality bridge at this shape (`modalApplyOneS4Keyed_boxPos_diaNeg_not_expanding`
+ `modalApplyOneS4Rules_boxPos_diaNeg_known_S4`, both un-privatized if consumed from
`FrameCompleteness.lean` the same way this dispatch un-privatized the propositional bridge).
Diamond-negative is the dual via `modalApplyOneS4_diaNeg_fst_eq` (`LoopChecking.lean:9658`),
`modalTDiaNegSelf_sound` (`FrameSoundness.lean:1037`), `modalFourDiaNegProp_sound`
(`FrameSoundness.lean:1143`).

**Suggested order for the next dispatch**: resolve the mint-blocked architectural question first
(it blocks assembling ANY complete dispatcher theorem, since every case must close for the
top-level step lemma to typecheck) — likely needs user/planning input on whether to strengthen
the induction invariant or restructure, rather than pure proof engineering — then, in parallel or
afterward, build the 4-rule box-positive merge lemma (dual gives diamond-negative faster).

#### Phase 7 Progress Record (second continuation dispatch — superseded by the record above,
retained for history)

**Confirmed scope, not anticipated at planning time**: `modalStepBranchS4KeyedOrdered` has
**no existing soundness theory at all** to build on — not even for the *plain* (unkeyed) S4
driver. `FrameSoundness.lean`'s `## S4 (Reflexive-Transitive Frame)` section contains only
rule-level building blocks (`modalFourBoxProp_sound`/`modalFourDiaNegProp_sound`,
`branchSatisfiableIn_s4FC_boxPos_trans_mem`/`_diaNeg_trans_mem`, the T-rule self-propagation
lemmas), never a full step-preservation theorem comparable to `modalStepBranchS5Gen_preserves_
satIn`/`modalStepBranchFive_preserves_satIn`/`modalStepBranchKb5''_preserves_satIn`. The bespoke
step lemma this phase needs is therefore full new content on the same order as those three
assemblies (each several hundred lines), not a small wiring shim — confirming the plan's own
flag that this workstream is "the least-specified" and may need a split.

**Landed this dispatch (sorry-free, `{propext, Quot.sound}` only)**:
- `boxPlusExtraS4_sat` (`FrameCompleteness.lean`): the one piece of genuinely new SEMANTIC
  content the mint-unblocked step case needs. `modalApplyOneS4KeyedMint`'s payload is
  `modalApplyOne`'s own K witness group **plus** `boxPlusExtraS4 b w` (BOXED transmission of
  every `T(□ψ)@w`/`F(◇ψ)@w` already on the branch, retargeted to the fresh witness `w'`). This
  lemma shows every `boxPlusExtraS4` element is satisfied at the extended world-assignment, via
  one hop of `s4FC`'s `IsTrans` off the mint edge `m.r (f w) ww`: a `T(□ψ)@w` fact universally
  quantifies over all `m.r`-successors of `f w`; any successor of the fresh witness `ww` is also
  a successor of `f w` by transitivity, so the SAME universal fact reinstates literally
  (`T(□ψ)@w'`, not just the unwrapped `T(ψ)@w'` K's own mint already transmits). Diamond-negative
  is the direct contrapositive dual.
- The Phase 7 layering-note module comment.

**Reusable ingredients catalogued for the remaining case-split** (the bespoke step lemma should
mirror `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv`'s case-split shape exactly --
`LoopChecking.lean`, `by_cases hmint : (neg,box) ∨ (pos,diamond)`, sub-split on
`blockingWorldS4Keyed`):

| Case | Ingredients (all pre-existing except `boxPlusExtraS4_sat`) |
|------|----|
| Mint, blocked (redirect) | `branchSatisfiableIn_s4FC_addEdge_of_blocked` (this file's own Phase 6 capstone) directly, with `hUniv := hLoopInv.bClosure`, `hkL := hLoopInv.keyLowerBd` (`S4LoopInv` field names confirmed by grep). Expected to be the **cheapest** remaining case. |
| Mint, unblocked | `modalApplyOneS4Keyed_boxNeg_unblocked_eq`/`_diaPos_unblocked_eq` + `modalApplyOneS4KeyedMint_boxNeg_witness`/`_diaPos_witness` (`LoopChecking.lean`) give the exact output shape (`modalApplyOne`'s own K witness group `++ boxPlusExtraS4 b lbl`, `.snd = acc.addEdge lbl (modalNextWorld b)`). Mirror the K mint construction in `FrameSoundness.lean` lines 412-472 (diamond-positive `T(◇φ)@w` mint) / 606-691 (box-negative `F(□φ)@w` mint) verbatim for the `f' := fun n => if n = w' then ww else f n` extension and the base witness/`boxProps`/`diaNegProps` satisfiability, then append `boxPlusExtraS4_sat` (landed) for the extra chunk. |
| 4-rule, box-positive (`T(□φ)@w`) | `modalApplyOneS4_boxPos_fst_eq` (`LoopChecking.lean:9587`) gives the exact three-layer closed form (K's `boxPropagation`, persistent-or-notApplicable, THEN `modalTBoxSelf` appended with a `filter (!kForms.any ...)` dedup, THEN `modalFourBoxProp` appended with the same dedup pattern). **Not yet built**: a merge lemma showing this dedup-append-of-three-sound-layers preserves `RuleResultSat`/`branchSatisfiableIn s4FC`, composing `modalApplyOne_boxPos_sound` (`SoundnessStep.lean:447`, K layer) + `modalTBoxSelf_sound` (`FrameSoundness.lean:1019`, T layer) + `modalFourBoxProp_sound` (`FrameSoundness.lean:1123`, 4 layer). This is the single largest remaining piece of new proof content (three `RuleResultSat`-preserving-append arguments chained, each needing to show the `filter` dedup doesn't drop any element whose satisfiability isn't ALREADY covered by an earlier layer). Also needs `(modalApplyOneS4Keyed φ₀ keys sf b acc).fst = (modalApplyOneS4 φ₀ sf b acc).fst` at this shape, via `modalApplyOneS4Keyed_boxPos_diaNeg_not_expanding` + `modalApplyOneS4Rules_boxPos_diaNeg_known_S4` (both `LoopChecking.lean`, already landed) bridging Keyed → Rules → (need one more bridge) S4. |
| 4-rule, diamond-negative (`F(◇φ)@w`) | Dual of the above via `modalApplyOneS4_diaNeg_fst_eq` (`LoopChecking.lean:9658`), `modalTDiaNegSelf_sound` (`FrameSoundness.lean:1037`), `modalFourDiaNegProp_sound` (`FrameSoundness.lean:1143`). |
| Propositional/non-modal (atom, bot, and, or, imp) | `modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box` (`LoopChecking.lean`, already landed) reduces to plain `modalApplyOne`. `tryAllPropRules_sat` (`SoundnessStep.lean:369`) then gives `RuleResultSat m f (tryAllPropRules ... sf)` from `sfSat m f sf` **in one call**, covering all five propositional shapes at once — this is dramatically cheaper than the ~350-line inline case-by-case duplication `modalStepBranchGen_preserves_satIn` (`FrameSoundness.lean:197`) uses (that duplication predates `tryAllPropRules_sat`'s extraction, or simply never adopted it). Only a small generic "append a `RuleResultSat` result to the branch preserves `branchSatisfiableIn FC`" wrapper is needed on top (not yet built, but mechanical, matching the `.linear`/`.branching`/`.persistent` pattern every existing assembly already uses inline). Expected to be the **second-cheapest** remaining case. |

**Suggested order for the next dispatch** (cheapest first, to bank incremental green commits):
propositional → mint-blocked (redirect) → mint-unblocked → 4-rule box-positive → 4-rule
diamond-negative (dual, should be faster once box-positive's pattern is established) → assemble
the full step lemma → extend the regression corpus → run the full gate set.

**Not yet determined**: whether Phase 7's "wiring" scope (per its literal task list) requires
only the STEP-level preservation lemma, or also the fuel-induction wrapper and a
`modalTableauS4KeyedOrdered_sound`-shaped end-to-end capstone (mirroring `modalTableauS5_sound`
etc.). The task list's four bullets (wire the step argument, layering note, regression,
full gate) read as bounded to the step lemma; if a future dispatch judges the fuel-induction/
capstone chain is also required, that is enough additional work (comparable in size to the S5
Bespoke Fuel-Induction Assembly, `FrameSoundness.lean:2453-3320`) that it should be split into
its own phase and recorded as such, not absorbed silently.

---

## Terminal Condition

**If Gate 0 (Phase 1) fails at outcome (iv) or (v), or Gate B (Phase 2) fails at outcome (iii) or
(iv), this plan does not propose a further route.**

Six routes have now failed at one obligation, by six distinct mechanisms: redirect inertness
(machine-checked false), the origin-edge revision (abandoned), ancestor-only blocking (arbitrary
witness model), the subtractive `red` channel (unwrapped facts have no persistence mechanism), the
pinned-witness agreement argument (escape to non-label model points), and — if Gate 0 fails — the
canonical-witness truth lemma (a downward-saturated branch is not decided at box-shaped formulas).
The probe task was itself the answer to the fifth failure's escalation, and it returned a
**conditional** GO whose condition is precisely what Gate 0 tests.

**The correct action on failure is to return to the blocker record**, not to invent a seventh route:

1. Write the verdict into this plan's `#### Phase N Verdict` subsection with the exact `lean_goal` or
   the exhibited counterexample branch.
2. Update `specs/553_.../reports/05_gate-a-canonical-witness-blocker-analysis.md` with a pointer to
   the new verdict.
3. Set the task to `[BLOCKED]` with a blocker record naming the specific obstruction, and escalate for
   a **user decision** between (a) a further apparatus-restructuring programme and (b) accepting that
   the keyed S4 guard's soundness obligation stays open with the standing documented `sorry`.
4. In an orchestrated dispatch, record this as a `state_updates_pending` entry in
   `.orchestrator-handoff.json` rather than editing `specs/state.json` directly.

Given six failures out of six, the base rate says a gate will fire. **That is the expected outcome,
and this plan is built to reach it in 2.5 hours rather than to avoid recording it.**

---

## Testing & Validation

- [ ] **Sorry census, at every phase boundary.** Run the **bare-tactic** grep — not a
      prose-matching grep, which returns 17 false positives from docstrings and module comments:
      ```bash
      grep -rn '^\s*sorry\s*$\|[^a-zA-Z_]sorry\s*$' Cslib/Logics/Modal/Tableau/ --include='*.lean'
      ```
      It MUST return **exactly one** line, `FrameSoundness.lean:1251:    sorry`. Any other count fails
      the phase, including a count of 0 (which would mean the standing sorry was removed in violation
      of the standing user decision).
- [ ] `lean_verify` on every new declaration; permitted axioms are exactly `propext`,
      `Classical.choice`, `Quot.sound`.
- [ ] Scoped `lake build` of each touched module at every phase boundary.
- [ ] `lake exe lint-style` clean at every phase boundary.
- [ ] Full `lake build` and `lake lint` at Phase 7.
- [ ] `CslibTests/S4LoopGuardRegression.lean` green, with every pre-existing row unchanged.
- [ ] **Preserved-declaration check** at every phase boundary:
      `git diff` shows no hunk touching `accPinnedBy`, `branchSatisfiablePinnedIn`,
      `branchSatisfiablePinnedIn_redirect_mechanical`, `branchSatisfiableIn_s4FC_ancestor_redirect`, or
      the latter's module comment. (Phase 6 is the one exception, and only for the removal of the probe
      lemma, which is none of the above.)
- [ ] **No task-number citations in any `.lean` file** touched by this plan.

---

## Artifacts & Outputs

- `specs/553_s4_loop_guard_soundness_reachability_restriction/plans/07_canonical-witness-truth-lemma.md`
  (this file), with `#### Phase 1 Verdict` and `#### Phase 2 Verdict` subsections appended by their
  respective dispatches.
- `specs/553_s4_loop_guard_soundness_reachability_restriction/summaries/07_canonical-witness-truth-lemma-summary.md`
  (on completion or on terminal-condition escalation).
- New sorry-free declarations in `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`: the canonical
  witness instance, the three collapsing conjuncts, the canonical truth lemma (both directions), the
  redirect-preservation lemma, and the soundness wiring.
- New sorry-free bridges in `Cslib/Logics/Modal/Tableau/LoopChecking.lean`:
  `hintikkaS4_box_pos_reflTransGen_wrapped`, `hintikkaS4_dia_neg_reflTransGen_wrapped`, and (on Gate B
  outcome (i)) `modalS4Saturated_of_ordered_settled`.
- A prose fix and, in Phase 6, the removal of the probe section in
  `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`.
- One new regression row in `CslibTests/S4LoopGuardRegression.lean`.

---

## Rollback/Contingency

- **Per-gate (Phases 1, 2)**: the append-then-revert-unless-sorry-free contract. Each gate's probe
  material is appended in a delimited section at end of file. If it does not close within its one
  dispatch, **revert the section** and record the exact `lean_goal` in this plan's verdict subsection.
  **Never commit a `sorry` at a gate** — a `sorry` there stands in for a possibly-false statement,
  which is the exact failure this task has already suffered twice. Material that lands sorry-free is
  retained even when the surrounding gate fails (the two `_wrapped` bridges and the Phase 1 prose fix
  are the named cases).
- **Per-phase (Phases 3-7)**: work is committed per green sub-step, so rollback is a revert of the
  last commit. A strategic-sorry skeleton remains a legitimate mid-phase recovery move in these
  **non-gate** phases and must be discharged before the phase is marked `[COMPLETED]`.
- **Whole-plan**: every phase is additive. Reverting this plan entirely means removing the appended
  sections from `FrameCompleteness.lean` and `LoopChecking.lean`, restoring the probe lemma and its
  header in `FrameSoundness.lean`, and reverting the one regression row. No landed declaration outside
  this plan's own additions is modified, so no prior result is at risk.
- **On terminal condition**: see the Terminal Condition section. Return to the blocker record; do not
  start a seventh route.
