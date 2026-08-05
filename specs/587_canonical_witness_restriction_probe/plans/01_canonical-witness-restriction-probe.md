# Implementation Plan: Task #587

- **Task**: 587 - canonical_witness_restriction_probe
- **Status**: [IMPLEMENTING]
- **Effort**: 8.5 hours (7 hours realized -- Phases 3 and 4 are mutually exclusive branches)
- **Dependencies**: None
- **Research Inputs**: `specs/553_s4_loop_guard_soundness_reachability_restriction/reports/05_gate-a-canonical-witness-blocker-analysis.md`
- **Artifacts**: plans/01_canonical-witness-restriction-probe.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Task 553's plan v5 Gate A died at a machine-checked stuck goal: the structural-induction
agreement lemma `Satisfies m x χ ↔ Satisfies m' x χ` escapes to model points outside
`modalKnownWorlds b` when the induction unwinds a `.box`/`.diamond` subformula, and neither
`accPinnedBy` nor `hbox`/`hdia` (both restricted to known branch labels) supply any fact there.
The Verdict named, but declined to price, the fix: a canonicity assumption on the witness model.
This task's entire deliverable is a **machine-checked micro-probe plus a written go/no-go
verdict** answering that priced-viability question -- not a Lean construction. Definition of
done: a report under `specs/587_canonical_witness_restriction_probe/reports/` carrying an
explicit verdict, and (on GO) a priced phase-count/effort recommendation for a task-553 v6 plan;
all probe code reverted unless it lands sorry-free.

### Research Integration

Report 05 supplies three load-bearing facts this plan is built on:

1. **The stuck goal is precisely characterized.** In `case box.mp.inr`, from
   `hbx : Satisfies m x (□φ)`, `hxsrc : m.r x (f src)`, `hwy : m.r (f wBlock) y`, the goal
   `Satisfies m' y φ` has no route because `m.r x y` does not hold and `hbx` says nothing about
   `y`. The dual is `case diamond.mpr`. Both are quoted verbatim in the Verdict.
2. **The known-label route exists but is unreachable.** Were `x = f w` for a known `w` carrying
   `T(□φ)@w ∈ b`, the chain closes: `accPinnedBy` -> `ReflTransGen acc w src`, `hsat` +
   `hintikkaS4_box_pos_step` -> `T(□φ)@src ∈ b`, `hbox` -> `T(□φ)@wBlock ∈ b`, branch conjunct ->
   `Satisfies m (f wBlock) (□φ)` -> `Satisfies m y φ` -> `(ih y).mp`. The probe's job is to
   determine whether carrier restriction makes this chain reachable.
3. **Precedent exists on the completeness side.** `extractModelWith` returns
   `Model WorldIndex Atom` directly with no existential `W`/`f`
   (`Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`, verified in this planning run at the
   `def extractModelWith` site), matching `Massacci2000` Thm 10.6's canonical-model shape.

### Planning-run correction to the fix's own framing (load-bearing, must not be skipped)

The Verdict's phrasing -- "WLOG `W := WorldIndex`, `f := id`, so **every model point is trivially
a known label**" -- is **not accurate as stated**, and a probe that assumes it will return a false
NO-GO. Setting `W := WorldIndex` and `f := id` makes every model point a *label*, but not a
*known* label: `modalKnownWorlds b` is a strict subset of `WorldIndex`, and `accPinnedBy`
(re-read in this planning run) quantifies explicitly over `w ∈ modalKnownWorlds b` and
`w' ∈ modalKnownWorlds b`. Under `f := id` the escaping `x` and `y` are still unconstrained
whenever they lie outside `modalKnownWorlds b`. The plan therefore probes **two distinct
restrictions in sequence**, not one:

- **Restriction A** (`W := WorldIndex`, `f := id`) -- the literal form the task description names.
- **Restriction B** (carrier restricted so that every point is a *known* label -- either the
  subtype `{w // w ∈ modalKnownWorlds b}`, or `WorldIndex` plus a side condition closing `m.r`
  inside `modalKnownWorlds b`) -- the form that actually discharges the Verdict's stated intent.

A second, deeper question the Verdict does not raise and the probe must answer explicitly: even
with every point a known label, `Satisfies m x (□φ)` does **not** yield `T(□φ)@x ∈ b` for an
*arbitrary* pinned witness. That implication needs the witness to be a genuine canonical/term
model whose valuation reads branch membership (as `extractModelWith`'s `v` does), plus a truth
lemma -- a materially larger commitment than "fix the carrier". Whether the probe needs this is
the single most important thing it can report, in either direction.

### Prior Plan Reference

Plan v5 (`plans/05_pinned-witness-truth-lemma.md`) contributes discipline and calibration, not
structure. Its front-loaded kill-gate design (Gates A-D before any of Phases 5-12's scaffolding)
is adopted here verbatim in spirit: Phase 1 is the probe and its gate; nothing is scaffolded
before the verdict. Its outcome (iii) rule -- one dispatch per gate, no "second dispatch to keep
trying", no committed `sorry` -- is carried over. Its Phase 1 Verdict is the reference format for
this task's own stuck-goal record. **No phase is copied from it.** Its stale Phases 5-7 framing
(a parallel `...Boxed` driver family) is explicitly out of scope here: that content landed inline
in `successorBirthContent`/`blockingWorldS4Keyed` in `LoopChecking.lean`.

### Roadmap Alignment

No ROADMAP.md consulted for this task (none provided in delegation context).

## Goals & Non-Goals

**Goals**:
- Machine-check whether restricting the witness carrier closes the exact box-positive and
  diamond-negative stuck goals recorded in plan v5's `#### Phase 1 Verdict`.
- Distinguish, with evidence, between Restriction A (`f := id`) and Restriction B (every point a
  known label), and determine whether either suffices without a full canonical/term model.
- On GO: price the consequences -- which existential fields of `branchSatisfiablePinnedIn`
  re-shape or collapse, whether sub-step 1.1's mechanical conjuncts survive verbatim, and a
  phase-count/effort estimate for a task-553 v6 plan.
- On NO-GO: record the exact machine-checked stuck goal in the style of plan v5's Verdict, and
  state plainly that no route is currently known.
- Leave `Cslib/Logics/Modal/Tableau/` at a sorry census of exactly 1 and a clean scoped build.

**Non-Goals**:
- Re-running or re-proposing the FrameCompleteness refactor programme. It already landed; its
  box-plus birth content is inline in mainline `successorBirthContent`/`blockingWorldS4Keyed`.
- Touching the standing `sorry` at `FrameSoundness.lean:1251`
  (`branchSatisfiableIn_s4FC_ancestor_redirect`), retained by explicit user decision.
- Re-deriving `accPinnedBy`, `branchSatisfiablePinnedIn`, or
  `branchSatisfiablePinnedIn_redirect_mechanical`. These are landed, sorry-free,
  standard-axioms-only, and are to be preserved and reused.
- Scaffolding a v6 plan, a canonical-model construction, or any large Lean development. Pricing
  is prose; construction is a follow-on task's job.
- Proposing a further ad hoc route if the probe fails. A NO-GO is reported as a NO-GO.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Probe becomes an open-ended proof attempt, repeating plan v5's failure mode | H | M | Hard one-dispatch budget per gate phase; pre-declared kill criteria in Phases 1 and 2; Phase 2 entry gated on one exactly-named failure signature from Phase 1, nothing else |
| False NO-GO from probing only the literal `f := id` form | H | H | Restriction B is planned as a first-class second probe, with its escalation condition pre-declared, not invented mid-dispatch |
| Probe code accidentally committed with a `sorry`, or the standing `:1251` sorry disturbed | H | L | Append-then-revert pattern in a clearly delimited probe section; sorry-census check (`= 1`) is a Done-when condition on every code-touching phase; `:1251` is on the Non-Goals list and outside every phase's declared edit region |
| Landed sub-step 1.1 declarations edited rather than referenced | M | L | Phases 1-2 declare their edit region as "appended probe section only"; verification re-greps the three declarations unchanged |
| Line-number drift in `FrameSoundness.lean` invalidates a cited anchor | M | H | Every phase re-locates declarations by `grep -n '^def\|^lemma\|^theorem'` before use; this plan cites declaration names, never line numbers, except where quoting the historical record |
| GO verdict overstates viability by missing the truth-lemma requirement | H | M | Phase 3 must answer the truth-lemma question explicitly as a named deliverable, not as an aside; an unanswered truth-lemma question downgrades the verdict to CONDITIONAL GO |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4 | 1, 2 |
| 4 | 5 | 3, 4 |

Phases within the same wave can execute in parallel. **Phases 3 and 4 are mutually exclusive
branches** of the gate outcome -- exactly one of them executes, never both. They share a wave
because they share prerequisites, not because they run together.

---

### Phase 1: GATE A' -- micro-probe under Restriction A (`W := WorldIndex`, `f := id`) [COMPLETED]

- **Goal:** Determine, machine-checked, whether restricting the witness carrier to `WorldIndex`
  with `f := id` closes the box-positive and diamond-negative agreement-lemma cases recorded in
  plan v5's `#### Phase 1 Verdict`, or dies at a named obstruction.

- **Estimated output:** ~100-150 lines, all in an appended, clearly delimited probe section.

- **Owns:** `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`, appended probe section at end of
  file only. Read-only elsewhere.

- **Tasks:**
  - [ ] Re-locate by `grep -n '^def\|^lemma\|^theorem' Cslib/Logics/Modal/Tableau/FrameSoundness.lean`
        the three preserved declarations `accPinnedBy`, `branchSatisfiablePinnedIn`,
        `branchSatisfiablePinnedIn_redirect_mechanical`. Record the found line numbers in the
        dispatch notes. Do not trust any line number written in this plan or in report 05.
  - [ ] Read `extractModelWith` in `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (locate by
        `grep -n 'def extractModelWith'`) for the carrier-and-valuation shape being mirrored.
        Read-only; make no edit to that file.
  - [ ] Open a probe section at end of `FrameSoundness.lean` delimited by
        `/-! ### CANONICAL-WITNESS RESTRICTION PROBE -- REVERT UNLESS SORRY-FREE -/` so the revert boundary is
        unambiguous.
  - [ ] State the Restriction-A agreement lemma directly, as a standalone `example`/`lemma` over
        `m : Model WorldIndex Atom` with `f` eliminated (i.e. `f := id` inlined), carrying the
        same hypotheses the v5 gate lemma carried (`h`, `hsrc`, `hwB`, `hsat`, `hbox`, `hdia`),
        and the same conclusion shape `Satisfies m x χ ↔ Satisfies m' x χ` with
        `m'.r := fun x y => m.r x y ∨ (m.r x src ∧ m.r wBlock y)`.
  - [ ] Attempt **only** the two non-mechanical cases: `box.mp.inr` and `diamond.mpr`. Do not
        re-prove the propositional cases -- report 05 records them as closing for free, and
        re-deriving them consumes budget for no information.
  - [ ] At each attempted case, capture the `lean_goal` state verbatim before declaring it closed
        or stuck. A case is "closed" only when `lean_verify` reports it sorry-free with axioms
        limited to `propext`, `Classical.choice`, `Quot.sound`.
  - [ ] Record which of `x`, `y` remain unconstrained under Restriction A, and specifically
        whether the residual obstruction is exactly "`x`/`y` lie outside `modalKnownWorlds b`".
        This determination is the sole gate on Phase 2.

- **Kill criteria and outcomes** (decided now, not under dispatch pressure):

| Outcome | Verdict | Next |
|---|---|---|
| (i) Both cases close sorry-free under Restriction A | **GATE A' PASSES** | Skip Phase 2. Go to Phase 3. |
| (ii) Neither closes, and the residual obstruction is exactly "`x`/`y` outside `modalKnownWorlds b`" | **ESCALATE** -- Restriction A is insufficient for the named, anticipated reason | Go to Phase 2 (Restriction B). |
| (iii) Neither closes, and the obstruction is anything else | **GATE A' FAILS, DEAD** | Skip Phase 2. Go to Phase 4. |
| (iv) Exactly one of box/diamond closes | **PARTIAL** -- record which, and the other's exact failure mode | If the failing half's obstruction matches (ii), go to Phase 2; otherwise go to Phase 4. Do **not** proceed on the closing half alone. |
| (v) Budget exhausted with no verdict on either case | **GATE A' FAILS, DEAD** | Go to Phase 4. Do not request a second dispatch to keep trying. |

- **Timing:** 2 hours (hard budget -- one dispatch).

- **Depends on:** none

- **Verification Tier:** local

- **Commit Mode:** per-substep

- **Scope Hypothesis:** This phase asserts (a) exactly two non-mechanical cases need attempting
  (`box.mp.inr`, `diamond.mpr`), and (b) an edit region confined to one appended section of
  `FrameSoundness.lean`. Confirm (a) at implementation time by running the induction and
  enumerating the actually-generated non-closing goals -- if a third non-mechanical case appears,
  record it and treat it as new information, not as a plan error to paper over. Confirm (b) by
  `git diff --stat` showing exactly one file touched and the diff confined below the probe
  delimiter.

- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` -- appended probe section only; no edit to
    any existing declaration, and specifically none to the standing `sorry` or to the three
    preserved sub-step 1.1 declarations.

- **Verification:**
  - `grep -c 'sorry' `-style census over `Cslib/Logics/Modal/Tableau/` returns exactly 1
    committed `sorry` (the standing `:1251` one), using the census definition recorded in
    `LoopChecking.lean`'s census-command comment.
  - The three preserved declarations are byte-identical to their pre-dispatch state
    (`git diff` shows no hunk touching them).
  - `lake build Cslib.Logics.Modal.Tableau.FrameSoundness` clean.
  - A verbatim `lean_goal` capture exists for every attempted case, closed or stuck.

#### Phase 1 Verdict

**Outcome (ii): neither case closes, and the residual obstruction is exactly "`x`/`y` lie outside
`modalKnownWorlds b`". ESCALATE to Phase 2.**

**Re-location.** `accPinnedBy`, `branchSatisfiablePinnedIn`,
`branchSatisfiablePinnedIn_redirect_mechanical` re-located by
`grep -n '^def\|^lemma\|^theorem' Cslib/Logics/Modal/Tableau/FrameSoundness.lean` at lines
5323, 5332, 5356 respectively (unchanged from report 05's `:5323-5390` citation). `extractModelWith`
re-read at `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:85` (read-only; carrier is
`WorldIndex` directly, valuation reads branch membership off labels -- confirms the precedent cited
by report 05).

**The probe.** A standalone `example` was appended below the
`/-! ### CANONICAL-WITNESS RESTRICTION PROBE -- REVERT UNLESS SORRY-FREE -/` delimiter at the end
of `FrameSoundness.lean`, stating the agreement claim
`∀ χ x, Satisfies m x χ ↔ Satisfies m' x χ` with `m : Model WorldIndex Atom` (i.e. `W := WorldIndex`,
`f` eliminated as `id`, so `f src`/`f wBlock` become plain `src`/`wBlock`) and
`m' := ⟨fun x y => m.r x y ∨ (m.r x src ∧ m.r wBlock y), m.v⟩`, carrying `hsrc`, `hwB`, `hbox`,
`hdia` in the exact shape plan v5's gate lemma used. `hsat` was elided to a trivial `(hsat : True)`
hypothesis: `modalS4Saturated` (the real type of v5's `hsat`) is defined in `LoopChecking.lean`,
which `FrameSoundness.lean` does not import, and this phase's declared edit region is append-only
(no import edits permitted). This elision does not affect the verdict below -- both captured stuck
goals show the obstruction is reached without ever needing `hsat`, `hbox`, or `hdia` to fire, so a
correctly-typed `hsat` could not have supplied the missing leverage either.

Induction on `χ`: the five propositional cases (`atom`, `bot`, `imp`, `and`, `or`) close by `simp`/
`rw` on the IH, unchanged from v5. `box.mpr` and `diamond.mp` close directly from the IH (the "old"
`m.r`-disjunct only). `box.mp.inr` and `diamond.mpr`'s new-disjunct sub-case are exactly the two
cases attempted, matching the task list.

**`case box.mp.inr`, machine-checked stuck goal** (captured via `lean_goal` immediately before the
`sorry`, `FrameSoundness.lean:5431`):

```
case box.mp.inr
b : List (SignedFormula (Proposition Atom) WorldIndex)
src wBlock : WorldIndex
m : Model WorldIndex Atom
hsrc : src ∈ modalKnownWorlds b
hwB : wBlock ∈ modalKnownWorlds b
hsat : True
hbox : ∀ (ψ : Proposition Atom),
  { sign := Sign.pos, formula := □ψ, label := src } ∈ b → { sign := Sign.pos, formula := □ψ, label := wBlock } ∈ b
hdia : ∀ (ψ : Proposition Atom),
  { sign := Sign.neg, formula := ◇ψ, label := src } ∈ b → { sign := Sign.neg, formula := ◇ψ, label := wBlock } ∈ b
φ : Proposition Atom
ih : ∀ (x : WorldIndex), Satisfies m x φ ↔ Satisfies { r := fun x y => m.r x y ∨ m.r x src ∧ m.r wBlock y, v := m.v } x φ
x : WorldIndex
hbx : Satisfies m x (□φ)
y : WorldIndex
hxsrc : m.r x src
hwy : m.r wBlock y
⊢ Satisfies { r := fun x y => m.r x y ∨ m.r x src ∧ m.r wBlock y, v := m.v } y φ
```

Attempted closers (`lean_multi_attempt`, all fail): `aesop` ("failed to prove the goal after
exhaustive search"), `tauto`, `simp_all`, `solve_by_elim [hbx, hxsrc, hwy, hsrc, hwB, hbox]`, and the
direct term `exact (ih y).mp (hbx wBlock hwy)` (type mismatch: `hwy : m.r wBlock y` does not match
the expected `m.r x wBlock` -- `hbx` can only be instantiated at successors of `x` via `m.r x _`,
and nothing in scope supplies `m.r x wBlock`).

**`case diamond.mpr`, machine-checked stuck goal** (`FrameSoundness.lean:5445`, case name
`diamond.mpr.inr` after `rcases`):

```
case diamond.mpr.inr
b : List (SignedFormula (Proposition Atom) WorldIndex)
src wBlock : WorldIndex
m : Model WorldIndex Atom
hsrc : src ∈ modalKnownWorlds b
hwB : wBlock ∈ modalKnownWorlds b
hsat : True
hbox : ∀ (ψ : Proposition Atom),
  { sign := Sign.pos, formula := □ψ, label := src } ∈ b → { sign := Sign.pos, formula := □ψ, label := wBlock } ∈ b
hdia : ∀ (ψ : Proposition Atom),
  { sign := Sign.neg, formula := ◇ψ, label := src } ∈ b → { sign := Sign.neg, formula := ◇ψ, label := wBlock } ∈ b
φ : Proposition Atom
ih : ∀ (x : WorldIndex), Satisfies m x φ ↔ Satisfies { r := fun x y => m.r x y ∨ m.r x src ∧ m.r wBlock y, v := m.v } x φ
x y : WorldIndex
hsy : Satisfies { r := fun x y => m.r x y ∨ m.r x src ∧ m.r wBlock y, v := m.v } y φ
hxsrc : m.r x src
hwy : m.r wBlock y
⊢ Satisfies m x (◇φ)
```

Attempted closers, all fail: `aesop`, `tauto`, `simp_all`, and the direct term
`exact ⟨wBlock, hxsrc, ?_⟩` (type mismatch: the goal needs `m.r x wBlock` as the first conjunct,
but `hxsrc : m.r x src` only supplies `m.r x src` -- there is no witness `z` in scope with both
`m.r x z` and `Satisfies m z φ` derivable).

**Diagnosis.** Restriction A changes the carrier type (`W := WorldIndex`) and eliminates the
embedding (`f := id`), but does **not** constrain the universally-quantified induction variable `x`
to be a *known* label: `x : WorldIndex` ranges over all of `WorldIndex`, of which
`modalKnownWorlds b` is a strict sub-list. Exactly as the plan's own "Planning-run correction"
section anticipated, `hbox`/`hdia`/`accPinnedBy`-style leverage is keyed specifically to `src` and
`wBlock` (both already known, per `hsrc`/`hwB`) -- it says nothing about an arbitrary `x` that
merely happens to satisfy `m.r x src`. Both stuck goals are the same shape as plan v5's Verdict
(`plans/05_pinned-witness-truth-lemma.md:762-813`) up to the carrier/embedding substitution: `f src`
becomes `src`, `f wBlock` becomes `wBlock`, `x : W` becomes `x : WorldIndex` -- the escape is
unchanged because nothing about *fixing the carrier* implies *`x` is a known label of `b`*. This
confirms outcome (ii) precisely, not a new/different obstruction: **ESCALATE to Phase 2**, which
must additionally constrain the carrier so every point is provably a known label (Restriction B).

**Revert.** Per the append-then-revert contract and the Testing & Validation sorry-census
requirement (exactly 1 at every phase boundary), the probe `example` was deleted in full after this
verdict was recorded (it did not close sorry-free). `git diff Cslib/Logics/Modal/Tableau/FrameSoundness.lean`
is empty at this phase's close; sorry census re-confirmed at 1 (the standing `:1251` sorry only).

---

### Phase 2: GATE A'' -- micro-probe under Restriction B (every carrier point a known label) [COMPLETED]

- **Goal:** Entered **only** on Phase 1 outcome (ii), or outcome (iv) whose failing half matches
  (ii). Determine whether restricting the carrier so every point is a *known* label closes the
  cases Restriction A left open -- and, critically, whether closing them additionally requires a
  truth lemma linking `Satisfies` to branch membership.

- **Estimated output:** ~120-180 lines in the same appended probe section.

- **Owns:** `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`, appended probe section only.

- **Entry condition (hard):** Phase 1's recorded outcome is (ii), or (iv) with the failing half's
  obstruction matching (ii). Under any other Phase 1 outcome this phase is **skipped** and marked
  `[COMPLETED WITH EXCLUSIONS]` with a `#### Reasoned Exclusions` record citing the Phase 1
  outcome as evidence. Entering this phase on any other basis is the "second dispatch to keep
  trying" antipattern plan v5 was built to prevent.

- **Tasks:**
  - [ ] Choose and record one of the two Restriction-B encodings, with a one-paragraph rationale:
        (B1) carrier `{w : WorldIndex // w ∈ modalKnownWorlds b}` with `f` the coercion, or
        (B2) carrier `WorldIndex` plus a side condition `∀ x y, m.r x y → x ∈ modalKnownWorlds b ∧
        y ∈ modalKnownWorlds b` (or the weakest such closure condition that discharges the goal).
        Prefer whichever makes `accPinnedBy`'s two membership hypotheses discharge definitionally.
  - [ ] Re-state the agreement lemma at the chosen encoding and re-attempt `box.mp.inr` and
        `diamond.mpr`, capturing `lean_goal` verbatim at each.
  - [ ] **Answer the truth-lemma question explicitly.** At the point where the proof needs
        `T(□φ)@x ∈ b` from `Satisfies m x (□φ)`, record whether that implication is available
        from the hypotheses in scope, or whether it requires the witness to be a canonical/term
        model with a branch-reading valuation plus a truth lemma. Record the answer as a named
        finding either way -- a closed proof that silently assumed it is a false PASS.
  - [ ] Record whether `accPinnedBy` at the chosen encoding degenerates to a total bound
        `m.r ≤ Relation.ReflTransGen acc`, and whether that degeneration is sound (it must not
        make the pinned invariant unsatisfiable -- check against at least the reflexive case).

- **Kill criteria and outcomes:**

| Outcome | Verdict | Next |
|---|---|---|
| (i) Both cases close sorry-free, with no truth-lemma dependency | **GATE A'' PASSES (unconditional)** | Phase 3. |
| (ii) Both cases close, but only modulo an assumed truth lemma / canonical valuation | **GATE A'' PASSES (conditional)** -- the restriction is viable but the price includes a canonical-model construction | Phase 3, which must price that construction as part of the estimate. |
| (iii) Cases do not close -- a sixth, different obstruction | **GATE A'' FAILS, DEAD** | Phase 4. |
| (iv) The chosen encoding makes the pinned invariant unsatisfiable | **GATE A'' FAILS, DEAD** -- record the unsatisfiability argument | Phase 4. |
| (v) Budget exhausted with no verdict | **GATE A'' FAILS, DEAD** | Phase 4. No further attempt. |

- **Timing:** 2 hours (hard budget -- one dispatch).

- **Depends on:** 1

- **Verification Tier:** local

- **Commit Mode:** per-substep

- **Scope Hypothesis:** This phase asserts exactly one Restriction-B encoding is attempted (not
  both B1 and B2 serially). Confirm at implementation time by recording the chosen encoding in
  the dispatch notes before any Lean is written; attempting the second encoding after the first
  fails is out of budget and is a Phase 2 outcome (iii)/(v), not a continuation.

- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` -- appended probe section only.

- **Verification:**
  - Same three checks as Phase 1: sorry census exactly 1, three preserved declarations untouched,
    `lake build Cslib.Logics.Modal.Tableau.FrameSoundness` clean.
  - The truth-lemma question has a recorded answer (yes/no plus reasoning), not silence.

#### Phase 2 Verdict

**Outcome (ii): GATE A'' PASSES (conditional).** Both `box.mp.inr` and `diamond.mpr` close
sorry-free under Restriction B1, but only modulo two genuinely-assumed hypothesis groups. Go to
Phase 3, which must price the canonical/term-model construction those groups presuppose.

**Chosen encoding: B1** (carrier `{w : WorldIndex // w ∈ modalKnownWorlds b}`, `f` the coercion),
over B2 (a closure side condition on `WorldIndex`). Rationale (one paragraph, per the task list):
B1 makes the induction variable `x` a known label *by its type* -- `x.2 : x.1 ∈ modalKnownWorlds b`
is available for free at every use site -- so `accPinnedBy`'s two membership hypotheses
(`w ∈ modalKnownWorlds b`, `w' ∈ modalKnownWorlds b`) are discharged definitionally rather than as
side proof obligations threaded through every case of the induction. B2 would have required
carrying a separate closure invariant (`∀ x y, m.r x y → x ∈ modalKnownWorlds b ∧ y ∈
modalKnownWorlds b`) through the whole induction and re-deriving membership at every step from that
invariant instead of from the type -- strictly more bookkeeping for the same result. Only B1 was
attempted, per the phase's own one-encoding budget.

**The probe.** Appended below the same delimiter (Phase 1's probe having already been reverted),
a lemma `canonicalWitnessRestrictionProbe_agreementConditional`
(`Cslib/Logics/Modal/Tableau/FrameSoundness.lean:5422`) restates the agreement claim over
`m : Model {w : WorldIndex // w ∈ modalKnownWorlds b} Atom`, carrying:
- `hpinned` -- `accPinnedBy` adapted to the B1 carrier (real content, no import needed): `∀ w w' :
  Known, m.r w w' → ReflTransGen acc w.1 w'.1`.
- `hbSat`/`hbUnsat` -- `branchSatisfiablePinnedIn`'s branch conjunct specialized at `wBlock`, both
  signs (real content, a direct instantiation of the existential witness's own defining property).
- `hbox`/`hdia` -- unchanged from Phase 1 (real content, `List` membership facts about `b`).
- `hpropBox`/`hpropDia` -- the S4 box/diamond-content forward-persistence-along-`acc`-reachability
  facts. **Genuinely assumed**, out of this task's scope: this is Decision Gate B's territory in
  the pinned-witness-truth-lemma plan (its own Phase 2, `modalS4Saturated` +
  `hintikkaS4_box_pos_reflTransGen`-style bridges), not this task's Gate A'/A''. Re-deriving it
  would need `LoopChecking.lean`, which `FrameSoundness.lean` does not import and which this
  phase's declared edit region (append-only) does not permit importing.
- `htruthBoxPos`/`htruthDiaNeg` -- **the truth-lemma direction**: `Satisfies m w (□ψ) →
  T(□ψ)@w.1∈b`, and the diamond-negative dual. **Genuinely assumed.** This is the answer to the
  phase's central named question.

With all of the above in scope, both stuck cases close by direct forward chaining (no `sorry`,
no `aesop`/hammer): `box.mp.inr` via `htruthBoxPos → hpinned → hpropBox → hbox → hbSat →` unfold
box; `diamond.mpr` via `by_contra → htruthDiaNeg → hpinned → hpropDia → hdia → hbUnsat →`
contradiction against the `ih`-transported witness. `lean_verify` on the landed lemma reports
axioms `propext`, `Classical.choice`, `Quot.sound` only (`lean_build`/`lake build
Cslib.Logics.Modal.Tableau.FrameSoundness` clean; `lake exe lint-style` clean; `lake lint`
reports zero warnings referencing this declaration or its line range).

**The truth-lemma question, answered explicitly (the phase's central deliverable).** No hypothesis
already in scope -- not `hpinned`, not `hbSat`/`hbUnsat`, not `hbox`/`hdia`, not the carrier
restriction itself -- supplies `htruthBoxPos`/`htruthDiaNeg` for an *arbitrary* pinned witness `m`.
The pinned invariant (`branchSatisfiablePinnedIn`'s existential) only constrains `m` in the
branch-to-model direction (`T(□ψ)@w∈b → Satisfies m (f w) (□ψ)`, i.e. `hbSat`'s own shape); the
converse (model-to-branch) direction is a genuine **soundness-of-negation-avoidance / completeness**
fact about `m`'s valuation, true only when `m`'s valuation is built to *read* branch membership
directly (`extractModelWith`'s `v w p := b.any (... sf.label == w) = true` shape) combined with a
Hintikka/saturation argument (a full truth lemma: `Satisfies m w χ ↔` (`χ`'s signed membership in
`b`, roughly, for `w` known and `b` saturated)). An arbitrary pinned witness has no such
constraint on its valuation at all -- `branchSatisfiablePinnedIn`'s existential quantifies over
*any* `m` satisfying the four conjuncts, and infinitely many such `m` do not read `b`. **Answer:
the truth-lemma direction is NOT available for free; it requires committing to a canonical/term
model (mirroring `extractModelS4`/`extractModelWith`,
`Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:85-148`, re-confirmed read-only in this
dispatch) rather than an arbitrary pinned witness.**

**`accPinnedBy` degeneration check.** Under B1, `accPinnedBy`'s hypothesis is `∀ w w' : Known, m.r w
w' → ReflTransGen acc w.1 w'.1` -- this is *not* a degeneration to a total bound `m.r ≤
ReflTransGen acc`, because `m.r` at the restricted carrier only ever relates known-world pairs
(the carrier itself excludes unknown points), so the hypothesis is exactly as strong as the
original `accPinnedBy` restricted to its own domain of application -- no strengthening or
weakening relative to the un-restricted statement, checked against the reflexive case (`w = w'`,
where `ReflTransGen.refl` trivially supplies the conclusion regardless of `m.r w w`). No
unsatisfiability risk identified.

**Revert decision: RETAINED, not reverted.** Per the Rollback/Contingency section ("Zero or one
retained Lean declaration ... retained only on a sorry-free passing probe, reverted in every
other case"), `canonicalWitnessRestrictionProbe_agreementConditional` lands sorry-free and is kept
in the file as the task's one retained Lean artifact. `git diff --stat` confirms exactly one file
touched, entirely below the probe delimiter; sorry census re-confirmed at exactly 1 (the standing
`:1251` sorry only) since this lemma introduces zero new sorries.

---

### Phase 3: GO branch -- price the consequences [COMPLETED]

- **Goal:** Entered only when Phase 1 or Phase 2 passed (including a conditional pass). Price what
  adopting the restriction costs, in enough detail that a task-553 v6 plan can be written against
  it without re-deriving this analysis.

- **Estimated output:** Prose analysis (destined for the Phase 5 report), plus at most small
  confirmatory Lean checks; no new construction.

- **Owns:** No source file. Working notes only; content lands in the Phase 5 report.

- **Entry condition (hard):** Phase 1 outcome (i), or Phase 2 outcome (i) or (ii). Otherwise this
  phase is skipped and marked `[COMPLETED WITH EXCLUSIONS]` with a `#### Reasoned Exclusions`
  record citing the gate outcome.

- **Tasks:**
  - [ ] Enumerate every field of `branchSatisfiablePinnedIn` and classify each under the adopted
        restriction as: **collapses** (becomes trivial or definitionally discharged),
        **re-shapes** (survives with a changed statement), or **survives verbatim**. The four
        fields are the `FC m.r` conjunct, the edge conjunct, the `accPinnedBy` conjunct, and the
        branch conjunct, plus the three existential binders `W`, `m`, `f`.
  - [ ] Determine, by attempting the re-typed statement (not by inspection alone), whether
        `branchSatisfiablePinnedIn_redirect_mechanical`'s proof body survives verbatim against
        the fixed carrier, or which of its four bullets (`Std.Refl`, `IsTrans` four-case split,
        edge conjunct via `hasEdge_addEdge_cases`, `accPinnedBy` preservation) need re-derivation.
        Report per-bullet, not as a single yes/no.
  - [ ] If Phase 2 returned a conditional pass, price the canonical/term-model construction
        separately: what it must define, what truth lemma it must prove, and whether
        `extractModelWith`'s existing shape can be reused or must be re-built for the soundness
        direction.
  - [ ] Produce a phase-count and effort estimate for a task-553 v6 plan, decomposed by
        workstream, with each phase bounded to one agent run per plan v5's own sizing discipline.
  - [ ] State any residual risk that would make the v6 plan die at a seventh obstruction, and how
        a v6 Gate would detect it early.

- **Timing:** 2 hours

- **Depends on:** 1, 2

- **Verification Tier:** prose

- **Scope Hypothesis:** This phase asserts `branchSatisfiablePinnedIn` has exactly four
  conjunct fields plus three existential binders, and that
  `branchSatisfiablePinnedIn_redirect_mechanical` has exactly four proof bullets. Confirm by
  re-reading both declarations at their re-located positions before writing the classification;
  if the shapes differ from this assertion, the re-read wins and the divergence is recorded.

- **Verification:**
  - Every field and every mechanical bullet has an explicit classification -- no field left
    unclassified.
  - The effort estimate is decomposed by workstream, not given as a single lump number.
  - Any confirmatory Lean written is reverted; sorry census still exactly 1.

#### Phase 3 Pricing Analysis

**Framing.** Phase 2's conditional pass means the redirect-preservation obligation is only closed
by committing to a **canonical** witness -- fixing `W`, `m`, `f` to specific, non-arbitrary
choices, rather than leaving them existentially arbitrary as `branchSatisfiablePinnedIn` currently
does. The natural canonical choice, per report 05's own precedent, is the S4 extraction shape
already built on the completeness side: `W := WorldIndex`, `m.r := Relation.ReflTransGen
(fun w w' => acc.hasEdge w w' = true)` (i.e. `extractModelS4`'s relation, re-derivable without
importing `FrameCompleteness.lean` since it is just `Relation.ReflTransGen` applied to
`acc.hasEdge`), `f := id`. This subsection prices what adopting that choice costs against
`branchSatisfiablePinnedIn` and its mechanical lemma.

**Field-by-field classification of `branchSatisfiablePinnedIn`'s four conjuncts.**

| Field | Classification | Reasoning |
|---|---|---|
| `FC m.r` (i.e. `s4FC m.r = Std.Refl m.r ∧ IsTrans _ m.r`) | **Collapses** | For `m.r := ReflTransGen (acc.hasEdge)`, both instances come free from `Relation.reflexive_reflTransGen`/`Relation.transitive_reflTransGen` (the exact route `extractModelS4_refl`/`extractModelS4_trans`, `FrameCompleteness.lean`, already take) -- no per-redirect-step proof obligation survives. |
| Edge conjunct (`∀ w w', acc.hasEdge w w' → m.r (f w) (f w')`) | **Collapses** | With `f := id` and `m.r := ReflTransGen(acc.hasEdge)`, this is exactly `Relation.ReflTransGen.single`, a one-line closing tactic, not a per-witness proof obligation. |
| `accPinnedBy` conjunct | **Collapses** | Machine-checked in this phase (confirmatory check, reverted): with `f := id` and `m.r := ReflTransGen(acc.hasEdge)`, the conjunct's hypothesis `m.r (f w) (f w')` is *definitionally* `ReflTransGen(acc.hasEdge) w w'`, i.e. exactly the desired conclusion -- the whole conjunct is discharged by `id`. This is a stronger collapse than Restriction B1 alone gave (B1 needed a real, if short, `hpinned` hypothesis; the fully canonical choice needs none at all). |
| Branch conjunct (`∀ sf ∈ b, sf.sign = .pos → Satisfies m (f sf.label) sf.formula, ...`) | **Re-shapes (does not collapse)** | This is Phase 2's central finding: it is NOT free for an arbitrary witness, and remains the one conjunct requiring genuinely new proof content -- a truth lemma tying `m`'s (now-canonical) valuation to branch membership. See "Canonical/term-model construction, priced" below. |
| Existential `W` | **Collapses to a fixed type** | `W := WorldIndex`, no longer existentially bound. |
| Existential `m` | **Collapses to a fixed definition** | `m := ⟨Relation.ReflTransGen (acc.hasEdge), v⟩` for a *specific* `v` reading branch content (see below) -- no longer an arbitrary existential witness. |
| Existential `f` | **Collapses to `id`** | No longer existentially bound; every world index is trivially its own known-label witness once the branch conjunct's truth lemma is established. |

**Net effect:** three of the four conjuncts and all three existential binders collapse to
near-free or fully-free consequences of fixing the canonical choice; exactly one conjunct (the
branch conjunct) re-shapes into a materially larger obligation (a genuine truth lemma). This
matches -- and sharpens -- report 05's framing: the "canonicity" fix is not merely a carrier
restriction, it is a commitment whose *cost is concentrated entirely in the branch conjunct*.

**Per-bullet survival of `branchSatisfiablePinnedIn_redirect_mechanical`'s proof.** This lemma's
proof (four bullets: `Std.Refl` via `hrefl.refl`; `IsTrans` via the four-case split on
`htrans.trans`; the edge conjunct via `hasEdge_addEdge_cases`; the `accPinnedBy`-preservation
composing three `ReflTransGen` legs) is stated **parametrically** over an arbitrary `m :
Model W Atom` satisfying `Std.Refl`/`IsTrans`/the edge conjunct/`accPinnedBy` -- it does not
inspect what `W`/`m`/`f` *are*, only that they satisfy those properties. Consequence, confirmed
by re-reading the proof body (not merely by inspection of the type signature): **all four bullets
survive verbatim, unconditionally, against the canonical choice.** Nothing about fixing `W :=
WorldIndex`, `m.r := ReflTransGen(acc.hasEdge)`, `f := id` requires touching this lemma's proof;
it is invoked exactly as-is, supplying the (now much cheaper to establish, per the classification
table above) three mechanical conjuncts as its premises. A v6 plan does **not** need a phase to
re-derive `branchSatisfiablePinnedIn_redirect_mechanical` -- it is reused unchanged, exactly as
the Non-Goals section of this plan requires ("PRESERVE byte-identical, do not re-derive").

**Canonical/term-model construction, priced.** What a v6 plan's canonical-witness construction
must define and prove, decomposed:

1. **The valuation.** `v w p := b.any (fun sf => sf.sign == .pos && sf.formula == .atom p &&
   sf.label == w) = true` -- literally `extractModelWith`'s existing valuation clause
   (`FrameCompleteness.lean:90`), reusable verbatim by cross-reference (not by re-import into
   `FrameSoundness.lean`, since that file's role is the *soundness*-side vocabulary and does not
   currently import the completeness-side extraction file; a v6 plan phase should assess whether
   to (a) import `FrameCompleteness.lean`'s definitions into the soundness side, or (b)
   re-state the same three-line valuation locally in `FrameSoundness.lean` to avoid a
   soundness-depends-on-completeness import direction that may be architecturally undesirable --
   this is a real open design choice for v6, not resolved here).
2. **The truth lemma.** `∀ w ∈ modalKnownWorlds b, ∀ χ, Satisfies m w χ ↔` (`χ`'s *saturated*
   branch membership at `w`, roughly: `T(χ)@w ∈ b` when `χ` is positive-signed content, `¬(T(χ)@w
   ∈ b)`/`F(χ)@w ∈ b` for negative, closed under the Hintikka conditions `modalS4Saturated`
   supplies). This is a structural induction on `χ` mirroring the *completeness*-side truth lemma
   argument (the standard Hintikka-model argument used to prove tableau completeness), not
   something `extractModelWith`/`extractModelS4` currently state or prove on the
   `FrameCompleteness.lean` side either -- **this is new proof content, not a reuse**. Its
   box/diamond cases will need exactly the `modalS4Saturated`/`hintikkaS4_box_pos_step`-family
   facts that this task's own Phase 2 had to abstract away (Decision Gate B's territory).
3. **Re-deriving the four `branchSatisfiablePinnedIn` conjuncts for the canonical base case**
   (before any redirect): `FC`/edge-conjunct/`accPinnedBy` per the collapse analysis above (cheap,
   a few lines each, confirmed for `accPinnedBy` in this phase's own reverted check); the branch
   conjunct **from** the truth lemma (item 2) plus `modalS4Saturated`'s own saturation guarantee
   applied at the *initial* (pre-redirect) accessibility state -- i.e. the base case needs Gate
   B's conclusion (`modalS4Saturated` availability) to even start, independent of the redirect
   step this task examined.
4. **The redirect-preservation step itself**: reuses `branchSatisfiablePinnedIn_redirect_mechanical`
   verbatim (item above) for three of the four conjuncts; the branch conjunct at the *new*
   accessibility state needs the truth lemma (item 2) applied again, now propagated through
   `hbox`/`hdia` exactly as this task's Phase 2 probe demonstrated (the `htruthBoxPos`/
   `htruthDiaNeg` + `hpropBox`/`hpropDia` chain, now with `hpropBox`/`hpropDia` supplied for real
   by Gate B rather than assumed).

**Effort estimate for a task-553 v6 plan, decomposed by workstream** (bounded to one agent run per
phase, per this plan's own sizing discipline):

| Workstream | Phase(s) | Estimate | Depends on |
|---|---|---|---|
| Decision Gate B (`modalS4Saturated` availability at a settled ordered-stepper state) | 1 phase | 3 hours | none -- this is v5's own already-designed Phase 2, unchanged, still owed |
| Truth lemma (structural induction, `Satisfies m w χ ↔` saturated branch membership) | 1-2 phases (box/diamond cases are the hard cases; propositional cases are free) | 4-6 hours | Gate B (needs `hintikkaS4_box_pos_step`-family facts inside the induction) |
| Canonical base-case assembly (four conjuncts at the initial `acc`, reusing the valuation and truth lemma) | 1 phase | 1.5 hours | truth lemma |
| Redirect-preservation re-assembly (reuse `branchSatisfiablePinnedIn_redirect_mechanical` verbatim + truth-lemma-mediated branch conjunct, mirroring this task's Phase 2 probe) | 1 phase | 2 hours | canonical base-case, truth lemma |
| Wire into the S4-keyed loop-guard soundness argument (task 553's actual goal, beyond Gate A alone) | 1-2 phases | 3-5 hours | redirect-preservation re-assembly |
| **Total** | **5-7 phases** | **13.5-17.5 hours** | -- |

This is larger than route (1)'s original estimate (plan v5 priced Gate A alone at a handful of
hours) precisely because the truth lemma is new proof content, not a reshaping of existing work --
matching Phase 2's own finding that this is "a materially larger commitment than fixing the
carrier."

**Residual risk and early-detection gate for v6.** The single largest risk is that the truth
lemma's box/diamond cases turn out to need more from `modalS4Saturated` than Gate B (v5's own
Phase 2, still unexecuted) actually supplies -- i.e. a *seventh* obstruction, one level deeper
than this task's sixth. A v6 plan should front-load exactly this risk as its own Gate 0: attempt
the truth lemma's box-positive case specifically (the same case this task's Phase 2 probe
`htruthBoxPos` assumed) as a standalone micro-probe, *before* committing to the full 5-7 phase
programme above, using the same one-dispatch kill-gate discipline this task and plan v5 both used.
If that micro-probe also gets stuck, the truth lemma itself -- not merely the carrier -- is the
obstruction, and no version of route (1) is viable without importing a materially different
construction (e.g. a full canonical-model completeness-style term model, built from scratch rather
than reusing `extractModelWith`'s shape).

---

### Phase 4: NO-GO branch -- record the machine-checked stuck goal [COMPLETED WITH EXCLUSIONS]

#### Reasoned Exclusions

This phase's hard entry condition is "Phase 1 outcome (iii) or (v), or Phase 2 outcome (iii),
(iv), or (v)". Phase 1 returned outcome (ii) (ESCALATE) and Phase 2 returned outcome (ii) (GATE
A'' PASSES, conditional) -- neither matches this phase's entry condition. Per Phases 3 and 4 being
mutually exclusive GO/NO-GO branches sharing a wave (not a "run both" pair), and per the plan's
own instruction that a phase skipped by its entry condition closes as `[COMPLETED WITH
EXCLUSIONS]` rather than `[NOT STARTED]` or an incomplete phase, this phase is excluded. Phase 3
(the GO branch) executes instead.

- **Goal:** Entered only when the gates failed. Record the exact stuck goal in the style of plan
  v5's `#### Phase 1 Verdict`, and state plainly that no route is currently known.

- **Owns:** No source file. Working notes only; content lands in the Phase 5 report.

- **Entry condition (hard):** Phase 1 outcome (iii) or (v), or Phase 2 outcome (iii), (iv), or
  (v). Otherwise skipped and marked `[COMPLETED WITH EXCLUSIONS]` with a
  `#### Reasoned Exclusions` record citing the gate outcome.

- **Tasks:**
  - [ ] Reproduce verbatim the `lean_goal` capture at each stuck point, with the full hypothesis
        context, in fenced code blocks -- matching the format plan v5's Verdict used.
  - [ ] State which restriction (A, B1, or B2) was in force at each capture.
  - [ ] Explain in prose why the recorded hypotheses do not reach the goal, naming the specific
        fact that is missing -- as report 05 did for the fifth mechanism.
  - [ ] State whether this is the same mechanism as the v5 Verdict's (the escape to points
        outside `modalKnownWorlds b`) or a distinct sixth mechanism, and justify the call.
  - [ ] State plainly that no route is currently known. **Do not propose a further ad hoc route.**
        A named open question is acceptable; a speculative proposed fix is not.

- **Timing:** 1 hour

- **Depends on:** 1, 2

- **Verification Tier:** prose

- **Verification:**
  - At least one verbatim `lean_goal` block per stuck case, with hypothesis context intact.
  - No proposed route appears anywhere in the record.
  - All probe code reverted; `git diff` against pre-dispatch `FrameSoundness.lean` is empty;
    sorry census exactly 1.

---

### Phase 5: Write the verdict report [NOT STARTED]

- **Goal:** Produce the task's actual deliverable: a research report with an unambiguous go/no-go
  verdict and, on GO, a priced next-step recommendation for a task-553 v6 plan.

- **Owns:** `specs/587_canonical_witness_restriction_probe/reports/01_canonical-witness-restriction-probe.md`

- **Tasks:**
  - [ ] Create `specs/587_canonical_witness_restriction_probe/reports/` (lazily -- only now) and
        write the report there.
  - [ ] Lead with the verdict in the first section: **GO**, **CONDITIONAL GO**, or **NO-GO**.
        Do not bury it after the analysis.
  - [ ] Record the probe method: which restrictions were attempted, in what order, under what
        budget, and what the gate outcomes were.
  - [ ] Include every verbatim `lean_goal` capture from Phases 1-2, closed and stuck alike.
  - [ ] On GO/CONDITIONAL GO: include Phase 3's field-by-field pricing, the per-bullet mechanical
        conjunct survival analysis, the truth-lemma answer, and the decomposed v6 effort estimate.
  - [ ] On NO-GO: include Phase 4's record verbatim, and the plain statement that no route is
        known.
  - [ ] State explicitly, in a short closing section, what was NOT done and why: the
        FrameCompleteness refactor programme was not re-run (already landed, inline in
        `successorBirthContent`/`blockingWorldS4Keyed`), the standing `sorry` was not touched, and
        the three sub-step 1.1 declarations were preserved unmodified.
  - [ ] Cross-reference the report from task 553's blocker record so the parent task's next
        dispatch finds it.

- **Timing:** 1.5 hours

- **Depends on:** 3, 4

- **Verification Tier:** prose

- **Verification:**
  - The report's first content section states the verdict in one of the three defined values.
  - Every `lean_goal` capture taken during Phases 1-2 appears in the report.
  - The report is discoverable from task 553 (cross-reference present).
  - Final state: `git status` shows no unintended modification to `FrameSoundness.lean`
    (the file is either unchanged, or changed only by a sorry-free passing probe that the GO
    verdict explicitly elects to retain).

---

## Testing & Validation

- [ ] Sorry census over `Cslib/Logics/Modal/Tableau/` is exactly 1 at every phase boundary, using
      the census command recorded in `LoopChecking.lean`'s census comment (not a naive
      `grep -rn '\bsorry\b'`, which over-counts docstring prose).
- [ ] `FrameSoundness.lean:1251`'s standing `sorry`
      (`branchSatisfiableIn_s4FC_ancestor_redirect`, re-located by grep) is untouched.
- [ ] `accPinnedBy`, `branchSatisfiablePinnedIn`, and
      `branchSatisfiablePinnedIn_redirect_mechanical` are byte-identical to their pre-task state.
- [ ] `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` is unmodified (read-only reference).
- [ ] `lake build Cslib.Logics.Modal.Tableau.FrameSoundness` clean at task close.
- [ ] `lake exe lint-style` clean at task close.
- [ ] Any retained probe declaration passes `lean_verify` with axioms limited to `propext`,
      `Classical.choice`, `Quot.sound`.
- [ ] The report exists, carries one of the three verdict values, and includes the verbatim goal
      captures.

## Artifacts & Outputs

- `specs/587_canonical_witness_restriction_probe/plans/01_canonical-witness-restriction-probe.md` (this file)
- `specs/587_canonical_witness_restriction_probe/reports/01_canonical-witness-restriction-probe.md` (the deliverable)
- `specs/587_canonical_witness_restriction_probe/summaries/01_canonical-witness-restriction-probe-summary.md`
- Zero or one retained Lean declaration in `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` --
  retained only on a sorry-free passing probe, reverted in every other case.

## Rollback/Contingency

The probe sections in Phases 1-2 use the append-then-revert pattern plan v5's sub-step 1.2 used.
Rollback is: delete everything below the `/-! ### CANONICAL-WITNESS RESTRICTION PROBE -- REVERT UNLESS SORRY-FREE -/`
delimiter and confirm `git diff Cslib/Logics/Modal/Tableau/FrameSoundness.lean` is empty. Because
the probe never edits an existing declaration, rollback cannot damage landed work.

If the task is interrupted mid-probe, the recorded `lean_goal` captures taken so far are the
salvageable output: mark the phase `[PARTIAL]`, revert the probe section, and write whatever
partial verdict the captures support. A partial record of where the probe got stuck is strictly
more useful to task 553 than an uncommitted proof attempt, and matches this task's deliverable
(a verdict, not a construction).

Under no circumstance is a `sorry` committed to close a probe, and under no circumstance is the
standing `:1251` sorry modified to make a probe go through.
