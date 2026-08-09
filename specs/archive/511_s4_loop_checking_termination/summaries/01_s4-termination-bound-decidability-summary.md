# Implementation Summary: Task #511 — S4 Loop-Checking Termination Bound & Decidability

- **Task**: 511 — s4_loop_checking_termination (follow-on to task 506, Phases 8-9)
- **Plan**: `specs/511_s4_loop_checking_termination/plans/01_s4-termination-bound-decidability.md`
- **Status**: [PARTIAL] — Phases 1-6 landed green, fully sorry-free (self-contained deliverable:
  the original task 506 Phase 8 world-bound blocker is closed); Phase 7 (Phase 9 decidability)
  [BLOCKED] with a precise, newly-sharpened goal state and a spawn recommendation
- **Files changed**: `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (primary); no changes to
  `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` this task (read/verified only)
- **Zero-debt**: zero `sorry`, zero new `axiom`, zero vacuous placeholders across every dispatch

*(Note: this summary supersedes an earlier draft written mid-task when Phase 5 was itself
transiently blocked on the guard-vs-keys mismatch described below; that gap was subsequently
closed by redesigning the guard used by the keyed shadow stepper — see Phase 5 below. The
sub-narrative is preserved because the *same class* of gap resurfaces, unresolved, at Phase 7.)*

## What Landed (Phases 1-6, all green, independently CI-verified, zero sorry)

1. **Phase 1 — Exponent fix**: `modalWorldBoundS4 φ₀` corrected from `2 ^ |Sf|` to
   `2 ^ (2 * |Sf|)` (the pigeonhole codomain must distinguish sign, per the research report).
   `modalUniverseS4_length_le` re-verified.

2. **Phase 2 — Finite signed-key infrastructure**: `signedSubfmls φ₀`, `relevantSetFinset φ₀ b w`,
   `signedSubfmls_card_le`, `signedSubfmls_powerset_card_le`, `relevantSetFinset_mono`
   (deviation: `≤` not `=`, sufficient and avoids an unproven `modalSubfmls`-nodup dependency).

3. **Phase 3 — Successor-birth-content guard redesign (fixes Gap 2)**: `successorBirthContent`
   and the redesigned `blockingWorldS4` (compares an existing known world's *current* relevant
   set against the *prospective successor's* content, not the *source* world's own set). All
   task-506 consumers (`modalHintikkaSetS4`, `modalTruthLemmaS4`, five bridge lemmas in
   `FrameCompleteness.lean`) re-verified unaffected.

4. **Phase 4 — Key-threaded S4 step + restated `S4LoopInv`**: `modalStepBranchS4Keyed`, an
   S4-specific stepper threading `keys : List (WorldIndex × Finset (Sign × Proposition Atom))`
   alongside `(b, e, acc)`. `S4LoopInv` restated over `keysTotal`/`keyLowerBd`/`keysDistinct`/
   `keysInUniverse` (replacing the unsound `worldSetsDistinct`).

5. **Phase 5 — `S4LoopInv` preservation (the crux, ~13h across 6 dispatches)**: **all 10 fields
   CLOSED, zero sorry.** The Phase-3 `blockingWorldS4` (live-set-based) guard proved
   *insufficient* to prove `keysDistinct` preservation for exactly the mismatch class
   documented in the (superseded) Phase 5 note above — the fix was a *second*, purpose-built
   guard `blockingWorldS4Keyed` (compares against the recorded `keys` list directly, not live
   sets), consumed only by the keyed shadow stepper `modalStepBranchS4Keyed`; the original
   `modalApplyOneS4`/`blockingWorldS4` were left untouched (task 506's Hintikka/truth-lemma
   consumers depend on them unchanged). `bClosure`/`eClosure` closed last, via a T-self/4-
   propagation formula-subset composite plus Phase 6's pigeonhole bound as a genuine
   prerequisite for their 2 minting shapes.

6. **Phase 6 — Pigeonhole world bound (closes the original task 506 Phase 8)**:
   `modalKnownWorlds_length_le_worldBoundS4` (injective map from known worlds into
   `(signedSubfmls φ₀).powerset` via `keysTotal`/`keysDistinct`/`keysInUniverse`) and
   `modalStepBranchS4_worldBound : modalMaxWorld b < modalWorldBoundS4 φ₀` — required a new
   proof-internal auxiliary invariant `worldsContiguousS4` (not anticipated in the plan's
   original wording) plus its own preservation lemma. **Both proven for `modalStepBranchS4Keyed`
   (the keyed shadow stepper), not for the real `modalStepBranchS4`/`modalTableauS4` driver** —
   this distinction is the root of Phase 7's blocker, below.

## Phase 7 — [BLOCKED]: the shadow-invariant does not (yet) reach the real decision procedure

**Task 1 (independent, already landed by a prior dispatch, re-verified clean this dispatch)**:
the Hintikka-alignment bridge `modalHintikkaSetS4_eq : modalHintikkaSetS4 φ₀ b acc =
modalHintikkaSetGen (modalApplyOneS4 φ₀) b acc` closes by `rfl`. `lean_verify` confirms only
`propext`/`Classical.choice`/`Quot.sound`, no `sorryAx`.

**Task 2 (Planner Decision 2, recorded)**: the abstract termination-measure interface (9-A)
should be spawned as a separate task, not inlined — confirmed, with an important update: a
task 515 dispatch (`CompletenessLoop.lean` commit `ecfa123e`, concurrent/later than this task's
own research) already landed a more general, rank-free top-loop lemma
`modalExpandBranchesHintikka`, parametrized over an abstract `Aux : List SF → List SF →
Accessibility → Prop` (`AuxStepPreserved`/`AuxBounds`/`ModalLoopInvHintikka`), built to support
S5's decidability (`ModalLoopAuxS5w`). This is real, useful groundwork for 9-A that did not
exist when this task was researched.

**Task 3 (9-B attempt, concrete, BLOCKED)**: a genuine attempt to wire
`modalStepBranchS4_worldBound` into fuel sufficiency for `Decidable (s4Valid φ)` surfaced a
structural gap not previously documented:

- `s4Valid`'s `Decidable` instance must run the REAL driver `modalTableauS4 φ := modalTableauGen
  (modalApplyOneS4 φ) φ`, guarded by `blockingWorldS4` — a **live-relevant-set** comparison.
- `S4LoopInv`/`modalStepBranchS4_worldBound` (Phases 4-6) are proven only for the KEYED shadow
  stepper `modalStepBranchS4Keyed`, guarded by `blockingWorldS4Keyed` — a **recorded-birth-key**
  comparison. Confirmed directly in the theorem signature: `modalStepBranchS4_preserves_S4LoopInv`
  takes `modalStepBranchS4Keyed φ₀ b e acc keys = some (...)` as its step hypothesis, not
  `modalStepBranchS4`.
- Since `keyLowerBd` gives only `keys ⊆ relevantSetFinset` (a strict subset in general, not
  equality), a live-set freshness guarantee (`blockingWorldS4_none_fresh`) does not imply a
  keys-freshness guarantee — this is the exact mismatch Phase 5's own guard redesign
  (introducing `blockingWorldS4Keyed` as a *second* guard) was built to route around, now
  re-encountered from the Decidable-instance side: the world-bound guarantee is proven about a
  driver `modalTableauS4` does not run.
- Wrapping the existential (`Aux(b,e,acc) := ∃ keys, S4LoopInv-fields`) inside the newly-found
  `modalExpandBranchesHintikka` does **not** sidestep this: `AuxStepPreserved` would still need
  to re-derive `keysDistinct` preservation using the REAL (live-set) guard's contract, which is
  exactly the insufficient argument above.
- **What would close it**: either (a) a bespoke S4-specific top-level driver around
  `modalStepBranchS4Keyed` (full `processNext`-style fuel induction, ~700 lines by the K/T/B/S5
  precedent, plus re-verification that soundness/truth-lemma connect to the keyed guard — this
  looks plausible in principle since the keyed and unkeyed guards' non-minting behavior and
  blocked-target-content contracts agree, but is unverified), or (b) extending the driver
  framework itself so `RuleApply`/`Accessibility` can carry extra opaque per-branch threaded
  state generically (a materially larger 9-A than originally scoped, since it would need to
  support state beyond a `Prop`-valued `Aux`).

No `sorry`/`axiom`/vacuous placeholder was introduced while investigating; no code was written
that could not close cleanly. `lake build` green on both files; `lean_verify` clean on every
lemma touched or re-checked this dispatch.

## Plan Deviations

- Phase 2: `≤` not `=` for `signedSubfmls_card`/`_powerset_card` (documented inline; sufficient,
  avoids an unproven `modalSubfmls`-nodup dependency).
- Phase 4: no bridge lemma from `modalStepBranchS4Keyed` to `modalStepBranchS4` was ever built
  (not required by any landed proof — Phase 5's "generic bridge to `modalStepBranchGen`" plan
  was superseded by direct case-splits on `modalStepBranchS4Keyed`'s own definition).
- Phase 6: `worldsContiguousS4`/`keysWorldsKnown` proof-internal auxiliary invariants (not
  `S4LoopInv` fields) were needed beyond the plan's original wording; both threaded as extra
  hypotheses/conclusions rather than reopening the completed Phase 4 structure design.
- Phase 7: marked `[BLOCKED]` after a concrete, code-informed attempt (not analysis alone)
  identified a structural driver/shadow-invariant mismatch; see above.

## Verification

- `lake build Cslib.Logics.Modal.Tableau.LoopChecking` — green (847 jobs), only pre-existing
  style-lint warnings, no errors, no `sorry` compiler warnings.
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` — green (880 jobs), only pre-existing
  style-lint warnings; all task-506 consumers unaffected (file untouched this task).
- `grep -c '\bsorry\b'` on both files: only doc-comment prose mentions ("zero sorry"), zero
  actual `sorry` tactic/term uses.
- `lean_verify` on `modalHintikkaSetS4_eq` and `modalStepBranchS4_worldBound`:
  `propext`/`Classical.choice`/`Quot.sound` only, no `sorryAx`.
- Full CSLib CI pipeline (`checkInitImports`/`lint`/`lint-style`/`shake`/`mk_all`/`test`) not
  re-run in full this dispatch (no new code was written — plan/summary/handoff docs only; the
  scoped module builds above are the relevant regression check, and concurrent task 517/530/531
  sessions have uncommitted edits elsewhere that make a full-project `lake build` non-diagnostic
  for this task per standing dispatch guidance).

## Next Steps for a Follow-On Task

Spawn a task scoped to `CompletenessLoop.lean`/`GenericDriver.lean`: "abstract termination-
measure interface for S4/B loop lemma (task 511 Phase 7 follow-on)", briefed with the exact
finding above — survey task 515's `Aux`-parametrized `modalExpandBranchesHintikka` first (it is
real, landed groundwork), but note it will need extending to support threaded state beyond a
`Prop`-valued `Aux` before it can close S4's `Decidable (s4Valid φ)`, OR a bespoke S4-local
`processNext`-style driver built directly around `modalStepBranchS4Keyed` if the generic
extension is judged too invasive. Shared context: tasks 505 (B-system) and 513 benefit from
either resolution. Phases 1-6 of this task (the world bound over the shadow driver) remain a
valid, self-contained, sorry-free deliverable regardless of Phase 7's outcome.
