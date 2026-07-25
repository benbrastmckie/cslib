# Phase 11 Dispatch Summary: Completeness (`modalTableauS4Keyed_complete`)

- **Task**: 535 - Abstract termination-measure interface for S4/B loop lemma
- **Plan**: `plans/03_completeness-line-rescope.md`, Phase 11 (final phase of the rescoped
  completeness line)
- **Scope of this dispatch**: Phase 11 only — the completeness half. The decidability half
  (`s4Valid_decides`/`instDecidableS4Valid`) remains deferred to the separately-spawned
  soundness task, as scoped by the plan.
- **Commits**:
  - `6a121a8e` — "task 535 phase 11.1: entry-state fix + S4LoopInv/S4KeyedHintikkaInv initial
    instance"
  - `2526ac15` — "task 535 phase 11.2: keyed-driver initial-branch membership persistence lemma"
  - (this dispatch's final commit, wrap-up)

## What landed

`modalTableauS4Keyed_complete` (`Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`): **the
task's closing deliverable.** If `φ₀` is `s4Valid`, the keyed S4 tableau `modalTableauS4Keyed`
closes on it; contrapositively, an open branch yields a genuine reflexive-transitive-frame
Kripke countermodel. Modeled directly on `modalTableauS5_complete`, assembled from:

- `modalExpandBranchesS4Keyed_hintikka` (Phase 10, `LoopChecking.lean:6654`) — supplies the
  Hintikka-set fact, already in the concrete `modalHintikkaSetS4` form.
- `modalExpandBranchesS4Keyed_openBranch_initial_mem` (new, `LoopChecking.lean`) — supplies
  `F(φ₀)@0 ∈ b`.
- `modalOpenBranchS4_countermodel` (already landed, `FrameCompleteness.lean:401`) — turns the
  Hintikka set + initial membership into the countermodel and the `s4FC` frame fact.
- `modalTableauS4Keyed_initial` (new, `private`, `FrameCompleteness.lean`) — the entry-point
  instance of the induction's per-index invariant.

## The obstruction found, and its fix (read this before touching Phase 1 again)

Instantiating Phase 10's induction at `i = 0` (the literal tableau entry) requires proving
`S4LoopInv φ₀ [F(φ₀)@0] [] Accessibility.empty keys` for whatever `keys` value
`modalTableauS4Keyed` actually uses at its entry. The as-landed entry used `keys := []`. This is
**unprovable**: `S4LoopInv.keysTotal` demands every known world have a recorded birth key, world
`0` is already a known world (it is the label of the entry formula itself), and no step of the
driver ever mints world `0` again to backfill one — confirmed computationally: intro-ing the
goal and `simp [modalKnownWorlds]` reduces the obligation to `⊢ False`.

This is a bookkeeping gap in the current task's own Phase 1 entry point (world `0` is
pre-existing, not minted, so it was never seeded with a birth key) — **not** a defect in the
frozen task-511 `S4LoopInv` struct, and not a defect in any already-proven Phase 1-10 theorem (all
of those are stated for an arbitrary `keys` list, so they are byte-for-byte unaffected by what
concrete `keys` value the entry actually uses). It surfaced only now because Phase 11 is the first
point at which anyone instantiates the invariant at the literal entry rather than assuming it as
an ambient hypothesis.

**Fix**: `modalTableauS4Keyed`'s entry `keyss` argument changed from `[[]]` to `[[(0, ∅)]]` — the
root world is seeded with the trivial empty birth key. This trivially satisfies `keysTotal`
(`(0, ∅)` witnesses it), `keyLowerBd` (`∅ ⊆` anything), `keysInUniverse` (`∅ ⊆` anything), and
`keysDistinct` (vacuous for a singleton list). It changes `modalTableauS4Keyed`'s *computational
behavior* only insofar as `blockingWorldS4Keyed` could in principle redirect a later mint whose
birth content happens to equal `∅` to world `0` instead of minting fresh — a scenario the guard's
own `keysDistinct`-preserving design already anticipates and handles safely (a match blocks the
mint precisely to avoid a `keysDistinct` violation). No frozen task-511 declaration, and no
already-landed Phase 1-10 theorem, needed re-verification: all are generic in `keys`. This is the
one edit to a Phase 1-10 declaration made in this dispatch.

Two new additive declarations close the remaining wiring gap:

- `modalTableauS4Keyed_initial` (`FrameCompleteness.lean`, `private`): the four-way conjunction
  `S4LoopInv ∧ S4KeyedHintikkaInv ∧ keysWorldsKnown ∧ worldsContiguousS4` at the corrected entry
  configuration `(b = [F(φ₀)@0], e = [], acc = Accessibility.empty, keys = [(0, ∅)])`. All ten
  `S4LoopInv` fields plus the five `S4KeyedHintikkaInv` fields are proved directly (most
  vacuously, since `e = []` and `keys` is a singleton); `bClosure` needs
  `⟨.neg, φ₀, 0⟩ ∈ modalUniverseS4 φ₀`, proved the same way as S5/Five/Kb5's own initial lemmas.
- `modalExpandBranchesS4Keyed_openBranch_initial_mem` (`LoopChecking.lean`, public): the
  keyed-driver analogue of `modalExpandBranchesGen_openBranch_initial_mem`
  (`CompletenessLoop.lean:2007`), needed because `modalExpandBranchesS4Keyed` is a bespoke driver
  (not an instance of `modalExpandBranchesGen`), so the generic lemma's statement does not apply
  to it directly. Structurally an exact port (outer induction on `fuel`, `suffices key : …`
  worklist restatement, inner induction on `pending`), extended with the extra `keys`/`keyss`
  worklist column exactly as Phase 10 did for the Hintikka top-loop. Uses
  `modalStepBranchS4Keyed_branch_superset` (old branch content survives into every child) in
  place of the generic driver's `modalStepBranchGen_mem_preserved`, and the already-landed
  territory-local `modalStepBranchS4Keyed_newExps_const` for the length-matching step.

## R1 (guard-narrowing blast radius) note, per the dispatch's request

This phase, like Phase 10, does **not** call `modalStepBranchS4Keyed_blocked_witness_mem`
directly — it is consumed only inside Phase 7's already-landed
`modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv`, which Phase 10's induction (not this
phase) invokes. Phase 11's own code path (the two new lemmas plus the assembly theorem) never
touches the blocked-redirect witness argument at all. This is consistent with Phase 10's finding
and further confirms R1's future guard-narrowing re-work is bounded to Phase 7's internals, not
spread across the completeness assembly.

## Plan Deviations

- **`hintikka_congr_S4` was not needed as a separate wiring step.** The plan's task list named it
  as one of the four wiring targets, but Phase 10's `modalExpandBranchesS4Keyed_hintikka` already
  concludes in the concrete `modalHintikkaSetS4 φ₀ bR aR` form (the congruence bridge is internal
  to that theorem's own proof), which is exactly the hypothesis shape
  `modalOpenBranchS4_countermodel` expects. No separate bridging call was required in this
  dispatch's own code.
- **Entry-state fix** (`modalTableauS4Keyed`'s `keys` seed, `[[]]` → `[[(0, ∅)]]`) and **two new
  additive helper declarations** — see the obstruction section above. Both were necessary,
  additive-only, safe (verified via full regression checks below), and required for the plan's
  own stated wiring list to actually close.

No other deviations. The theorem's statement and overall proof shape match the plan's Phase 11
task list exactly.

## Verification

- `lake build Cslib.Logics.Modal.Tableau.LoopChecking`: 847 jobs, exit 0, zero new warnings (same
  10 pre-existing: 8 `unusedSimpArgs` + 1 hypothesis-unused note + 1 `longLine`).
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness`: 880 jobs, exit 0, zero new warnings.
- `lake build` (full project): 3253 jobs, exit 0. Remaining `sorry`s are all in unrelated,
  out-of-territory files (`Propositional/Tableau/{Intuitionistic,Minimal}/*.lean`), matching the
  Phase 9/10 baseline.
- `grep -n '\bsorry\b'` on both touched files: only the pre-existing docstring-prose mentions
  (`LoopChecking.lean:4619`, `FrameCompleteness.lean:576`). Zero actual `sorry`.
- `grep -n "instDecidableS4Valid\|s4Valid_decides" Cslib/`: only pre-existing docstring-prose
  mentions (two in `LoopChecking.lean`, one in this phase's own docstring, all referencing the
  deferred future work) — zero declarations. Confirms the deferred half was not attempted.
- `lean_verify modalTableauS4Keyed_complete`: `propext`, `Classical.choice`, `Quot.sound` only.
- `lean_verify modalTableauS4Keyed_initial`,
  `modalExpandBranchesS4Keyed_openBranch_initial_mem`: same three axioms only.
- `lean_verify instDecidableS5Valid` (regression): unchanged, same three axioms only.
- `lean_verify modalTableauB_sound` (regression): unchanged, same three axioms only.
- `lake exe checkInitImports`: clean.
- `lake lint`: 2 pre-existing errors, both in unrelated files (`CS5Completeness.lean`,
  `Temporal/Tableau/Saturation.lean`, concurrent out-of-scope work) — zero hits in either touched
  file.
- `lake exe lint-style`: zero hits in either touched file.
- `lake shake --add-public --keep-implied --keep-prefix`: zero new findings in `LoopChecking.lean`
  beyond the pre-existing baseline warnings; no hits in `FrameCompleteness.lean`.
- `lake exe mk_all --module`: no update necessary (no new files).
- Frozen task-511 deliverables (`S4LoopInv`, `blockingWorldS4Keyed`, `modalStepBranchS4Keyed`,
  `modalStepBranchS4_worldBound`, `modalHintikkaSetS4_eq`) byte-unchanged. `FmpMeasure.lean`,
  `Saturation.lean`, `CompletenessLoop.lean` byte-unchanged (read-only). Live `modalTableauS4` and
  S5/B call sites unchanged.

## Status

Phase 11 `[COMPLETED]`. **The task's completeness line is now COMPLETE**: `modalTableauS4Keyed`
is proven both to satisfy the termination-line Hintikka top-loop (Phase 10) and to close on every
`s4Valid` formula (Phase 11), with an explicit reflexive-transitive-frame countermodel construction
on any open branch. All 11 phases of `plans/03_completeness-line-rescope.md` are now
`[COMPLETED]`.

**Decidability remains explicitly out of scope and unachieved**, as the plan states plainly:
`Decidable (s4Valid φ)` needs BOTH the completeness line (this task, now done) and the soundness
line, which is blocked on a genuine mathematical gap in the current `blockingWorldS4Keyed` guard
(the blocked-mint-redirect edge's soundness, recorded in the plan's "Deferred / Spawned Scope")
and is carried by a separately-spawned task with its own authorization to revise the frozen guard.
This dispatch does not touch that guard and does not attempt `s4Valid_decides` or
`instDecidableS4Valid` in any form.
