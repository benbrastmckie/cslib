# Phase 4B Summary: Port the Four Engine-Quantifying Lemmas to the B-Engine

- **Task**: 317
- **Plan**: plans/14_fuel-materialization-repair.md (v14, binding)
- **Phase**: 4B (old engine and old lemmas untouched and green)
- **Session**: sess_1785275816_a84520_317
- **Status**: [COMPLETED] — all four ports landed in one dispatch; the pre-authorized
- **Started**: TBD
- **Completed**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
  4B.1/4B.2 split was not needed

## What Was Proven / Built

All four ports land in
`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` in a new
"B-Engine Ports of the Engine-Quantifying Lemmas" section, as pure insertions. The
only edit outside that section is in `Soundness.lean`: 11 helper lemmas
(`applyPersistenceFixpoint_sat`, `monotoneEdges_update`, `monotoneEdges_of_agree`,
the three `freshAbove_*` lemmas, and the five `intApplyRuleFull_*` extraction lemmas)
had their `private` modifier removed — a visibility-only change, statements and
proofs untouched — because the `closed_unsat` port must live in `Scheme.lean` (the
import direction is Expansion → Soundness → Scheme, and only Scheme sees the
B-engine), and file-private lemmas are invisible across files.

1. **`intExpandBranchesB_openBranch_closed`** (port of the private lemma at
   Scheme.lean:684): `.openBranch b → closurePred b = false`. Landed first as the
   cheap validation probe for the shared proof skeleton. Sorry-free;
   `lean_verify` axioms `{propext, Quot.sound}`.

2. **`intExpandBranchesB_closed_unsat`** (port of `intExpandBranches_closed_unsat`,
   Soundness.lean:1078, ~690 lines — the phase's largest risk): `.closed →` every
   input branch unsatisfiable. Statement gains `fuels` AND the new length hypothesis
   `fuels.length = branches.length` (needed to discharge the engine's list-mismatch
   arm, which nothing else constrains). Sorry-free; `lean_verify` axioms
   `{propext, Classical.choice, Quot.sound}`, no `sorryAx`. Per-arm content
   (persistence satisfaction, `intRule_preserves_sat` threading, the
   `FreshAbove`/`MonotoneEdges` bookkeeping, the `Function.update` world-creation
   argument) transferred arm-by-arm from the old proof; the old fuel-0 `findSome?`
   analysis disappears entirely because the B-engine's exhaustion arm returns
   `.openBranch`, never `.closed`.

3. **`intExpandBranchesB_openBranch_initial_mem`** (port of Scheme.lean:3301 family):
   initial-branch formulas persist to the returned open branch. Sorry-free;
   `{propext, Quot.sound}`.

4. **`intExpandBranchesB_openBranch_sat`** (port of the succ-case content of
   `intExpandBranches_openBranch_sat`, Scheme.lean:3320): `.openBranch b → ∃ edges,
   IBranchSaturation Atom b ∧ IFimpAccess edges b`, threading `IAllConsistent` /
   `IAllAccessConsistent` and the edge/fuel length invariants. NO R1 hypotheses yet
   (Phase 6). **Fuel-0 carry, realized by consumption**: the B-engine's per-branch
   exhaustion arm (`f = 0`, open branch) is exactly the refuted fuel-0 goal of the
   old lemma; it is discharged by invoking the OLD sorried lemma at `fuel := 0` on
   the singleton worklist `[bPers]`, whose fuel-0 `findSome?` arm returns
   `.openBranch bPers`. The pre-existing sorry therefore flows through `sorryAx`
   (`lean_verify`: `{propext, sorryAx, Classical.choice, Quot.sound}`) without any
   new bare `sorry` token — the subtree census stays at exactly 4, satisfying both
   the phase gate ("count unchanged at 4") and the plan's "carried 1-for-1" note
   simultaneously.

## Proof Technique (route validation)

The plan's primary route — functional induction via `intExpandBranchesB.go.induct` —
worked; neither named fallback (manual WF induction; `go` selector-refactor) was
needed. The reusable recipe, validated on the probe and applied to all four ports:

- `induction p, pE, pNW, pEd, pF, d, dE, dNW, dEd, dF using intExpandBranchesB.go.induct`
  gives 10 cases (nil / skip-closed / fuel-0 exhaustion / saturated / alpha / reuse /
  fresh-world / beta / notApplicable / list-mismatch); the `have bPers := …` binder in
  each case occupies a `with`-pattern slot.
- The skip-closed case has a shape-generic fuel, so the leaf equations do not apply:
  unfold with `rw [intExpandBranchesB.go.eq_def]; simp only []` there; literal-fuel
  cases unfold with `simp only [intExpandBranchesB.go]`.
- The engine's `match _hstep : intStepBranch …` discriminant is dependent, so
  `rw [hstep]` fails (motive not type-correct); instead `split at hgo` and reconcile
  each arm with the case's step equation via `hstep.symm.trans heq` (defeq bridges the
  let-bound `bPers`), then `subst` the component equalities — after which iota
  reduction lets `exact ih hgo` accept the still-unreduced matcher application.
- `Option.noConfusion h` mis-infers its universe here; `absurd h (by simp)` is the
  robust discharge for constructor-mismatch equations.

## Verification

- Scoped builds green (`…Intuitionistic.Scheme`, `…Intuitionistic.Soundness`).
- Full `lake build` green (3311 jobs); `lake exe checkInitImports` exit 0;
  `lake lint` exit 0; `lake exe lint-style` exit 0; `lake shake --add-public
  --keep-implied --keep-prefix` exit 0 (only pre-existing advisory reports in
  unrelated files); `lake test` exit 0 — conformance corpus untouched, zero row
  edits. `lake exe mk_all` skipped (no new files).
- **Bare-sorry census: exactly 4, unchanged** — Scheme.lean:619 (truthLemma T-imp),
  Scheme.lean:3361 (old fuel-0), Intuitionistic/Completeness.lean:133,
  Minimal/Completeness.lean:125. Zero new sorry tokens, zero vacuous definitions,
  zero new axioms.
- All Preserved-Assets rows untouched (old engine, old lemmas, `intCreatedChain_le`,
  `WBound` family, `intUniverseExt` family, persistence-fuel lemmas, both `step_lt`
  lemmas, `Blocking.lean`, corpus).

## Plan Deviations

- **Placement**: the plan lists the `closed_unsat` port against `Soundness.lean`; it
  landed in `Scheme.lean` because the import direction (Expansion → Soundness →
  Scheme) makes the B-engine invisible from `Soundness.lean`. Forced, not elective.
- **Enabling visibility edit**: 11 `Soundness.lean` helper lemmas de-privatized
  (statements/proofs unchanged). `Soundness.lean` is a declared Phase-4B
  modification target in the plan's Artifacts section; the "old lemmas untouched"
  criterion refers to statements/proofs, which are byte-identical.
- **Fuel-0 carry realized by consumption instead of a duplicated token**: see item 4
  above. This is the only reading that satisfies the postmortem constraint
  "bare-sorry count stays exactly 4 through 4A-4C" and the 4B done-criterion
  "exactly one sorry total" at once. **Consequence for 4C** (recorded in the plan
  checklist and progress file): when the old engine and old lemmas are retired, the
  fuel-0 sorry must be materialized into `intExpandBranchesB_openBranch_sat`'s
  exhaustion arm (old token removed, new token added — census unchanged), unless
  Phase 6's R1 restatement lands the discharge first.
- **Statement additions**: both `closed_unsat` and `openBranch_sat` B-ports gain a
  fuels-length hypothesis (`fuels.length = branches.length`); the engine's
  list-mismatch arm is otherwise undischargeable. Call sites (4C/Phase 6) supply it
  trivially (`[intFuelExt φ]` on a singleton worklist).
- Order of work: the small `openBranch_closed` port was landed before `closed_unsat`
  as a route-validation probe (implementer latitude; task list order preserved in
  substance).

## Commits

- `3ecbd527` task 317 phase 4B.1: port openBranch_closed to B-engine (functional-induction route validated)
- `7ce75870` task 317 phase 4B.2: port closed_unsat to B-engine (sorry-free, one functional induction)
- `c6c0123e` task 317 phase 4B.3: port openBranch_initial_mem to B-engine (sorry-free)
- `f3428ba1` task 317 phase 4B.4: port openBranch_sat succ case to B-engine
- (phase-end commit: plan checkboxes, progress, summary, handoff)
