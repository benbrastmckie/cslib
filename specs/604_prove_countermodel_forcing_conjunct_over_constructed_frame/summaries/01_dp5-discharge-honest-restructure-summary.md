# Implementation Summary: Discharge DP-5 and land the honest conjunct-2 negative result

- **Task**: 604 - Prove the countermodel forcing conjunct over the constructed frame
- **Status**: [COMPLETED] (implementation) — the task's literal target is a documented negative
- **Plan**: `plans/01_dp5-discharge-honest-restructure.md`
- **Session**: sess_1786312852_6b5c1b_604

## Negative result (the task's literal target)

Conjunct 2 of `openBranch_countermodel` (`¬IForces …`) over the frame task 603 constructed
(`rawEdges`) is **machine-refuted**, not merely hard. `CslibTests/WitnessProbe.lean:174-176`
shows `rawEdges` is upward-closed but FORCES `phiRef1` at world 0, and
`CslibTests/BetaSplitRefutation.lean:304,387` confirms that `rawEdges` list is the real
algorithm's actual output at the real fuel. No proof of the literal target exists to be found.
This was the delegation-authorised negative outcome, and it is what this task delivers, alongside
the positive result below.

The full frame-adequacy disposition — the machine-checked table showing `IFimpAccess` and
positive persistence sit on opposite frames, the three excluded pruning/fixpoint constructions,
and the residual open obligation — is now recorded in-source in `openBranch_countermodel`'s
docstring (`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`), not just in the
research report.

## Positive result: DP-5 discharged

`truthLemma`'s T(φ'→ψ') case (the sole obstruction historically named "DP-5" and "Gap 1" in the
file's own STOP-gate notes) is now **proved, sorry-free**. `truthLemma` gained an explicit
`hpers` hypothesis (positive-formula persistence along `edges`) and the case closes by chaining
`hpers` along `Relation.ReflTransGen` (`induction hle`) to transfer the source world's
`T(φ'→ψ')` membership to the accessible world, then applying `sat_timp`. `truthLemma` is now an
unconditionally true, reusable theorem over any frame carrying `hpers` — provable at the raw
frame (`IPosPersistRaw`/`IWorldsPlanted`, both already sorry-free) and refuted at the augmented
frame (`CslibTests/BetaSplitRefutation.lean`).

## Restructure: the surviving sorry moved from refuted to open

`openBranch_countermodel` previously `refine`d the AUGMENTED (`augSets`) `edges` witness and
`sorry`d only the upward-closure conjunct — a REFUTED statement, since `hpers` fails at that
frame. The proof now commits to no `edges` witness at all: the whole existential is a single
`sorry`, and that goal is genuinely OPEN, not refuted. The dropped extraction/`refine` machinery
survives verbatim in `openBranch_rawEdges_upward_closed` immediately below, so nothing is lost.

## Net effect (measured, not asserted)

- `Scheme.lean` live sorry count: **2 → 1** (confirmed via `lake build`'s own "declaration uses
  `sorry`" warning: exactly one, at `openBranch_countermodel`, `Scheme.lean:8012`).
- Zero new sorries anywhere in the repo.
- Zero new axioms: `lean_verify` on `truthLemma`, `intTruthLemma`, and `minTruthLemma` reports
  only the standard `propext`/`Classical.choice`/`Quot.sound` triple for all three.
- Zero new definitions, typeclasses, notations, or imports (confirmed via diff grep against the
  four phase-1/3 commits).
- No task-number citation entered any file outside `specs/**` (confirmed via targeted grep of
  all seven touched `Cslib/` files).

## Phases completed

1. **Discharge DP-5 and restructure `openBranch_countermodel`** — `truthLemma` gains `hpers` and
   the 15-line verified proof; `intTruthLemma`/`minTruthLemma` thread `hpers` through (the two
   external call sites the research report flagged as incomplete in its own scope); the
   frame-committing `refine` is dropped. Files: `Scheme.lean`, `Intuitionistic/Completeness.lean`,
   `Minimal/Completeness.lean`. Commit `0e22f0d9`.
2. **Record the frame-adequacy verdict** — rewrote the `truthLemma` STOP-gate note, the T-imp
   in-body comment, `IPosPersistRaw`'s docstring, `openBranch_countermodel`'s docstring and
   sorry-site, and `openBranch_rawEdges_upward_closed`'s stale "successor task" claim. Vocabulary
   discipline applied throughout: "refuted" only for the machine-checked cells (CI-cited),
   "open" for `openBranch_countermodel` itself, "excluded" for the four eliminated
   constructions. Commit `6265117a`.
3. **Sweep stale cross-file `truthLemma`-carries-a-sorry claims** — six files matching the
   plan's hypothesised set exactly: both `DecisionProcedure.lean` "Notes on sorry" inventories
   (removed the `truthLemma` bullet, corrected the deferred-sorry count), both
   `Completeness.lean` wrapper docstrings, both `Metalogic/*Decidability.lean`
   factoring-deferred notes. Commit `66fbab50`.
4. **Follow-on task for the root cause** — created task 609, "Re-validate
   `intFImpReuseWitnessAnc?` loop-back containment as the branch grows"
   (`Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`, depends on 604), naming
   the root cause every route in the frame-adequacy analysis dead-ends on, without citing this
   task's number in any deliverable file. Commit `8ed4e308`.
5. **Final verification** (this phase) — full CSLib CI gate, sorry/axiom counts, summary.

## Verification (measured)

- `lake exe cache get`, `lake build` (full): **green**, 3325 jobs, only the three expected
  sorry warnings (`Scheme.lean:8012` `openBranch_countermodel`,
  `Intuitionistic/Completeness.lean:160` `intuitionisticTableau_complete` DP-3,
  `Minimal/Completeness.lean:156` `minimalTableau_complete` DP-4 — all pre-existing, unrelated
  to `truthLemma`).
- `lake exe checkInitImports`: clean, no output.
- `lake lint`: 373 pre-existing warnings repo-wide, **zero** in any of the seven files this task
  touched (confirmed via targeted grep of the full lint log against each touched file's path).
- `lake exe lint-style`: clean, no output, exit 0.
- `lake shake --add-public --keep-implied --keep-prefix`: ran clean against the touched files
  (only reproduces the same three pre-existing sorry warnings, no import-minimization findings).
- `lake exe mk_all --module`: "No update necessary" (no new files were created).
- `lake test`: **all 9396 jobs built**, including the CI-protected assertions this task's
  disposition depends on (`CslibTests.BetaSplitRefutation`, `CslibTests.WitnessProbe`,
  `CslibTests.HvalidShapeRefutation`, `CslibTests.TableauConformance`).
- `lean_verify` (lean-lsp MCP): `truthLemma`, `intTruthLemma`, `minTruthLemma` each report
  exactly `["propext", "Classical.choice", "Quot.sound"]` — no `sorryAx`, no unexpected axiom.
- `check-task-references.sh`: fails only on pre-existing `.memory/` entries from unrelated
  tasks (552, 317, 557, 426/427) that predate this session; zero new violations in any tree this
  task's changes could have touched (`Cslib/`, `agent-system/extensions/`, `.opencode/`, `lua/`).

## Plan Deviations

None. All five phases were executed as planned, including the plan's own discovered scope
widening (the two external `truthLemma` call sites in `Completeness.lean`) which the plan had
already identified and pre-authorised in its "Discovered during planning" section.

## Follow-on

Task 609 (`revalidate_intfimpreuse_witness_anc_loopback_containment`) tracks the calculus-level
root-cause repair in `Expansion.lean` that would let the augmented frame carry both
`IFimpAccess` and positive persistence simultaneously, collapsing `openBranch_countermodel`'s
remaining existential into a direct `truthLemma` instantiation. It is explicitly out of scope
for `Scheme.lean`-only dispatches.

## Modified Files

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean`
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/DecisionProcedure.lean`
- `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean`
- `Cslib/Logics/Propositional/Metalogic/IntDecidability.lean`
- `Cslib/Logics/Propositional/Metalogic/MinDecidability.lean`
- `specs/state.json`, `specs/TODO.md` (task 609 creation)
- `specs/604_prove_countermodel_forcing_conjunct_over_constructed_frame/plans/01_dp5-discharge-honest-restructure.md`
  (phase status markers)
