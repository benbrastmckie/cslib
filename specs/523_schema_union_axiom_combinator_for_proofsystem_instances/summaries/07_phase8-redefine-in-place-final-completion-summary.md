# Implementation Summary: Phase 8 (Redefine-in-Place Finish) + Task 523 Completion

- **Task**: 523 - Replace the 15 hand-written per-system axiom inductives with a compositional
  schema-union combinator
- **Plan**: plans/02_schema-union-per-file-rollout.md
- **Phases covered by this summary**: Phase 8 sub-phase 8.4 (the task's final sub-phase);
  Phases 1-8.3 were completed and summarized in prior dispatches (summaries 02-06 plus inline
  plan records for 8.1-8.3).
- **Status**: [COMPLETED] (task and plan both)

## What Was Done

Phase 8 sub-phase 8.4 was the terminal cleanup step, executed after the abbrev redefinition
(8.3) made every `<Sys>Axiom φ` and `SchemaUnion sysTags φ` the same type by definitional
equality:

- **8.4a**: Simplified all 432 `(schemaUnion_..._iff_...).mp ⟨...⟩` call sites across the 15
  `Systems/*/Completeness.lean` files to the bare `⟨...⟩` witness, in 4 scoped/committed
  sub-groups (K/T/D/B; K4/K5/K45/S4; S5/TB/KB5; D4/D5/D45/DB).
- **8.4b**: Simplified the single `(schemaUnion_..._iff_....mpr h_ax)` call site in each of the
  15 `Systems/*/Soundness.lean` files to the bare `h_ax`, same 4 sub-groups.
- **8.4c**: Collapsed all 24 direct-edge lemmas in `InterSystem/AxiomSubsumption.lean` from
  `bridge_y.mp (SchemaUnion.subsumption (by decide) (bridge_x.mpr h))` to
  `SchemaUnion.subsumption (by decide) h`.
- **8.4d**: Simplified the 12 code sites in `InterSystem/IntToClassical.lean` and updated three
  stale docstrings that named the now-deleted bridge lemmas.
- **8.4e**: Deleted `Cslib/Logics/Modal/ProofSystem/SchemaBridges.lean` after a repo-wide grep
  confirmed zero remaining `schemaUnion_..._iff_...` references and zero remaining imports of
  `ProofSystem.SchemaBridges` anywhere in `Cslib/`. Updated `SchemaTags.lean`'s docstring to
  stop referencing the deleted file.
- **8.4f**: Ran the full CSLib CI pipeline (`lake build`, `checkInitImports`, `lake lint`,
  `lake exe lint-style`, `lake test`, `lake exe mk_all --module`, `lake shake`), `lean_verify`
  spot-checks, and computed the net line delta.

## Verification Results

- **Full `lake build`**: green, 3250/3250 jobs.
- **`lake exe checkInitImports`**: clean (no output).
- **`lake lint`**: "Linting passed for Cslib." — clean.
- **`lake exe lint-style`**: clean (exit 0, no output).
- **`lake test`**: green, 9242/9242 jobs (exit 0).
- **`lake exe mk_all --module`**: added `SchemaSoundness`, `SchemaTags`, `SchemaUnion` to the
  `Cslib.lean` barrel (previously missing from earlier phases); `SchemaBridges` is naturally
  absent since it was deleted. Full `lake build Cslib` re-verified green after the barrel edit.
- **`lake shake --add-public --keep-implied --keep-prefix`**: flagged zero of this task's
  touched files. The full shake run surfaces ~2900 lines of pre-existing, unrelated import-
  minimization debt across the Propositional/Temporal modules — out of this task's scope and
  left untouched.
- **`lean_verify`** (axioms only, zero `sorry`):
  - `k_soundness`: `propext`, `Classical.choice`, `Quot.sound`
  - `s5_soundness`: `propext`, `Classical.choice`, `Quot.sound`
  - `KAxiom_implies_TAxiom`: `propext`, `Quot.sound`
  - `unionSound`: `propext`, `Classical.choice`, `Quot.sound`
  - No new axioms introduced anywhere in the refactor.
- **`sorry` count**: zero in `Cslib/Logics/Modal/` (repo-wide grep confirms only "sorry-free"
  prose mentions in docstrings/comments, no live `sorry` tactic).
- **`KB5 → S5` edge**: confirmed still absent (deliberate, per the resolved design decision —
  `modalFive ∈ kb5Tags` but `modalFive ∉ s5Tags`).

## Net Line Delta

Baseline = `ad2d13d6^` (the commit immediately before task 523's first code commit,
`ad2d13d6`, "task 523 phase 1: land ModalSchemaTag + SchemaUnion + generic subsumption").

`git diff --numstat ad2d13d6^ HEAD -- Cslib/Logics/Modal/`, excluding the two files touched by
the concurrent task-517/537 session (`Metalogic/Constructive/Labelled/{Completeness,
Soundness}.lean` — pure additions, +582/-0, unrelated to this refactor and outside this task's
territory):

**+1483 / -2105, net -622 lines** for task 523's actual scope.

(For transparency: including those two unrelated files, the whole-`Modal/`-tree net is still
negative, -40 lines — the conclusion "net line-negative" holds either way.)

## Plan Deviations

None. All four sub-phase-8.4 checklist items were executed exactly as planned. The mechanical
call-site simplifications were textually regular (verified via `grep`/`sed` pattern audits
before each edit) and every scoped build was green before committing.

## Files Modified (Phase 8 sub-phase 8.4)

- `Cslib/Logics/Modal/Metalogic/Systems/{K,T,D,B,K4,K5,K45,S4,S5,TB,KB5,D4,D5,D45,DB}/Completeness.lean` (15 files)
- `Cslib/Logics/Modal/Metalogic/Systems/{K,T,D,B,K4,K5,K45,S4,S5,TB,KB5,D4,D5,D45,DB}/Soundness.lean` (15 files)
- `Cslib/Logics/Modal/Metalogic/InterSystem/AxiomSubsumption.lean`
- `Cslib/Logics/Modal/Metalogic/InterSystem/IntToClassical.lean`
- `Cslib/Logics/Modal/ProofSystem/SchemaTags.lean` (docstring update)
- DELETED `Cslib/Logics/Modal/ProofSystem/SchemaBridges.lean`
- `Cslib.lean` (barrel update via `mk_all --module`)
- `specs/523_schema_union_axiom_combinator_for_proofsystem_instances/plans/02_schema-union-per-file-rollout.md`
  (sub-phase 8.4, Phase 8, and overall plan Status marked `[COMPLETED]`)

## Task Completion

This was the task's final sub-phase. Task 523 is now `[COMPLETED]`. Per the pr-prohibition rule
and this task's own binding constraints, no branch, PR, or Zulip post was created by this
agent — the plan's "Pre-PR user step" (a Zulip heads-up about the large-blast-radius but
net-line-negative landing) and any subsequent `/pr` invocation are left to the user.
