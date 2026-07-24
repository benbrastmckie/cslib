# Implementation Summary: InterSystem Lattice Subsumption/Monotonicity Consolidation

- **Task**: 546 - factor_intersystem_lattice_onto_schemaunion
- **Plan**: `specs/546_factor_intersystem_lattice_onto_schemaunion/plans/01_intersystem-lattice-consolidation.md`
- **Status**: Implemented -- all 4 phases COMPLETED
- **Type**: cslib

## What Was Done

Consolidated the 8 near-parallel Subsumption/Monotonicity files in
`Cslib/Logics/Modal/Metalogic/InterSystem/` down to 4 files, per the R1 confined-consolidation
scope decided in research report 01:

1. **Phase 1 (verification)**: Confirmed via `lean_multi_attempt`/`lean_goal` (using temporary,
   fully-reverted scratch lemmas, since the tool's single-line substitution left dangling
   `match`-arm tokens) that `cases h <;> constructor` soundly discharges every tested
   representative constructor-match arm across all three same-base tracks (Constructive,
   Minimal, Intuitionistic) and both cross-base directions (`M*/C* -> I*`). No mis-selection
   observed on any of the 8 tested lemmas, including the parameterless `dbot` constructor and
   the disjoint-alphabet cross-base `MS4`/`CS4 -> IS4` arms. Adopted uniformly; no explicit-match
   fallback was needed.

2. **Phase 2 (Subsumption layer)**: Created
   `Cslib/Logics/Modal/Metalogic/InterSystem/LatticeSubsumption.lean`, merging
   `ConstructiveLatticeSubsumption.lean` + `MinimalLatticeSubsumption.lean` +
   `IntuitionisticLatticeSubsumption.lean` (9 lemmas total, 3 per base) with `## Constructive
   base` / `## Minimal base` / `## Intuitionistic base` section headers and a merged module
   docstring. Shortened `PropositionalStrengthSubsumption.lean`'s 8 lemmas in place with the
   verified tactic (file, name, and MK/CK-incomparability docstring preserved unchanged). Deleted
   the 3 original same-base files, re-pointed the 3 same-base Monotonicity files' Subsumption
   import to `LatticeSubsumption`, and regenerated the `Cslib.lean` barrel.

3. **Phase 3 (Monotonicity layer)**: Created
   `Cslib/Logics/Modal/Metalogic/InterSystem/LatticeMonotonicity.lean`, merging
   `ConstructiveLatticeMonotonicity.lean` + `MinimalLatticeMonotonicity.lean` +
   `IntuitionisticLatticeMonotonicity.lean` (18 `Derivable_mono` instantiation theorems + 9
   frame-condition inclusion lemmas, 6+3 per base) with per-base section headers. Deleted the 3
   original files, re-pointed `Modularity.lean:10` to `LatticeMonotonicity`
   (`PropositionalStrengthMonotonicity` on line 11 untouched), and regenerated the barrel.

4. **Phase 4 (Full CI gate)**: Ran the complete CSLib CI pipeline -- all green, zero `sorry`.

**Net effect**: `InterSystem/` file count reduced from 14 to 10 (the 8 subsumption/monotonicity
files -> 4: `LatticeSubsumption`, `PropositionalStrengthSubsumption`, `LatticeMonotonicity`,
`PropositionalStrengthMonotonicity`). All 17 subsumption lemma names and all 27
monotonicity theorem/lemma names preserved verbatim. Zero home-file (axiom-inductive) changes.

## Files Changed

**Created**:
- `Cslib/Logics/Modal/Metalogic/InterSystem/LatticeSubsumption.lean`
- `Cslib/Logics/Modal/Metalogic/InterSystem/LatticeMonotonicity.lean`

**Deleted**:
- `Cslib/Logics/Modal/Metalogic/InterSystem/ConstructiveLatticeSubsumption.lean`
- `Cslib/Logics/Modal/Metalogic/InterSystem/MinimalLatticeSubsumption.lean`
- `Cslib/Logics/Modal/Metalogic/InterSystem/IntuitionisticLatticeSubsumption.lean`
- `Cslib/Logics/Modal/Metalogic/InterSystem/ConstructiveLatticeMonotonicity.lean`
- `Cslib/Logics/Modal/Metalogic/InterSystem/MinimalLatticeMonotonicity.lean`
- `Cslib/Logics/Modal/Metalogic/InterSystem/IntuitionisticLatticeMonotonicity.lean`

**Modified**:
- `Cslib/Logics/Modal/Metalogic/InterSystem/PropositionalStrengthSubsumption.lean` (8 lemmas
  shortened in place to `by cases h <;> constructor`; file/name/docstring preserved)
- `Cslib/Logics/Modal/Metalogic/InterSystem/Modularity.lean` (import re-point, line 10)
- `Cslib.lean` (barrel regenerated via `lake exe mk_all --module`, twice)

## Verification

All 8 CSLib CI pipeline steps passed:

| Step | Result |
|------|--------|
| `lake build` (full) | 3252/3252 jobs, `Built Cslib` |
| `lake exe checkInitImports` | pass (no output) |
| `lake lint` | "Linting passed for Cslib." -- zero warnings |
| `lake exe lint-style` | pass (no output) |
| `lake test` | 9245/9245 jobs green |
| `lake shake --add-public --keep-implied --keep-prefix` | none of the 4 touched files flagged |
| `lean_verify` (3 representative theorems across the 3 merged/edited files) | `axioms: []`, `warnings: []` each |
| `lake exe mk_all --module` | barrel diff limited to the intended InterSystem entries |

- `sorry_count` in touched files: 0
- `vacuous_count` introduced: 0
- New `axiom` count: 0
- Repo-wide baselines (145 pre-existing `sorry`, 1 pre-existing vacuous `def`, 27 pre-existing
  `axiom` declarations) are unchanged and lie entirely in files this task never touched
  (Tableau/Computability modules).

## Plan Deviations

None. All four phases were executed exactly as specified in the plan, including the Phase 1
tactic-verification gate before any file was rewritten. One methodological addition not spelled
out in the plan: `lean_multi_attempt`'s single-line substitution left the subsequent `match`-arm
lines as dangling top-level tokens (a parser artifact, not a tactic failure), so Phase 1
verification used temporary scratch lemmas (fully reverted via `git diff --stat` = empty before
proceeding) checked with `lean_goal`/`lake build` instead. This is a verification-technique
detail, not a deviation from the plan's task sequence or scope.

One incidental hazard encountered and handled: `Cslib.lean` is a large, frequently-regenerated
barrel file, and concurrent orchestrated tasks running in parallel in this repository also
touch it (via their own `lake exe mk_all --module` runs). Several times, this task's targeted
edit to `Cslib.lean` (removing a `FragmentConservativity` import line unrelated to this task's
scope, or the InterSystem removals themselves) was overwritten by a concurrent write before it
could be committed. Each time, the fix was reapplied and the diff re-verified with
`git diff Cslib.lean | grep "^+public\|^-public"` to confirm it contained *only* the 4
InterSystem-related import lines, then staged and committed immediately to minimize the race
window. No unrelated barrel changes were included in any of this task's commits.

## Follow-Up / Future Work (Out of Scope, Per Plan)

- **R2 full SchemaUnion migration**: redefining the 12 non-classical `<Sys>ModalAxiom` inductives
  as `SchemaUnion`/`NCSchemaUnion` abbrevs and rewriting ~370 home-file match arms. Requires its
  own multi-phase plan and a design decision on the non-classical tag alphabet.
- Merging the parallel Lindenbaum/prime-theory completeness scaffolding between the
  Intuitionistic and Minimal tracks -- not a byproduct of this consolidation.
