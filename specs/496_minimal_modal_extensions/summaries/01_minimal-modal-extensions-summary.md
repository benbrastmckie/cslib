# Implementation Summary: Task #496 — Minimal Modal Extensions MT / MS4 / MS5

- **Task**: 496 - Minimal modal extensions MT / MS4 / MS5 (minimal-base analogues of T/S4/S5 as
  modular extensions of MK)
- **Status**: [COMPLETED] — all 5 phases green
- **Plan**: `specs/496_minimal_modal_extensions/plans/01_minimal-modal-extensions.md`
- **Session**: sess_1784044271_09e821_496

## Outcome

All 5 phases completed and committed with per-phase green CI checkpoints:

| Phase | File | Status |
|-------|------|--------|
| 1 | `Cslib/Logics/Modal/Metalogic/Minimal/MinExtension.lean` | COMPLETED |
| 2 | `Cslib/Logics/Modal/Metalogic/Minimal/MT.lean` | COMPLETED |
| 3 | `Cslib/Logics/Modal/Metalogic/Minimal/MS4.lean` | COMPLETED |
| 4 | `Cslib/Logics/Modal/Metalogic/Minimal/MS5.lean` | COMPLETED |
| 5 | Barrel wiring (`Cslib.lean`) + full CI | COMPLETED |

Zero `sorry`, zero new axioms (only `propext`/`Classical.choice`/`Quot.sound`, matching MK's own
`mk_completeness` footprint via the same Zorn's-lemma/`noncomputable` technique), zero vacuous
placeholders, across all four new files.

## Plan Deviations

**Phase 1 scope was substantially larger than planned** (the single material deviation). The
plan's Phase 1 text (`MinExtension.lean scaffold`) estimated ~120-160 lines, assuming task 495's
MK canonical-model machinery (`MinCanonicalPrimeWorld`, `minCanonicalR`, `min_canonical_f1`/`f2`,
`min_canonical_truth_lemma`, `min_head_realization` in `MinCanonicalModel.lean`/
`MinTruthLemma.lean`/`MinCompleteness.lean`) could be reused directly, mirroring how IK's
`Extension.lean` (task 494) reused IK's already-`Axioms`-generic base canonical model
(`Intuitionistic/CanonicalModel.lean`, built generically from task 480/492 onward).

During implementation this premise proved false: unlike IK's base files, MK's task-495 canonical
model files are hard-coded to `MKModalAxiom` throughout (every axiom-instance site writes
`MKModalAxiom.foo args` directly rather than threading a hypothesis). Since `mkvalidFC_completeness`
must produce `Derivable Axioms φ` for `Axioms := MTModalAxiom` / `MS4ModalAxiom` / `MS5ModalAxiom`
in Phases 2-4, reusing MK's `MKModalAxiom`-fixed worlds verbatim was structurally impossible.

The actual necessary Phase 1 work was to *genericize* task 495's ~1090-line efq-free "nonempty
Lindenbaum-pair" canonical-model construction over an abstract `Axioms : Proposition Atom → Prop`,
threading the 12 MK-core axiom-schema witnesses (`h_implyK, h_implyS, h_andI, h_andE1, h_andE2,
h_orI1, h_orI2, h_orE, h_k, h_kdia, h_cd, h_idb`) explicitly through every canonical-model theorem
— exactly mirroring IK's own established `canonical_f1`/`canonical_box_witness` convention
(`Intuitionistic/CanonicalModel.lean:636,1140`, confirmed by direct inspection to already use this
exact full-explicit-hypothesis-list pattern). This is a like-for-like repeat, at MK's scale, of
genericization work IK's *base* task already performed — it was not optional, since Phases 2-4
structurally require it.

Result: `MinExtension.lean` is ~1580 lines (not ~150). All declarations live under a nested
`Cslib.Logic.Modal.MinExt` namespace to avoid colliding with task 495's `MKModalAxiom`-specific
declarations of the same short name in the same outer namespace (`MinCanonicalPrimeWorld`,
`minCanonicalR`, `min_canonical_f1`, etc. all already public in `Cslib.Logic.Modal`); the four
names the plan specifies unqualified in `Cslib.Logic.Modal` (`MValidFC`, `mkvalidFC_completeness`,
`min_axiom_mem`, `min_imp_property`) are defined at the outer level, referencing `MinExt.*`
internally. Phases 2-4 (MT/MS4/MS5) then proceeded almost exactly as planned — each compiled on
essentially the first attempt (MT: first try; MS4: first try; MS5: one line-length fix only),
confirming the plan's prediction that once the generic scaffold exists, the per-system files are
"straightforward modular extension[s]" mirroring the delivered IK-extension pattern.

No other deviations. All Zero-Debt STOP clauses (Phase 3 transitivity, Phase 4 MS5 symmetry)
closed sorry-free on the first attempt via verbatim ports of `is4_canonical_transitive`
(`Intuitionistic/IS4.lean:291`) and `is5_canonical_symmetric` (`Intuitionistic/IS5.lean:341`)
respectively, matching the plan's HIGH-confidence prediction for Phase 4 and LOW-MODERATE-risk
assessment for Phase 3 — neither BLOCKED, no escalation needed.

**Phase 5 minor fix**: `MinExtension.lean`'s import was corrected mid-verification from
`Minimal.MinCompleteness` (an unnecessarily heavy, MK-specific transitive import providing nothing
actually used beyond docstring references) to the direct `Semantics.Birelational` +
`Constructive.SegmentLindenbaum` it actually needs — caught by `lake shake` scoped analysis, fixed
before final commit.

## Deliverables

- `Cslib/Logics/Modal/Metalogic/Minimal/MinExtension.lean` (new, ~1580 lines): `MValidFC`,
  `mvalid_iff_mvalidFC_true`, `MinExt.{MinCanonicalPrimeWorld, minCanonicalR, minCanonicalVal,
  minBotForces, min_head_realization, min_canonical_f1, min_canonical_f2,
  min_canonical_truth_lemma}` (all `Axioms`-generic), `min_axiom_mem`, `min_imp_property`,
  `mkvalidFC_completeness`.
- `Cslib/Logics/Modal/Metalogic/Minimal/MT.lean` (new): `MTModalAxiom`, `mtFC`, `mt_axiom_sound`,
  `mt_soundness`, `mt_soundness_derivable`, `min_canonical_reflexive_mt`, `mt_completeness`,
  `mt_consistent`, `mt_soundness_completeness`.
- `Cslib/Logics/Modal/Metalogic/Minimal/MS4.lean` (new): `MS4ModalAxiom`, `ms4FC`,
  `ms4_axiom_sound`, `ms4_soundness`, `ms4_soundness_derivable`, `min_canonical_reflexive_ms4`,
  `min_canonical_transitive_ms4`, `min_canonical_ms4FC`, `ms4_completeness`, `ms4_consistent`,
  `ms4_soundness_completeness`.
- `Cslib/Logics/Modal/Metalogic/Minimal/MS5.lean` (new): `MS5ModalAxiom`, `ms5FC`,
  `ms5_axiom_sound`, `ms5_soundness`, `ms5_soundness_derivable`, `min_canonical_reflexive_ms5`,
  `min_canonical_transitive_ms5`, `min_canonical_symmetric_ms5`, `min_canonical_ms5FC`,
  `ms5_completeness`, `ms5_consistent`, `ms5_soundness_completeness`.
- `Cslib.lean` — barrel updated (4 new `public import` lines, alphabetically ordered by
  `lake exe mk_all --module`).

## Verification

- `lake build` (full library, 3221 jobs): green.
- `lake exe checkInitImports`: clean (all files import `Cslib.Init`).
- `lake lint`: zero findings in the 4 new files (only 1 pre-existing, unrelated error in
  `Foundations/Logic/Metalogic/PrimeExclusion.lean`).
- `lake exe lint-style`: clean.
- `lake shake --add-public --keep-implied --keep-prefix`: no findings beyond the pre-existing,
  repo-wide `remove import Cslib.Init` false positive (also flagged on task-495's own
  `MinPrimeTheory.lean` and multiple unrelated files across `Propositional/SequentCalculus/{LK,LJ}`
  and `Temporal/Tableau` — `scripts/noshake.json`, the config meant to suppress it, is absent from
  the repository, a pre-existing condition unrelated to task 496).
- `lake test`: exit 0.
- `grep -rn '\bsorry\b'` across the 4 new files: 0 matches.
- `grep -rn '^axiom '` across the 4 new files: 0 matches.
- `lean_verify` on `mkvalidFC_completeness`, `mt_soundness_completeness`,
  `ms4_soundness_completeness`, `ms5_soundness_completeness`: axioms =
  `["propext", "Classical.choice", "Quot.sound"]` (standard, matching MK's own footprint).
- Positive-closure discipline confirmed: `min_canonical_reflexive_{mt,ms4,ms5}`,
  `min_canonical_transitive_{ms4,ms5}`, `min_canonical_symmetric_ms5` contain no `by_contra`, no
  negation, no consistency appeal — pure `min_axiom_mem`/`min_imp_property` (MP-closure) chaining.

## Concurrency Note

Confined all edits to `Cslib/Logics/Modal/Metalogic/Minimal/` plus `Cslib.lean` (barrel, via
`lake exe mk_all --module` only, never hand-edited). Mid-Phase-5, an unrelated concurrent session
(task 507, `Cslib/Logics/Modal/Tableau/FmpMeasure.lean`) transiently broke the full-project build;
this resolved itself once that session's edit stabilized and was confirmed unrelated to any
task-496 file via `git diff --stat` polling before re-running the full CI pipeline.
