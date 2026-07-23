# Implementation Summary: Consolidate Modal Truth Lemma to a Single Generic Route

- **Task**: 539 - consolidate_modal_truth_lemma_single_generic_route
- **Status**: [COMPLETED]
- **Started**: 2026-07-23T18:54:00Z
- **Completed**: 2026-07-23T19:28:00Z
- **Artifacts**: plans/01_consolidate-truth-lemma.md

## Overview

The classical modal `Systems/` subtree previously proved the canonical-model truth lemma three
times (`truth_lemma` requiring axiom T, `k_truth_lemma` for K-family systems, `d_truth_lemma` for
D-family systems), even though the box case genuinely needs only `EFQ + K` from `kCore` and never
axiom T or D. This task promoted `k_truth_lemma` into `Metalogic/Completeness.lean` as the single
generic `truth_lemma` route for all 15 classical systems, deleted the two redundant families and
their dead support code, repointed all 15 `*_truth_lemma_applied`, and deduped the 432 copy-pasted
`by decide` schema-witness invocations down to 141 via a generic per-core-tag witness API.

## What Changed

- **Promoted and renamed**: `k_truth_lemma`'s body (and its dependencies
  `k_derive_box_from_inconsistency`, `k_mcs_box_witness`) moved from
  `Systems/K/Completeness.lean` into `Metalogic/Completeness.lean`, renamed to `truth_lemma` --
  reusing the name vacated by the deleted T-requiring family, **not** `canonical_truth_lemma`
  (already taken by the intuitionistic truth lemma in the same namespace).
- **Deleted dead code**: the old T-requiring `truth_lemma`, `mcs_box_witness` and the T-route
  `derive_box_from_inconsistency` (both in `MCS.lean`), and the entire D-route block
  (`d_derive_box_from_inconsistency`, `d_mcs_box_witness`, `d_truth_lemma` in
  `Systems/D/Completeness.lean`). `mcs_box_closure` was retained untouched -- it does not depend
  on the deleted symbols and is still used by `canonical_refl`.
- **Relocated `d_canonical_serial`** (a genuine frame property, not a truth-lemma duplicate) from
  `Systems/D/Completeness.lean` into `Metalogic/Completeness.lean` so it survives the D-file
  shrink and remains available to all 5 D-family `d_canonical_FC` consumers.
- **Added 13 `holds*` witness helpers** (`holdsImplyK`, `holdsImplyS`, `holdsEfq`, `holdsPeirce`,
  `holdsModalK`, `holdsAndI`, `holdsAndE1`, `holdsAndE2`, `holdsOrI1`, `holdsOrI2`, `holdsOrE`,
  `holdsDiaDualityFwd`, `holdsDiaDualityBack`) in `ProofSystem/SchemaTags.lean`, built on
  `SchemaUnion.subsumption`, plus the `canonicalTruthLemmaOfKCore {S} (h : kCore ⊆ S) (w) (φ)`
  convenience wrapper in `Metalogic/Completeness.lean`.
- **Repointed all 15 systems'** `*_truth_lemma_applied` (K, B, K4, K5, K45, KB5, T, S4, S5, TB, D,
  D4, D5, D45, DB) to `canonicalTruthLemmaOfKCore (by decide) S φ`, dropping the T-family's
  `h_T` witness and the D-family's `h_D` witness entirely.
- **Deduped strong-completeness/compactness call sites**: each of the 15 systems gained a private
  `coreSubset : kCore ⊆ <sysTags> := by decide` fact, feeding the `holds*` helpers into every
  `*_strong_completeness`/`*_compactness` call site instead of repeating the 4 `implyK/implyS/
  efq/peirce` witnesses by hand. `by decide` count in `Systems/*/Completeness.lean` dropped from
  432 to 141 (67% reduction).
- **Dropped now-redundant imports**: `Systems.K.Completeness` from B/K4/K5/K45/KB5, and
  `Systems.D.Completeness` from D4/D5/D45/DB.
- **Rewrote the stale "three truth lemma families" module docstring** in
  `Metalogic/Completeness.lean` to describe the single generic route and the name-collision
  rationale.

## Decisions

- **K's `k_truth_lemma_applied` repoint was folded into the Phase 1 pass** rather than staged as
  an interim call to the newly-renamed `truth_lemma`: once the promoted symbols were removed from
  `Systems/K/Completeness.lean`, its own `k_truth_lemma_applied` had to be fixed in the same edit
  to keep the file green, and the wrapper (`canonicalTruthLemmaOfKCore`, nominally Phase 3/4) was
  built immediately after so this could resolve directly -- Phases 1-4 for the K file were
  therefore implemented together and verified in one green checkpoint.
- **Witness helper names use no `_of` suffix** (`holdsImplyK` etc., not `implyK_of`): the
  `defsWithUnderscore` linter flags underscores in declaration names, so the plan's own suggested
  fallback (lowerCamelCase, e.g. `holdsImplyK`) was used from the start rather than trying the
  `_of` form first.
- **Per-file `private theorem coreSubset : kCore ⊆ <sysTags> := by decide`** (rather than an
  inline `(by decide : kCore ⊆ S)` at each call site) shares one fact across all of that file's
  `*_strong_completeness`/`*_compactness` sites -- same effect as the plan's literal wording, less
  repetition.
- **`mcs_box_closure` required no inlining**: it is a direct one-line `mcs_mp_axiom` proof using
  `h_T`, independent of the deleted `mcs_box_witness`/`derive_box_from_inconsistency` machinery,
  so the plan's soft blocker resolved to "retain as-is."

## Impacts

- **Zero semantic change**: no new mathematical content, no new axioms (`lean_verify` on
  `truth_lemma` and `canonicalTruthLemmaOfKCore` reports only `propext`, `Classical.choice`,
  `Quot.sound`), no proof gaps. All 15 systems' `*_strong_completeness`/`*_compactness`/
  `*_completeness`/`*_completeness_iff` statements are unchanged.
- **Zero sorry** in the classical `Systems/` subtree (confirmed by grep audit).
- Full CSLib CI pipeline green: `lake build` (3254 jobs), `checkInitImports`, `lake lint`
  ("Linting passed for Cslib"), `lint-style`, `lake shake` (no findings on any touched file),
  `mk_all --module` (no update necessary), `lake test`.
- No change to the intuitionistic/constructive subtrees or their separate `canonical_truth_lemma`
  / `ck_truth_lemma`.

## Follow-ups

- None required. The plan's own noted out-of-scope item (parametric
  `strong_completeness`/`compactness`/`weak_completeness` taking `(h : kCore ⊆ S)` internally)
  remains explicitly deferred, as it was flagged only as an optional future trade-off.

## References

- `specs/539_consolidate_modal_truth_lemma_single_generic_route/plans/01_consolidate-truth-lemma.md`
- `specs/539_consolidate_modal_truth_lemma_single_generic_route/reports/01_truth-lemma-consolidation.md`
- Modified: `Cslib/Logics/Modal/Metalogic/Completeness.lean`
- Modified: `Cslib/Logics/Modal/Metalogic/MCS.lean`
- Modified: `Cslib/Logics/Modal/ProofSystem/SchemaTags.lean`
- Modified: all 15 `Cslib/Logics/Modal/Metalogic/Systems/*/Completeness.lean`
