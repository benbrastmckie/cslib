# Implementation Plan: Consolidate Modal Truth Lemma to a Single Generic Route

- **Task**: 539 - consolidate_modal_truth_lemma_single_generic_route
- **Status**: [COMPLETED]
- **Effort**: 11 hours
- **Dependencies**: None
- **Research Inputs**: specs/539_consolidate_modal_truth_lemma_single_generic_route/reports/01_truth-lemma-consolidation.md
- **Artifacts**: plans/01_consolidate-truth-lemma.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/plan-format-enforcement.md
  - .claude/rules/state-management.md
- **Type**: cslib

## Overview

The canonical-model truth lemma is currently proved three times across the classical modal
`Systems/` subtree: `k_truth_lemma` (fully generic, box case needs only EFQ+K from kCore),
`truth_lemma` (demands a semantically unnecessary `h_T`), and `d_truth_lemma` (demands an
unnecessary `h_D`). Because every one of the 15 axiom predicates is `SchemaUnion sysTags` with
`kCore ⊆ sysTags`, all 15 systems can be served by the generic route. This plan promotes
`k_truth_lemma` into `Metalogic/Completeness.lean` as THE truth lemma, relocates its shared
machinery out of the K/D leaf files, deletes the two redundant families plus their support code
(~545 duplicated lines), repoints all 15 `*_truth_lemma_applied`, and dedupes the 432 copy-pasted
`by decide` schema-witness invocations via a single generic core-witness helper. **Definition of
done:** the classical `Systems/` subtree remains sorry-free and compile-green (`lake build`
passes, `lake lint` clean), with zero semantic change.

### Research Integration

The plan integrates the verified 8-phase decomposition from
`reports/01_truth-lemma-consolidation.md`, including its per-symbol file/line anchors and its two
critical blockers that override the literal task instructions:

1. **Name collision (hard blocker).** `canonical_truth_lemma` is already taken by the
   intuitionistic truth lemma at `Metalogic/Intuitionistic/TruthLemma.lean:465` in the same
   namespace `Cslib.Logic.Modal`, and both files are imported by the `Cslib.lean` barrel.
   Renaming the promoted lemma to `canonical_truth_lemma` would be a duplicate declaration. The
   promoted lemma **reuses the vacated name `truth_lemma`** instead.

2. **`mcs_box_closure` is NOT dead (soft blocker).** The task lists it for deletion, but after
   removing `mcs_box_witness` it is still used by `canonical_refl`
   (`Metalogic/Completeness.lean:81`). It is **retained** (or inlined-then-deleted); it must not
   be blind-deleted.

The research also flagged an unnamed deletion target the task omitted: the T-route
`derive_box_from_inconsistency` (`MCS.lean:382-446`), dead once `mcs_box_witness` is removed —
included below.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (roadmap flag not set).

## Goals & Non-Goals

**Goals**:
- Promote `k_truth_lemma` into `Metalogic/Completeness.lean`, renamed to `truth_lemma`, as the
  single generic truth-lemma route for all 15 classical systems.
- Relocate shared machinery (`k_derive_box_from_inconsistency`, `k_mcs_box_witness`,
  `d_canonical_serial`) out of the K/D leaf files into `Metalogic/Completeness.lean`.
- Delete the genuinely-dead redundant code: old T-requiring `truth_lemma`, `mcs_box_witness`,
  T-route `derive_box_from_inconsistency`, `d_derive_box_from_inconsistency`, `d_mcs_box_witness`,
  `d_truth_lemma`.
- Repoint all 15 `*_truth_lemma_applied` at the promoted lemma via a convenience wrapper.
- Dedupe the 432 `by decide` schema-witness invocations via generic per-core-tag `_of` helpers
  discharged from one `kCore ⊆ sysTags` subset fact each.
- Preserve the sorry-free, compile-green state throughout (zero semantic change).

**Non-Goals**:
- No change to the intuitionistic/constructive subtrees or their separate `canonical_truth_lemma`
  / `ck_truth_lemma`.
- No new mathematical content, no new axioms, no proof gaps.
- No aggressive refactor of the parametric `strong_completeness`/`compactness`/`weak_completeness`
  layer to accept `(h : kCore ⊆ S)` internally (flagged as an optional trade-off in research,
  explicitly out of scope here to preserve zero-semantic-change).
- Do NOT delete `mcs_box_closure` without first satisfying its `canonical_refl` dependency.
- Do NOT use the name `canonical_truth_lemma` for the promoted lemma.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Renaming promoted lemma to `canonical_truth_lemma` causes duplicate-declaration compile error | H | M | Reuse vacated name `truth_lemma` (Phase 1); never introduce `canonical_truth_lemma` in the classical subtree |
| Deleting `mcs_box_closure` breaks `canonical_refl` (T/S4/S5/TB depend on it) | H | M | Retain `mcs_box_closure`, or inline its one line into `canonical_refl` then delete; verify `canonical_refl` still builds (Phase 1) |
| Import cycle when helpers reference `kCore`/`SchemaUnion` from `Metalogic/Completeness.lean` | M | M | Place `_of` helpers in `ProofSystem/SchemaTags.lean` (imports only `SchemaUnion.lean`); confirm acyclicity with scoped `lake build` before proceeding (Phase 3) |
| Relocated `d_canonical_serial` stops resolving for the 5 D-family `d_canonical_FC` | M | L | D-family leaves all import `Metalogic.Completeness`; relocation is transparent — verify each D leaf builds (Phase 5) |
| A repoint silently changes semantics (wrong witness dropped) | H | L | Phase-scoped `lake build` per leaf after repointing; final `lean_verify` sorry/axiom audit on promoted `truth_lemma` (Phase 8) |
| Dropping redundant `Systems.K.Completeness` imports breaks a transitive dependency | M | L | Drop imports only after promotion; rebuild each affected leaf immediately (Phases 4-6) |
| Linter rejects `_of` helper naming (`defsWithUnderscore` mixed style) | L | M | Prefer lowerCamelCase names (e.g. `holdsImplyK`) if `lake lint` objects; check against lint-prevention rules (Phase 3/8) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4, 5, 6 | 3 |
| 5 | 7 | 4, 5, 6 |
| 6 | 8 | 7 |

Phases within the same wave can execute in parallel. Phases 4, 5, and 6 touch disjoint
`Systems/*/Completeness.lean` files and are parallel-safe; Phases 1-3 all edit
`Metalogic/Completeness.lean` (and MCS/SchemaTags) and are sequential to avoid write conflicts.

### Phase 1: Promote and Rename the Generic Truth Lemma [COMPLETED]

**Goal**: Move the generic K-route machinery into `Metalogic/Completeness.lean`, rename the
promoted lemma to `truth_lemma`, delete the old T-requiring family, and resolve the
`mcs_box_closure` blocker — leaving Metalogic building green.

**Tasks**:
- [x] Move `k_derive_box_from_inconsistency` (`Systems/K/Completeness.lean:51-119`) into
  `Metalogic/Completeness.lean` (private acceptable). *(deviation: kept public, matching its
  original visibility -- no consumer outside the file needed it private, and the plan marked
  private as merely "acceptable" not mandatory)*
- [x] Move `k_mcs_box_witness` (`Systems/K/Completeness.lean:127-155`) into
  `Metalogic/Completeness.lean`.
- [x] Move the body of `k_truth_lemma` (`Systems/K/Completeness.lean:163-331`) into
  `Metalogic/Completeness.lean`, **renamed to `truth_lemma`** (reuse the vacated name; do NOT use
  `canonical_truth_lemma`).
- [x] Delete the old T-requiring `truth_lemma` (`Metalogic/Completeness.lean:262-444`).
- [x] Resolve the `mcs_box_closure` blocker: RETAIN `mcs_box_closure` (`MCS.lean:139-148`) --
  confirmed it does not depend on `mcs_box_witness`/`derive_box_from_inconsistency` (it is a
  direct one-line `mcs_mp_axiom` proof using `h_T`), so no inlining was needed; left untouched.
  `canonical_refl` still builds.
- [x] Delete `mcs_box_witness` (`MCS.lean:452-482`).
- [x] Delete the T-route `derive_box_from_inconsistency` (`MCS.lean:382-446`) — dead once
  `mcs_box_witness` is gone (task did not name this explicitly; include it).
- [x] Verify no other consumer of the deleted symbols remains (grep for each deleted name).
  *(deviation: `k_truth_lemma_applied` in `Systems/K/Completeness.lean` was repointed directly to
  the Phase 3/4 wrapper `canonicalTruthLemmaOfKCore` in this same pass, rather than as an interim
  step calling `truth_lemma` with the full 13-witness list -- both the promotion and K's own
  Phase 4 repoint were implemented together since K's file cannot type-check with the promoted
  symbols removed until the wrapper exists; verified green only once Phases 1-3 landed together)*

**Timing**: ~2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/K/Completeness.lean` — remove promoted symbols
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` — add promoted symbols; delete old `truth_lemma`; possibly edit `canonical_refl`
- `Cslib/Logics/Modal/Metalogic/MCS.lean` — delete `mcs_box_witness` and T-route `derive_box_from_inconsistency`; retain `mcs_box_closure`

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Completeness` succeeds
- `lake build Cslib.Logics.Modal.Metalogic.MCS` succeeds
- No unresolved references to `mcs_box_witness`, T-route `derive_box_from_inconsistency`, or the
  old `truth_lemma`
- `canonical_refl` still builds (reflexivity property intact)

---

### Phase 2: Relocate Seriality [COMPLETED]

**Goal**: Move `d_canonical_serial` (a genuine frame property, NOT a truth-lemma duplicate) into
`Metalogic/Completeness.lean` so it survives the D-file shrink and remains available to all 5
D-family `d_canonical_FC` consumers.

**Tasks**:
- [x] Move `d_canonical_serial` (`Systems/D/Completeness.lean:189-231`) into
  `Metalogic/Completeness.lean`.
- [x] Confirm all D-family consumers (D, D4, D5, D45, DB `*_canonical_FC`) resolve it transparently
  via their existing `import Metalogic.Completeness`. (verified via scoped build in Phase 5,
  since D4/D5/D45/DB's `*_canonical_FC` bodies are unchanged and untouched by this move)

**Timing**: ~0.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/D/Completeness.lean` — remove `d_canonical_serial`
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` — add `d_canonical_serial`

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Completeness` succeeds
- `d_canonical_serial` resolves from Metalogic (spot-check one D-family leaf builds)

---

### Phase 3: Add Witness Helpers and Convenience Wrapper [COMPLETED]

**Goal**: Introduce the thin per-core-tag `SchemaUnion.*_of` witness helpers (13 one-liners) and
one `canonicalTruthLemma_of_kCore` convenience wrapper, so each leaf's 13-witness block can later
collapse to a single subset fact. Confirm no import cycle.

**Tasks**:
- [x] Add the 13 per-core-tag `_of` helpers (for `implyK, implyS, efq, peirce, modalK, andI,
  andE1, andE2, orI1, orI2, orE, diaDualityFwd, diaDualityBack`) built on
  `SchemaUnion.subsumption` (`SchemaUnion.lean:155`) — place in `ProofSystem/SchemaTags.lean`
  (imports only `SchemaUnion.lean`, keeping the graph acyclic). *(deviation: named `holdsImplyK`,
  `holdsImplyS`, etc. from the start, not `implyK_of` -- `defsWithUnderscore` flags underscores
  in declaration names, so the `_of` suffix was never viable; went straight to the
  plan's own fallback naming)*
- [x] Add `canonicalTruthLemma_of_kCore {S} (h : kCore ⊆ S) (w) (φ)` in `Metalogic/Completeness.lean`
  that feeds the `_of` helpers into the promoted `truth_lemma`; add `import SchemaTags` to
  `Metalogic/Completeness.lean` if needed. *(deviation: named `canonicalTruthLemmaOfKCore`,
  camelCase, for the same `defsWithUnderscore` reason as above)*
- [x] Confirm helper naming passes the linter; if `defsWithUnderscore` objects to mixed style,
  rename `_of` helpers to lowerCamelCase (e.g. `holdsImplyK`). Used `holdsImplyK` etc. verbatim.
- [x] Verify import acyclicity with a scoped `lake build`. No cycle: `SchemaTags.lean` was
  already in `Metalogic/Completeness.lean`'s transitive closure via
  `MCS -> ... -> DerivationTree -> SchemaTags`; the explicit `public import` is now direct.

**Timing**: ~1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/ProofSystem/SchemaTags.lean` — add 13 `_of` witness helpers
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` — add `canonicalTruthLemma_of_kCore` wrapper; add `import SchemaTags` if required

**Verification**:
- `lake build Cslib.Logics.Modal.ProofSystem.SchemaTags` succeeds
- `lake build Cslib.Logics.Modal.Metalogic.Completeness` succeeds (no import cycle)
- `lake lint` clean on new declarations (docBlame, defsWithUnderscore)

---

### Phase 4: Repoint K-Family [COMPLETED]

**Goal**: Repoint the 6 K-family systems (K, B, K4, K5, K45, KB5) `*_truth_lemma_applied` at the
convenience wrapper, shrink K to the ~180-line sibling shape, and drop now-redundant imports.

**Tasks**:
- [x] Repoint each `*_truth_lemma_applied` for K, B, K4, K5, K45, KB5 to
  `canonicalTruthLemmaOfKCore (by decide) S φ` (13 witnesses -> 1 subset fact).
- [x] Shrink `Systems/K/Completeness.lean` to the sibling instance shape (its promoted machinery
  now lives in Metalogic). (done in the Phase 1 combined pass; K/Completeness.lean is now
  ~185 lines, matching the B/K4/K5 sibling shape)
- [x] Drop redundant `public import ...Systems.K.Completeness` where a leaf imported it only for
  `k_truth_lemma` (e.g. B, `line 11`), since the promoted `truth_lemma` lives in
  `Metalogic.Completeness`. Dropped from B, K4, K5, K45, KB5.
- [x] Build each of the 6 leaves.

**Timing**: ~1.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/K/Completeness.lean`
- `Cslib/Logics/Modal/Metalogic/Systems/B/Completeness.lean`
- `Cslib/Logics/Modal/Metalogic/Systems/K4/Completeness.lean`
- `Cslib/Logics/Modal/Metalogic/Systems/K5/Completeness.lean`
- `Cslib/Logics/Modal/Metalogic/Systems/K45/Completeness.lean`
- `Cslib/Logics/Modal/Metalogic/Systems/KB5/Completeness.lean`

**Verification**:
- `lake build` succeeds for each of the 6 K-family `Completeness.lean` files
- Each `*_truth_lemma_applied` resolves through the wrapper

---

### Phase 5: Repoint and Shrink D-Family [COMPLETED]

**Goal**: Delete the duplicated D-route box block, repoint the 5 D-family systems (D, D4, D5, D45,
DB) at the wrapper, and use the relocated `d_canonical_serial`.

**Tasks**:
- [x] Delete `d_derive_box_from_inconsistency` (`Systems/D/Completeness.lean:57-138`).
- [x] Delete `d_mcs_box_witness` (`Systems/D/Completeness.lean:146-177`).
- [x] Delete `d_truth_lemma` (`Systems/D/Completeness.lean:241-412`).
- [x] Repoint each `*_truth_lemma_applied` for D, D4, D5, D45, DB to
  `canonicalTruthLemmaOfKCore (by decide) S φ` (drops the extra `h_D` witness).
- [x] Confirm each D-family `d_canonical_FC` uses the relocated `d_canonical_serial` from Metalogic.
  (their bodies were unchanged, and all 5 build green pulling `d_canonical_serial` transitively
  through `import Metalogic.Completeness`)
- [x] Drop redundant imports if any D leaf imported `Systems.D.Completeness` only for the deleted
  block. Dropped from D4, D5, D45, DB (all four only used `d_canonical_serial`/`d_truth_lemma`,
  both now gone/relocated).
- [x] Build each of the 5 leaves.

**Timing**: ~1.5 hours

**Depends on**: 2, 3

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/D/Completeness.lean`
- `Cslib/Logics/Modal/Metalogic/Systems/D4/Completeness.lean`
- `Cslib/Logics/Modal/Metalogic/Systems/D5/Completeness.lean`
- `Cslib/Logics/Modal/Metalogic/Systems/D45/Completeness.lean`
- `Cslib/Logics/Modal/Metalogic/Systems/DB/Completeness.lean`

**Verification**:
- `lake build` succeeds for each of the 5 D-family `Completeness.lean` files
- No unresolved references to the deleted D-route symbols
- `d_canonical_serial` resolves from Metalogic for all 5

---

### Phase 6: Repoint T-Family [COMPLETED]

**Goal**: Repoint the 4 T-family systems (T, S4, S5, TB) at the wrapper, dropping the now-unused
`h_T` witness.

**Tasks**:
- [x] Repoint each `*_truth_lemma_applied` for T, S4, S5, TB to
  `canonicalTruthLemmaOfKCore (by decide) S φ` (drops the extra `h_T` witness). *(note: these
  four files were left calling the old 14-argument `truth_lemma` -- now type-incorrect since the
  promoted `truth_lemma` dropped `h_T` in Phase 1 -- so this repoint was required, not optional,
  to bring the tree back to green; verified via scoped build immediately after)*
- [x] Build each of the 4 leaves.

**Timing**: ~1 hour

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/T/Completeness.lean`
- `Cslib/Logics/Modal/Metalogic/Systems/S4/Completeness.lean`
- `Cslib/Logics/Modal/Metalogic/Systems/S5/Completeness.lean`
- `Cslib/Logics/Modal/Metalogic/Systems/TB/Completeness.lean`

**Verification**:
- `lake build` succeeds for each of the 4 T-family `Completeness.lean` files
- Each `*_truth_lemma_applied` resolves through the wrapper with no `h_T`

---

### Phase 7: Dedupe Strong-Completeness / Compactness Witness Blocks [COMPLETED]

**Goal**: Replace the remaining 4-witness `by decide` blocks inside each `*_strong_completeness`
and `*_compactness` across all 15 systems with the `SchemaUnion.*_of` helpers, sharing one subset
fact per block.

**Tasks**:
- [x] For each of the 15 systems, replace the 4 inline `by decide` witnesses in
  `*_strong_completeness` (needs `implyK/implyS/efq/peirce`, all kCore) with `SchemaUnion.*_of h`
  helper applications sharing one `(by decide : kCore ⊆ S)` fact. *(deviation: named
  `holdsImplyK`/etc. per the Phase 3 naming decision, and used a per-file `private theorem
  coreSubset : kCore ⊆ <sysTags> := by decide` rather than an inline `(by decide : kCore ⊆ S)` at
  each call site -- same effect, one fact shared across all of that file's call sites)*
- [x] Do the same for the 4 witnesses in each `*_compactness`.
- [x] Confirm the `by decide` count drops materially from the baseline 432 (research-confirmed
  count) and record the new count. **New count: 141** (432 -> 141, a 67% reduction). The
  remaining 141 are: (a) the per-system `coreSubset` facts themselves (15, one per file), (b)
  differentiator-tag witnesses inside `canonical_FC` proofs (`modalT`/`modalD`/`modalB`/
  `modalFour`/`modalFive`, which are NOT part of `kCore` and so fall outside this phase's
  `implyK/implyS/efq/peirce` dedup scope by design), and (c) the `canonicalTruthLemmaOfKCore (by
  decide) S φ` call in each `*_truth_lemma_applied` (Phases 4-6, 15 more `by decide` sites, one
  per system, each proving that same file's `kCore ⊆ sysTags` fact -- arguably a 16th
  `coreSubset`-shaped duplicate per file, but left as constructed in Phases 4-6 per the plan's
  literal call shape `canonicalTruthLemmaOfKCore (by decide) S φ`).
- [x] Build each affected leaf.

**Timing**: ~1.5 hours

**Depends on**: 4, 5, 6

**Files to modify**:
- All 15 `Cslib/Logics/Modal/Metalogic/Systems/*/Completeness.lean` (strong_completeness and
  compactness witness blocks only)

**Verification**:
- `lake build` succeeds for all 15 `Systems/*/Completeness.lean` files
- `by decide` count reduced from 432 (record the delta)
- No semantic change (all `*_strong_completeness` / `*_compactness` statements unchanged)

---

### Phase 8: Docstring Fix, Full Build, Lint, and Sorry Audit [COMPLETED]

**Goal**: Rewrite the stale "three truth lemma families" docstring, run the full build and linter,
and confirm the classical subtree is sorry-free and axiom-clean.

**Tasks**:
- [x] Rewrite `Metalogic/Completeness.lean:240-260` to describe the single promoted `truth_lemma`
  and note that the intuitionistic/constructive subtrees keep their separate
  `canonical_truth_lemma` / `ck_truth_lemma` (unrelated).
- [x] Run full `lake build` on the modal metalogic tree. Ran the full project `lake build`
  (3254 jobs) -- all green.
- [x] Run `lake lint` (docBlame, defsWithUnderscore) and resolve any findings on new helpers.
  `lake lint` reports "Linting passed for Cslib" -- zero warnings anywhere, including the new
  `holds*`/`coreSubset`/`canonicalTruthLemmaOfKCore` declarations.
- [x] Run `lean_verify` on the promoted `truth_lemma` to confirm no `sorry` and no unexpected
  axioms. Result: `{"axioms":["propext","Classical.choice","Quot.sound"]}` -- only the standard
  foundational axioms, no `sorryAx`, no new axioms. Also verified
  `canonicalTruthLemmaOfKCore` with the same clean result.
- [x] Grep the classical `Systems/` subtree for `sorry` to confirm zero. Confirmed: `grep -rn
  "\bsorry\b" Cslib/Logics/Modal/Metalogic/Systems/` returns nothing.

**Additional verification beyond the plan's checklist** (full CSLib CI pipeline, all green):
`lake exe cache get` (already warm), `lake exe checkInitImports` (silent success), `lake exe
lint-style` (silent success), `lake shake --add-public --keep-implied --keep-prefix` (reports
pre-existing findings across unrelated parts of the repo -- zero findings for any file this task
touched, confirming the Phase 4/5 import drops left every touched file's imports minimal), `lake
exe mk_all --module` ("No update necessary" -- no new files), `lake test` (full `CslibTests/`
suite green). Also confirmed zero vacuous-definition patterns
(`def X := True`/`trivial`/`Unit`) in every file this task touched.

**Timing**: ~1 hour

**Depends on**: 7

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` — docstring rewrite

**Verification**:
- Full `lake build` passes
- `lake lint` clean
- `lean_verify` on `Cslib.Logic.Modal.truth_lemma` reports no `sorry`, no unexpected axioms
- Zero `sorry` in the classical `Systems/` subtree

---

## Testing & Validation

- [x] `lake build Cslib.Logics.Modal.Metalogic.Completeness` passes after each Metalogic-editing
  phase (1, 2, 3)
- [x] `lake build` passes for each `Systems/*/Completeness.lean` leaf after its repoint (Phases 4-7)
- [x] Full `lake build` of the modal metalogic tree passes (Phase 8) -- full project `lake build`
  (3254 jobs), all green
- [x] `lake lint` clean, including `defsWithUnderscore` / `docBlame` on the new `_of` helpers --
  "Linting passed for Cslib"
- [x] `lean_verify` on the promoted `truth_lemma`: no `sorry`, no unexpected axioms -- confirmed,
  only `propext`/`Classical.choice`/`Quot.sound`
- [x] Zero `sorry` across the classical `Systems/` subtree (grep audit) -- confirmed
- [x] `by decide` count reduced from the research-confirmed baseline of 432 (record final count)
  -- **final count: 141** (67% reduction)

## Artifacts & Outputs

- `specs/539_consolidate_modal_truth_lemma_single_generic_route/plans/01_consolidate-truth-lemma.md` (this plan)
- `specs/539_consolidate_modal_truth_lemma_single_generic_route/summaries/01_consolidate-truth-lemma-summary.md` (on implementation)
- Modified: `Cslib/Logics/Modal/Metalogic/Completeness.lean` (promoted `truth_lemma`, relocated
  `d_canonical_serial`, wrapper, docstring)
- Modified: `Cslib/Logics/Modal/Metalogic/MCS.lean` (deletions; `mcs_box_closure` retained)
- Modified: `Cslib/Logics/Modal/ProofSystem/SchemaTags.lean` (13 `_of` helpers)
- Modified: all 15 `Cslib/Logics/Modal/Metalogic/Systems/*/Completeness.lean`

## Rollback/Contingency

- Each phase ends at a compile-green checkpoint; commit per green phase so any later failure rolls
  back only to the last green phase (never discard uncommitted work — fix forward per
  `error-handling.md`).
- If the import cycle in Phase 3 proves unavoidable from `SchemaTags.lean`, fall back to placing
  the `canonicalTruthLemma_of_kCore` wrapper and `_of` helpers together in
  `Metalogic/Completeness.lean` (accepting a slightly larger Metalogic file) rather than splitting
  across `SchemaTags.lean`.
- If a repoint (Phases 4-6) fails to build for a specific system, the promoted `truth_lemma` and
  wrapper remain intact — only that leaf reverts to its prior in-file witness block until the
  discrepancy (usually a missing kCore tag in that system's `sysTags`, which cannot occur by the
  verified `kCore ⊆ sysTags` fact) is resolved.
- Deletions (old `truth_lemma`, `mcs_box_witness`, D-route block) are the last-touched items in
  their phases; if a hidden consumer surfaces, restore the symbol from git and re-audit before
  re-deleting.
