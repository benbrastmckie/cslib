# Implementation Plan: Retire wrap/unwrap Combinator Bridge Layers

- **Task**: 540 - retire_wrap_unwrap_combinator_bridge_layers
- **Status**: [IMPLEMENTING]
- **Effort**: 8 hours
- **Dependencies**: None (coordinate with tasks 393/41 only if Phase 6 requires editing GenericMCSBridge — see Non-Goals)
- **Research Inputs**: specs/540_retire_wrap_unwrap_combinator_bridge_layers/reports/01_bridge-lemma-elimination.md
- **Artifacts**: plans/01_retire-bridge-layers.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This is a pure consolidation refactor: retire the three local `wrap`/`unwrap` derivability
bridges and the per-target propositional-combinator restatements that sit on top of them, and
fold the drop-eligible PL→X embedding-commutation `rfl` restatements into the existing generic
`embed_*` `@[simp]` lemmas. The reuse-first verdict from research is decisive: **no new bridge
typeclass** is introduced — `wrap`/`unwrap` already duplicate
`InferenceSystem.DerivableIn.fromDerivation`/`.toDerivation`, which already carry bidirectional
`Coe` instances. The only new surface is one thin, once-proved raw-`S⇓·`-typed combinator layer
over `[InferenceSystem S F]`. Definition of done: `wrap`/`unwrap` primitives deleted from all
three helper files, per-target combinator defs repointed to the generic layer, the 9 PL→X
`_atom/_bot/_imp` restatements dropped, and a full `lake build` green with no new `sorry`, axioms,
or lint regressions.

### Research Integration

The plan integrates `reports/01_bridge-lemma-elimination.md` in full, honoring its three scope
corrections:

1. **wrap/unwrap is redundant with the Foundations `InferenceSystem` API** (`InferenceSystem.lean:71-85`).
   The generic combinators already exist once in
   `Foundations/Logic/Theorems/{Combinators,Propositional/Core,Propositional/Connectives}.lean`.
   The one new declaration set is a raw-derivation-typed thin layer (`S⇓φ`, not `DerivableIn S φ`).
2. **The embedding drop set is 9 lemmas, not 34.** Only the PL→{Modal,Temporal,Bimodal}
   `_atom/_bot/_imp` restatements (`toModal`/`toTemporal`/`PL.Proposition.toBimodal`, which literally
   *are* `φ.embed`) are foldable. The Modal→Bimodal (`ModalEmbedding.lean`) and Temporal→Bimodal
   (`TemporalEmbedding.lean`) embeddings are separate structural recursions, **not** `PL.embed`, and
   their restatements are retained entirely. `_and/_or/_neg` also stay per the task.
3. **Modal item 3 collides with the SCOPE GUARD.** Routing Modal `imp_trans0` through the generic
   layer needs the `MinimalHilbert (Modal.HilbertOf Axioms)` instance in the scope-guarded
   `Modal/Metalogic/GenericMCSBridge.lean`. *Using* the existing instance is in scope; *editing* the
   bridge is not. Phase 6 is therefore narrow and optional, and is marked `[BLOCKED]` rather than
   forcing a bridge edit if instance resolution is not available.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this dispatch (roadmap flag not set).

## Goals & Non-Goals

**Goals**:
- Add one thin, once-proved raw-`S⇓·`-typed generic combinator layer over `[InferenceSystem S F]`.
- Delete all three `wrap`/`unwrap` (and `wrap'`/`unwrap'`) primitive pairs.
- Repoint every drop-eligible per-target propositional-combinator def to the generic layer,
  preserving the per-target names (option B1) so downstream call sites stay untouched.
- Drop the 9 PL→X `_atom/_bot/_imp` embedding restatements in favor of generic `embed_*`.
- Keep a green `lake build` and zero-debt (no `sorry`, no new axioms) throughout.

**Non-Goals**:
- No new bridge typeclass, and no change to the generic combinator *statements* in Foundations.
- No renaming or removal of the genuinely tree/context-structural defs (`ecq`, `ldi`, `rdi`,
  `rcp`, `lce`, `rce`, `iffElimLeft/Right`, `boxToFuture/Past/Present`, `tempFutureDerived`) or the
  `{fc}`-lift shims — these stay.
- No folding of `_and/_or/_neg` restatements, and no touching the Modal→Bimodal or Temporal→Bimodal
  embedding files.
- **No edit to `Modal/Metalogic/GenericMCSBridge.lean` or any MCS/deduction-theorem seam** (owned by
  tasks 393 and 41). Phase 6 uses the existing instance read-only or is blocked.
- Option B2 (deleting per-target names and updating all consumers) is out of scope for this plan.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| simp normal-form drift after embedding folding (constructor-form vs typeclass-form) | H | M | Phase 5 validated by full `lake build Cslib.Logics.{Modal,Temporal,Bimodal}`, not assumed benign; revert the `toX_eq_embed` unfolder if drift is unresolved |
| Connectives `wrap'`/`unwrap'` alias Perpetuity's `wrap`/`unwrap`; deleting the latter first leaves the tree red | M | H | Sequence: repoint Core+Connectives and delete `wrap'`/`unwrap'` (Phase 3) **before** deleting Perpetuity's `wrap`/`unwrap` (Phase 4) |
| `{fc}`-polymorphic Bimodal defs (`efqAxiom`, `peirceAxiom`, `doubleNegation`, `lceImp`, `rceImp`) wrap Base result in `DerivationTree.lift`; generic layer produces `.Base` only | M | M | Retain a one-line per-target `.lift` shim; do not assume these collapse to zero lines |
| Phase 6 requires editing scope-guarded GenericMCSBridge | M | M | Use existing `MinimalHilbert (HilbertOf Axioms)` instance read-only; if instance resolution needs a bridge change, mark Phase 6 `[BLOCKED]` and coordinate with tasks 393/41 — never edit the guarded file |
| Hidden by-name consumer of a deleted primitive (e.g. `MCSProperties.lean`) | M | L | Grep each primitive's name across the repo before deletion (research §7 flags `MCSProperties.lean`) |
| New generic defs trip `docBlame` lint | L | M | Give every new generic def a docstring in Phase 1 |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 5 | -- |
| 2 | 2, 3, 6 | 1 |
| 3 | 4 | 1, 3 |
| 4 | 7 | 2, 3, 4, 5, 6 |

Phases within the same wave can execute in parallel. Phase 5 (embedding) is independent of the
combinator layer and may run in Wave 1. Phase 6 is optional/guarded.

### Phase 1: Generic raw-`S⇓·`-typed combinator layer [COMPLETED]

**Goal**: Add the single new surface — thin combinators typed at `S⇓·` over `[InferenceSystem S F]`
(plus the minimal Hilbert/Classical typeclass constraints each needs), delegating to the
already-proved `Theorems.Combinators` / `Theorems.Propositional.{Core,Connectives}` results via the
existing `Coe`s. No deletions in this phase.

**Tasks**:
- [x] Create `Cslib/Foundations/Logic/Theorems/DerivationCombinators.lean` (or extend
  `Combinators.lean` — prefer a new module to keep the raw-typed layer separable).
- [x] Provide raw-typed combinators mirroring the delegating-def families actually consumed:
  `impTransD`, `identity`, `dni`, `pairing`, `combineImpConj`, `combineImpConj3`, `doubleNegation`,
  `efqAxiom`, `lceImp`, `rceImp`, `contraposition`, `classicalMerge`, `iffIntro`, `contraposeImp`,
  `contraposeIff`, `iffNegIntro`, `demorgan*`, `peirceAxiom`, `raa`, `efqNeg`, `lem`. Each body:
  `(Theorems.….lemma (d1 : DerivableIn S _) …).toDerivation` (mark `noncomputable`). *(deviation:
  altered -- bodies use `InferenceSystem.DerivableIn.fromDerivation d1` explicitly rather than
  relying on implicit `Coe` insertion, since Lean's elaborator does not reliably insert the `Coe`
  for multi-argument applications before unifying implicit formula metavariables; verified via
  `lean_run_code` before committing to the pattern. This still uses only the existing `Coe`-backing
  functions, no new bridge.)*
- [x] Add a docstring to every new def (satisfy `docBlame`).
- [x] Import the new module where Phases 2-4/6 will consume it (or leave imports to those phases).

**Timing**: ~1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Theorems/DerivationCombinators.lean` (new) - the thin raw-typed layer.

**Verification**:
- `lake build Cslib.Foundations.Logic.Theorems.DerivationCombinators` green.
- `lake lint` clean on the new file (no `docBlame`); no `sorry`/axioms.

---

### Phase 2: Temporal `PropositionalHelpers` repoint + delete wrap/unwrap [NOT STARTED]

**Goal**: Repoint the 8 Temporal delegating combinator defs to the Phase 1 generic layer (option
B1: keep names, one-liner bodies) and delete the `wrap`/`unwrap` primitives, keeping every
downstream `Temporal/Metalogic/**` consumer untouched.

**Tasks**:
- [ ] Repoint `doubleNegation`, `efqAxiom`, `impTrans`, `pairing`, `lceImp`, `rceImp`, `dni`,
  `identity`, `demorganDisjNegBackward` to `DerivationCombinators.*` one-liners.
- [ ] Grep `wrap`/`unwrap` by name across `Temporal/**` to confirm no external by-name use; delete
  `PropositionalHelpers.lean:51,56` (`wrap`, `unwrap`).
- [ ] Retain any genuinely tree-structural helpers unchanged.

**Timing**: ~1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean` - repoint defs, delete wrap/unwrap.

**Verification**:
- `lake build Cslib.Logics.Temporal` green; ~21 consumer files unchanged and compiling.

---

### Phase 3: Bimodal Core + Connectives repoint + delete wrap'/unwrap' [NOT STARTED]

**Goal**: Repoint the delegating defs in `Theorems/Propositional/{Core,Connectives}.lean` to the
generic layer and delete Connectives' `wrap'`/`unwrap'` aliases. This phase precedes Phase 4 so that
the aliases of the Perpetuity pair are removed before that pair itself is deleted.

**Tasks**:
- [ ] Core: repoint `lem`, `efqAxiom`, `peirceAxiom`, `doubleNegation`, `raa`, `efqNeg`, `lceImp`,
  `rceImp` to the generic layer; **keep** `ecq`, `ldi`, `rdi`, `rcp`, `lce`, `rce` (context/tree
  structural) unchanged.
- [ ] Connectives: repoint `classicalMerge`, `iffIntro`, `contraposeImp`, `contraposition`,
  `contraposeIff`, `iffNegIntro`, `demorgan*`; **keep** `iffElimLeft/Right` and re-route or keep
  `demorganConjNeg/DisjNeg`.
- [ ] Retain the `{fc}`-polymorphic `DerivationTree.lift (FrameClass.base_le fc)` shim as a one-line
  per-target wrapper where the generic layer only yields `.Base` (do not expect zero lines).
- [ ] Delete Connectives' `wrap'`/`unwrap'` (`Connectives.lean:45,50`) once its defs no longer use
  them.

**Timing**: ~1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean` - repoint delegating defs, keep structural.
- `Cslib/Logics/Bimodal/Theorems/Propositional/Connectives.lean` - repoint defs, delete wrap'/unwrap'.

**Verification**:
- `lake build Cslib.Logics.Bimodal` green; ~18 `Bimodal/Metalogic/**` consumers unchanged.

---

### Phase 4: Bimodal Perpetuity `Helpers` repoint + delete wrap/unwrap [NOT STARTED]

**Goal**: Repoint the 8 Perpetuity delegating combinator defs to the generic layer and delete
Perpetuity's `wrap`/`unwrap`, now that Connectives' aliases (Phase 3) are gone. Keep the 4 genuinely
tree-structural temporal helpers.

**Tasks**:
- [ ] Repoint `impTrans`, `identity`, `combineImpConj3`, `combineImpConj`, `dni`, `contraposition`,
  `doubleNegation`, `lceImp`, `rceImp` to `DerivationCombinators.*` one-liners.
- [ ] **Keep** `boxToFuture`, `boxToPast`, `boxToPresent`, `tempFutureDerived` unchanged.
- [ ] Grep `wrap`/`unwrap` by name across `Bimodal/**` (research §7 flags
  `Bimodal/Metalogic/Core/MCSProperties.lean` — confirm it references the combinator defs, not the
  primitives) before deleting `Perpetuity/Helpers.lean:56,60`.

**Timing**: ~1 hour

**Depends on**: 1, 3

**Files to modify**:
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Helpers.lean` - repoint defs, delete wrap/unwrap, keep
  the 4 tree-structural helpers.

**Verification**:
- `lake build Cslib.Logics.Bimodal` green; `MCSProperties.lean` still compiles.

---

### Phase 5: Embedding consolidation (PL→X only) [NOT STARTED]

**Goal**: Fold the 9 drop-eligible `_atom/_bot/_imp` restatements for `toModal`/`toTemporal`/
`toBimodal` into the generic `embed_*` `@[simp]` lemmas, via a single `toX_eq_embed` `@[simp]`
unfolder per target. Keep `_and/_or/_neg` and the entire Modal→Bimodal / Temporal→Bimodal files.

**Tasks**:
- [ ] Add `@[simp] theorem toModal_eq_embed : φ.toModal = φ.embed := rfl` (and `toTemporal_eq_embed`,
  `toBimodal_eq_embed`) so simp reaches `embed_*`; prefer this over making `toX` an `abbrev`.
- [ ] Delete the 9 restatements: `toModal_atom/bot/imp` (`Modal/FromPropositional.lean:50-61`),
  `toTemporal_atom/bot/imp` (`Temporal/FromPropositional.lean:49-60`), `toBimodal_atom/bot/imp`
  (`Bimodal/Embedding/PropositionalEmbedding.lean:59-73`).
- [ ] **Keep** `_and/_or/_neg`, and do **not** touch `ModalEmbedding.lean` or `TemporalEmbedding.lean`.
- [ ] Treat normal-form drift as the real risk: validate with a full build of all three logic trees,
  not just the edited files.

**Timing**: ~1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/FromPropositional.lean` - add `toModal_eq_embed`, drop 3 restatements.
- `Cslib/Logics/Temporal/FromPropositional.lean` - add `toTemporal_eq_embed`, drop 3 restatements.
- `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` - add `toBimodal_eq_embed`, drop 3.

**Verification**:
- `lake build Cslib.Logics.Modal`, `Cslib.Logics.Temporal`, `Cslib.Logics.Bimodal` all green —
  deterministically catches any simp normal-form drift.

---

### Phase 6: Modal `imp_trans0` re-route (optional / scope-guarded) [NOT STARTED]

**Goal**: Replace only Modal's pure-propositional `imp_trans0` body with a call to the generic
`impTransD`/`imp_trans` at `HilbertOf Axioms`, **iff** the existing
`MinimalHilbert (HilbertOf Axioms)` instance is usable without editing `GenericMCSBridge.lean`.
`box_mono`/`dia_mono`/`boxOr_of_boxDisj`/`box_mono_or_*` are genuinely modal and are left as-is.

**Tasks**:
- [ ] Confirm `MinimalHilbert (Modal.HilbertOf Axioms)` resolves at
  `Modal/Metalogic/Intuitionistic/CanonicalModel.lean:223` via import + instance resolution only.
- [ ] If resolvable: replace `imp_trans0`'s body (currently a manual `deductionTheorem` + K/S witness
  proof) with the generic combinator; keep the signature stable.
- [ ] If instance resolution requires ANY change to `GenericMCSBridge.lean`: do **not** edit it —
  mark this phase `[BLOCKED]` with a note to coordinate with tasks 393/41, and proceed to Phase 7
  without this change.

**Timing**: ~1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean` - `imp_trans0` body only (if
  unblocked).

**Verification**:
- `lake build Cslib.Logics.Modal` green, or phase marked `[BLOCKED]` with rationale and no file edit.

---

### Phase 7: Full verification [NOT STARTED]

**Goal**: Confirm the whole refactor is green and debt-free across the repository.

**Tasks**:
- [ ] `lake build` (full) green.
- [ ] `lake exe checkInitImports` clean.
- [ ] `lake lint` clean on all touched files (watch `docBlame` on the new generic defs).
- [ ] Confirm zero new `sorry` and no new axioms (`lean_verify` / grep for `sorry`/`axiom`).

**Timing**: ~0.5 hour

**Depends on**: 2, 3, 4, 5, 6

**Files to modify**:
- None (verification only).

**Verification**:
- All commands above pass; no regressions introduced.

## Testing & Validation

- [ ] Full `lake build` green with all phases applied.
- [ ] `lake build Cslib.Logics.Temporal`, `…Bimodal`, `…Modal` each green (scoped checks per phase).
- [ ] `lake exe checkInitImports` and `lake lint` clean on touched files.
- [ ] No new `sorry`, no new axioms, no vacuous definitions (zero-debt invariant preserved).
- [ ] All three `wrap`/`unwrap`(`'`) primitive pairs removed; no dangling by-name references.
- [ ] The 9 PL→X `_atom/_bot/_imp` restatements removed; `_and/_or/_neg` and X→Bimodal files intact.
- [ ] Downstream `Temporal/Metalogic/**` (~21 files) and `Bimodal/Metalogic/**` (~18 files) compile
  unchanged (option B1 name preservation confirmed).

## Artifacts & Outputs

- `plans/01_retire-bridge-layers.md` (this plan).
- `Cslib/Foundations/Logic/Theorems/DerivationCombinators.lean` (new generic layer).
- Edited: `Temporal/Metalogic/PropositionalHelpers.lean`,
  `Bimodal/Theorems/Perpetuity/Helpers.lean`,
  `Bimodal/Theorems/Propositional/{Core,Connectives}.lean`,
  `Modal/FromPropositional.lean`, `Temporal/FromPropositional.lean`,
  `Bimodal/Embedding/PropositionalEmbedding.lean`, and (if unblocked)
  `Modal/Metalogic/Intuitionistic/CanonicalModel.lean`.
- `summaries/01_retire-bridge-layers-summary.md` (produced at implementation time).

## Rollback/Contingency

- The refactor is per-file and per-phase; each phase ends green and is committed independently, so
  any phase can be reverted via `git revert` of its commit without disturbing earlier green phases.
- If Phase 5 surfaces unresolvable simp normal-form drift, revert only the `toX_eq_embed` unfolders
  and the 9 deletions (restore the restatements) — the combinator phases (1-4) are unaffected.
- If Phase 6 is blocked by the scope guard, it is skipped entirely with no file change; the rest of
  the plan stands on its own.
