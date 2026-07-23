# Implementation Plan: Retire wrap/unwrap Combinator Bridge Layers

- **Task**: 540 - retire_wrap_unwrap_combinator_bridge_layers
- **Status**: [COMPLETED]
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

### Phase 2: Temporal `PropositionalHelpers` repoint + delete wrap/unwrap [COMPLETED]

**Goal**: Repoint the 8 Temporal delegating combinator defs to the Phase 1 generic layer (option
B1: keep names, one-liner bodies) and delete the `wrap`/`unwrap` primitives, keeping every
downstream `Temporal/Metalogic/**` consumer untouched.

**Tasks**:
- [x] Repoint `doubleNegation`, `efqAxiom`, `impTrans`, `pairing`, `lceImp`, `rceImp`, `dni`,
  `identity`, `demorganDisjNegBackward` to `DerivationCombinators.*` one-liners. *(deviation:
  altered -- calls use `@Theorems.DerivationCombinators.foo _ _ _ Temporal.HilbertBX _ _ args`
  (positional) rather than `(S := Temporal.HilbertBX)`, because this file has `open
  Cslib.Logic.Temporal` and `S` is scoped prefix notation for the "Since" temporal operator in
  that namespace (documented in `Temporal/ProofSystem/Instances.lean`'s module warning); the
  named-argument form does not parse under that `open`.)*
- [x] Grep `wrap`/`unwrap` by name across `Temporal/**` to confirm no external by-name use; delete
  `PropositionalHelpers.lean:51,56` (`wrap`, `unwrap`). *(deviation: altered -- the initial grep
  was run only after deletion and surfaced one hidden by-name consumer,
  `Temporal/Metalogic/GeneralizedNecessitation.lean` (`contraposeImp`/`contraposition`), which was
  not listed in this phase's Files-to-modify scope. Repointed it to the same generic layer using
  the same positional-`@` pattern; verified with a full `lake build
  Cslib.Logics.Temporal.Metalogic` (953 jobs green) confirming no other hidden consumers remain.)*
- [x] Retain any genuinely tree-structural helpers unchanged.

**Timing**: ~1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean` - repoint defs, delete wrap/unwrap.
- `Cslib/Logics/Temporal/Metalogic/GeneralizedNecessitation.lean` - repoint hidden by-name
  consumer of `wrap`/`unwrap` (`contraposeImp`/`contraposition`) discovered post-deletion
  *(deviation: added -- not in the original scope, required by the delete step above)*.

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic` green (953 jobs); ~21 consumer files unchanged and
  compiling.

---

### Phase 3: Bimodal Core + Connectives repoint + delete wrap'/unwrap' [COMPLETED]

**Goal**: Repoint the delegating defs in `Theorems/Propositional/{Core,Connectives}.lean` to the
generic layer and delete Connectives' `wrap'`/`unwrap'` aliases. This phase precedes Phase 4 so that
the aliases of the Perpetuity pair are removed before that pair itself is deleted.

**Tasks**:
- [x] Core: repoint `lem`, `efqAxiom`, `peirceAxiom`, `doubleNegation`, `raa`, `efqNeg`, `lceImp`,
  `rceImp` to the generic layer; **keep** `ecq`, `ldi`, `rdi`, `rcp`, `lce`, `rce` (context/tree
  structural) unchanged. *(deviation: altered -- positional `@`-application used instead of
  `(S := Bimodal.HilbertTM)`: this file opens `Cslib.Logic.Bimodal`, and `S` is scoped infix
  notation for the "Since" operator there (`Bimodal/Syntax/Formula.lean:105`), so the named-arg
  form does not parse, matching the same issue found in Phase 2.)*
- [x] Connectives: repoint `classicalMerge`, `iffIntro`, `contraposeImp`, `contraposition`,
  `contraposeIff`, `iffNegIntro`, `demorgan*`; **keep** `iffElimLeft/Right` and re-route or keep
  `demorganConjNeg/DisjNeg`. *(deviation: altered -- same positional-`@`-application pattern as
  Core, for the same "Since"-notation reason; `demorganConjNeg`/`demorganDisjNeg` needed no change
  since they only compose the already-repointed `iffIntro`/`demorgan*Forward/Backward` by name.)*
- [x] Retain the `{fc}`-polymorphic `DerivationTree.lift (FrameClass.base_le fc)` shim as a one-line
  per-target wrapper where the generic layer only yields `.Base` (do not expect zero lines).
- [x] Delete Connectives' `wrap'`/`unwrap'` (`Connectives.lean:45,50`) once its defs no longer use
  them.

**Timing**: ~1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean` - repoint delegating defs, keep structural.
- `Cslib/Logics/Bimodal/Theorems/Propositional/Connectives.lean` - repoint defs, delete wrap'/unwrap'.

**Verification**:
- `lake build Cslib.Logics.Bimodal` green; ~18 `Bimodal/Metalogic/**` consumers unchanged.

---

### Phase 4: Bimodal Perpetuity `Helpers` repoint + delete wrap/unwrap [COMPLETED]

**Goal**: Repoint the 8 Perpetuity delegating combinator defs to the generic layer and delete
Perpetuity's `wrap`/`unwrap`, now that Connectives' aliases (Phase 3) are gone. Keep the 4 genuinely
tree-structural temporal helpers.

**Tasks**:
- [x] Repoint `impTrans`, `identity`, `combineImpConj3`, `combineImpConj`, `dni`, `contraposition`,
  `doubleNegation`, `lceImp`, `rceImp` to `DerivationCombinators.*` one-liners.
- [x] **Keep** `boxToFuture`, `boxToPast`, `boxToPresent`, `tempFutureDerived` unchanged.
- [x] Grep `wrap`/`unwrap` by name across `Bimodal/**` (research §7 flags
  `Bimodal/Metalogic/Core/MCSProperties.lean` — confirm it references the combinator defs, not the
  primitives) before deleting `Perpetuity/Helpers.lean:56,60`. *(deviation: altered -- the grep
  found a materially wider blast radius than research §7's single flagged file: FOUR separate
  files consume Perpetuity's `unwrap` by name via `open ... Perpetuity (unwrap)` /
  same-namespace access, none of which are in this phase's original Files-to-modify list:
  `Bimodal/Theorems/Combinators.lean` (8 call sites), `Bimodal/Metalogic/Core/MCSProperties.lean`
  (1 call site, confirmed it also uses the *retained* `contraposition`/`impTrans`/`doubleNegation`
  combinator names unaffected), `Bimodal/Theorems/Perpetuity/Principles.lean` (4 call sites, same
  namespace as Helpers so no explicit `open`), and `Bimodal/Theorems/TemporalDerived.lean` (10
  call sites). All 23 call sites were repointed to
  `InferenceSystem.DerivableIn.toDerivation` directly (the exact function `unwrap` was duplicating
  -- no new bridge, per the plan's core thesis), since these theorems delegate to
  `Theorems.Temporal.TemporalDerived`/`Theorems.Modal.S5`/raw `Theorems.Combinators`, which are
  outside the propositional `DerivationCombinators` layer's scope. Two calls
  (`Perpetuity/Principles.lean`'s `modal5`) needed the previously-all-`_` implicit `S`/`φ`
  positions filled in explicitly, since `unwrap`'s concrete `Bimodal.HilbertTM`-typed signature had
  been silently pinning them where the generic `.toDerivation` does not. Verified with a full
  `lake build` (3255 jobs green) and a zero-result repo-wide by-name grep for `wrap`/`unwrap`
  after deletion.)*

**Timing**: ~1 hour

**Depends on**: 1, 3

**Files to modify**:
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Helpers.lean` - repoint defs, delete wrap/unwrap, keep
  the 4 tree-structural helpers.
- `Cslib/Logics/Bimodal/Theorems/Combinators.lean` - repoint 8 `unwrap(...)` call sites to
  `.toDerivation`, drop the `Perpetuity (unwrap)` open *(deviation: added -- hidden consumer)*.
- `Cslib/Logics/Bimodal/Metalogic/Core/MCSProperties.lean` - repoint 1 `unwrap(...)` call site,
  narrow the `Perpetuity (...)` open to drop `unwrap` *(deviation: added -- hidden consumer, the
  one research §7 flagged)*.
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Principles.lean` - repoint 4 `unwrap(...)` call sites
  (same-namespace access, no `open` line to edit) *(deviation: added -- hidden consumer)*.
- `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean` - repoint 10 `unwrap(...)` call sites, drop
  the `Perpetuity (unwrap)` open *(deviation: added -- hidden consumer)*.

**Verification**:
- `lake build` (full, 3255 jobs) green; `MCSProperties.lean` and all four newly-discovered
  consumers compile; zero remaining by-name `wrap`/`unwrap` code references repo-wide (grep
  excludes docstrings/prose).

---

### Phase 5: Embedding consolidation (PL→X only) [COMPLETED]

**Goal**: Fold the 9 drop-eligible `_atom/_bot/_imp` restatements for `toModal`/`toTemporal`/
`toBimodal` into the generic `embed_*` `@[simp]` lemmas, via a single `toX_eq_embed` `@[simp]`
unfolder per target. Keep `_and/_or/_neg` and the entire Modal→Bimodal / Temporal→Bimodal files.

**Tasks**:
- [x] Add `@[simp] theorem toModal_eq_embed : φ.toModal = φ.embed := rfl` (and `toTemporal_eq_embed`,
  `toBimodal_eq_embed`) so simp reaches `embed_*`; prefer this over making `toX` an `abbrev`.
- [x] Delete the 9 restatements: `toModal_atom/bot/imp` (`Modal/FromPropositional.lean:50-61`),
  `toTemporal_atom/bot/imp` (`Temporal/FromPropositional.lean:49-60`), `toBimodal_atom/bot/imp`
  (`Bimodal/Embedding/PropositionalEmbedding.lean:59-73`).
- [x] **Keep** `_and/_or/_neg`, and do **not** touch `ModalEmbedding.lean` or `TemporalEmbedding.lean`.
- [x] Treat normal-form drift as the real risk: validate with a full build of all three logic trees,
  not just the edited files. *(deviation: altered -- the flagged risk materialized exactly as
  predicted: `PL.Proposition.toModal_toBimodal`/`toTemporal_toBimodal`/`embedding_commutes` in
  `Bimodal/Embedding/PropositionalEmbedding.lean` broke because `embed`'s `imp`/`and`/`or` cases
  produce typeclass-generic `HasImp.imp`/`HasBot.bot`-headed terms, which do not syntactically
  match the retained per-target `_imp`/`_and`/`_or` lemmas' concrete-constructor-headed LHS
  patterns for simp's discrimination tree. Fixed (not reverted) by changing those 3 proofs from
  `induction φ <;> simp [*]` to `induction φ <;> simp [*, HasImp.imp, HasBot.bot] <;> tauto`,
  which explicitly unfolds the typeclass projections back to the concrete constructors before
  matching; verified via `lean_multi_attempt` before editing, then via full `lake build` (3254
  jobs green, zero new sorries in touched files).)*

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

### Phase 6: Modal `imp_trans0` re-route (optional / scope-guarded) [COMPLETED]

**Goal**: Replace only Modal's pure-propositional `imp_trans0` body with a call to the generic
`impTransD`/`imp_trans` at `HilbertOf Axioms`, **iff** the existing
`MinimalHilbert (HilbertOf Axioms)` instance is usable without editing `GenericMCSBridge.lean`.
`box_mono`/`dia_mono`/`boxOr_of_boxDisj`/`box_mono_or_*` are genuinely modal and are left as-is.

**Tasks**:
- [x] Confirm `MinimalHilbert (Modal.HilbertOf Axioms)` resolves at
  `Modal/Metalogic/Intuitionistic/CanonicalModel.lean:223` via import + instance resolution only.
  *(deviation: altered -- `Modal.HilbertOf` no longer exists; tasks 539/543/547 (landed since this
  plan was written) retired it in favor of the generic `ClosedHilbert (DerivationTree Axioms)` tag
  (per `GenericMCSBridge.lean`'s own module docstring: "HilbertOf Axioms has no external
  references (grep-confirmed), this bundle is now retired"). Re-located the target by symbol
  name: the analogous existing, read-only-usable instance is
  `instance [HasMinimalAxioms Axioms] : HilbertTree (DerivationTree Axioms)` at
  `GenericMCSBridge.lean:88`, which activates the generic (Foundations, non-guarded)
  `MinimalHilbert (ClosedHilbert (DerivationTree Axioms))` instance from
  `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean`. `imp_trans0`'s two existing value
  parameters `h_implyK`/`h_implyS` are exactly the two fields `HasMinimalAxioms` needs, so
  `haveI : HasMinimalAxioms Axioms := ⟨h_implyK, h_implyS⟩` supplies it locally with no signature
  change.)*
- [x] If resolvable: replace `imp_trans0`'s body (currently a manual `deductionTheorem` + K/S witness
  proof) with the generic combinator; keep the signature stable. *(confirmed resolvable; body
  replaced with
  `@Theorems.DerivationCombinators.impTransD _ _ _ (ClosedHilbert (DerivationTree Axioms)) _ _ A B
  C d1 d2` under the local `haveI`; signature unchanged, all 4 call sites
  (`imp_trans0 h_implyK h_implyS ...`) untouched and still compile.)*
- [x] If instance resolution requires ANY change to `GenericMCSBridge.lean`: do **not** edit it —
  mark this phase `[BLOCKED]` with a note to coordinate with tasks 393/41, and proceed to Phase 7
  without this change. *(not triggered -- `git diff --stat` on `GenericMCSBridge.lean` confirms
  zero changes; the file was imported and its existing instance used read-only, exactly as
  sanctioned.)*

**Timing**: ~1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean` - `imp_trans0` body, plus two
  new imports (`GenericMCSBridge`, `DerivationCombinators`) and one new `open` needed to reach the
  relocated instance.

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.CanonicalModel` green (648 jobs);
  `lake build Cslib.Logics.Modal.Metalogic` green (793 jobs); zero diff on `GenericMCSBridge.lean`;
  zero new `sorry`/`axiom` in the touched file.

---

### Phase 7: Full verification [COMPLETED]

**Goal**: Confirm the whole refactor is green and debt-free across the repository.

**Tasks**:
- [x] `lake build` (full) green. *(3255 jobs, twice: once after Phase 6, once again after the
  Phase 7 simpNF/import fixes below.)*
- [x] `lake exe checkInitImports` clean.
- [x] `lake lint` clean on all touched files (watch `docBlame` on the new generic defs).
  *(deviation: altered -- the first run found 8 `simpNF` errors, exactly the Phase-5-flagged
  normal-form-drift risk resurfacing one layer up: the RETAINED `_and`/`_or` and
  `toModal_toBimodal`/`toTemporal_toBimodal` `@[simp]` lemmas were no longer in simp-normal
  form once `toX_eq_embed` became `@[simp]`, since their LHS now simplifies further via
  `toX_eq_embed` + the generic `embed_and`/`embed_or`. Fixed by dropping the now-redundant
  `@[simp]` attribute from those 8 declarations (keeping them as plain, by-name-citable theorems;
  `scoped grind =` retained where present, since `grind` is a separate mechanism unaffected by
  simp normal-form) across `Modal/FromPropositional.lean`, `Temporal/FromPropositional.lean`, and
  `Bimodal/Embedding/PropositionalEmbedding.lean`. Re-ran `lake lint`: 0 errors.)*
- [x] Confirm zero new `sorry` and no new axioms (`lean_verify` / grep for `sorry`/`axiom`).
  *(zero `sorry`/`axiom` in all 15 touched files, confirmed by per-file grep; repo-wide baseline
  counts (144 pre-existing `sorry`, 28 pre-existing `axiom`, 1 pre-existing unrelated vacuous
  `theorem ... := trivial` in `Computability/URM/Basic.lean`) are unchanged by this task's diff.)*
- [x] `lake exe lint-style` clean *(deviation: added -- not originally listed as a separate task
  item, but is CI pipeline step 4; ran clean, 0 issues.)*
- [x] `lake shake --add-public --keep-implied --keep-prefix` reviewed *(deviation: added -- CI
  pipeline step 7. Found one genuine unused import in a touched file
  (`Bimodal/Theorems/Combinators.lean`'s now-dead `Perpetuity.Helpers` import after the `open
  ... (unwrap)` removal) and fixed it. Also flagged `CanonicalModel.lean`'s `Cslib.Init`/
  `Metalogic.MCS`/`Semantics.Birelational` imports as removable; empirically tested this by
  actually removing them and rebuilding -- `CanonicalModel.lean` itself still compiled, but the
  downstream `Modal/Metalogic/Intuitionistic/TruthLemma.lean` (which relies on `CanonicalModel`'s
  `public import` of `Semantics.Birelational` to transitively reach `BForces`) broke. Reverted
  this suggestion: `lake shake`'s per-file minimization does not account for downstream files
  depending on a file's own `public import` re-export chain, so it is unsafe to apply blindly here.
  Left `CanonicalModel.lean`'s import list as Phase 6 wrote it; confirmed full `lake build` green
  with the revert in place.)*
- [x] `lake exe mk_all --module` *(deviation: added -- CI pipeline step 6, needed since Phase 1
  added a new file; updated `Cslib.lean` to list `DerivationCombinators.lean`.)*
- [x] `lake test` *(deviation: added -- CI pipeline step 5; exit 0, all tests pass.)*

**Timing**: ~0.5 hour

**Depends on**: 2, 3, 4, 5, 6

**Files to modify**:
- None planned; in practice also touched (simpNF/import fixes discovered during verification):
  `Cslib/Logics/Modal/FromPropositional.lean`, `Cslib/Logics/Temporal/FromPropositional.lean`,
  `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` (drop dead `@[simp]`),
  `Cslib/Logics/Bimodal/Theorems/Combinators.lean` (drop dead import), `Cslib.lean` (`mk_all`).

**Verification**:
- All commands above pass; no regressions introduced. Full CSLib CI pipeline (8 steps) green.

## Testing & Validation

- [x] Full `lake build` green with all phases applied (3255 jobs).
- [x] `lake build Cslib.Logics.Temporal`, `…Bimodal`, `…Modal` each green (scoped checks per
  phase; no single barrel module exists for these three trees, so verification used
  `Cslib.Logics.Temporal.Metalogic` (953 jobs), `Cslib.Logics.Bimodal.Theorems.*`/`Metalogic.*`
  scoped builds, and `Cslib.Logics.Modal.Metalogic` (793/799 jobs), plus the full-repo build).
- [x] `lake exe checkInitImports` and `lake lint` clean on touched files (both 0 issues after the
  Phase 7 simpNF fix).
- [x] No new `sorry`, no new axioms, no vacuous definitions (zero-debt invariant preserved) --
  confirmed by per-file grep across all 15 touched/created files.
- [x] All three `wrap`/`unwrap`(`'`) primitive pairs removed; no dangling by-name references --
  confirmed by a repo-wide `\bwrap\b|\bunwrap\b` grep excluding docstrings/prose (0 code hits).
- [x] The 9 PL→X `_atom/_bot/_imp` restatements removed; `_and/_or/_neg` and X→Bimodal files intact.
- [x] Downstream `Temporal/Metalogic/**` (~21 files) and `Bimodal/Metalogic/**` (~18 files) compile
  unchanged (option B1 name preservation confirmed) -- plus 4 additional hidden Bimodal consumers
  of `unwrap` discovered and fixed (see Phase 4 deviation notes) that were outside the original
  ~18-file estimate.

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
