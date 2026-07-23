# Implementation Summary: Retire wrap/unwrap Combinator Bridge Layers

- **Task**: 540 - retire_wrap_unwrap_combinator_bridge_layers
- **Status**: [COMPLETED]
- **Started**: 2026-07-23T19:30:15Z
- **Completed**: 2026-07-23T20:17:34Z
- **Artifacts**: plans/01_retire-bridge-layers.md

## Overview

Consolidated three duplicated local `wrap`/`unwrap` propositional-derivability bridge pairs
(Temporal `PropositionalHelpers`, Bimodal `Perpetuity/Helpers`, Bimodal `Connectives`'
`wrap'`/`unwrap'` aliases) into one generic raw-derivation-typed combinator layer,
`Cslib.Foundations.Logic.Theorems.DerivationCombinators`, and folded the 9 PL→X embedding
`_atom/_bot/_imp` restatements into the existing generic `embed_*` simp lemmas via a
`toX_eq_embed` unfolder per target. All 7 planned phases completed; none blocked.

## What Changed

- **New file**: `Cslib/Foundations/Logic/Theorems/DerivationCombinators.lean` -- ~24 raw
  `S⇓·`-typed combinators (`impTransD`, `identity`, `dni`, `pairing`, `combineImpConj[3]`,
  `doubleNegation`, `efqAxiom`, `lceImp`, `rceImp`, `contraposition`, `classicalMerge`, `iffIntro`,
  `contraposeImp`, `contraposeIff`, `iffNegIntro`, 4 `demorgan*`, `peirceAxiom`, `raa`, `efqNeg`,
  `lem`), each delegating to the already-proved `Theorems.Combinators`/
  `Theorems.Propositional.{Core,Connectives}` results via the *existing*
  `InferenceSystem.DerivableIn.fromDerivation`/`.toDerivation` bridge functions. No new typeclass.
- Repointed and deleted `wrap`/`unwrap` (and `wrap'`/`unwrap'`) from all three original helper
  files: `Temporal/Metalogic/PropositionalHelpers.lean`, `Bimodal/Theorems/Perpetuity/Helpers.lean`,
  `Bimodal/Theorems/Propositional/Connectives.lean`.
- Discovered and fixed a materially wider blast radius than the plan anticipated: 4 additional
  files consumed Perpetuity's `unwrap` by name (`Bimodal/Theorems/Combinators.lean`,
  `Bimodal/Metalogic/Core/MCSProperties.lean`, `Bimodal/Theorems/Perpetuity/Principles.lean`,
  `Bimodal/Theorems/TemporalDerived.lean`; 23 call sites total). Repointed all of them directly to
  `InferenceSystem.DerivableIn.toDerivation` (the exact function `unwrap` was duplicating).
- Folded PL→Modal/Temporal/Bimodal `_atom/_bot/_imp` restatements (9 lemmas) into the generic
  `embed_*` lemmas via one `@[simp] toX_eq_embed` unfolder per target; kept `_and/_or/_neg` and
  the Modal→Bimodal/Temporal→Bimodal embedding files untouched.
- Re-routed Modal's `imp_trans0` (in `CanonicalModel.lean`) through the generic combinator layer,
  using the existing `[HasMinimalAxioms Axioms] → HilbertTree (DerivationTree Axioms)` instance in
  the scope-guarded `GenericMCSBridge.lean` read-only (zero diff on that file).
- Fixed a `simpNF` regression the `toX_eq_embed` unfolders introduced in the retained `_and`/`_or`
  and `toModal_toBimodal`/`toTemporal_toBimodal` lemmas by dropping their now-redundant `@[simp]`
  tag (kept as plain, by-name theorems).

## Decisions

- Used positional `@`-style application (`@Theorems.DerivationCombinators.foo _ _ _
  Target.HilbertX _ _ args`) instead of named `(S := ...)` in every file that has `open
  Cslib.Logic.Temporal` or `open Cslib.Logic.Bimodal` in scope, because `S` is scoped
  prefix/infix notation for the "Since" temporal operator there and the named-arg form does not
  parse.
- `Modal.HilbertOf Axioms` (the plan's original Phase 6 anchor) no longer exists -- tasks
  539/543/547 retired it in favor of the generic `ClosedHilbert (DerivationTree Axioms)` tag.
  Re-located the target by symbol name (`HasMinimalAxioms`/`HilbertTree`) rather than assuming the
  plan's line/name anchors still held.
- Investigated but declined a `lake shake` suggestion to remove `Cslib.Init`/`Metalogic.MCS`/
  `Semantics.Birelational` imports from `CanonicalModel.lean`: empirically this broke the
  downstream `TruthLemma.lean`, which relies on `CanonicalModel.lean`'s `public import` of
  `Semantics.Birelational` to transitively reach `BForces`. `lake shake`'s per-file minimization
  does not account for downstream re-export dependents, so it was not safe to apply here; reverted
  and left the import list as Phase 6 wrote it.

## Impacts

- Zero net behavior change for all downstream consumers: every per-target combinator def kept its
  original name and signature (option B1), so ~21 `Temporal/Metalogic/**` and ~18+
  `Bimodal/Metalogic/**`/`Theorems/**` consumer files compile unchanged.
- One new file added to the public API surface: `Cslib.Foundations.Logic.Theorems.
  DerivationCombinators` (registered in `Cslib.lean` via `mk_all`).
- Full CSLib CI pipeline green: `lake build` (3255 jobs), `lake exe checkInitImports`,
  `lake lint` (0 issues after the simpNF fix), `lake exe lint-style` (0 issues), `lake shake`
  (one genuine unused import fixed in a touched file), `lake exe mk_all --module`, `lake test`
  (exit 0). Zero new `sorry`, zero new axioms, zero vacuous definitions across all 15
  touched/created files.

## Follow-ups

- None required for this task. The `lake shake` false-positive on `CanonicalModel.lean` may be
  worth a note in CSLib's own tooling docs (per-file import minimization can be unsafe when a
  file's `public import`s are relied on transitively by its downstream importers), but that is a
  tooling-process observation, not a code change this task's scope covers.

## References

- `specs/540_retire_wrap_unwrap_combinator_bridge_layers/plans/01_retire-bridge-layers.md`
- `specs/540_retire_wrap_unwrap_combinator_bridge_layers/reports/01_bridge-lemma-elimination.md`
