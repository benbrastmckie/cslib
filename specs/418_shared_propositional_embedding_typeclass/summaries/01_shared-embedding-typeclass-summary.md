# Implementation Summary: Task 418 — Shared `PropositionalEmbedding` typeclass

- **Task**: 418 - Shared PropositionalEmbedding typeclass + single limitation note
- **Status**: implemented
- **Completed**: 2026-06-29
- **Session**: sess_1751204400_a7b3c9

## Outcome

All 5 phases completed. Full CSLib CI pipeline passes (build, checkInitImports, lint-style,
shake, mk_all, test). 0 new sorry, 0 new axiom, zero lint warnings in modified files.

## Changes Made

### New File

- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Embedding.lean` (~115 lines):
  - `class PropositionalEmbedding (Atom F) [HasBot F] [HasImp F]` with `atomEmbed : Atom → F`
  - `def PL.Proposition.embed`: structural on atom/bot/imp, Łukasiewicz on and/or
  - `@[simp]` lemmas `embed_atom/bot/imp/and/or` (all `rfl`)
  - Single authored classical-scope limitation note (Łukasiewicz / [Wajsberg1938] / [McKinsey1939])
  - `class NativePropositionalEmbedding` extension point (uninstantiated)

### Modified Files

- `Cslib/Logics/Modal/FromPropositional.lean`:
  - Added `instance instPropositionalEmbeddingModal`
  - `toModal` → thin wrapper `φ.embed`
  - Bridge proof repointed from `simp only [PL.Proposition.toModal, ...]` to
    `simp only [PL.Proposition.toModal_imp/and/or, ...]`
  - Module header collapsed to one-line pointer to `Embedding.lean`
  - All `toModal_*` simp lemmas kept verbatim (still `rfl`)

- `Cslib/Logics/Temporal/FromPropositional.lean`:
  - Added `instance instPropositionalEmbeddingTemporal`
  - `toTemporal` → thin wrapper `φ.embed`
  - Module header collapsed to one-line pointer
  - All `@[simp, scoped grind =]` lemmas kept verbatim (still `rfl`)

- `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean`:
  - Added `instance instPropositionalEmbeddingBimodal`
  - `toBimodal` → thin wrapper `φ.embed`
  - Module header collapsed to one-line pointer
  - All `toBimodal_*` simp lemmas kept verbatim (still `rfl`)
  - Commuting-diamond lemmas (`toModal_toBimodal`, `toTemporal_toBimodal`,
    `embedding_commutes`) verified still close by `induction φ <;> simp [*]`

- `Cslib.lean`: barrel updated via `lake exe mk_all --module`

### Files Not Modified

- `Cslib/Logics/Temporal/ConservativeExtension.lean`: Task 417 already rewrote
  the bridge proof to use `evaluate_iff_of_classicalBridge PL.Proposition.toTemporal`
  (function-as-argument), which remains valid after `toTemporal = φ.embed`. No edit needed.
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean`:
  Same situation — Task 417's `evaluate_iff_of_classicalBridge` abstraction already handles
  the wrapper change transparently.

## Plan Deviations

- **Phases 3/4 bridge repoint** (plan expected `simp only [PL.Proposition.toTemporal, ...]`
  edits in ConservativeExtension files): Task 417 had already replaced the structural induction
  proofs with `evaluate_iff_of_classicalBridge`, which takes the embedding as a function
  argument and uses definitional reduction for `Iff.rfl` hypotheses. The typeclass-unfold path
  works because `HasBot.bot` and `HasImp.imp` reduce to concrete constructors via instances.
  No bridge repoint was needed for Temporal or Bimodal.
- **Typeclass form**: Chose plain `(Atom F)` parameters (no `outParam`) — elaborates cleanly
  since `Atom` is determined by the `PL.Proposition Atom` input type.

## Verification

| Check | Result |
|-------|--------|
| `lake build Cslib.Logics.Propositional.Embedding` | green |
| `lake build Cslib.Logics.Modal.FromPropositional` | green |
| `lake build Cslib.Logics.Temporal.FromPropositional` | green |
| `lake build Cslib.Logics.Temporal.ConservativeExtension` | green |
| `lake build Cslib.Logics.Bimodal.Embedding.PropositionalEmbedding` | green |
| `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.PropositionalConservativity` | green |
| `lake build` (full) | green (3156 jobs) |
| `lake exe checkInitImports` | pass |
| `lake lint` (modified files) | no warnings |
| `lake exe lint-style` | pass |
| `lake shake --add-public --keep-implied --keep-prefix` | no issues in modified files |
| `lake exe mk_all --module` | no update needed (barrel already current) |
| `lake test` | exit 0 (pre-existing sorry in Minimal/Completeness, not new) |
| sorry count in modified files | 0 |
| new axioms | 0 |
