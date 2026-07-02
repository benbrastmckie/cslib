# Implementation Summary: Restore model-class-parametric Proposition.Equiv and LogicalEquivalence framework integration (PR #662)

- **Task**: 472
- **Plan**: plans/01_restore-model-class-equivalence.md
- **Research**: reports/01_restore-model-class-equivalence.md
- **Status**: Implemented
- **Date**: 2026-07-02

## What Was Done

Restored Fabrizio Montesi's model-class-parametric `Proposition.Equiv (S : Set (Model World
Atom))` and its integration with the `Cslib.Foundations.Logic.LogicalEquivalence` framework in
`Cslib/Logics/Modal/LogicalEquivalence.lean`, in the locked "Option A hybrid" form: PR #662's
`{atom, bot, imp, box}` primitives and `{hole, impL, impR, box}` `Proposition.Context`/`fill` were
kept unchanged; the standalone, all-models-hardwired `LogicallyEquivalent` definition (introduced
by task 137, commit `a084f9f2`) was removed entirely.

Added to the file:
- `public import Cslib.Foundations.Logic.LogicalEquivalence` (re-added; removed by #662).
- `open scoped InferenceSystem Proposition` (required in this file specifically -- scoped
  notation opens do not propagate across file imports).
- `Proposition.Equiv (S : Set (Model World Atom)) (φ₁ φ₂ : Proposition Atom) : Prop` over the
  ambient, per-declaration auto-bound `World` (no `∀ World : Type v` quantifier).
- Scoped notation `≡[S]` / `≡` (`:= Equiv Set.univ`) at precedence 50.
- `Proposition.equiv_def` (`Iff.rfl`), `Proposition.equiv_iff` (splits the object-level `↔` into
  a meta-level `Iff`), `Proposition.equiv_valid` (bridges to `Proposition.valid`) -- all with
  docstrings, `equiv_def`/`equiv_iff` tagged `@[scoped grind =]`.
- `instance : HasContext (Proposition Atom)`.
- `instance (S) : IsEquiv (Proposition Atom) (Proposition.Equiv S)`.
- `instance (S) : Congruence (Proposition Atom) (Proposition.Equiv S)` -- `elim` proved by
  rewriting the goal to the meta-`Iff` level via `Proposition.equiv_iff` *before* inducting on
  the context, which let the `impL`/`impR`/`box` cases port verbatim from the previous standalone
  `LogicallyEquivalent.congruence` proof content.
- `Satisfies.Context`, `Satisfies.Context.fill`, `instance judgementalContext : HasHContext
  (Judgement World Atom) (Proposition Atom)`.
- `instance : LogicalEquivalence (Proposition Atom) (Judgement World Atom) Satisfies.Bundled`
  with `eqv := Proposition.Equiv Set.univ` and a proved `eqvFillValid`.

Removed: `def LogicallyEquivalent` and `theorem LogicallyEquivalent.congruence` -- no abbrev
retained. `git grep -n "LogicallyEquivalent"` over `Cslib/` now returns zero matches.

## Key Implementation Insight

`grind`'s default unfolding of the file's Lukasiewicz-derived `and`/`or`/`iff` connectives down to
raw `imp`/`bot` requires classical (`Classical.em`) reasoning that `grind` does not attempt
automatically for this double-negation-style encoding. The fix used throughout: apply
`Proposition.equiv_iff` (or the underlying `Satisfies.and_iff_and` / `Satisfies.impl_iff_impl`
bridge lemmas) as an explicit `rw`/`have` step to lift a goal or hypothesis to the meta-`Iff`
level *before* any induction or further simplification, rather than relying on blanket
`grind`/`simp only [...]` normalization to find the classical bridge on its own. Once lifted, all
remaining reasoning (including the `Congruence.elim` induction) is pure intuitionistic
propositional logic and closes with plain `grind`, `exact`, or pointfree `⟨fun ..., fun ...⟩`
terms -- in fact the `impL`/`impR`/`box` congruence cases became verbatim ports of the prior
standalone proof once expressed at the meta level.

## Deviations from Plan

- **Line-number drift (documented in Phase 1)**: the plan/report cited `Satisfies.box_iff_forall`
  at `Basic.lean:116`; it is actually at `Basic.lean:235`. Content unchanged; anchor re-verified
  directly before use.
- **IsEquiv proof approach (Phase 3)**: the report sketched `rw [← equivalence_iff_isEquiv]; grind
  [Equivalence]`; implemented instead as direct `refl`/`symm`/`trans` fields each proved by `rw
  [Proposition.equiv_iff]; grind` (or with hypotheses rewritten too for `symm`/`trans`) --
  functionally equivalent, matches the exact style already used by the live `HML`/`CLL` `IsEquiv`
  instances in this codebase. `equivalence_iff_isEquiv` was confirmed to exist at
  `Mathlib/Order/Defs/Unbundled.lean:107` per the plan's verification requirement, but the
  simpler idiomatic route was used for the actual proof.
- **`equiv_iff`/`equiv_valid`/`Congruence.elim` proof bodies (Phase 2-3)**: the report's sketch
  proposed single-line `grind`/`simp` closings; these did not close automatically (see "Key
  Implementation Insight" above) and were replaced with explicit `rw`-based bridging steps
  followed by direct term proofs. No change to the theorem statements, notation, or instance
  signatures -- only the tactic proof scripts differ from the sketch.

No phase was skipped, altered in scope, or deferred. All five phases completed as planned.

## Verification

CSLib CI pipeline (all green):
- `lake exe cache get` -- warm, no-op.
- `lake build` (whole tree, 3189 jobs) -- success.
- `lake build Cslib.Logics.Modal.LogicalEquivalence` (scoped) -- success, zero warnings.
- `lake build Cslib.Logics.Modal.Cube` (downstream sanity) -- success.
- `lake exe checkInitImports` -- exit 0.
- `lake lint` -- "Linting passed for Cslib." (zero environment-linter warnings library-wide).
- `lake exe lint-style` -- exit 0, no warnings.
- `lake shake --add-public --keep-implied --keep-prefix` -- exit 1, but `Modal/LogicalEquivalence.lean`
  is confirmed **not** among the ~58 flagged files (all pre-existing, unrelated
  import-minimization opportunities in other Propositional/Temporal/Modal-Tableau files,
  verified against a stashed pre-change baseline).
- `lake exe mk_all --module` -- "No update necessary".
- `lake test` -- exit 0, full `CslibTests/` suite passes.

Zero-debt:
- `grep -n "sorry\|admit"` on the file -- zero matches.
- `grep -n "^axiom "` on the file -- zero matches.
- `lean_verify` on `Proposition.equiv_iff`/`Proposition.equiv_valid` -- only the three standard
  foundational axioms (`propext`, `Classical.choice`, `Quot.sound`); no new axioms.
- No vacuous definitions introduced.

Downstream compile:
- `git grep` confirms zero files in `Cslib/` import `Modal/LogicalEquivalence.lean` (it is a leaf
  module) -- matches the research report's "no external users" finding, so there was nothing to
  break.

Standards compliance:
- Every `def`/`theorem`/`inductive`/`structure` has a docstring; unnamed `instance`s follow the
  codebase's existing no-docstring convention for typeclass instances (matches
  `HML/LogicalEquivalence.lean` and `LinearLogic/CLL/Basic.lean`).
- `≡[S]`/`≡` notation is `scoped` under `Cslib.Logic.Modal`.
- `LogicallyEquivalent` fully removed; zero references anywhere in `Cslib/`.

## Files Changed

- `Cslib/Logics/Modal/LogicalEquivalence.lean` (only file touched; 120 insertions / 33 deletions).

## Artifacts

- Plan: `specs/472_restore_model_class_equivalence_pr_662/plans/01_restore-model-class-equivalence.md`
- Research: `specs/472_restore_model_class_equivalence_pr_662/reports/01_restore-model-class-equivalence.md`
- This summary: `specs/472_restore_model_class_equivalence_pr_662/summaries/01_restore-model-class-equivalence-summary.md`
