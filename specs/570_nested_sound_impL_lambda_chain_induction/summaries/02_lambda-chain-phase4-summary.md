# Implementation Summary: Phase 4 — Land `lambdaChain_XZ_imp_Y` and the Two Shape Lemmas

- **Task**: 570 - nested_sound_impL_lambda_chain_induction
- **Plan**: `specs/570_nested_sound_impL_lambda_chain_induction/plans/01_lambda-chain-induction-plan.md`
  (Phase 4 of 8)
- **Research**: `specs/570_nested_sound_impL_lambda_chain_induction/reports/01_lambda-chain-induction.md`
- **Status**: [COMPLETED]
- **Session**: sess_1785113705_bcf38a

## Overview

Landed the induction this task is named for: `lambdaChain_XZ_imp_Y`, the source's page-10
"induction on `n` together with Lemma 4.7.(ii) and (iv)" over the `Λ{ }` chain, plus the two
`Λ = []` normalisation shape lemmas (`psiX_fm`, `primeRhs_fm`) the Phase 5 assembly needs. All
three were transcribed verbatim (statement and proof term) from the research report's
Lean-verified, sorry-free compilation — this was a transcription task, not a proof-discovery
task, per the dispatch's settled design.

## What Changed

**File**: `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean`

Added a new section `/-! ## The Λ-Chain Induction (Lemma 4.9, ⊃•) -/`, placed after the
Λ-Chain Toolkit section (Phase 3's `mpAnd`/`topBase`/`andMP`/`lambdaChain_step2`) and before the
`⊃•` (`impL`) deferred-sorry section:

- **`lambdaChain_XZ_imp_Y (A B : Proposition Atom) : ∀ (Λ : OutputCtx Atom), ⊢ ((Λ.fillRhs A°).fm ∧
  (Λ.fillLhs (A⊃B)•).fm) ⊃ (Λ.fillLhs B•).fm`** — the three-case structural recursion:
  - `[]` closed by `topBase A B`
  - `[Λ₀]` closed by `lemma4_7_ii Λ₀.fm (mpAnd A B)`
  - `Λ₀ :: Λ₁ :: rest` closed by `lemma4_7_ii Λ₀.fm (lemma4_7_iv (lambdaChain_XZ_imp_Y A B (Λ₁ :: rest)))`

  The docstring records the induction motive `P(Λ) := ⊢ ((Λ.fillRhs A°).fm ∧ (Λ.fillLhs
  (A⊃B)•).fm) ⊃ (Λ.fillLhs B•).fm` with `A`, `B` fixed outside the recursion, the reading of the
  three cases against the source's `Λ{ } = Λ0, [Λ1, [..., [Λn, { }]...]]` (`[]` = degenerate
  `Λ{ } = { }`, `[Λ₀]` = `n = 0`, `Λ₀::Λ₁::rest` = `n ≥ 1`), a per-case goal/discharge table, and
  the `rfl`-definitional identity `(buildRhsChain (Λ₁::rest) Ψ).fm = □ ((OutputCtx.fillRhs
  (Λ₁::rest) Ψ).fm)` the cons-cons step relies on to line up with `lemma4_7_iv`'s `□A ∧ ◇B ⊃ ◇C`
  shape with no rewriting.

- **`psiX_fm (ctx : InputCtx Atom) (A : Proposition Atom)`** — `(buildRhsChain (ctx.Λ.headD .empty
  :: ctx.Λ.tail) (NestedRhs.atom A)).fm = Proposition.box ((ctx.Λ.fillRhs (.atom A)).fm)`, closed
  by `cases ctx.Λ <;> rfl`.

- **`primeRhs_fm (ctx : InputCtx Atom) (A : Proposition Atom)`** — `(OutputCtx.fillRhs
  (ctx.Λ.headD .empty :: ctx.Λ.tail) (NestedRhs.atom A)).fm = (ctx.Λ.fillRhs (.atom A)).fm`,
  closed by `cases ctx.Λ <;> rfl`.

## Decisions

- **Verbatim transcription, no redesign.** Per the dispatch's settled-design contract, all three
  statements and proof terms were copied from the research report's L2/L4 sections without
  modification to the mathematical content.
- **Explicit `OutputCtx.fillRhs` application in `primeRhs_fm`** rather than dot notation on a raw
  list-literal cons expression — see Plan Deviations below.

## Plan Deviations

- **`primeRhs_fm`'s call syntax**: the plan's task text (and the research report's L4 statement)
  wrote `(ctx.Λ.headD .empty :: ctx.Λ.tail).fillRhs (NestedRhs.atom A)`. This fails to elaborate:
  `OutputCtx` is an `abbrev` for `List (NestedLhs Atom)`, not a distinct type with its own head
  symbol, so Lean's dot-notation namespace resolution on a raw `List.cons` literal cannot find
  `OutputCtx.fillRhs` — it reports `Invalid field 'fillRhs': the environment does not contain
  'List.fillRhs'`. (`ctx.Λ.fillRhs` elsewhere in the same file works because `ctx.Λ` is a
  projection whose *declared* type is `OutputCtx Atom`, which dot notation resolves before
  unfolding the abbrev; a bare list-cons expression has no such declared-type annotation to
  resolve against.) Fixed by writing the equivalent explicit application `OutputCtx.fillRhs
  (ctx.Λ.headD .empty :: ctx.Λ.tail) (NestedRhs.atom A)`. Same statement (definitionally and
  syntactically identical up to the call form), same proof (`cases ctx.Λ <;> rfl` unaffected),
  purely a Lean-encoding fix with no mathematical content change. Not a re-opening of the settled
  design — it is the same theorem.
- **Two docstring table rows exceeded the 100-character line-length linter** (the `[Λ₀]` and
  `Λ₀::Λ₁::rest` rows of the goal/discharge table). Shortened wording (e.g. `via mpAnd` instead of
  `applied to mpAnd : ⊢ (A ∧ (A ⊃ B)) ⊃ B`, and compacted the formula spacing in the cons-cons
  row) to fit within the limit. No content lost — the omitted hypothesis types are already fully
  spelled out in the theorem signature and the motive prose immediately above the table.

## Impacts

- `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean` gains three new sorry-free
  declarations (`lambdaChain_XZ_imp_Y`, `psiX_fm`, `primeRhs_fm`), all public (no `private`
  marker — matching the plan, since `lambdaChain_XZ_imp_Y` is a named source step and the shape
  lemmas are consumed by name in Phase 5's assembly).
- Module's diagnostic set is unchanged from Phase 3's baseline: exactly two pre-existing
  diagnostics remain —
  `Soundness.lean:1502:2: Missing cases: _, (NestedProof.cut (InputCtx.mk _ _ _) _ _ _)` and
  `Soundness.lean:1479:8: declaration uses 'sorry'` (line numbers shifted by the ~64 lines this
  phase added). No third diagnostic.
- Cslib bare-sorry census: unchanged at 41 (`bash .claude/scripts/lean-sorry-census.sh Cslib`),
  as expected — this phase adds no sorry and removes none.
- All 18 existing `nested_sound_*` case lemmas and the eight reused declarations listed in the
  plan's Preserved Assets table are untouched.

## Follow-ups

- Phase 5 (`nested_sound_impL`'s discharge, `Soundness.lean:1488`) is now unblocked — it depends
  on Phase 2 (repaired `outputPruning`, landed) and Phase 4 (this dispatch, landed).
- Phase 6 (`OutputCtx.fillLhs_empty_imp_fillEmpty` in `Translation.lean`) remains independently
  available (depends only on Phase 2).
- Phase 7 (the `cut` arm, RED-to-green transition) still requires both Phase 5 and Phase 6.

## References

- Research report: `specs/570_nested_sound_impL_lambda_chain_induction/reports/01_lambda-chain-induction.md`,
  §"The Λ-Chain Induction: Proposed Statements, Motive, and Verified Proofs" (L2, L4).
- Source: R. Arisaka, A. Das, L. Straßburger, *On Nested Sequents for Constructive Modal Logics*,
  LMCS 11(3:7), 2015, page 10. BibKey `ArisakaDasStrassburger2015`.
- Plan: `specs/570_nested_sound_impL_lambda_chain_induction/plans/01_lambda-chain-induction-plan.md`,
  Phase 4.
