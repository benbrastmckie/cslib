# Implementation Plan: Task #341

- **Task**: 341 - Theory-parametric algebraic completeness for propositional logic
- **Status**: [IMPLEMENTING]
- **Effort**: 3.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/341_theory_parametric_completeness/reports/01_theory-parametric-completeness.md
- **Artifacts**: plans/01_theory-parametric-completeness.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, cslib.md, lean4.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Restate propositional algebraic completeness theory-parametrically over the existing-but-unused
`AlgTValid` predicate (Thomas Waring's `v ⊨ T` formulation), introduce a single
theory-parametric completeness theorem `hilbert_alg_complete_theory`, and recover the three
existing tier theorems (MPL/IPL/CPL `hilbert_alg_complete`) as corollaries. The entire strategy
was already compile-verified end-to-end in a scratch file (`lake build` green, 0 sorries, 0 new
axioms; scratch removed). This plan transcribes that verified strategy into the three target
files in dependency order, with CI verification at each phase boundary.

### Research Integration

The research report compile-verified all three work items and supplies exact Lean one-liners.
This plan adopts them verbatim:
- **Item 1** `alg_theory_soundness` mirrors `min_alg_soundness` (Soundness.lean:168) with only the
  `.ax` case changed to `exact hT ψ (by simpa [AxiomTheory] using h_ax)`.
- **Item 2** `canonicalV_algTValid` is a one-liner reusing the already-existing
  `canonicalV_axiom_top` (HilbertLindenbaum.lean:624).
- **Item 3** `hilbert_alg_complete_theory` MUST pin `{Atom : Type u}` and `∀ (H : Type u)`
  (verified: `Type _` causes universe-metavariable mismatches). Each tier corollary uses an
  explicit two-direction proof.

The grounded source facts used by this plan:
- `AlgTValid` is `∀ B ∈ T, AlgEvaluate v bot_val B = ⊤` (Algebra.lean:149).
- `min_alg_soundness` matches on `DerivationTree`; cases `.ax/.assumption/.modus_ponens/.weakening`
  (Soundness.lean:168-190).
- `*_alg_axiom_sound` lemmas: `min_alg_axiom_sound` (:58), `int_alg_axiom_sound` (:121),
  `prop_alg_axiom_sound` (:142).
- Existing tier theorems: `MPL.hilbert_alg_complete` (HilbertCompleteness.lean:57),
  `IPL.hilbert_alg_complete` (:80), `CPL.hilbert_alg_complete` (:105) — these reuse
  `canonicalV_spec`, `hilbertLindenbaumMk_eq_top_iff`, and the IPL/CPL `rfl` bridge
  `(⊥ : HilbertLindenbaumAlgebra _) = canonicalBotVal _`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

ROADMAP.md exists but the `--roadmap` flag was not set for this planning invocation, so no
roadmap review/update phases are added. This task advances the Propositional Logic algebraic
semantics line by unifying the three tier completeness theorems under a single
theory-parametric statement.

## Goals & Non-Goals

**Goals**:
- Add `alg_theory_soundness` (parametric soundness) to `Soundness.lean`.
- Add `canonicalV_algTValid` to `HilbertLindenbaum.lean`.
- Add `hilbert_alg_complete_theory` plus MPL/IPL/CPL tier-corollary bridges to
  `HilbertCompleteness.lean`, with mandatory universe pinning.
- Keep the three existing tier theorems available (recovered as corollaries of the parametric
  theorem) so downstream callers are unaffected.
- Keep the full CI pipeline green: `lake build`, `lake test`, `lake exe checkInitImports`,
  `lake exe lint-style`, `lake shake`.

**Non-Goals**:
- No change to `AlgTValid`, `AxiomTheory`, `MinimalAxioms`, or the Lindenbaum scaffolding.
- No re-derivation of the completeness backward direction from the validity predicate (the
  resolved `bot_val` obstacle forbids this — see Risks).
- No new axioms, no `sorry`, no vacuous definitions.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Universe inference fails if `Type _` used instead of `{Atom : Type u}` / `∀ (H : Type u)` | H | M | Pin `universe u`, write `{Atom : Type u}` and `(H : Type u)` explicitly, mirroring existing `.{u,u}` annotations (Phase 3) |
| Backward (completeness) direction mistakenly sourced from `AlgTValid` | H | M | Each tier corollary reuses the verbatim original Lindenbaum route (`canonicalV_spec` + `hilbertLindenbaumMk_eq_top_iff`, with IPL/CPL `rfl` bridge), NOT the validity predicate |
| `.ax` case unfold of `AxiomTheory` fails | M | L | Use the verified `by simpa [AxiomTheory] using h_ax` form (Item 1) / `by simpa [AxiomTheory] using hB` (Item 2) |
| `lake shake` flags import minimization changes | L | M | Run `lake shake --add-public --keep-implied --keep-prefix`; apply `--fix` only if it reports; no new imports are expected since all reused lemmas are already imported |
| Existing tier theorem signatures change, breaking downstream | M | L | Keep tier theorem names/signatures identical; only the proof body changes to route through the parametric theorem |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |
| 3 | 4 | 3 |

Phases 1 and 2 touch disjoint files (`Soundness.lean`, `HilbertLindenbaum.lean`) and can run in
parallel. Phase 3 consumes both. Phase 4 is the final full-pipeline CI gate.

---

### Phase 1: Parametric soundness lemma `alg_theory_soundness` [COMPLETED]

**Goal**: Add the theory-parametric soundness lemma to `Soundness.lean`, discharging the `.ax`
case from an `AlgTValid` hypothesis instead of the per-tier `*_alg_axiom_sound` lemmas.

**Tasks**:
- [ ] Add `alg_theory_soundness` parametric in `(Axioms : Proposition Atom → Prop)`
  `[MinimalAxioms Axioms]`, structured exactly like `min_alg_soundness` (Soundness.lean:168):
  match on the `DerivationTree`, taking an extra hypothesis
  `hT : AlgTValid (AxiomTheory Axioms) v bot_val`.
- [ ] In the `.ax _ ψ h_ax` case, replace the `min_alg_axiom_sound` call with
  `exact hT ψ (by simpa [AxiomTheory] using h_ax)`.
- [ ] Leave the `.assumption`, `.modus_ponens`, and `.weakening` cases identical to
  `min_alg_soundness` (recursing into `alg_theory_soundness` with `hT` threaded through).
- [ ] Confirm reuse of `himp_eq_top_iff` in the `.modus_ponens` case is unchanged.

**Timing**: 0.75 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/Soundness.lean` - add `alg_theory_soundness`
  after `min_alg_soundness` (around :191); no imports added (`AlgTValid`, `AxiomTheory` reachable
  via existing `Algebra` import).

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.Soundness` succeeds.
- `lean_verify` on `Cslib.Logic.PL.alg_theory_soundness`: 0 sorries, no new axioms.
- Run `lake build` (scoped fallback to full if module name resolution differs).

---

### Phase 2: Canonical valuation satisfies `AlgTValid` (`canonicalV_algTValid`) [COMPLETED]

**Goal**: Add the one-liner lemma that the canonical/Lindenbaum valuation models
`AxiomTheory Axioms`, reusing the already-existing `canonicalV_axiom_top`.

**Tasks**:
- [ ] Add `canonicalV_algTValid (Axioms) [MinimalAxioms Axioms] :`
  `AlgTValid (AxiomTheory Axioms) (canonicalV Axioms) (canonicalBotVal Axioms)`.
- [ ] Prove with the verified one-liner:
  `by intro B hB; exact canonicalV_axiom_top Axioms B (by simpa [AxiomTheory] using hB)`.
- [ ] Place it after `canonicalV_axiom_top` (HilbertLindenbaum.lean:624).

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaum.lean` - add
  `canonicalV_algTValid` after :630.

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaum` succeeds.
- `lean_verify` on `Cslib.Logic.PL.canonicalV_algTValid`: 0 sorries, no new axioms.

---

### Phase 3: Parametric theorem + tier corollary bridges [COMPLETED]

**Goal**: Add `hilbert_alg_complete_theory` to `HilbertCompleteness.lean` and re-derive the three
tier theorems as corollaries via explicit two-direction proofs, with mandatory universe pinning.

**Tasks**:
- [ ] Add `hilbert_alg_complete_theory {Atom : Type u}`
  `(Axioms : PL.Proposition Atom → Prop) [MinimalAxioms Axioms] {φ : PL.Proposition Atom} :`
  `Derivable Axioms φ ↔ ∀ (H : Type u) [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),`
  `AlgTValid (AxiomTheory Axioms) v bot_val → AlgEvaluate v bot_val φ = ⊤`.
  - **Forward**: `intro` derivation; `obtain ⟨d⟩`; apply `alg_theory_soundness` (Phase 1) with the
    supplied `hT : AlgTValid …` and empty context.
  - **Backward**: instantiate the RHS at `HilbertLindenbaumAlgebra Axioms`, `canonicalV Axioms`,
    `canonicalBotVal Axioms`, discharge the `AlgTValid` premise with `canonicalV_algTValid`
    (Phase 2), then `rw [canonicalV_spec]` and finish with `hilbertLindenbaumMk_eq_top_iff.mp`.
  - **MUST** keep `universe u`, `{Atom : Type u}`, and `∀ (H : Type u)` — do NOT use `Type _`.
- [ ] Rewrite `MPL.hilbert_alg_complete` proof body as a corollary (signature unchanged
    `… ↔ GHAValid.{u, u} φ`):
  - Forward: `hilbert_alg_complete_theory.mp`, instantiate at `bot_val = ⊥`, discharge `AlgTValid`
    via `min_alg_axiom_sound` (per-axiom soundness), matching `GHAValid`.
  - Backward: reuse the **original** Lindenbaum route verbatim (`canonicalV_spec` +
    `hilbertLindenbaumMk_eq_top_iff`); MPL has no `rfl` bot bridge.
- [ ] Rewrite `IPL.hilbert_alg_complete` (`… ↔ HAValid.{u, u} φ`):
  - Forward via `hilbert_alg_complete_theory.mp` at `bot_val = ⊥`, discharging `AlgTValid` with
    `int_alg_axiom_sound`.
  - Backward via original Lindenbaum route, reusing the verbatim `rfl` bridge
    `(⊥ : HilbertLindenbaumAlgebra (@IntPropAxiom Atom)) = canonicalBotVal (@IntPropAxiom Atom)`.
- [ ] Rewrite `CPL.hilbert_alg_complete` (`… ↔ BAValid.{u, u} φ`):
  - Forward via `hilbert_alg_complete_theory.mp` at `bot_val = ⊥`, discharging `AlgTValid` with
    `prop_alg_axiom_sound`.
  - Backward via original Lindenbaum route, reusing the verbatim `rfl` bridge for
    `PropositionalAxiom`.
- [ ] **Obstacle guard**: do NOT attempt to source any backward direction from `AlgTValid`;
  `AlgTValid` only forces `bot_val` to be a lower bound on the image of `v`, not the algebra's `⊥`.

**Timing**: 1.5 hours

**Depends on**: 1, 2

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean` - add
  `hilbert_alg_complete_theory`; rewrite the three tier theorem bodies (signatures/names
  unchanged) to route through it.

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertCompleteness` succeeds.
- `lean_verify` on `Cslib.Logic.PL.hilbert_alg_complete_theory`,
  `Cslib.Logic.PL.MPL.hilbert_alg_complete`, `…IPL.hilbert_alg_complete`,
  `…CPL.hilbert_alg_complete`: each 0 sorries, no new axioms.
- Confirm the three tier theorem names and signatures are byte-for-byte unchanged (only proof
  bodies differ).

---

### Phase 4: Full CI pipeline verification [COMPLETED]

**Goal**: Run the complete CSLib CI pipeline and confirm green with zero debt and all three tier
theorems preserved.

**Tasks**:
- [ ] `lake exe cache get` (once, if cache missing) to avoid a long Mathlib rebuild.
- [ ] `lake build` — full project, syntax linters during build.
- [ ] `lake test` — run `CslibTests/`.
- [ ] `lake exe checkInitImports` — all touched files import `Cslib.Init` (no new files added,
  so this should pass unchanged).
- [ ] `lake exe lint-style` — text linters (run `--fix` only if violations reported).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — import minimization (apply `--fix`
  only if it reports redundant imports).
- [ ] Final axiom audit: `lean_verify` on `hilbert_alg_complete_theory` and the three tier
  theorems to confirm 0 sorries / 0 new axioms across the change.

**Timing**: 0.75 hours

**Depends on**: 3

**Files to modify**:
- None (verification only). Any lint/shake `--fix` edits land in the three files already touched.

**Verification**:
- All five CI commands exit 0 (or report only auto-fixable items, which are then fixed and re-run
  green).
- `MPL.hilbert_alg_complete`, `IPL.hilbert_alg_complete`, `CPL.hilbert_alg_complete` still exist
  and type-check as corollaries.

---

## Testing & Validation

- [ ] `lake build` green (full project).
- [ ] `lake test` green (`CslibTests/`).
- [ ] `lake exe checkInitImports` green.
- [ ] `lake exe lint-style` green (after any `--fix`).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` green (after any `--fix`).
- [ ] `lean_verify`: 0 sorries, 0 new axioms on all new/modified declarations.
- [ ] Three existing tier theorems remain available with unchanged signatures.

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Algebra/Soundness.lean` — new `alg_theory_soundness`.
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaum.lean` — new
  `canonicalV_algTValid`.
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean` — new
  `hilbert_alg_complete_theory`; three tier theorems re-proved as corollaries.
- Execution summary at `summaries/01_*-summary.md` (produced by `/implement`).

## Rollback/Contingency

All changes are additive (new lemmas) plus body-only rewrites of three existing theorems whose
signatures are unchanged. If any phase fails to build:
- Revert the touched file(s) via `git checkout -- <file>` (no schema/state changes involved).
- The original tier theorems remain valid independently of the parametric theorem, so reverting
  Phase 3 alone restores the prior green state while keeping Phases 1-2 additions (which are
  self-contained and harmless).
- Because the strategy was already scratch-verified end-to-end, a build failure most likely
  indicates a universe-pinning slip (use `{Atom : Type u}` / `∀ (H : Type u)`, never `Type _`) or
  an `AxiomTheory` unfold form (use the verified `by simpa [AxiomTheory] using …`).
