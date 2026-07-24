# Implementation Plan: BX⁺ metric tense base

- **Task**: 449 - define_bxplus_metric_tense_base
- **Status**: [COMPLETED]
- **Effort**: 4 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_bxplus-metric-tense-survey.md
- **Artifacts**: plans/01_bxplus-metric-tense-plan.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Introduce `BX⁺`, the metric tense logic sound over ordered-abelian-group time, as a new
Temporal frame class layered above `Base` (`Base < Metric`, incomparable to `Dense`/`Discrete`).
The work is a clean mirror of the existing `Dense` layering: add a 4th `FrameClass` constructor
and four pure-temporal uniformity axioms gated to `.Metric`, then prove soundness of those axioms
over ordered-abelian-group frames and extend Temporal derivation soundness to `FrameClass.Metric`
with a `BXPlusDerivable` abbreviation. Research verdict is GREEN and low-risk: every load-bearing
claim was machine-verified with `lake env lean` (exit 0), two of the four soundness proofs were
fully reproduced in the temporal `Satisfies` semantics and compiled clean, and the remaining plumbing
is already frame-class-parameterized. Definition of done: no `sorry`, no vacuous defs, house-style
docstrings on every new declaration, and full CI green (`lake build` / `checkInitImports` / `lint` /
`lint-style` / `test`). The conservativity theorem and box-necessity handling are out of scope.

### Research Integration

The plan is built directly on `reports/01_bxplus-metric-tense-survey.md`, which supplies:
verified frame-class instance extension (all three `FrameClass` instances use
`cases … <;> …` and extend automatically to a 4th constructor); the exact four axiom constructor
shapes (`untl bot top`-based, mirroring `dense_indicator`); the `minFrameClass` gating lines; the
machine-verified per-axiom soundness proofs (`discrete_symm_fwd_sound`, `discrete_propagate_fwd_sound`
ported verbatim from `Bimodal/.../Soundness.lean:451-511`, the two `bwd` variants as swap-duals);
the key simplification that a nontrivial ordered abelian group auto-synthesizes `NoMaxOrder`/
`NoMinOrder` (so the metric hypotheses are only `[AddCommGroup D] [LinearOrder D]
[IsOrderedAddMonoid D] [Nontrivial D]`); and the identification of the exactly TWO mandatory
exhaustive-match ripple sites (`Soundness.lean:78` `axiom_sound`, `DenseSoundness.lean:88`
`axiom_sound_dense`), each needing four absurd-discharge cases like the existing `density`/
`dense_indicator` cases at `Soundness.lean:325-326`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this dispatch (no roadmap_path provided; roadmap_flag not set).

## Goals & Non-Goals

**Goals**:
- Add `FrameClass.Metric` with `Base < Metric` in `ProofSystem/Axioms.lean`, extending the `LE`,
  `DecidableRel`, `PartialOrder`, and `base_le` instances.
- Add the four pure-temporal uniformity axioms (`discrete_symm_fwd`, `discrete_symm_bwd`,
  `discrete_propagate_fwd`, `discrete_propagate_bwd`) to `inductive Axiom`, gated to `.Metric` in
  `Axiom.minFrameClass`.
- Repair the two exhaustive `cases h_ax with` sites so the codebase compiles after adding the four
  constructors (`axiom_sound`, `axiom_sound_dense`).
- Create `Metalogic/MetricSoundness.lean` proving the four axioms sound over ordered-abelian-group
  frames, plus `axiom_sound_metric`, `swap_valid_of_valid_metric`, `soundness_metric`,
  `soundness_thderivable_metric`, and the `BXPlusDerivable` abbreviation.
- Wire the new module into the barrel and `Cslib.lean`; pass full CI with zero debt.

**Non-Goals**:
- The conservativity theorem (`TM` over `BX⁺`) — deferred to the follow-up task.
- The `discrete_box_necessity` (`χ → □χ`) axiom — it has no pure-temporal form; explicitly deferred.
- Relocating `DerivFc`/`ThDerivableFc` out of `DenseMCS.lean` to a neutral module — nice-to-have,
  out of scope (avoid scope creep).
- Introducing any new notation typeclass or `@[simp]` lemma.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| One of the two exhaustive-match sites is missed | M | L | Hard compile error is self-announcing; Phase 1 verification is a green `lake build` that fails loudly if a case is missing. |
| `import` layering for `ThDerivableFc` pulls dense-completeness baggage | L | M | Define `BXPlusDerivable` via `ThDerivableFc FrameClass.Metric` importing only `DenseMCS`; fallback is inline `Nonempty (DerivationTree FrameClass.Metric [] φ)` if the dense dependency is undesirable. |
| Soundness proof rewritten with `omega`/`aesop` instead of the settled `calc` spine | M | L | Axioms are abstract ordered-abelian-group arithmetic (not ℤ/ℕ); port the verified term-style `calc` proofs verbatim — `omega` does not apply. |
| Lint failures (docBlame, defsWithUnderscore, dupNamespace) | M | M | House-style docstring on every new declaration; `BXPlusDerivable` is lowerCamelCase with `@[nolint dupNamespace]`; axiom constructor underscores are exempt (constructors, not defs). |
| Missing `Cslib.Init` transitive import in the new module | L | L | First import is `Cslib.Logics.Temporal.Metalogic.Soundness` (resolves `Cslib.Init` transitively); confirm via `lake exe checkInitImports` in Phase 4. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel. This plan is fully sequential: each phase is
one agent run and independently green-committable.

### Phase 1: FrameClass.Metric, four axioms, minFrameClass gating, exhaustive-match repair [COMPLETED]

- **Goal:** Add the metric frame class and the four uniformity axioms to `ProofSystem/Axioms.lean`,
  gate them to `.Metric`, and repair the two exhaustive-match sites so the whole library builds.
- **Tasks:**
  - [x] Add `| Metric` to `inductive FrameClass` (`Axioms.lean:40-44`).
  - [x] Extend the `LE` instance: add `| .Metric, .Metric => True` before the `_, _ => False`
    catch-all (yields `Base < Metric`, incomparable to `Dense`/`Discrete`). The
    `DecidableRel`, `PartialOrder`, and `FrameClass.base_le` bodies extend automatically
    (`cases … <;> …`); confirm they need no manual edits.
  - [x] Update the `FrameClass` docstring to mention `Metric` (metric / ordered-abelian-group time).
  - [x] Add the four axiom constructors to `inductive Axiom` as a "Layer: Metric Uniformity" block,
    each a house-style docstring saying "metric uniformity / homogeneity of ordered-abelian-group
    time" (NOT "discreteness"): `discrete_symm_fwd` (`U(⊥,⊤) → S(⊥,⊤)`), `discrete_symm_bwd`
    (`S(⊥,⊤) → U(⊥,⊤)`), `discrete_propagate_fwd` (`U(⊥,⊤) → G(U(⊥,⊤))`), `discrete_propagate_bwd`
    (`U(⊥,⊤) → H(U(⊥,⊤))`). Use the exact shapes from the research report §2.
  - [x] Gate the four constructors in `Axiom.minFrameClass` to `.Metric` before the `| _ => .Base`
    catch-all.
  - [x] Repair `Metalogic/Soundness.lean` `axiom_sound` (the `cases h_ax with` at line ~78): add four
    cases discharged by `exact absurd _h_fc (by simp [Axiom.minFrameClass, LE.le])` (since
    `.Metric ≰ .Base`), identical to the `density`/`dense_indicator` cases at lines 325-326.
  - [x] Repair `Metalogic/DenseSoundness.lean` `axiom_sound_dense` (the `cases h_ax with` at line ~88):
    add four cases discharged the same way (since `.Metric ≰ .Dense`).
  - [x] Confirm no other file matches exhaustively on the whole `Axiom` inductive (research verified
    only these two; re-check with `grep -rn "cases h_ax with" Cslib/Logics/Temporal`). Confirmed:
    only `Soundness.lean:78` and `DenseSoundness.lean:88` match, and full `lake build` (640/640
    jobs) is green.
- **Timing:** ~1 hour
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` — new frame-class constructor, instance edit,
    four axiom constructors, `minFrameClass` gating, docstrings.
  - `Cslib/Logics/Temporal/Metalogic/Soundness.lean` — four absurd cases in `axiom_sound`.
  - `Cslib/Logics/Temporal/Metalogic/DenseSoundness.lean` — four absurd cases in `axiom_sound_dense`.
- **Verification:**
  - `lake build` is green (a missing exhaustive case is a hard, self-announcing compile error).
  - No new `sorry`; every new declaration has a docstring.

### Phase 2: MetricSoundness.lean — four axiom soundness proofs + axiom_sound_metric [COMPLETED]

- **Goal:** Create the new module and prove each of the four uniformity axioms sound over
  ordered-abelian-group frames, then assemble `axiom_sound_metric`.
- **Tasks:**
  - [x] Create `Cslib/Logics/Temporal/Metalogic/MetricSoundness.lean` with the license header,
    `module`, and `public import Cslib.Logics.Temporal.Metalogic.Soundness`.
  - [x] Prove `discrete_symm_fwd_sound` and `discrete_propagate_fwd_sound` (verbatim ports of the
    machine-verified term-style `calc` proofs from the research report §3 / `Bimodal/.../Soundness.lean`
    `discrete_symm_fwd_valid`, `discrete_propagate_fwd_valid`), under
    `[AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]`.
  - [x] Prove `discrete_symm_bwd_sound` and `discrete_propagate_bwd_sound` as the past mirrors
    (templates `discrete_symm_bwd_valid`/`discrete_propagate_bwd_valid`); same arithmetic spine.
  - [x] Assemble `axiom_sound_metric` under `[AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [Nontrivial D]`: the four new constructors dispatch to the `*_sound` lemmas; `density`/
    `dense_indicator` discharge by `absurd` (`.Dense ≰ .Metric`); all Base axioms delegate to
    `axiom_sound … (FrameClass.base_le _) M t` (copy the delegation block from `axiom_sound_dense`,
    `DenseSoundness.lean:91-124`, changing only the frame-class name). Base delegation type-checks
    with no explicit `NoMaxOrder`/`NoMinOrder` (Mathlib synthesizes them from the metric hypotheses)
    *(deviation: altered -- required adding explicit `public import Mathlib.Algebra.Order.Group.Defs`
    for the `NoMaxOrder`/`NoMinOrder` auto-synthesis instances to resolve; the two candidate imports
    named in the research report did not carry that instance)*.
  - [x] House-style docstring on every new theorem; use `theorem` (Prop-valued), not `def`.
  - [x] Use the settled `calc` lemma spine (`sub_lt_self`, `sub_pos`, `add_lt_add_left`,
    `sub_add_cancel`, `add_sub_sub_cancel`, `sub_sub_cancel`); do NOT substitute `omega`/`aesop`.
- **Timing:** ~1.5 hours
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Logics/Temporal/Metalogic/MetricSoundness.lean` (new) — four `*_sound` theorems,
    `axiom_sound_metric`.
- **Verification:**
  - `lake build` compiles the new module green; no `sorry`.
  - `axiom_sound_metric` type-checks with the four metric instance hypotheses only.

### Phase 3: Derivation soundness at Metric + BXPlusDerivable [COMPLETED]

- **Goal:** Extend Temporal derivation soundness to `FrameClass.Metric` and add the `BX⁺`
  derivability abbreviation.
- **Tasks:**
  - [x] Prove `swap_valid_of_valid_metric` (mirror of `swap_valid_of_valid_dense`,
    `DenseSoundness.lean:141-151`): transfer a metric-valid φ to `swapTemporal φ` via the `OrderDual`
    model. `OrderDual D` preserves all six instances (`AddCommGroup`, `LinearOrder`,
    `IsOrderedAddMonoid`, `Nontrivial`, `NoMaxOrder`, `NoMinOrder`) — verified — so the hypothesis
    re-instantiates at `OrderDual D` *(deviation: altered -- required an additional
    `public import Mathlib.Algebra.Order.Monoid.OrderDual` for the `IsOrderedAddMonoid Dᵒᵈ`/
    `AddCommGroup Dᵒᵈ` transfer instances beyond the imports added in Phase 2)*.
  - [x] Prove `soundness_metric` (mirror of `soundness_dense`): `match` on the `DerivationTree`
    constructors (`.axiom`→`axiom_sound_metric`, `.assumption`, `.modus_ponens`,
    `.temporal_necessitation`, `.temporal_duality`→`swap_valid_of_valid_metric`, `.weakening`).
  - [x] Prove `soundness_thderivable_metric : ThDerivableFc FrameClass.Metric φ → Satisfies M t φ`
    over the metric domain (mirror `soundness_thderivable_dense`).
  - [x] Add `Temporal.BXPlusDerivable (φ : Formula Atom) : Prop := Temporal.ThDerivableFc
    FrameClass.Metric φ` with a house-style docstring and `@[nolint dupNamespace]` (mirror
    `Temporal.ThDerivableFc`, `DenseMCS.lean:66`). Add `import`/`public import` of `DenseMCS` (for
    `ThDerivableFc`) to `MetricSoundness.lean`; fallback is inline
    `Nonempty (DerivationTree FrameClass.Metric [] φ)` if the dense dependency is undesirable.
  - [x] Ensure `BXPlusDerivable` is a genuine `Prop` abbreviation (not `def X := True`); lowerCamelCase.
- **Timing:** ~1 hour
- **Depends on:** 2
- **Files to modify:**
  - `Cslib/Logics/Temporal/Metalogic/MetricSoundness.lean` — `swap_valid_of_valid_metric`,
    `soundness_metric`, `soundness_thderivable_metric`, `BXPlusDerivable`; add `DenseMCS` import.
- **Verification:**
  - `lake build` green; no `sorry`.
  - `soundness_thderivable_metric` and `BXPlusDerivable` type-check over the metric domain.

### Phase 4: Barrel wiring + full CI [COMPLETED]

- **Goal:** Wire the new module into the import graph and pass the full zero-debt CI pipeline.
- **Tasks:**
  - [x] Add `public import Cslib.Logics.Temporal.Metalogic.MetricSoundness` to the barrel
    `Cslib/Logics/Temporal/Metalogic.lean`.
  - [x] Run `lake exe mk_all --module` to register the new file in `Cslib.lean`.
  - [x] Run `lake exe cache get` (if needed), then `lake build`.
  - [x] Run `lake exe checkInitImports` — confirm `Cslib.Init` resolves transitively via the import
    chain.
  - [x] Run `lake lint`, `lake exe lint-style`, and `lake test`; resolve any docBlame /
    defsWithUnderscore / dupNamespace / simpNF / unusedSectionVars findings (prefix intentionally
    unused `_h_fc`/variables with `_`). Zero findings across all four commands; no resolution
    needed. `lake shake` also checked (informational, not in this plan's Testing & Validation
    gate): the four touched files surface only the same pre-existing repo-wide `Cslib.Init`/
    public-import normalization backlog already present throughout the codebase, not new debt.
- **Timing:** ~0.5 hour
- **Depends on:** 3
- **Files to modify:**
  - `Cslib/Logics/Temporal/Metalogic.lean` — barrel import.
  - `Cslib.lean` — regenerated by `mk_all` (do not hand-edit).
- **Verification:**
  - Full CI green: `lake build` → `lake exe checkInitImports` → `lake lint` →
    `lake exe lint-style` → `lake test`, all exit 0.
  - Zero debt: no `sorry`, no vacuous defs, docstrings on every new declaration.

## Testing & Validation

- [x] `lake build` exits 0 after each phase (green, independently committable).
- [x] `lake exe checkInitImports` passes (new module resolves `Cslib.Init`).
- [x] `lake lint` passes (docBlame: docstrings on all new declarations; defLemma: soundness results
  are `theorem`s).
- [x] `lake exe lint-style` passes.
- [x] `lake test` passes.
- [x] No `sorry` anywhere in the new/edited files (`grep -rn "sorry" Cslib/Logics/Temporal`
  confirms zero actual `sorry` tactic uses in the whole Temporal tree; the only textual hits are
  docstring mentions of "sorry-free" in `Tableau/Completeness.lean`, task 425's territory).
- [x] `BXPlusDerivable` is a real `Prop` abbreviation, not a vacuous `def X := True`.
- [x] The two exhaustive-match sites (`axiom_sound`, `axiom_sound_dense`) compile with the four new
  absurd cases.

## Artifacts & Outputs

- `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` (modified) — `FrameClass.Metric`, four axioms,
  `minFrameClass` gating.
- `Cslib/Logics/Temporal/Metalogic/Soundness.lean` (modified) — four absurd cases in `axiom_sound`.
- `Cslib/Logics/Temporal/Metalogic/DenseSoundness.lean` (modified) — four absurd cases in
  `axiom_sound_dense`.
- `Cslib/Logics/Temporal/Metalogic/MetricSoundness.lean` (new) — metric soundness + `BXPlusDerivable`.
- `Cslib/Logics/Temporal/Metalogic.lean` (modified) — barrel import.
- `Cslib.lean` (regenerated) — new module registration.
- `specs/449_define_bxplus_metric_tense_base/summaries/01_bxplus-metric-tense-summary.md` (on completion).

## Rollback/Contingency

- Each phase is a self-contained green-committable unit; revert is per-phase via `git revert` of the
  phase commit.
- If Phase 1's exhaustive-match repair reveals an additional (unanticipated) exhaustive site, add the
  same four absurd cases there — a hard compile error makes any missed site self-announcing.
- If the `DenseMCS` import for `ThDerivableFc` proves undesirable (dense-completeness baggage), fall
  back to defining `BXPlusDerivable` inline via `Nonempty (DerivationTree FrameClass.Metric [] φ)`
  (both routes verified equivalent for this purpose).
- The whole task is additive (new frame class, new axioms gated to `.Metric`, new module); no existing
  behavior is changed, so reverting the plan's commits restores the pre-task state exactly.
