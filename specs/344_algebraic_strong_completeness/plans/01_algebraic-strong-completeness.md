# Implementation Plan: Task #344 — Algebraic Strong (Context/Theory) Completeness for the Hilbert System

- **Task**: 344 - algebraic_strong_completeness
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Dependencies**: 343 (SatisfiesTheory / `v ⊨ T` machinery; SetDerivable)
- **Research Inputs**: reports/01_algebraic-strong-completeness.md
- **Artifacts**: plans/01_algebraic-strong-completeness.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Add algebraic STRONG (context/theory) completeness for the Hilbert system, extending task 341's
weak completeness and factoring through 343's `v ⊨ T` machinery. The target theorem is the
pointwise-⊤ biconditional

```
SetDerivable Axioms Γ φ ↔
  ∀ (H) [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
    v ⊨[bot_val] AxiomTheory Axioms → SatisfiesTheory (AlgEvaluate v bot_val) Γ →
    AlgEvaluate v bot_val φ = ⊤
```

recovering 341's weak theorem as the `Γ = ∅` case. The forward (soundness) direction is a one-line
reuse of the existing `alg_theory_soundness` (Soundness.lean:200), verified by research to compile.
The backward (completeness) direction is the substantive work and uses **Route A2**: a
**Γ-relativized Lindenbaum quotient** built in a NEW file, where "provability" is
`SetDerivable Axioms Γ` instead of `Derivable Axioms`, so every `ψ ∈ Γ` evaluates to `⊤`. This is
the only sound route — the Kripke-bridge route was researched and REJECTED as unsound for the strong
case (the algebraic `= ⊤`-at-all-worlds premise is strictly stronger than per-world Kripke forcing).

**Definition of done**: the iff theorem and a `Γ = ∅` recovery lemma compile, zero `sorry`, zero new
axioms, full CI green, 341's proof files untouched.

### Research Integration

Integrated from reports/01_algebraic-strong-completeness.md:
- **Statement form** (report §3): pointwise-⊤ via `SatisfiesTheory`; the `SValid`/≤ encoding is
  DEFERRED to task 345 (a non-complete GHA lacks arbitrary infima for infinite Γ).
- **Forward direction** (report §4.1, §5.1): verified to compile via `alg_theory_soundness` reuse.
- **Backward direction** (report §4.2): Route A2 — fresh relativized quotient file.
- **Route B REJECTED** (report §4.3): Kripke bridge is unsound for the strong case; do not plan it.
- **Only new metatheorem** (report §4.2, §5.2): `setDeriv_deduction`, mirroring the proven
  `min_deriv_imp_of_union` (MinLindenbaum.lean:116); `setDeriv_cut` reduces to it +
  `SetDerivable_mp` (verified shape).
- **Reuse checks** (report §5.3): `SetDerivable_mp`, `SetDerivable_of_mem`,
  `SetDerivable_of_Derivable`, `SetDerivable_weakening`, `SetDerivable_empty_iff`,
  `alg_theory_soundness`, `deductionTheorem`, `deductionWithMem`, `removeAll` all EXIST.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided to this planning run; no ROADMAP.md consultation performed.

## Goals & Non-Goals

**Goals**:
- Prove `setDeriv_deduction : SetDerivable Axioms (insert A Γ) B → SetDerivable Axioms Γ (A.imp B)`,
  generic over `[MinimalAxioms Axioms]`, plus the one-line `setDeriv_cut` corollary.
- Build a Γ-relativized Lindenbaum quotient (GHA) in a NEW file with the top-characterization
  `relMk_eq_top_iff : relMk Axioms Γ ψ = ⊤ ↔ SetDerivable Axioms Γ ψ` and the relativized
  canonical valuation + truth lemma.
- Prove `hilbert_alg_strong_complete_theory` (pointwise-⊤ form), forward via `alg_theory_soundness`,
  backward via relativized instantiation.
- Provide a `Γ = ∅` recovery lemma certifying that 341's `hilbert_alg_complete_theory` is the
  special case (regression guard).
- Each phase ends CI-green; zero `sorry`; zero new axioms.

**Non-Goals**:
- The `SValid`/≤ (`v⟦Γ⟧ ≤ v⟦φ⟧`) encoding and any `Finset.inf` bridge — DEFERRED to task 345.
- The Kripke-bridge route (Route B) — REJECTED as unsound; not pursued.
- Route A1 (parameterizing the existing `HilbertLindenbaum.lean` construction in place) — out of
  scope here to honor the "341 untouched" invariant; may be a later refactor (task 345+).
- Editing any 341 proof file (`HilbertLindenbaum.lean`, `HilbertCompleteness.lean`,
  `Soundness.lean`, etc.).
- Touching the Prop-valued `SemanticEntails` family (343+ scope).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `setDeriv_deduction` harder than the `min_deriv_imp_of_union` template suggests | H | L | Mirror MinLindenbaum.lean:116 line-for-line; reuse generic `deductionTheorem`/`deductionWithMem`/`removeAll` (DeductionTheorem.lean) with `inst.h_K`/`inst.h_S` witnesses. If intractable, mark phase `[BLOCKED]` — never `sorry`. |
| Relativized GHA axiom transfer (≈10 lemmas) is bulkier than expected (P2 exceeds one agent run) | M | M | P2 is sized as the largest phase; if the GHA-instance lemmas + truth lemma overflow, split P2 into P2a (quotient + GHA instance) and P2b (truth lemma + `algTValid` + `satisfiesΓ`) at implementation time. Reuse existing `SetDerivable_*` lemmas to keep each lemma short. |
| Universe-metavariable mismatch against the Lindenbaum construction | M | M | Pin `{Atom : Type u}` and `(H : Type u)` to the SAME `u`, matching HilbertCompleteness.lean:64. Avoid `Type _`. |
| New file breaks `Cslib.lean` / module aggregation or `checkInitImports` | M | M | Run `lake exe mk_all --module` (or update the aggregator) after adding the file; run `checkInitImports` in every phase that touches imports. |
| Lint failures (docBlame, defLemma, simpNF, unusedSectionVars) on new declarations | M | H | Add docstrings to all new decls; `theorem`/`lemma` for Prop; match the local `SetDerivable_*` underscore naming convention; `@[simp]` only with verified LHS; use `omit` for unused section vars. Run `lake exe lint-style` per phase. |
| Accidental edit to a 341 file violates the hard invariant | H | L | Confine all new constructions to the NEW file (`HilbertLindenbaumRel.lean`) and P3's target; P1 adds only to `SemanticConsequence.lean` (343 layer, not 341). Verify with `git diff --name-only` before each commit. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel. This plan is fully sequential: each phase
consumes the lemmas the previous phase establishes.

---

### Phase 1: SetDerivable deduction metatheory [COMPLETED]

**Goal**: Establish the one genuinely new metatheorem — a deduction theorem at the `SetDerivable`
level — generic over `[MinimalAxioms Axioms]`, plus its `cut` corollary. These are the building
blocks the relativized GHA instance (P2) needs.

**Target file**: `Cslib/Logics/Propositional/Semantics/SemanticConsequence.lean` (343 layer — this
is NOT a 341 file, so the hard invariant is respected). If adding here causes import or scope
friction, fall back to a new `Cslib/Logics/Propositional/Metalogic/SetDeduction.lean`.

**Tasks**:
- [ ] Read `MinLindenbaum.lean:116` (`min_deriv_imp_of_union`) and the generic
      `deductionTheorem`/`deductionWithMem`/`removeAll`/`removeAll_subset_of_subset`
      (DeductionTheorem.lean:71,:130) to confirm signatures and the `h_K`/`h_S` witness shapes.
- [ ] Add `setDeriv_deduction (Axioms) [MinimalAxioms Axioms] {Γ A B} :
      SetDerivable Axioms (insert A Γ) B → SetDerivable Axioms Γ (A.imp B)`, mirroring
      `min_deriv_imp_of_union`: `obtain ⟨L, hL, ⟨d⟩⟩`, weaken to `A :: L`, apply
      `deductionTheorem inst.h_K inst.h_S`, then `deductionWithMem` + `removeAll` (case split on
      `A ∈ L`) to clear `A` from the list context.
- [ ] Add `setDeriv_cut (Axioms) [MinimalAxioms Axioms] {Γ A B} :
      SetDerivable Axioms (insert A Γ) B → SetDerivable Axioms Γ A → SetDerivable Axioms Γ B :=
      fun hAB hA => SetDerivable_mp (setDeriv_deduction Axioms hAB) hA` (verified shape, report §5.2).
- [ ] Add docstrings to both declarations (docBlame). Match the local `SetDerivable_*` underscore
      naming convention. Use `omit`/`variable` discipline to avoid `unusedSectionVars`.

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/SemanticConsequence.lean` — add `setDeriv_deduction`,
  `setDeriv_cut` (or a new `Metalogic/SetDeduction.lean` if scoping requires).

**Verification**:
- [ ] `lake build` of the touched module succeeds (no `sorry`, no new axioms).
- [ ] `lake exe lint-style` clean on the touched file.
- [ ] `lake exe checkInitImports` passes if imports changed.
- [ ] `git diff --name-only` shows NO 341 file touched.

---

### Phase 2: Γ-relativized Lindenbaum quotient + top characterization [COMPLETED]

**Goal**: In a NEW file, build the Γ-relativized Lindenbaum GHA — the model in which every `ψ ∈ Γ`
is `⊤` — by reusing the `HilbertLindenbaumAlgebra` construction shape with `SetDerivable Axioms Γ`
as the provability relation. Produce the relativized top-characterization and the relativized
canonical valuation + truth lemma. This is Route A2 (fresh relativized copy), chosen to keep 341
files untouched.

**Target file (NEW)**: `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaumRel.lean`.

**Tasks**:
- [ ] Define `RelEquiv Axioms Γ A B := SetDerivable Axioms Γ (A.imp B) ∧ SetDerivable Axioms Γ (B.imp A)`;
      prove it is a setoid (refl/symm/trans use `SetDerivable_of_Derivable` for identity/`hilbertImpI`
      analogues, P1 `setDeriv_deduction`/`setDeriv_cut` + `SetDerivable_mp` for trans).
- [ ] Define `RelLindenbaumAlgebra Axioms Γ := Quotient (relSetoid Axioms Γ)`, `relMk`, `relLe`
      (`relLe [A] [B] ↔ SetDerivable Axioms (insert A Γ) B`, or the `imp`-form mirroring
      `hilbertLindenbaumLe`).
- [ ] Transfer the ≈10 GHA-axiom lemmas (mirror HilbertLindenbaum.lean's `le_himp_iff` (439),
      `le_trans` (348), `le_refl` (339), `sup`/`inf`/congruence) using the
      `Deriv → SetDerivable` analogue table from report §4.2: `setDeriv_deduction` + `SetDerivable_mp`
      for himp adjunction, `setDeriv_cut` for transitivity, `SetDerivable_of_mem` for refl,
      `SetDerivable_weakening` + `SetDerivable_mp` for sup/inf congruence. Provide the
      `GeneralizedHeytingAlgebra (RelLindenbaumAlgebra Axioms Γ)` instance.
- [ ] Prove `relMk_eq_top_iff : relMk Axioms Γ ψ = ⊤ ↔ SetDerivable Axioms Γ ψ` (mirror
      `hilbertLindenbaumMk_eq_top_iff` (557): `setDeriv_deduction` + `cut`).
- [ ] Define `relCanonicalV := fun x => relMk Axioms Γ (atom x)` and `relCanonicalBotVal := relMk Axioms Γ ⊥`.
- [ ] Prove `relCanonicalV_spec` (truth lemma:
      `AlgEvaluate relCanonicalV relCanonicalBotVal A = relMk Axioms Γ A`) by structural induction
      mirroring `canonicalV_spec` (607).
- [ ] Prove `relCanonicalV_algTValid : relCanonicalV ⊨[relCanonicalBotVal] AxiomTheory Axioms`
      (axioms are `Derivable` from `[]`, hence `SetDerivable Axioms Γ` via `SetDerivable_of_Derivable`,
      then `relMk_eq_top_iff`).
- [ ] Prove `relCanonicalV_satisfiesΓ : SatisfiesTheory (AlgEvaluate relCanonicalV relCanonicalBotVal) Γ`
      (for `ψ ∈ Γ`: `SetDerivable_of_mem` gives `SetDerivable Axioms Γ ψ`, then `relMk_eq_top_iff` +
      `relCanonicalV_spec` give `= ⊤`). THIS is the step that fails for the standard `canonicalV`.
- [ ] Pin `{Atom : Type u}` and the algebra at the same universe `u`. Docstrings on all decls.

**Timing**: 2.5 hours (largest phase). Split into P2a (setoid + GHA instance) / P2b (truth lemma +
`algTValid` + `satisfiesΓ`) at implementation time if it overflows one agent run.

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaumRel.lean` — NEW file (all of the
  above).
- Module aggregator (`Cslib.lean` or the relevant `*/Algebra.lean` import hub) — add the new file
  via `lake exe mk_all --module` or manual import insertion.

**Verification**:
- [ ] `lake build` of the new module succeeds (no `sorry`, no new axioms).
- [ ] `lake exe mk_all --module` run (or aggregator updated) so the new file is tracked.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake exe lint-style` clean on the new file.
- [ ] `git diff --name-only` shows the only Algebra/ change is the NEW file (no 341 file edited).

---

### Phase 3: Strong-completeness iff + 341 recovery [NOT STARTED]

**Goal**: Prove the headline theorem and certify the `Γ = ∅` recovery of 341, then run the full CI
gate.

**Target file**: a NEW `Cslib/Logics/Propositional/Semantics/Algebra/HilbertStrongCompleteness.lean`
(preferred, keeps `HilbertCompleteness.lean` — a 341 file — untouched). Do NOT add to
`HilbertCompleteness.lean`.

**Tasks**:
- [ ] State `hilbert_alg_strong_complete_theory {Atom : Type u} (Axioms) [MinimalAxioms Axioms]
      {Γ : Set (PL.Proposition Atom)} {φ}` as the pointwise-⊤ iff (report §3 statement).
- [ ] Forward (→): `intro hd H _ v bot_val hT hΓ; obtain ⟨L, hL_sub, ⟨d⟩⟩ := hd;
      exact alg_theory_soundness d v bot_val hT (fun ψ hψ => hΓ ψ (hL_sub ψ hψ))` (report §5.1,
      verified to compile).
- [ ] Backward (←): instantiate the hypothesis at `RelLindenbaumAlgebra Axioms Γ` with
      `relCanonicalV`/`relCanonicalBotVal`, discharge `algTValid` via `relCanonicalV_algTValid` and
      `SatisfiesTheory Γ` via `relCanonicalV_satisfiesΓ`; `rw [relCanonicalV_spec]` then
      `exact relMk_eq_top_iff.mp ...` (report §4.2).
- [ ] Add `hilbert_alg_strong_complete_theory_empty` (lemma or `example`): at `Γ = ∅`, the
      `SatisfiesTheory _ ∅` premise is vacuous (`fun A hA => absurd hA (Set.not_mem_empty A)`), and
      `SetDerivable_empty_iff` collapses the statement to 341's `hilbert_alg_complete_theory`.
      Regression guard certifying "recover 341".
- [ ] (Optional, only if cheap) per-tier corollaries (MPL/IPL/CPL) mirroring
      HilbertCompleteness.lean:93/122/155.
- [ ] Docstrings on all decls; universe pinning consistent with P2.

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertStrongCompleteness.lean` — NEW file
  (theorem + recovery lemma).
- Module aggregator — add the new file (`lake exe mk_all --module`).

**Verification (FULL CI GATE)**:
- [ ] `lake build` succeeds (no `sorry`, no new axioms).
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake exe lint-style` passes.
- [ ] `lake test` (CslibTests suite) passes.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` clean (no unused/missing imports).
- [ ] `lake exe mk_all --module` confirms both new files are aggregated.
- [ ] `lean_verify` on `hilbert_alg_strong_complete_theory` and the recovery lemma reports no new
      axioms (only the standard `propext`/`Classical.choice`/`Quot.sound` as used by the existing
      341 construction).
- [ ] `git diff --name-only` confirms NO 341 proof file was edited.

---

## Testing & Validation

- [ ] `lake build` green at the end of every phase.
- [ ] `lake exe checkInitImports` green after any import change.
- [ ] `lake exe lint-style` green on every new/modified file.
- [ ] `lake test` green (Phase 3).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` green (Phase 3).
- [ ] `lake exe mk_all --module` run for each new file (P2, P3).
- [ ] Zero `sorry` and zero new axioms across all phases (`lean_verify` spot-check on the headline
      theorem).
- [ ] `Γ = ∅` recovery lemma compiles, certifying 341's `hilbert_alg_complete_theory` is the special
      case.
- [ ] 341 invariant: `git diff --name-only` shows no edits to `HilbertLindenbaum.lean`,
      `HilbertCompleteness.lean`, `Soundness.lean`, or any other 341 proof file.

## Artifacts & Outputs

- `plans/01_algebraic-strong-completeness.md` (this file)
- `Cslib/Logics/Propositional/Semantics/SemanticConsequence.lean` — `setDeriv_deduction`,
  `setDeriv_cut` (P1; or new `Metalogic/SetDeduction.lean`)
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaumRel.lean` — NEW (P2)
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertStrongCompleteness.lean` — NEW (P3)
- `summaries/01_algebraic-strong-completeness-summary.md` (on completion)

## Rollback/Contingency

- All substantive new work lives in NEW files (`HilbertLindenbaumRel.lean`,
  `HilbertStrongCompleteness.lean`); the only edits to existing files are additive declarations in
  `SemanticConsequence.lean` (343 layer) and the module aggregator. Reverting = delete the two new
  files, remove the additive declarations, and re-run `lake exe mk_all --module`.
- If `setDeriv_deduction` (P1) proves intractable: mark P1 `[BLOCKED]` and stop — do NOT introduce a
  `sorry`. The whole plan depends on it; record the blocker in the orchestrator handoff.
- If P2's GHA-axiom transfer overflows: split into P2a/P2b as noted; each sub-phase still ends
  CI-green.
- If a universe mismatch appears: re-pin `Atom`/`H` to the same `u` (do not use `Type _`); this is a
  known, fixable failure mode (report §7).
