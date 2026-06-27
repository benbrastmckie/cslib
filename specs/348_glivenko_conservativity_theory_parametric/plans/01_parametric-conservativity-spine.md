# Implementation Plan: Theory-Parametric Glivenko & Conservativity Spine

- **Task**: 348 - glivenko_conservativity_theory_parametric
- **Status**: [IN PROGRESS]
- **Effort**: 9 hours
- **Dependencies**: Task 345 (`IsMinimal`/`MinimalAxioms` inclusion bridge — planned, must land first); Task 343 (done); Task 341 (parametric algebraic completeness — done, fixed backend)
- **Research Inputs**: specs/348_glivenko_conservativity_theory_parametric/reports/01_parametric-conservativity-spine.md
- **Artifacts**: plans/01_parametric-conservativity-spine.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; CONTRIBUTING.md (full CSLib CI)
- **Type**: cslib
- **Lean Intent**: true

## Overview

Unify the **syntactic spine** of the propositional Hilbert conservativity programme by
parametrizing over the axiom set rather than restating per-fragment. The programme is three
layers: **L1** algebraic completeness (`hilbert_alg_complete_theory`, task 341 — fixed backend,
not re-derived), **L2** the syntactic subsumption + ND-bridge skeleton (the core deliverable to
parametrize), and **L3** the five completion-specific commutation lemmas (irreducibly
per-fragment — kept as explicit hypotheses, never unified). The headline deliverable is a
theory-parametric Glivenko (`hilbertGlivenko_theory`) over a classical-strength source and an
intuitionistic-strength target, plus a `conservative_via_embedding` combinator parameterised by
the bespoke L3 commutation lemma. Every existing per-tier theorem is then re-derived as a
one-line instantiation, which doubles as a hard regression guard. Definition of done: all new
parametric statements land sorry-free and axiom-free, all existing public per-tier theorems
still typecheck (as corollaries or in place), and the full CSLib CI pipeline is green.

### Research Integration

This plan is built directly on `reports/01_parametric-conservativity-spine.md`:
- **F1** -> Phase 1 `derivable_mono` (collapses six `derivableXOfDerivableY` to one-liners).
- **F2** -> Phase 1 `derivableIn_axiomTheory_iff_derivable [MinimalAxioms]` (collapses the three
  `derivableIn*Iff*` ND bridges).
- **F3** -> Phase 2 `hilbertGlivenko_theory` + `hilbertGlivenko_strength` wrapper, target pinned
  at `HAValid`/`IsIntuitionistic`.
- **F4** -> Phase 3 `conservative_via_embedding` combinator with the commutation lemma as an
  explicit hypothesis; the five completions stay distinct.
- **F5/F8** -> Phase 4 corollary-recovery map (regression guard).
- **F6** -> Phase 5 optional `AlgEvaluate_heytingHom`; verified that
  `GeneralizedHeytingHom.map_interpret` / Waring `Heyting.lean` **do not exist** — any hom
  machinery must be introduced, not reused, and cannot cover the Brouwerian/free-meet fragments.
- **F7** -> 345 reuse: strength hypotheses stated as `IPL ⊆ AxiomTheory A_int` /
  `CPL ⊆ AxiomTheory A_cl`, discharged via 345's `mem_axiomTheory = Iff.rfl` +
  `setOf_subset_setOf` adapter and `isIntuitionisticIff`/`isClassicalIff`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this plan (no roadmap path provided). The task advances the
propositional algebra conservativity programme (tasks 341/345/348/352 cluster).

## Goals & Non-Goals

**Goals**:
- Introduce `derivable_mono` and `derivableIn_axiomTheory_iff_derivable` (L2 parametric core).
- Introduce theory-parametric Glivenko `hilbertGlivenko_theory` plus an `IsClassical`/
  `IsIntuitionistic` strength wrapper.
- Introduce the `conservative_via_embedding` combinator with the commutation lemma as an
  explicit hypothesis.
- Re-derive every existing per-tier theorem (Glivenko, IPL/MPL/ConjImp/ConjImpBot/Imp
  conservativity, the `_iff_chain` biconditionals, the `derivableIn*Iff*` bridges) as
  instantiations — a hard regression guard that the public surface is unchanged.
- Pass full CSLib CI (`lake build`, `lake test`, `lake exe checkInitImports`,
  `lake exe lint-style`, `lake shake`); zero `sorry`, zero new axiom.

**Non-Goals**:
- Re-deriving or modifying L1 algebraic completeness (`hilbert_alg_complete_theory`) — treated
  as a fixed black box.
- Unifying the five L3 completions (`WithBot`, `Heyting.Regular`, `FreeMeetExtension`,
  `LowerSet`, `NonemptyLowerSet`) or their commutation lemmas behind a single hom typeclass.
- Folding classical-fragment completeness (truth-assignment / Boolean / Kalmár, task 352) into
  this algebraic spine — the classical fragments are **not** Heyting/Brouwerian-complete.
- Relying on `GeneralizedHeytingHom.map_interpret` or any Waring `Heyting.lean` (verified absent).
- Renaming the existing snake_case ND corollaries (pre-existing, out of scope).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| R1: Collapsing the classical/algebraic boundary (silently asserting Heyting/Brouwerian completeness for classical fragments — Peirce invalid in free Heyting completions) | H | M | Pin Glivenko target at `HAValid`/`IsIntuitionistic`; keep `conservative_via_embedding`'s commutation lemma an explicit hypothesis so no instantiation exists without a real embedding proof. Phase 4 regression guard catches any drift. |
| R2: Phantom Heyting-hom reuse (`GeneralizedHeytingHom.map_interpret` / Waring `Heyting.lean` do not exist) | M | H | Treat any intertwining lemma as a new (optional) asset over Mathlib `HeytingHom`; never route Brouwerian/free-meet cases through it. Phase 5 is optional and gated. |
| R3: Carrier mismatch (`IsIntuitionistic`/`IsClassical` on `Theory` (Set) vs predicate-keyed backend) | M | M | Use 345's `mem_axiomTheory = Iff.rfl` + `setOf_subset_setOf` adapter and `isIntuitionisticIff`/`isClassicalIff`; depend on 345 landing first. |
| R4: Universe pinning (`hilbert_alg_complete_theory` pins `{Atom : Type u}`/`(H : Type u)`; validity abbrevs use `.{u,u}`) | M | M | Carry explicit `.{u,u}` annotations on every parametric statement, mirroring `MPL/IPL/CPL.hilbert_alg_complete`. |
| R5: `attribute [-instance]` fragility (`MplConservativeChain.lean` suppresses `BrouwerianSemilattice.toHilbertAlgebra` to avoid a `Preorder` diamond) | M | M | Keep the combinator's `BigValid`/`SmallValid` as opaque `Prop`s so instance resolution stays at the call site; preserve the local attribute scoping. |
| R6: Import-cycle when relocating `liftDerivationTree` so per-tier files can consume `derivable_mono` | M | M | Host the foundational L2 lemmas in a low file imported by all per-tier files; relocate (do not duplicate) `liftDerivationTree`; rebuild the whole `Algebra` subtree. |
| R7: New lemmas perturb `simp`/`grind` in downstream files | L | M | Build the entire `Logics/Propositional/Semantics/Algebra` subtree each phase, not just touched files. |
| R8: 345 not yet landed when implementation starts | M | M | Phase ordering treats 345 as a hard prerequisite; if 345 is unavailable, state strength hypotheses directly as `… ⊆ AxiomTheory …` inclusions and inline the `Iff.rfl` adapter locally rather than importing 345's named lemmas. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |

Phases within the same wave can execute in parallel.

### Phase 1: L2 parametric core — `derivable_mono` + parametric ND bridge [COMPLETED]

**Goal**: Introduce the two foundational L2 parametric lemmas and place them where every per-tier
file can consume them, without re-deriving any per-tier subsumption yet.

**Tasks**:
- [ ] Decide host file for foundational L2 lemmas. Recommended: a low file in
  `Cslib/Logics/Propositional/Semantics/Algebra/` (e.g. extend `Conservative.lean` or add a new
  `ParametricSpine.lean`) that imports the definition of `liftDerivationTree` and is imported by
  the per-tier files. If a cycle would result (because `liftDerivationTree` currently lives in
  `ConjImpConservative.lean`), **relocate** `liftDerivationTree` to the foundational file and
  update imports — do not duplicate it.
- [ ] Add `derivable_mono {A₁ A₂} (h_sub : ∀ ψ, A₁ ψ → A₂ ψ) (h : Derivable A₁ φ) : Derivable A₂ φ`
  := `let ⟨d⟩ := h; ⟨liftDerivationTree h_sub d⟩` (research F1, verbatim shape). Public, docstring,
  carry `.{u,u}` if needed.
- [ ] Add `derivableIn_axiomTheory_iff_derivable (Axioms) [MinimalAxioms Axioms] {φ} :
  DerivableIn (AxiomTheory Axioms) φ ↔ Derivable Axioms φ` (research F2) by composing the generic
  `[MinimalAxioms]` `hilbert_iff_nd_*` equivalence (`Equivalence.lean:291,307`) with
  `axiomTheory_*_iff_*`. Public, docstring.
- [ ] Optionally state the inclusion-view alias of `derivable_mono` with hypothesis
  `AxiomTheory A₁ ⊆ AxiomTheory A₂` (defeq via `mem_axiomTheory = Iff.rfl`, 345) to match the
  `AxiomTheory ⊆` idiom the task names.
- [ ] `lake build` the touched file(s) and the `Algebra` subtree; confirm sorry-free, axiom-free.

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean` or new
  `Cslib/Logics/Propositional/Semantics/Algebra/ParametricSpine.lean` - host `derivable_mono`,
  `derivableIn_axiomTheory_iff_derivable`, relocated `liftDerivationTree`.
- `Cslib/Logics/Propositional/Semantics/Algebra/ConjImpConservative.lean` - remove relocated
  `liftDerivationTree`, add import (if relocation chosen).

**Verification**:
- New lemmas typecheck; `lake build` green on the subtree.
- `lean_verify` (or grep) confirms no `sorry`/`axiom` in the new decls.

---

### Phase 2: Theory-parametric Glivenko [COMPLETED]

**Goal**: Introduce the headline deliverable: a theory-parametric Glivenko over a
classical-strength source and intuitionistic-strength target, plus a strength-predicate wrapper.

**Tasks**:
- [ ] Add `hilbertGlivenko_theory (A_cl A_int) [MinimalAxioms A_cl] [MinimalAxioms A_int]
  (h_cl : ∀ φ, Derivable A_cl φ → BAValid.{u,u} φ) (h_int : ∀ φ, HAValid.{u,u} φ → Derivable A_int φ)
  (h : Derivable A_cl φ) : Derivable A_int (¬¬φ)` := `h_int _ (glivenko_algebraic (h_cl _ h))`
  (research F3, verbatim). `glivenko_algebraic` (`Glivenko.lean:88`) is already theory-agnostic.
- [ ] Add the strength wrapper `hilbertGlivenko_strength (A_cl A_int) [MinimalAxioms …]
  (hcl : CPL ⊆ AxiomTheory A_cl) (hint : IPL ⊆ AxiomTheory A_int) (h : Derivable A_cl φ) :
  Derivable A_int (¬¬φ)`, discharging `h_cl`/`h_int` through `IsClassical`/`IsIntuitionistic` via
  345's bridge (`isClassicalIff`/`isIntuitionisticIff`) plus the BA/HA soundness facts
  (`hilbert_alg_complete_theory.mp`/`.mpr`).
- [ ] **Boundary check (R1)**: keep the target pinned at `HAValid`/`IsIntuitionistic`; do not weaken
  `h_int` to a GHA target nor push the `¬¬φ` conclusion below IPL. Add a docstring note recording
  why the target cannot be weakened.
- [ ] Carry explicit `.{u,u}` annotations (R4).
- [ ] `lake build` the touched file and subtree; sorry-free, axiom-free.

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean` (or the
  `ParametricSpine.lean` host) - add `hilbertGlivenko_theory`, `hilbertGlivenko_strength`.

**Verification**:
- Both new statements typecheck and are sorry-free/axiom-free.
- Manual check that target universe and strength hypotheses match `MPL/IPL/CPL.hilbert_alg_complete`.

---

### Phase 3: `conservative_via_embedding` combinator (L3 as hypothesis) [IN PROGRESS]

**Goal**: Introduce the shared four-move conservativity skeleton as one combinator, with the
bespoke commutation/embedding lemma supplied as an explicit hypothesis — never derived from a hom
typeclass.

**Tasks**:
- [ ] Add `conservative_via_embedding (A_big A_small) {P : Proposition → Bool}
  (big_complete : ∀ φ, Derivable A_big φ → BigValid φ)
  (small_complete : ∀ φ, P φ = true → SmallValid φ → Derivable A_small φ)
  (commute : ∀ φ, P φ = true → (BigValid φ → SmallValid φ))
  (hP : P φ = true) (h : Derivable A_big φ) : Derivable A_small φ`
  := `small_complete φ hP (commute φ hP (big_complete φ h))` (research F4, verbatim).
- [ ] Keep `BigValid`/`SmallValid` as **opaque `Prop`s** (parameters), so instance resolution and
  any `attribute [-instance]` scoping (R5) stay at the call site.
- [ ] Docstring must state explicitly that `commute` is the irreducible per-completion hypothesis
  and that the combinator must **not** be specialised to a generic Heyting hom (R1/R2).
- [ ] `lake build`; sorry-free, axiom-free.

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean` (or `ParametricSpine.lean`) -
  add `conservative_via_embedding`.

**Verification**:
- Combinator typechecks standalone; no instance leakage (compiles without importing any specific
  completion).
- Sorry-free, axiom-free.

---

### Phase 4: Corollary recovery — re-derive per-tier theorems (regression guard) [NOT STARTED]

**Goal**: Re-derive every existing public per-tier theorem as an instantiation of the Phase 1-3
parametric statements, proving the public surface is preserved. This is the **hard regression
check**: existing theorem names and signatures must still hold.

**Tasks**:
- [ ] Recover the six subsumptions (`derivableConjImpOfDerivableInt`, `derivableMinOfDerivableInt`,
  `derivableIntOfDerivableProp`, `derivableImpOfDerivableInt`, `derivableConjImpBotOfDerivableInt`,
  the MPL `…OfDerivable…` chain) as `derivable_mono (fun _ h => h.toX…)` one-liners (F1/F8).
- [ ] Recover the three `derivableIn{Mpl,Ipl,Cpl}Iff…` bridges via
  `(axiomTheory_*_iff_*).trans (derivableIn_axiomTheory_iff_derivable …)` (F2/F8).
- [ ] Recover `hilbertGlivenko` / `glivenko` as
  `hilbertGlivenko_theory PropositionalAxiom IntPropAxiom (fun _ => CPL.hilbert_alg_complete.mp)
  (fun _ => IPL.hilbert_alg_complete.mpr)`; ND form via the Phase 1 bridge (F8).
- [ ] Recover each `hilbertXConservativeOverY` as a `conservative_via_embedding` instantiation at
  its own completion + commutation lemma (`WithBot`/`coe_AlgEvaluate`,
  `LowerSet`/`brouwerianEmbeddingLemma`, `NonemptyLowerSet`/`nonemptyLowerSet_evaluate_commutes`,
  `FreeMeetExtension`/`freeMeetEvaluateEq`), and the MPL chain as compositions of
  `conservative_via_embedding` + `derivable_mono` (F4/F8).
- [ ] Recover the `*_iff_chain` / `*Axiom_iff_*` biconditionals as
  `⟨conservativity, derivable_mono (toX…)⟩` anonymous constructors (F5).
- [ ] **Regression assertion**: confirm every previously-public theorem name still resolves with an
  unchanged signature (diff the public surface; no rename, no signature change). Keep each bespoke
  commutation lemma intact — do not attempt to unify L3.
- [ ] `lake build` the entire `Algebra` subtree; confirm green.

**Timing**: 2.5 hours

**Depends on**: 2, 3

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/ConjImpConservative.lean`
- `Cslib/Logics/Propositional/Semantics/Algebra/ConjImpBotConservative.lean`
- `Cslib/Logics/Propositional/Semantics/Algebra/ImpConservative.lean`
- `Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean`
- `Cslib/Logics/Propositional/Semantics/Algebra/MplConservativeChain.lean`
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean`
- `Cslib/Logics/Propositional/Semantics/Algebra/Glivenko.lean` (ND recovery only)

**Verification**:
- Full `Algebra` subtree builds; every recovered theorem typechecks.
- Public-surface diff shows no removed/renamed/changed-signature public theorem.
- Sorry-free, axiom-free across all touched files.

---

### Phase 5: Optional `AlgEvaluate_heytingHom` + full CI gate [NOT STARTED]

**Goal**: Add the optional hom-intertwining lemma only if it lands clean and demonstrably shortens
the Glivenko/`WithBot` cases; then run the complete CSLib CI pipeline as the final gate.

**Tasks**:
- [ ] (Optional) Add `AlgEvaluate_heytingHom {H K} [HeytingAlgebra H] [HeytingAlgebra K]
  (f : HeytingHom H K) (v) (bot_val) (φ) : AlgEvaluate (f ∘ v) (f bot_val) φ = f (AlgEvaluate v bot_val φ)`
  by induction reusing `map_himp/map_inf/map_sup` (research F6). **Gate**: include only if it lands
  sorry-free AND shortens the `coe_AlgEvaluate`/Glivenko cases. Do **not** route the
  Brouwerian/free-meet cases through it — those embeddings are not full homs. If it does not pay
  off, skip and record the decision in the summary.
- [ ] Ensure every new file `import Cslib.Init`; docstrings on all new public decls (docBlame);
  `theorem`/`lemma` for Prop-valued; camelCase for new names (no underscores); pre-existing
  snake_case ND corollaries left as-is.
- [ ] Run full CI: `lake build`, `lake test`, `lake exe checkInitImports`,
  `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] Fix any lint/shake/import findings; rebuild until all green.
- [ ] Final zero-debt check: grep the touched files for `sorry`/`admit`/new `axiom` — must be zero.

**Timing**: 1 hour

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/Glivenko.lean` or `Conservative.lean` - optional
  `AlgEvaluate_heytingHom`.
- Any file flagged by lint/shake.

**Verification**:
- `lake build` succeeds.
- `lake test` passes (CslibTests).
- `lake exe checkInitImports` passes.
- `lake exe lint-style` passes.
- `lake shake --add-public --keep-implied --keep-prefix` reports no unused imports.
- Zero `sorry`, zero new `axiom`.

## Testing & Validation

- [ ] `lake build` green across `Logics/Propositional/Semantics/Algebra` subtree after each phase.
- [ ] `lake test` passes.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake exe lint-style` passes (docBlame on all new public decls; camelCase new names).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no unused imports.
- [ ] Public-surface regression: every pre-existing per-tier theorem still resolves with unchanged
  signature (Phase 4).
- [ ] Boundary preserved: Glivenko target pinned at `HAValid`/`IsIntuitionistic`; combinator's
  commutation lemma remains an explicit hypothesis (no classical-fragment Heyting completeness
  asserted).
- [ ] Zero `sorry`, zero new `axiom` in all touched files.

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean` (or new `ParametricSpine.lean`):
  `derivable_mono`, `derivableIn_axiomTheory_iff_derivable`, `conservative_via_embedding`,
  relocated `liftDerivationTree`.
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean`:
  `hilbertGlivenko_theory`, `hilbertGlivenko_strength`; recovered ND bridges.
- Per-tier files (ConjImp, ConjImpBot, Imp, ConservativeChain, MplConservativeChain, Glivenko):
  per-tier theorems re-derived as instantiations (regression guard).
- Optional `AlgEvaluate_heytingHom`.
- `specs/348_glivenko_conservativity_theory_parametric/summaries/01_*-summary.md` (at /implement).

## Rollback/Contingency

- Each phase is an additive, independently-buildable commit; revert the offending phase's commit to
  restore green.
- If relocating `liftDerivationTree` (Phase 1) causes an import cycle, fall back to placing
  `derivable_mono` in `ConjImpConservative.lean` next to `liftDerivationTree` and recover only the
  subsumptions reachable without a cycle; record the limitation in the summary.
- If 345 has not landed (R8), state strength hypotheses directly as `… ⊆ AxiomTheory …` inclusions
  and inline the `mem_axiomTheory = Iff.rfl` adapter locally instead of importing 345's named
  lemmas; revisit once 345 merges.
- Phase 5's `AlgEvaluate_heytingHom` is optional — drop it entirely if it does not land clean; the
  core deliverables (Phases 1-4) stand without it.
- If any conservativity recovery in Phase 4 fails to typecheck, keep the original per-tier proof in
  place (do not delete it) and mark that recovery as deferred; the parametric statements still land.
