# Implementation Plan: Task #306

- **Task**: 306 - Brouwerian Soundness and Completeness
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: 302 (IsOrBotFree), 303 (BrouwerianSemilattice, BrouwerianEvaluate), 305 (ConjImpAxiom)
- **Research Inputs**: specs/306_brouwerian_soundness_completeness/reports/01_brouwerian-completeness-research.md
- **Artifacts**: plans/01_brouwerian-completeness-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Prove soundness and completeness of IPL{and,imp,top} w.r.t. Brouwerian semilattices in a single new file `Cslib/Logics/Propositional/Semantics/Algebra/BrouwerianCompleteness.lean`. Soundness states that `Derivable ConjImpAxiom phi` implies `BrouwerianValid phi` for all formulas. Completeness, restricted to `IsOrBotFree` formulas, constructs the Brouwerian Lindenbaum algebra (quotient of `Proposition Atom` by `ConjImpAxiom`-derivational equivalence), proves it is a `BrouwerianSemilattice`, and uses a truth lemma to extract derivability from validity. The construction closely follows `HilbertLindenbaum.lean` but omits join/sup operations since `BrouwerianSemilattice` has no lattice join. Estimated ~400 lines total.

### Research Integration

The research report (01_brouwerian-completeness-research.md) provides the complete proof architecture:
- Soundness via 5-case analysis on `ConjImpAxiom` constructors using `BrouwerianSemilattice` lemmas (`le_himp_iff`, `himp_eq_top_iff`, `inf_le_left`, etc.)
- Critical discovery: the truth lemma MUST be restricted to `IsOrBotFree` formulas because `BrouwerianEvaluate v .bot = top` but `[bot]` is NOT the top element in the Lindenbaum algebra (no EFQ in `ConjImpAxiom`)
- Completeness theorem restricted to `IsOrBotFree`: `phi.IsOrBotFree = true -> BrouwerianValid phi -> Derivable ConjImpAxiom phi`
- `HilbertLindenbaum.lean` (727 lines) as the primary template, with the Brouwerian version being ~55% the size (no join, no orI/orE, no Sup congruence)

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Prove `conjImp_brouwerian_soundness_derivable`: `Derivable ConjImpAxiom phi -> BrouwerianValid phi` (unrestricted)
- Construct `BrouwerianLindenbaumAlgebra`: quotient of `Proposition Atom` by `ConjImpEquiv`
- Prove `BrouwerianSemilattice` instance on the Lindenbaum algebra
- Prove truth lemma for `IsOrBotFree` formulas: `BrouwerianEvaluate brouwerianCanonicalV A = brouwerianLindenbaumMk A`
- Prove `conjImp_brouwerian_complete`: `IsOrBotFree phi -> BrouwerianValid phi -> Derivable ConjImpAxiom phi`
- Prove biconditional: `IsOrBotFree phi -> (Derivable ConjImpAxiom phi <-> BrouwerianValid phi)`
- Pass CSLib CI verification (`lake build`, `checkInitImports`, `lint-style`)

**Non-Goals**:
- Bridge between `BrouwerianEvaluate` and `AlgEvaluate` (that is task 308)
- Hilbert algebra completeness for the implicational fragment (separate task)
- Extending completeness to formulas containing bot or or connectives

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `le_himp_iff` proof difficulty in Lindenbaum algebra | M | M | Follow exact structure from `hilbertLindenbaumLe_himp_iff`; use deduction theorem + andI/andE |
| Universe mismatch in `BrouwerianValid.{u,u}` instantiation | M | L | Follow `HilbertCompleteness.lean` universe annotation pattern exactly |
| Quadratic blowup from Quotient.lift proofs | L | M | Use `Quotient.sound` and existing congruence patterns from HilbertLindenbaum |
| Missing helper lemmas for `ConjImpAxiom` derivations | M | L | Reuse `hilbertCutSingletonDeriv`, `hilbertImpIDeriv`, `hilbertAndIDeriv` etc. which take explicit K/S witnesses |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Brouwerian Soundness [COMPLETED]

**Goal**: Prove that every `ConjImpAxiom`-derivable formula evaluates to top in every `BrouwerianSemilattice`.

**Tasks**:
- [ ] Create file `Cslib/Logics/Propositional/Semantics/Algebra/BrouwerianCompleteness.lean` with module header, copyright, and imports
- [ ] Define `conjImp_brouwerian_axiom_sound`: for each `ConjImpAxiom` constructor, prove `BrouwerianEvaluate v phi = top` in any `BrouwerianSemilattice`
  - `implyK`: via `himp_eq_top_iff` + `le_himp_iff` + `inf_le_left`
  - `implyS`: via `le_himp_iff` + `himp_inf_le` (parallel to Soundness.lean pattern)
  - `andI`: via `le_himp_iff` + `le_refl`
  - `andE1`: via `himp_eq_top_iff` + `inf_le_left`
  - `andE2`: via `himp_eq_top_iff` + `inf_le_right`
- [ ] Define `conjImp_brouwerian_soundness`: derivation-level soundness by induction on `DerivationTree` (ax, assumption, modus_ponens, weakening cases)
- [ ] Define `conjImp_brouwerian_soundness_derivable`: `Derivable ConjImpAxiom phi -> BrouwerianValid phi`
- [ ] Run `lake build Cslib.Logics.Propositional.Semantics.Algebra.BrouwerianCompleteness` to verify

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/BrouwerianCompleteness.lean` - Create new file (~60-80 lines for soundness section)

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.BrouwerianCompleteness` compiles without errors
- All 3 soundness theorems have no `sorry`

---

### Phase 2: Brouwerian Lindenbaum Construction and BrouwerianSemilattice Instance [COMPLETED]

**Goal**: Construct the quotient algebra `BrouwerianLindenbaumAlgebra` and prove it is a `BrouwerianSemilattice`.

**Tasks**:
- [ ] Define `ConjImpEquiv A B := Deriv ConjImpAxiom [A] B /\ Deriv ConjImpAxiom [B] A`
- [ ] Prove `conjImpEquiv_refl`, `conjImpEquiv_symm`, `conjImpEquiv_trans` (using `hilbertCutSingletonDeriv` with `ConjImpAxiom.mem_implyK`/`mem_implyS`)
- [ ] Define `conjImpPropositionSetoid` and `BrouwerianLindenbaumAlgebra` quotient type
- [ ] Define `brouwerianLindenbaumMk` quotient map
- [ ] Prove congruence lemmas:
  - `conjImpEquivAndCongr`: if `A ~ A'` and `B ~ B'` then `A.and B ~ A'.and B'` (uses `hilbertAndIDeriv`, `hilbertAndE1Deriv`, `hilbertAndE2Deriv`)
  - `conjImpEquivImpCongr`: if `A ~ A'` and `B ~ B'` then `A.imp B ~ A'.imp B'` (uses `hilbertImpIDeriv`, cut)
- [ ] Define quotient operations via `Quotient.lift2`:
  - `brouwerianLindenbaumLe`: `[A] <= [B] iff Deriv ConjImpAxiom [A] B`
  - `brouwerianLindenbaumInf`: `[A] inf [B] = [A.and B]`
  - `brouwerianLindenbaumHimp`: `[A] himp [B] = [A.imp B]`
  - Top element: `brouwerianLindenbaumMk Proposition.top` (where `Proposition.top = .imp .bot .bot`)
- [ ] Prove simp lemmas: `brouwerianLindenbaumLe_mk`, `brouwerianLindenbaumInf_mk`, `brouwerianLindenbaumHimp_mk`
- [ ] Prove `BrouwerianSemilattice` axioms on the quotient:
  - `le_refl`: via `assumption_deriv`
  - `le_trans`: via `hilbertCutSingletonDeriv`
  - `le_antisymm`: via `Quotient.sound`
  - `inf_le_left`: via `hilbertAndE1Deriv`
  - `inf_le_right`: via `hilbertAndE2Deriv`
  - `le_inf`: via `hilbertAndIDeriv` + cut
  - `le_top`: derive `[A] |- bot.imp bot` via `hilbertImpIDeriv` + assumption
  - `le_himp_iff`: forward direction via andE + impE; backward via impI + andI (the hardest axiom; follows `hilbertLindenbaumLe_himp_iff` pattern)
- [ ] Register the `BrouwerianSemilattice` instance: `brouwerianLindenbaumBSL`
- [ ] Run `lake build Cslib.Logics.Propositional.Semantics.Algebra.BrouwerianCompleteness`

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/BrouwerianCompleteness.lean` - Add Lindenbaum construction (~200-250 lines)

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.BrouwerianCompleteness` compiles without errors
- `BrouwerianSemilattice (BrouwerianLindenbaumAlgebra)` instance resolves
- All definitions and lemmas have no `sorry`

---

### Phase 3: Truth Lemma and Completeness Theorem [COMPLETED]

**Goal**: Prove the restricted truth lemma and completeness theorem for `IsOrBotFree` formulas, plus the biconditional.

**Tasks**:
- [ ] Prove `brouwerianLindenbaumMk_eq_top_iff`: `brouwerianLindenbaumMk A = top <-> Derivable ConjImpAxiom A`
  - Forward: extract `ConjImpEquiv A (bot.imp bot)`, cut with `Derivable (bot.imp bot)` (provable via impI + assumption)
  - Backward: from `Derivable ConjImpAxiom A`, show `[A] = top` via weakening
- [ ] Define `brouwerianCanonicalV`: `fun p => brouwerianLindenbaumMk (.atom p)`
- [ ] Prove `brouwerianCanonicalV_spec` (truth lemma, restricted to `IsOrBotFree`):
  ```
  A.IsOrBotFree = true ->
  BrouwerianEvaluate brouwerianCanonicalV A = brouwerianLindenbaumMk A
  ```
  - By induction on A; bot/or cases discharged by `simp [Proposition.IsOrBotFree]`
  - atom case: definitional
  - imp case: IH + `brouwerianLindenbaumHimp_mk` simp lemma
  - and case: IH + `brouwerianLindenbaumInf_mk` simp lemma
- [ ] Prove `conjImp_brouwerian_complete`: `A.IsOrBotFree = true -> BrouwerianValid A -> Derivable ConjImpAxiom A`
  - Instantiate `BrouwerianValid` at `BrouwerianLindenbaumAlgebra` with `brouwerianCanonicalV`
  - Rewrite via `brouwerianCanonicalV_spec` (using `IsOrBotFree` hypothesis)
  - Extract via `brouwerianLindenbaumMk_eq_top_iff`
- [ ] Prove biconditional `conjImp_brouwerian_iff`: `A.IsOrBotFree = true -> (Derivable ConjImpAxiom A <-> BrouwerianValid A)`
- [ ] Run `lake build Cslib.Logics.Propositional.Semantics.Algebra.BrouwerianCompleteness`
- [ ] Update `Cslib.lean` barrel import: `lake exe mk_all --module`
- [ ] Run full CI: `lake exe checkInitImports && lake exe lint-style`

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/BrouwerianCompleteness.lean` - Add truth lemma + completeness (~80-100 lines)
- `Cslib.lean` - Add import for new file (via `mk_all`)

**Verification**:
- `lake build` succeeds (full project build)
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- All theorems have no `sorry`
- `lean_verify` on `conjImp_brouwerian_complete` confirms no axioms beyond the standard ones

---

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Semantics.Algebra.BrouwerianCompleteness` compiles cleanly
- [ ] No `sorry` in final file (verify with `grep sorry BrouwerianCompleteness.lean`)
- [ ] `lake exe checkInitImports` passes (file imports `Cslib.Init`)
- [ ] `lake exe lint-style` passes
- [ ] `lean_verify` on key theorems (`conjImp_brouwerian_soundness_derivable`, `conjImp_brouwerian_complete`, `conjImp_brouwerian_iff`) confirms no sorry axioms
- [ ] Universe annotations match `BrouwerianValid.{u, u}` pattern from HilbertCompleteness.lean

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Algebra/BrouwerianCompleteness.lean` - Main implementation file (~400 lines)
- `specs/306_brouwerian_soundness_completeness/plans/01_brouwerian-completeness-plan.md` - This plan
- `specs/306_brouwerian_soundness_completeness/summaries/01_brouwerian-completeness-summary.md` - Post-implementation summary

## Rollback/Contingency

Since this creates a single new file with no modifications to existing files (other than `Cslib.lean` barrel import), rollback is trivial: delete `BrouwerianCompleteness.lean` and revert `Cslib.lean`. If the `le_himp_iff` proof in Phase 2 proves unexpectedly difficult, mark Phase 2 as [PARTIAL] and document the stuck goal state for manual intervention.
