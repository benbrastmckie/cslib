# Implementation Plan: Task #318

- **Task**: 318 - IPL conservative over IPL⟨∧,→,⊥,⊤⟩ for or-free formulas
- **Status**: [COMPLETED]
- **Effort**: 8 hours
- **Dependencies**: Tasks 303, 306, 307 (completed)
- **Research Inputs**: specs/318_ipl_conservative_over_conj_imp_bot/reports/01_conj-imp-bot-research.md
- **Artifacts**: plans/01_conj-imp-bot-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Extend the existing IPL conservative extension chain from the `{∧,→,⊤}` fragment (or-bot-free
formulas) to the `{∧,→,⊥,⊤}` fragment (or-free formulas). This requires adding bot/EFQ support
throughout: a new axiom system `ConjImpBotAxiom`, a pointed Brouwerian evaluator
`PointedBrouwerianEvaluate`, soundness and completeness via a Pointed Brouwerian Lindenbaum
Algebra with `OrderBot`, and a conservative extension proof using a new `NonemptyLowerSet`
Heyting algebra construction that preserves bot under the `Iic` embedding.

### Research Integration

The research report (01_conj-imp-bot-research.md) identified a **critical obstacle**: the task
description's claim that "the existing free join completion embedding already preserves bot" is
incorrect. `LowerSet.Iic (bot : B) = {bot}` while `(bot : LowerSet B) = empty`, confirmed by
Mathlib's `LowerSet.Iic_ne_bot`. The recommended workaround is `NonemptyLowerSet B` -- the
subtype `{S : LowerSet B // bot in S}` -- which IS a Heyting algebra where `Iic` preserves all
four operations `{inf, top, himp, bot}`. This plan follows that recommendation.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Define `ConjImpBotAxiom` with 6 constructors (K, S, andI, andE1, andE2, efq)
- Define `PointedBrouwerianEvaluate` and `PointedBrouwerianValid` for BSL+OrderBot
- Prove soundness and completeness of `ConjImpBotAxiom` w.r.t. pointed Brouwerian validity
- Construct `NonemptyLowerSet B` as a Heyting algebra with bot-preserving `Iic` embedding
- Prove `hilbertIplConservativeOverConjImpBot`: IPL conservative over ConjImpBot for or-free formulas

**Non-Goals**:
- Modifying the existing `BrouwerianSemilattice` typeclass
- Creating a new `PointedBrouwerianSemilattice` class (use mixin `[BSL] [OrderBot]` instead)
- Adding disjunction support to the pointed Brouwerian fragment
- Modifying `FreeJoinCompletion.lean` or `ConjImpConservative.lean`

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `NonemptyLowerSet` HA instance proof is nontrivial | H | M | Follow research report's verified closure analysis; test Heyting implication closure early |
| Lindenbaum `OrderBot` via efq requires careful proof engineering | M | M | Mirror `BrouwerianCompleteness.lean` pattern exactly; efq gives `[bot] <= [A]` directly |
| Or-free commutation lemma with `Iic` and custom bot_val | M | L | Induction is straightforward: bot case becomes `Iic bot = Iic bot` (trivial) |
| Universe polymorphism issues in validity quantifiers | M | L | Follow existing `BrouwerianValid.{u, u}` pattern |
| `NonemptyLowerSet` himp closure proof: need `bot in (S => T)` | M | M | Verified informally: `{bot} cap S subseteq T` holds since `bot in T`, so `bot in S => T` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |
| 3 | 4 | 1, 3 |
| 4 | 5 | 2, 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: ConjImpBotAxiom Definition and Infrastructure [IN PROGRESS]

**Goal**: Define the axiom system for IPL⟨∧,→,⊥,⊤⟩ with all supporting lemmas.

**Tasks**:
- [ ] Define `ConjImpBotAxiom` inductive with 6 constructors: `implyK`, `implyS`, `andI`, `andE1`, `andE2`, `efq`
- [ ] Prove `ConjImpAxiom.toConjImpBotAxiom` subsumption (5 cases)
- [ ] Prove `ConjImpBotAxiom.toIntPropAxiom` subsumption (via MinPropAxiom + efq)
- [ ] Define `ConjImpBotAxiom.mem_implyK` and `ConjImpBotAxiom.mem_implyS` witnesses
- [ ] Prove `subst_preserves_conjImpBotAxiom` (substitution closure)
- [ ] Prove `IsOrFree` compatibility for each constructor (6 lemmas)
- [ ] Prove `conjImpBotAxiom_hasDeductionTheorem` instance

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` -- Add `ConjImpBotAxiom` and all infrastructure

**Verification**:
- `lake build Cslib.Logics.Propositional.ProofSystem.FragmentAxioms` succeeds
- All 6 constructors type-check
- Subsumption chain: `ConjImpAxiom -> ConjImpBotAxiom -> IntPropAxiom` verified
- Deduction theorem instance resolves

**Estimated lines**: ~100

---

### Phase 2: PointedBrouwerianEvaluate and Validity [NOT STARTED]

**Goal**: Define the evaluation function and validity predicate for BSL+OrderBot semantics.

**Tasks**:
- [ ] Define `PointedBrouwerianEvaluate` -- maps `bot` to `bot` (not `top` like `BrouwerianEvaluate`), maps `or` to `top`, requires `[BrouwerianSemilattice H] [OrderBot H]`
- [ ] Define `PointedBrouwerianValid` -- universal quantification over all pointed BSLs
- [ ] Prove simp lemmas: `PointedBrouwerianEvaluate_atom`, `_bot`, `_imp`, `_and`, `_or`
- [ ] Prove or-free bridge: for `IsOrFree` formulas in a `HeytingAlgebra H`, `PointedBrouwerianEvaluate v phi = AlgEvaluate v bot phi` (via the forgetful `HA -> BSL + OrderBot` path)

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/PointedBrouwerian.lean` -- NEW file

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.PointedBrouwerian` succeeds
- `PointedBrouwerianEvaluate v (.bot) = bot` confirmed by `lean_goal`
- Bridge lemma type-checks with correct universe annotations

**Estimated lines**: ~80

---

### Phase 3: Pointed Brouwerian Soundness [NOT STARTED]

**Goal**: Prove soundness of `ConjImpBotAxiom` w.r.t. pointed Brouwerian validity.

**Tasks**:
- [ ] Prove `conjImpBot_pointedBrouwerian_axiom_sound` -- 6 cases, the efq case uses `bot_le` + `himp_eq_top_iff`
- [ ] Prove `conjImpBot_pointedBrouwerian_soundness` -- derivation tree level (match on tree constructors)
- [ ] Prove `conjImpBot_pointedBrouwerian_soundness_derivable` -- `Derivable ConjImpBotAxiom phi -> PointedBrouwerianValid phi`

**Timing**: 1 hour

**Depends on**: 1, 2

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/PointedBrouwerianCompleteness.lean` -- NEW file (first section)

**Verification**:
- All 6 axiom cases close (especially efq: `bot_le` gives `bot <= phi_val`, then `himp_eq_top_iff`)
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.PointedBrouwerianCompleteness` succeeds
- No sorries remain

**Estimated lines**: ~60

---

### Phase 4: Pointed Brouwerian Lindenbaum Algebra and Completeness [NOT STARTED]

**Goal**: Build the Lindenbaum algebra for `ConjImpBotAxiom` with `OrderBot` instance and prove completeness for or-free formulas.

**Tasks**:
- [ ] Define `ConjImpBotEquiv` (derivational equivalence for `ConjImpBotAxiom`)
- [ ] Prove `conjImpBotEquiv_refl`, `_symm`, `_trans`
- [ ] Define `conjImpBotPropositionSetoid`
- [ ] Define `PointedBrouwerianLindenbaumAlgebra` (quotient type)
- [ ] Define `pointedBrouwerianLindenbaumMk` (quotient map)
- [ ] Define order, inf, himp operations on the quotient (mirror `BrouwerianCompleteness.lean`)
- [ ] Prove congruence lemmas: `conjImpBotEquivAndCongr`, `conjImpBotEquivImpCongr`
- [ ] Prove `BrouwerianSemilattice` instance (same pattern as `brouwerianLindenbaumBSL`)
- [ ] Prove `OrderBot` instance with `bot := pointedBrouwerianLindenbaumMk .bot` and `bot_le` via efq: for any `[A]`, `Deriv ConjImpBotAxiom [.bot] A` holds via `hilbertImpEDeriv (axiom_deriv (.efq A)) (assumption_deriv ...)`
- [ ] Prove `pointedBrouwerianLindenbaumMk_eq_top_iff`: `[A] = top <-> Derivable ConjImpBotAxiom A`
- [ ] Define `pointedBrouwerianCanonicalV`: canonical valuation `x -> [atom x]`
- [ ] Prove truth lemma `pointedBrouwerianCanonicalV_spec` for `IsOrFree` formulas -- key difference from `brouwerianCanonicalV_spec`: the bot case NOW works because `PointedBrouwerianEvaluate v bot = bot = [bot]` (instead of being excluded by `IsOrBotFree`)
- [ ] Prove `conjImpBot_pointedBrouwerian_complete`: `IsOrFree phi -> PointedBrouwerianValid phi -> Derivable ConjImpBotAxiom phi`
- [ ] Prove `conjImpBot_pointedBrouwerian_iff`: biconditional version

**Timing**: 2.5 hours

**Depends on**: 1, 3

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/PointedBrouwerianCompleteness.lean` -- Continue in same file (completeness section)

**Verification**:
- `OrderBot` instance: `bot_le` proof closes via efq axiom
- Truth lemma: bot case closes with `rfl` or `simp` (both sides are `[bot]`)
- `conjImpBot_pointedBrouwerian_complete` type-checks with `IsOrFree` (not `IsOrBotFree`)
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.PointedBrouwerianCompleteness` succeeds
- No sorries

**Estimated lines**: ~280

---

### Phase 5: NonemptyLowerSet Construction and Conservative Extension [NOT STARTED]

**Goal**: Construct the `NonemptyLowerSet` Heyting algebra, prove the bot-preserving embedding lemma, and prove the conservative extension theorem.

**Tasks**:
- [ ] Define `NonemptyLowerSet B` as `{S : LowerSet B // (bot : B) in S}` (subtype)
- [ ] Prove `NonemptyLowerSet` is closed under `inf` (intersection): if `bot in S` and `bot in T` then `bot in S cap T`
- [ ] Prove `NonemptyLowerSet` is closed under `sup` (union): if `bot in S` then `bot in S cup T`
- [ ] Prove `NonemptyLowerSet` is closed under `himp`: if `bot in T` then `bot in (S => T)` because `{bot} cap S subseteq T` holds since `bot in T`
- [ ] Define `top := LowerSet.Iic top = Set.univ` and `bot := LowerSet.Iic bot = {bot}`
- [ ] Prove `HeytingAlgebra (NonemptyLowerSet B)` instance
- [ ] Define `nonemptyLowerSetIic : B -> NonemptyLowerSet B` embedding
- [ ] Prove `nonemptyLowerSetIic` preserves `inf`: `Iic (a inf b) = Iic a inf Iic b`
- [ ] Prove `nonemptyLowerSetIic` preserves `himp`: `Iic (a himp b) = Iic a himp Iic b`
- [ ] Prove `nonemptyLowerSetIic` preserves `bot`: `Iic (bot : B) = bot : NonemptyLowerSet B`
- [ ] Prove `nonemptyLowerSetIicEqTopIff`: `Iic x = top <-> x = top`
- [ ] Prove or-free embedding lemma: for `IsOrFree phi`, `AlgEvaluate (Iic . v) (bot : NonemptyLowerSet B) phi = Iic (PointedBrouwerianEvaluate v phi)` -- induction with bot case: `Iic bot = Iic bot` (trivial since `bot` in `NonemptyLowerSet` IS `Iic bot`)
- [ ] Prove embedding biconditional: `PointedBrouwerianEvaluate v phi = top <-> AlgEvaluate (Iic . v) (bot : NonemptyLowerSet B) phi = top`
- [ ] Prove `hilbertIplConservativeOverConjImpBot`: route `Derivable IntPropAxiom phi` -> `HAValid phi` -> instantiate at `NonemptyLowerSet B` -> embedding lemma -> `PointedBrouwerianValid phi` -> `conjImpBot_pointedBrouwerian_complete`
- [ ] Prove `derivableConjImpBotOfDerivableInt`: subsumption direction
- [ ] Prove `hilbertIplConservativeOverConjImpBot_iff`: biconditional for or-free formulas
- [ ] Prove `ipl_conservative_over_conjImpBot`: ND corollary
- [ ] Register new files in `Cslib.lean` via `lake exe mk_all --module`
- [ ] Run full CI pipeline: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`, `lake test`

**Timing**: 2 hours

**Depends on**: 2, 4

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/NonemptyLowerSet.lean` -- NEW file (NonemptyLowerSet HA construction + embedding lemma)
- `Cslib/Logics/Propositional/Semantics/Algebra/ConjImpBotConservative.lean` -- NEW file (conservative extension theorem)
- `Cslib.lean` -- Update barrel import (via `lake exe mk_all --module`)

**Verification**:
- `NonemptyLowerSet` HA instance: `le_himp_iff` is the key axiom to verify
- Bot preservation: `nonemptyLowerSetIic bot = bot` confirmed
- Conservative extension theorem type-checks with `IsOrFree` hypothesis
- Full CI passes: `lake build && lake exe checkInitImports && lake exe lint-style && lake test`
- `lean_verify` on the main conservative extension theorem shows no axiom violations

**Estimated lines**: ~170

---

## Testing & Validation

- [ ] `lake build` succeeds with no errors on all new files
- [ ] `lake exe checkInitImports` passes (all new files import `Cslib.Init`)
- [ ] `lake exe lint-style` passes on all new files
- [ ] `lake test` passes
- [ ] `lean_verify` on `hilbertIplConservativeOverConjImpBot` -- no sorry, no axiom violations
- [ ] `lean_verify` on `conjImpBot_pointedBrouwerian_complete` -- no sorry
- [ ] `lean_verify` on `NonemptyLowerSet` HeytingAlgebra instance -- no sorry
- [ ] The subsumption chain `ConjImpAxiom -> ConjImpBotAxiom -> IntPropAxiom` is verified
- [ ] The conservative extension chain for or-free formulas: `Derivable IntPropAxiom phi <-> Derivable ConjImpBotAxiom phi` (when `IsOrFree phi`)

## Artifacts & Outputs

- `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` -- Modified (add ConjImpBotAxiom)
- `Cslib/Logics/Propositional/Semantics/Algebra/PointedBrouwerian.lean` -- NEW (evaluator + validity)
- `Cslib/Logics/Propositional/Semantics/Algebra/PointedBrouwerianCompleteness.lean` -- NEW (soundness + Lindenbaum + completeness)
- `Cslib/Logics/Propositional/Semantics/Algebra/NonemptyLowerSet.lean` -- NEW (NonemptyLowerSet HA + embedding)
- `Cslib/Logics/Propositional/Semantics/Algebra/ConjImpBotConservative.lean` -- NEW (conservative extension)
- `specs/318_ipl_conservative_over_conj_imp_bot/plans/01_conj-imp-bot-plan.md` -- This plan

## Rollback/Contingency

All changes are additive (new files + additions to FragmentAxioms.lean). Rollback:
1. Delete the 4 new `.lean` files
2. Revert `FragmentAxioms.lean` to its pre-edit state via `git checkout`
3. Revert `Cslib.lean` barrel import via `git checkout`
4. Run `lake build` to confirm clean state

If the `NonemptyLowerSet` HA construction proves unexpectedly difficult:
- **Fallback A**: Skip Phase 5 entirely; deliver soundness+completeness (Phases 1-4) as a [PARTIAL] result. The conservative extension can be added later.
- **Fallback B**: Use a simpler construction: directly prove the conservative extension through the Lindenbaum algebra without an embedding, by showing that `HAValid` at the HA `NonemptyLowerSet(PBLA)` gives `PointedBrouwerianEvaluate` at the PBLA equals top. This avoids the generic `NonemptyLowerSet` construction but is less reusable.
