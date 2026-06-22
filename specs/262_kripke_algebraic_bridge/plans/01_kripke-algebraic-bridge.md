# Implementation Plan: Task #262

- **Task**: 262 - Implement Kripke-algebraic bridge
- **Status**: [IMPLEMENTING]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: specs/262_kripke_algebraic_bridge/reports/01_kripke-algebraic-bridge.md
- **Artifacts**: plans/01_kripke-algebraic-bridge.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Create a single new file `Cslib/Logics/Propositional/Semantics/Algebra/KripkeBridge.lean` that proves upward-closed sets of a Kripke frame's preorder form a Heyting algebra via Mathlib's `LowerSet (OrderDual World)`, then connects `IForces` to `AlgEvaluate` over this algebra via a structural induction. The file adds a type alias `UpsetAlgebra`, constructor helpers (`mkUpset`, `upsetVal`, `upsetBotVal`), the main bridge theorem `kripkeAlgBridge`, and corollaries relating `IValid`/`MValid` to `HAValid`/`GHAValid`.

### Research Integration

Research report `01_kripke-algebraic-bridge.md` confirmed:
- `LowerSet (OrderDual World)` is the correct Mathlib type for upward-closed sets with subset ordering and HeytingAlgebra instance.
- The Heyting implication characterization via `le_himp_iff` matches the Kripke forcing clause for implication exactly (verified in Lean).
- All five induction cases (atom, bot, imp, and, or) are straightforward using `LowerSet.coe_inf`, `LowerSet.coe_sup`, `LowerSet.coe_bot`.
- No new axioms, typeclasses, or sorry deferral needed.
- Existing CSLib files (`Kripke.lean`, `Algebra.lean`, `Bridge.lean`) provide the necessary infrastructure.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task does not directly correspond to a ROADMAP.md item (the roadmap tracks the BimodalLogic porting effort). However, it strengthens the propositional semantics layer that underpins the algebraic completeness results referenced in the roadmap's completed Foundations/Logic section.

## Goals & Non-Goals

**Goals**:
- Define `UpsetAlgebra World` as a type alias for `LowerSet (OrderDual World)` with HeytingAlgebra instance
- Provide `mkUpset` constructor to build upset algebra elements from upward-closed predicates
- Define `upsetVal` and `upsetBotVal` to lift Kripke valuations/bot_forces to algebra elements
- Prove `kripkeAlgBridge`: `IForces v bf w phi <-> toDual w in AlgEvaluate (upsetVal v v_uc) (upsetBotVal bf bf_uc) phi`
- Prove corollaries connecting `IValid`/`MValid` to `HAValid`/`GHAValid` via the bridge (semantic path, no detour through derivability)
- Pass full CSLib CI pipeline

**Non-Goals**:
- Modifying existing files (Kripke.lean, Algebra.lean, Bridge.lean)
- Proving the reverse direction of validity corollaries that would require completeness theorems with `DecidableEq Atom`
- Adding this bridge to the Lindenbaum algebra completeness pipeline (that uses a different route)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| OrderDual coercion ceremony is verbose | M | M | The `mkUpset` constructor abstracts toDual/ofDual; keep helper lemmas for membership |
| himp characterization requires non-obvious intermediate steps | M | L | Research verified `le_himp_iff` works; use `lowerClosure` for principal lower sets if needed |
| `upsetBotVal (fun _ => False) = bot` proof is fiddly | L | M | Use `LowerSet.ext` + `LowerSet.coe_bot` + set extensionality; small auxiliary lemma |
| Mathlib import resolution slow for new file | L | L | Use `lake build Cslib.Logics.Propositional.Semantics.Algebra.KripkeBridge` for scoped builds |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Type Alias, Constructors, and Helper Lemmas [COMPLETED]

**Goal**: Establish the `UpsetAlgebra` type alias and provide constructor functions that abstract the `OrderDual` ceremony, plus membership lemmas.

**Tasks**:
- [ ] Create file `Cslib/Logics/Propositional/Semantics/Algebra/KripkeBridge.lean` with module docstring, copyright header, and imports (`Cslib.Init`, `Cslib.Logics.Propositional.Semantics.Kripke`, `Cslib.Logics.Propositional.Semantics.Algebra`, `Mathlib.Order.UpperLower.CompleteLattice`)
- [ ] Define `UpsetAlgebra (World : Type*) := LowerSet (OrderDual World)` as an abbreviation or def
- [ ] Define `mkUpset` constructor taking a predicate `P : World -> Prop` and upward-closure proof, returning `UpsetAlgebra World`
- [ ] Prove `mem_mkUpset` simp lemma: `toDual w in mkUpset P hP <-> P w`
- [ ] Define `upsetVal` lifting a Kripke valuation `v : World -> Atom -> Prop` with upward-closure proof to `Atom -> UpsetAlgebra World`
- [ ] Define `upsetBotVal` lifting `bot_forces : World -> Prop` with upward-closure proof to `UpsetAlgebra World`
- [ ] Prove `upsetBotVal_false`: `upsetBotVal (fun _ => False) _ = bot` (needed for IValid corollary)
- [ ] Verify phase builds: `lake build Cslib.Logics.Propositional.Semantics.Algebra.KripkeBridge`

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/KripkeBridge.lean` - new file

**Verification**:
- File compiles with `lake build Cslib.Logics.Propositional.Semantics.Algebra.KripkeBridge`
- `lean_verify` on key definitions shows no sorry/axiom beyond standard ones

---

### Phase 2: Bridge Theorem (kripkeAlgBridge) [COMPLETED]

**Goal**: Prove the main bridge theorem by structural induction on formulas, connecting `IForces` to `AlgEvaluate` over `UpsetAlgebra World`.

**Tasks**:
- [ ] Prove `upset_himp_char` helper lemma: `toDual w in (U himp V : UpsetAlgebra World) <-> forall w', w <= w' -> toDual w' in U -> toDual w' in V` (uses `le_himp_iff` and `lowerClosure`)
- [ ] Prove `kripkeAlgBridge` by induction on `phi : PL.Proposition Atom`:
  - [ ] Case `atom p`: unfold both sides, apply `mem_mkUpset`
  - [ ] Case `bot`: unfold both sides, apply `mem_mkUpset`
  - [ ] Case `and phi psi`: use IH + `LowerSet.coe_inf` (inf = intersection)
  - [ ] Case `or phi psi`: use IH + `LowerSet.coe_sup` (sup = union)
  - [ ] Case `imp phi psi`: use IH + `upset_himp_char`
- [ ] Add docstring to `kripkeAlgBridge` explaining it as the semantic bridge between Kripke and algebraic semantics
- [ ] Verify phase builds: `lake build Cslib.Logics.Propositional.Semantics.Algebra.KripkeBridge`

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/KripkeBridge.lean` - add bridge theorem

**Verification**:
- `kripkeAlgBridge` compiles without sorry
- `lean_verify` on `kripkeAlgBridge` shows no sorry/axiom beyond standard Lean axioms

---

### Phase 3: Corollaries, Registration, and CI Verification [IN PROGRESS]

**Goal**: Prove the validity corollaries connecting IValid/MValid to HAValid/GHAValid, update barrel imports, and pass full CI.

**Tasks**:
- [ ] Prove `iforces_iff_algEvaluate_mem` (convenient restatement of `kripkeAlgBridge` in `KripkeModel` bundled form, if useful)
- [ ] Prove `HAValid_of_IValid`: if `IValid phi` then `HAValid phi` (instantiate IValid at `UpsetAlgebra World` for arbitrary HA; direction uses the bridge)
- [ ] Prove `GHAValid_of_MValid`: if `MValid phi` then `GHAValid phi` (analogous using `upsetBotVal` with arbitrary bot)
- [ ] Add module docstring subsection documenting the semantic path vs. the syntactic path through derivability
- [ ] Run `lake exe mk_all --module` to update `Cslib.lean` barrel import
- [ ] Run `lake exe checkInitImports` to verify `Cslib.Init` is imported
- [ ] Run `lake exe lint-style` to verify style compliance
- [ ] Run `lake build` (full project build)
- [ ] Run `lake test` to verify test suite passes

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/KripkeBridge.lean` - add corollaries
- `Cslib.lean` - updated by `mk_all` to include new module

**Verification**:
- All corollaries compile without sorry
- `lake build` succeeds (full project)
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lake test` passes

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Semantics.Algebra.KripkeBridge` compiles all definitions and theorems
- [ ] `lean_verify` on `kripkeAlgBridge`, `HAValid_of_IValid`, `GHAValid_of_MValid` shows no sorry
- [ ] `lake build` (full project) succeeds with no errors
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Algebra/KripkeBridge.lean` - new file (~200-300 lines)
- `Cslib.lean` - updated barrel import (via `mk_all`)
- `specs/262_kripke_algebraic_bridge/plans/01_kripke-algebraic-bridge.md` - this plan

## Rollback/Contingency

If implementation fails:
- The single new file `KripkeBridge.lean` can be deleted with no impact on existing code
- No existing files are modified (except `Cslib.lean` barrel import, which is auto-generated)
- Revert the `Cslib.lean` change and delete `KripkeBridge.lean` to restore pristine state
