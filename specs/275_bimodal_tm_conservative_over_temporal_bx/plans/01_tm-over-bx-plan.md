# Implementation Plan: Task #275 -- Bimodal TM Conservative over Temporal BX

- **Task**: 275 - bimodal_tm_conservative_over_temporal_bx
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Dependencies**: None (soundness and completeness infrastructure exists)
- **Research Inputs**: specs/275_bimodal_tm_conservative_over_temporal_bx/reports/01_tm-over-bx-conservativity.md
- **Artifacts**: plans/01_tm-over-bx-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Prove that Bimodal TM is a conservative extension of Temporal BX for temporal formulas: if
`phi : Temporal.Formula Atom` and `phi.toBimodal` is TM-derivable, then `phi` is BX-derivable.
The proof uses the semantic bridge approach following the established pattern in
`PropositionalConservativity.lean`, with the critical addition of a validity transfer lemma
to bridge the domain mismatch between bimodal soundness (`AddCommGroup D`) and temporal
completeness (arbitrary `LinearOrder D`).

### Research Integration

The research report (01_tm-over-bx-conservativity.md) identified two approaches:

1. **Semantic bridge** (recommended): soundness + semantic bridge + completeness, following
   PropositionalConservativity.lean
2. **Syntactic derivation translation**: translate bimodal derivation trees to temporal ones

The semantic approach is chosen because it follows an established codebase pattern and
requires less infrastructure. The main technical challenge is the domain mismatch:

- **Bimodal soundness** requires `D` with `[AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D] [Nontrivial D]`
- **Temporal completeness** requires validity over ALL `D` with `[LinearOrder D] [Nontrivial D] [NoMaxOrder D] [NoMinOrder D]`

The completeness proof constructs its countermodel on `ChronicleSubtype` (a subtype of Q),
which inherits `LinearOrder` but NOT `AddCommGroup`. The plan addresses this gap through
a validity transfer lemma that extends temporal models from ChronicleSubtype-like domains
to Q (which has all required structures).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the "BX conservative extension" item in the Completed section of ROADMAP.md,
extending it from propositional conservativity to temporal conservativity.

## Goals & Non-Goals

**Goals**:
- Prove `bimodal_conservative_over_temporal` theorem
- Implement semantic bridge lemma for temporal formulas (`truthAt` vs `Satisfies`)
- Handle the domain mismatch between bimodal and temporal type constraints
- Follow the existing `PropositionalConservativity.lean` proof pattern

**Non-Goals**:
- Prove conservativity for dense/discrete frame classes (base only)
- Implement the syntactic derivation translation approach
- Prove a general "standard model property" for temporal BX
- Add `IsTemporal` or `boxFree` predicates to the bimodal formula type

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Domain mismatch blocks semantic approach | H | M | Phase 2 handles this first; fallback to syntactic approach in Phase 4 |
| Semantic bridge has unexpected complications with atom case | M | L | Atom case well-understood: `exists (ht : tau.domain t), M.valuation (tau.states t ht) p` vs `M.valuation t p`; trivial world history gives `domain = True` |
| Temporal completeness contrapositive interacts badly with extended model | H | M | Phase 2 explores multiple transfer strategies; the Q-embedding with downward-closed valuation is the primary approach |
| Argument order mismatch in untl/snce between temporal and bimodal | L | L | Research confirmed both follow Burgess convention; toBimodal preserves argument order |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Semantic Bridge Lemma [NOT STARTED]

**Goal**: Prove that for temporal formulas, bimodal `truthAt` in a constructed task model
is equivalent to temporal `Satisfies`.

**Tasks**:
- [ ] Create file `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean`
- [ ] Add module header, imports (`TemporalEmbedding`, `Soundness`, temporal `Completeness`, `Satisfies`)
- [ ] Define the task model construction: for a temporal model `M : TemporalModel D Atom` on D (with `AddCommGroup D` etc.), construct `TaskModel Atom (TaskFrame.trivialFrame)` with `valuation := fun _ p => M.valuation t p` -- but this must be parameterized to allow different times
- [ ] Actually, use the approach: `WorldState = D`, `TaskFrame` with `taskRel w d u := u = w + d`, or better: use `trivialFrame` (WorldState = Unit) with valuation `fun () p => M.valuation t p` where `t` is the evaluation point. Wait -- the valuation is FIXED per model, not per time point. So use `trivialFrame` and `M.valuation := fun () p => M.valuation t p`; then for each time `t` construct a fresh model. No -- the semantic bridge must work for ALL `t` simultaneously. The correct construction: set `WorldState = Unit`, use `trivialFrame`, set `valuation () p := True` (or any fixed value). Then `truthAt M Omega tau t (.atom p) = exists (ht : True), True`, which is always True. That's wrong.

  **Correct construction** (following the propositional pattern more carefully): The PropositionalConservativity uses `valuation := fun _ p => v p` where `v : Atom -> Prop`. For the temporal case, we need the valuation to DEPEND on time. But `TaskModel.valuation` maps `WorldState -> Atom -> Prop`, not `D -> Atom -> Prop`. In the trivial frame, `WorldState = Unit` and `WorldHistory.trivial.states t ht = ()`, so `truthAt M Omega tau t (.atom p) = exists (ht : True), valuation () p`. This equals `valuation () p` (since the existential over True is trivially witnessed).

  The temporal `Satisfies M t (.atom p) = M.valuation t p`. For the bridge to work, we need `valuation () p = M.valuation t p` for all t. But `valuation ()` is a FIXED function -- it can't depend on `t`.

  **Resolution**: We CANNOT use the trivial frame with Unit world states if we want time-dependent valuations. Instead, we need a custom task frame where `WorldState = D` and the world history maps each time point to itself as a world state. Then `valuation w p := temporal_M.valuation w p` makes the atom case work.

  Define:
  - `TaskFrame D` with `WorldState := D`, `taskRel w d u := u = w + d` (this requires `AddCommGroup D`)
  - `WorldHistory` with `domain := fun _ => True`, `states t _ := t`, `respects_task` follows from the taskRel definition
  - `TaskModel` with `valuation w p := temporal_M.valuation w p`

  Then `truthAt M Omega tau t (.atom p) = exists (ht : True), temporal_M.valuation (tau.states t True.intro) p = temporal_M.valuation t p` (since `tau.states t _ = t`).

- [ ] Prove `temporal_bridge_atom`: truthAt atom case equals Satisfies atom case
- [ ] Prove `temporal_bridge_bot`: both are False
- [ ] Prove `temporal_bridge_imp`: follows from induction hypotheses
- [ ] Prove `temporal_bridge_untl`: both use `exists s, t < s /\ ... /\ forall r, ...`; structural match since both use the same `<` on D
- [ ] Prove `temporal_bridge_snce`: symmetric to untl
- [ ] Combine into main semantic bridge theorem:
  ```lean
  theorem bimodal_truthAt_toBimodal_iff_temporal_satisfies
      {D : Type*} [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
      (M_temp : TemporalModel D Atom) (t : D)
      (phi : Temporal.Formula Atom) :
      truthAt (taskModelOfTemporal M_temp) Set.univ
        (temporalWorldHistory D) t phi.toBimodal
        <-> Satisfies M_temp t phi
  ```
- [ ] Verify with `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.TemporalConservativity`

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean` - NEW file

**Verification**:
- Semantic bridge theorem compiles without sorry
- `lake build` succeeds for this module

---

### Phase 2: Domain Mismatch Resolution [NOT STARTED]

**Goal**: Prove that if `phi.toBimodal` is TM-derivable, then `Satisfies M t phi` holds
for ALL temporal models on ALL serial linear orders (not just those with `AddCommGroup`).

This is the crux of the proof. The strategy is to show that for any `D` with
`[LinearOrder D] [Nontrivial D] [NoMaxOrder D] [NoMinOrder D]` and any temporal model M
on D, we can TRANSFER the problem to a domain that has `AddCommGroup`.

**Tasks**:
- [ ] Investigate the contrapositive approach: assume `phi` is not BX-derivable and derive a contradiction from the TM-derivability of `phi.toBimodal`. The completeness proof builds a countermodel on `ChronicleSubtype` (subtype of Q). Check if ChronicleSubtype can be given `AddCommGroup` structure, or if the temporal model can be extended to Q preserving non-satisfaction.
- [ ] **Primary strategy**: Prove a `transfer_to_addcommgroup` lemma. For any temporal model on D (without AddCommGroup), construct an equivalent temporal model on some D' (with AddCommGroup) such that satisfaction of temporal formulas at corresponding points is preserved. The construction: define a new temporal model on Z (or Q) that encodes the relevant structure of D. For temporal formulas of bounded depth, only finitely many time points matter. We can embed the relevant finite set of points order-preservingly into Z.
- [ ] **Alternative strategy** (if transfer is too complex): Prove the result directly by strengthening temporal completeness. Show that temporal completeness holds even if the validity hypothesis is restricted to D's with AddCommGroup. This works if we can show ChronicleSubtype (the countermodel domain from completeness) can be endowed with AddCommGroup structure, OR if we can modify the completeness proof to use a different countermodel domain that has AddCommGroup (e.g., construct the countermodel directly on Q instead of a subtype).
- [ ] **Fallback strategy**: Check if there exists a simpler way to get the needed type constraints. For example, if `NoMaxOrder D` and `NoMinOrder D` together with `LinearOrder D` and `Nontrivial D` allow defining an `AddCommGroup` structure on D. This is false in general (e.g., the unit interval (0,1) is a nontrivial linear order with no max/min but no group structure). However, we might be able to add an additional hypothesis or use a different formulation.
- [ ] Choose and implement the resolution strategy
- [ ] Prove the universal validity lemma:
  ```lean
  theorem temporal_valid_of_bimodal_derivable
      [Infinite Atom] [DecidableEq Atom]
      {phi : Temporal.Formula Atom}
      (h : Bimodal.Bimodal.ThDerivable phi.toBimodal)
      (D : Type) [LinearOrder D] [Nontrivial D]
      [NoMaxOrder D] [NoMinOrder D]
      (M : TemporalModel D Atom) (t : D) :
      Satisfies M t phi
  ```

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean` - add validity transfer

**Verification**:
- Universal validity lemma compiles without sorry
- All helper lemmas used are sorry-free

---

### Phase 3: Main Conservativity Theorem [NOT STARTED]

**Goal**: Combine the semantic bridge, universal validity, and temporal completeness to
prove the main theorem.

**Tasks**:
- [ ] Prove the main theorem:
  ```lean
  theorem bimodal_conservative_over_temporal
      [Infinite Atom] [DecidableEq Atom]
      {phi : Temporal.Formula Atom}
      (h : Bimodal.Bimodal.ThDerivable phi.toBimodal) :
      Temporal.ThDerivable phi
  ```
- [ ] The proof structure:
  1. Apply temporal `completeness` (needs `[Denumerable (Formula Atom)]` -- check if `[Infinite Atom] [DecidableEq Atom]` implies this or if we need to add it as a hypothesis)
  2. Introduce arbitrary D, M, t with the required constraints
  3. Apply `temporal_valid_of_bimodal_derivable` from Phase 2
- [ ] Check the exact typeclass requirements: temporal completeness needs `[Denumerable (Formula Atom)]`. This typically requires `[Denumerable Atom]` or `[Countable Atom]`. The existing conservative extension theorems use `[Infinite Atom] [DecidableEq Atom]` -- verify this suffices for `Denumerable (Formula Atom)`.
- [ ] Add `import Cslib.Init` at the top of the file
- [ ] Update `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension.lean` barrel import to include the new file (if barrel file exists)

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean` - add main theorem
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension.lean` - update barrel import (if exists)

**Verification**:
- Main theorem compiles without sorry
- `lean_verify` confirms no axioms beyond standard ones

---

### Phase 4: Verification and CI [NOT STARTED]

**Goal**: Run the full CI pipeline and ensure the new file meets all CSLib standards.

**Tasks**:
- [ ] Run `lake build` (full project build)
- [ ] Run `lake exe checkInitImports` to verify `Cslib.Init` import
- [ ] Run `lake exe lint-style` to check style compliance
- [ ] Run `lake test` for regression testing
- [ ] Run `lake exe mk_all --module` to update barrel imports if needed
- [ ] Add docstrings to all public definitions and theorems
- [ ] Verify no `sorry` remains: `lean_verify` on main theorem
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` for import minimization

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean` - lint fixes, docstrings
- `Cslib.lean` - barrel import update (if needed)

**Verification**:
- All CI checks pass
- No sorry, no lint warnings
- Docstrings on all public declarations

## Testing & Validation

- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.TemporalConservativity` builds cleanly
- [ ] `lean_verify` on `bimodal_conservative_over_temporal` reports no axioms beyond Classical/Quot
- [ ] `lake build` (full project) succeeds
- [ ] `lake test` passes
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes

## Artifacts & Outputs

- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean` - main implementation file
- `specs/275_bimodal_tm_conservative_over_temporal_bx/plans/01_tm-over-bx-plan.md` - this plan
- `specs/275_bimodal_tm_conservative_over_temporal_bx/summaries/01_tm-over-bx-summary.md` - post-implementation summary

## Rollback/Contingency

- If the semantic approach fails at Phase 2 (domain mismatch is truly unresolvable):
  1. Preserve the semantic bridge from Phase 1 (useful regardless)
  2. Pivot to the syntactic derivation translation approach (Approach B from research)
  3. This would require defining `boxFree` or `isTemporal` predicates and proving that box-free derivations can be normalized
  4. Estimated additional effort: 4-6 hours
- If the syntactic approach also fails, mark the theorem with sorry and document the gap as a known limitation requiring either a strengthened completeness theorem or a model-theoretic transfer result
- Git revert to pre-implementation state if needed: `git stash` before starting Phase 1
