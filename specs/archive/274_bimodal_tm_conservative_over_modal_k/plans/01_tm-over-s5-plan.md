# Implementation Plan: TM Conservative over Modal S5

- **Task**: 274 - bimodal_tm_conservative_over_modal_s5
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: None (all required infrastructure exists)
- **Research Inputs**: specs/274_bimodal_tm_conservative_over_modal_k/reports/01_tm-over-k-conservativity.md
- **Artifacts**: plans/01_tm-over-s5-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Prove that Bimodal TM is a conservative extension of Modal S5 for the modal fragment: if
`phi.toBimodal` is TM-derivable then `phi` is S5-derivable. The proof uses a semantic bridge
approach matching the existing `PropositionalConservativity.lean` pattern: (1) TM soundness
gives truth in all task models, (2) a Kripke-to-TaskModel adapter constructs a task model from
any S5 Kripke model, (3) a bridge lemma by structural induction on `Modal.Proposition` relates
bimodal `truthAt` to modal `Satisfies`, and (4) S5 completeness yields derivability.

### Research Integration

The research report (01_tm-over-k-conservativity.md) identified:

- The original "over K" statement is **false** -- TM includes full S5 modal axioms (T, 4, B, 5, K distribution) for box, so conservativity holds over S5, not K.
- The concrete counterexample: `box p -> p` (axiom T) is TM-derivable but not K-derivable.
- All required infrastructure exists: `Modal.Proposition.toBimodal`, `Bimodal.ThDerivable`, TM `soundness`, `Modal.Derivable ModalAxiom`, `s5_completeness`, `ShiftClosed`, `WorldHistory.universal`, `TaskFrame.identityFrame`.
- The semantic bridge approach (matching `PropositionalConservativity.lean`) is recommended.
- A custom task frame with `taskRel w d u := w = u` (identity regardless of duration) is needed because `identityFrame` also requires `x = 0`.
- Estimated ~150-250 lines.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Define `kripkeAdapterFrame`: a `TaskFrame Z` with `WorldState = World` and `taskRel w d u := w = u`
- Construct constant-state world histories for each Kripke world using `WorldHistory.universal`
- Prove semantic bridge lemma: `truthAt M Omega tau_w 0 phi.toBimodal <-> Modal.Satisfies m w phi`
- Prove main theorem: `bimodal_conservative_over_s5`
- Register the new file in `Cslib.Init` imports (if required by CI)

**Non-Goals**:
- Proving conservativity over other modal systems (K, T, S4, etc.)
- Syntactic/direct derivation translation approach
- Modifying existing files

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Box case in bridge lemma needs S5 equivalence class stability | H | M | Omega = equivalence class under S5 relation ensures `{u \| r w u} = {u \| r w' u}` when `r w w'` |
| ShiftClosed for non-trivial Omega (not Set.univ) | M | M | Constant-state histories are shift-invariant: `tau_w.timeShift s` has same constant state `w`, so remains in Omega |
| Universe polymorphism mismatch between S5 completeness (Type u) and TM soundness | L | L | Standard universe annotation; S5 completeness is universe-polymorphic |
| `kripkeAdapterFrame` TaskFrame axioms (forward_comp, converse) | L | L | With `taskRel w d u := w = u`, forward_comp follows from eq.trans, converse from eq.symm |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Kripke Adapter Frame and History Construction [COMPLETED]

**Goal**: Define the `kripkeAdapterFrame` task frame and the constant-state world history constructor, plus prove ShiftClosed for the adapter's Omega.

**Tasks**:
- [ ] Create new file `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ModalConservativity.lean`
- [ ] Add module docstring, copyright header, and imports (`ModalEmbedding`, `Soundness`, `S5.Completeness`)
- [ ] Define `kripkeAdapterFrame (World : Type*) : TaskFrame Z` with `WorldState := World`, `taskRel := fun w _ u => w = u`
- [ ] Prove TaskFrame axioms: `nullity_identity` (w = u iff w = u), `forward_comp` (eq.trans), `converse` (eq.symm)
- [ ] Define `kripkeAdapterHistory (w : World) : WorldHistory (kripkeAdapterFrame World)` using `WorldHistory.universal` with the proof `forall d, taskRel w d w` (which is `w = w`, i.e., `rfl`)
- [ ] Define `kripkeAdapterOmega` as the set `{kripkeAdapterHistory w' | r w w'}` parameterized by a Kripke model and world
- [ ] Prove `kripkeAdapterOmega_shiftClosed`: ShiftClosed for the adapter omega (timeShift of constant-state history with state w' is still the same history)

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ModalConservativity.lean` - new file

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ModalConservativity` compiles without errors
- All definitions type-check with correct signatures

---

### Phase 2: Semantic Bridge Lemma [COMPLETED]

**Goal**: Prove the bridge lemma relating bimodal `truthAt` on the adapter model to modal `Satisfies` on the Kripke model.

**Tasks**:
- [ ] Define `kripkeAdapterModel (m : Modal.Model World Atom) : TaskModel Atom (kripkeAdapterFrame World)` with `valuation := fun ws p => m.v ws p`
- [ ] Prove `bimodal_truthAt_toBimodal_iff_satisfies`: for S5 model `m` with world `w`, `truthAt M Omega (kripkeAdapterHistory w) 0 phi.toBimodal <-> Modal.Satisfies m w phi`
- [ ] The proof proceeds by structural induction on `phi : Modal.Proposition Atom` with four cases:
  - `atom p`: Both sides reduce to `m.v w p`; the `exists ht : True` on the truthAt side is dispatched by `True.intro`
  - `bot`: Both sides are `False`
  - `imp phi psi`: Both sides are material implication; apply IH to both subformulas
  - `box phi`: The critical case. `truthAt` quantifies over all `sigma in Omega`; `Satisfies` quantifies over all `w'` with `r w w'`. Need to show these are equivalent by:
    (a) Each `sigma in Omega` is `kripkeAdapterHistory w'` for some `w'` with `r w w'`
    (b) The IH applies at `w'` using the SAME Omega (requires S5: `r` is equivalence, so the equivalence class of `w'` equals that of `w`)
    (c) Both directions: forward maps sigma membership to accessibility, backward maps accessibility to sigma membership
- [ ] The S5 equivalence class stability argument needs: if `r` is reflexive, transitive, Euclidean, and `r w w'`, then `{u | r w u} = {u | r w' u}`. This should be proved as a helper lemma.

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ModalConservativity.lean` - add bridge lemma

**Verification**:
- Bridge lemma compiles and type-checks
- All four induction cases close without sorry

---

### Phase 3: Main Conservativity Theorem and CI [COMPLETED]

**Goal**: Compose soundness + bridge + completeness into the main theorem and pass CI verification.

**Tasks**:
- [ ] Prove `bimodal_conservative_over_s5`: `ThDerivable phi.toBimodal -> Derivable ModalAxiom phi`
  - Apply `s5_completeness`: need to show `forall World m, (refl) -> (trans) -> (eucl) -> forall w, Satisfies m w phi`
  - For given S5 model and world, extract derivation tree from `ThDerivable`, construct adapter model/omega/history, apply TM `soundness` to get `truthAt`, apply bridge lemma `.mp` to get `Satisfies`
- [ ] Run `lake exe mk_all --module` to update barrel imports if adding a new file
- [ ] Run `lake exe checkInitImports` to verify `Cslib.Init` import
- [ ] Run `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ModalConservativity`
- [ ] Run `lake exe lint-style` for style compliance
- [ ] Run `lake test` to verify no regressions

**Timing**: 0.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ModalConservativity.lean` - add main theorem
- `Cslib.lean` - updated by `mk_all` if new file added

**Verification**:
- Main theorem compiles without sorry
- Full CI pipeline passes: `lake build`, `checkInitImports`, `lint-style`, `lake test`
- `lean_verify` confirms no axioms beyond standard foundations

## Testing & Validation

- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ModalConservativity` compiles clean
- [ ] `lean_verify` on `bimodal_conservative_over_s5` reports no sorry, no non-standard axioms
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes (no regressions)

## Artifacts & Outputs

- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ModalConservativity.lean` - new file (~150-250 lines)
- `specs/274_bimodal_tm_conservative_over_modal_k/plans/01_tm-over-s5-plan.md` - this plan

## Rollback/Contingency

- If the bridge lemma's box case fails due to Omega stability issues: fall back to using `Set.univ` as Omega (universal set is trivially shift-closed), which requires proving the bridge lemma for ALL worlds rather than just accessible ones. This changes the theorem structure but remains sound.
- If universe constraints block S5 completeness application: adjust universe annotations on the adapter constructions.
- If the task frame axioms are harder than expected: use the existing `trivialFrame` (WorldState = Unit) with a modified approach where the valuation encodes world-state information differently. This would require a different bridge construction.
- Git revert: single new file, so `git rm` suffices for full rollback.
