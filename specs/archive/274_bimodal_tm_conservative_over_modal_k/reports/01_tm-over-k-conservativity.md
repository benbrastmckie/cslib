# Research Report: Bimodal TM Conservative over Modal K

**Task**: 274 -- bimodal_tm_conservative_over_modal_k
**Session**: sess_1782161605_f646ec_274
**Date**: 2026-06-22

## Executive Summary

The stated conservativity result -- "if phi.toBimodal is TM-derivable then phi is K-derivable" -- is **false** as written. TM's axiom system includes the full S5 modal axioms (T, 4, B, 5, K distribution) for its box operator, which are strictly stronger than Modal K's single modal axiom (K distribution only). A concrete counterexample is the T axiom: `box p -> p` is TM-derivable (it is axiom `modal_t` at `FrameClass.Base`), but `box p -> p` is NOT K-derivable.

The **corrected statement** is: TM is conservative over **S5** (`Derivable ModalAxiom`) for the modal fragment. This result is provable via the semantic bridge approach and all required infrastructure exists in the codebase.

## 1. Codebase Analysis

### 1.1 The Modal Embedding

`Modal.Proposition.toBimodal` (in `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean`) maps modal formulas structurally into bimodal formulas:

```
atom p  -> Formula.atom p
bot     -> Formula.bot
imp a b -> Formula.imp a.toBimodal b.toBimodal
box a   -> Formula.box a.toBimodal
```

The embedding preserves all four primitive constructors by `rfl`. Derived connectives (neg, diamond) are also preserved.

### 1.2 TM Derivability

`Bimodal.ThDerivable` (in `Cslib/Logics/Bimodal/Metalogic/Core/DerivationTree.lean`):
```lean
def Bimodal.ThDerivable (phi : Formula Atom) : Prop :=
  Bimodal.Deriv [] phi
-- where Deriv := Nonempty (DerivationTree FrameClass.Base [] phi)
```

This is derivability from the empty context at `FrameClass.Base`.

### 1.3 Bimodal Axiom System (FrameClass.Base)

The `Bimodal.Axiom` type (in `Cslib/Logics/Bimodal/ProofSystem/Axioms.lean`) has 42 constructors. At `FrameClass.Base` (minFrameClass = Base), 37 axioms are available:

- **Propositional (4)**: imp_k, imp_s, efq, peirce
- **S5 Modal (5)**: modal_t (T), modal_4 (4), modal_b (B), modal_5_collapse (5), modal_k_dist (K)
- **BX Temporal (22)**: serial_future, serial_past, left_mono_until_G, etc.
- **Modal-Temporal Interaction (1)**: modal_future
- **Uniformity (5)**: discrete_symm_fwd, etc.

The 7 inference rules are: axiom, assumption, modus_ponens, necessitation, temporal_necessitation, temporal_duality, weakening.

### 1.4 Modal K Axiom System

`KAxiom` (in `Cslib/Logics/Modal/ProofSystem/Instances/K.lean`) has 5 constructors:

- **Propositional (4)**: implyK, implyS, efq, peirce
- **Modal (1)**: modalK (K distribution)

The 5 inference rules are: ax, assumption, modus_ponens, necessitation, weakening.

### 1.5 S5 Axiom System

`ModalAxiom` (in `Cslib/Logics/Modal/Metalogic/DerivationTree.lean`) has 8 constructors:

- **Propositional (4)**: implyK, implyS, efq, peirce
- **Modal (4)**: modalK (K), modalT (T), modalFour (4), modalB (B)

These match exactly the modal axioms in TM's `Bimodal.Axiom` (T, 4, B, K distribution; plus modal_5_collapse which is derivable from T+4+B).

## 2. Counterexample to TM-over-K Conservativity

### Concrete Counterexample

Let `phi := Modal.Proposition.box (Modal.Proposition.atom p) |>.imp (Modal.Proposition.atom p)`.

**TM-derivable**: `phi.toBimodal = Formula.box (Formula.atom p) |>.imp (Formula.atom p)`, which is exactly `Bimodal.Axiom.modal_t (Formula.atom p)`. This axiom has `minFrameClass = .Base`, so `ThDerivable phi.toBimodal` holds via a height-0 derivation tree.

**NOT K-derivable**: The T axiom (`box p -> p`) is valid only on reflexive frames, not on all frames. It is the canonical example of a formula separating K from T. Standard modal logic results (Blackburn et al., Chapter 4) confirm this.

### Root Cause

TM's box operator represents **metaphysical necessity** and is axiomatized as S5 (T + 4 + B + K + 5-collapse). This is semantically justified: in task semantics, `truthAt M Omega tau t (box phi) = forall sigma in Omega, truthAt M Omega sigma t phi`, which quantifies universally over all histories -- an inherently S5-like modality.

Modal K, by contrast, has only the K distribution axiom and imposes no frame conditions. K's box is a "minimal" normal modality.

## 3. Corrected Statement and Proof Strategy

### 3.1 Correct Theorem

```lean
theorem bimodal_conservative_over_s5 {Atom : Type*} {phi : Modal.Proposition Atom}
    (h : Cslib.Logic.Bimodal.Bimodal.ThDerivable phi.toBimodal) :
    Modal.Derivable (@Modal.ModalAxiom Atom) phi
```

This says: if `phi.toBimodal` is TM-derivable, then `phi` is S5-derivable.

### 3.2 Proof Strategy (Semantic Bridge)

The proof follows the same pattern as `bimodal_conservative_extension` (TM over CPL) in PropositionalConservativity.lean, adapted for the modal fragment:

**Step 1: TM Soundness** -- `ThDerivable phi.toBimodal` gives, via TM soundness, that `phi.toBimodal` is true at every `(M, Omega, tau, t)`.

**Step 2: Semantic Bridge Lemma** -- For any S5 Kripke model `(World, r, v)` with r reflexive, transitive, and Euclidean, and any world `w`:

Construct a task model:
- `D = Z` (integers)
- `WorldState = World` (state type is the Kripke world type)
- `taskRel w d u := (d = 0 -> w = u)` (or trivial task frame)
- For each Kripke world `w' : World`, define a world history `tau_{w'}` with `domain := fun _ => True` and `states t _ := w'` (constant state)
- Valuation: `M.valuation ws p := v ws p`
- `Omega := { tau_{w'} | r w w' }` (the equivalence class of w)

Then prove by structural induction on `phi`:
```
truthAt M Omega tau_w 0 phi.toBimodal <-> Modal.Satisfies m w phi
```

The key cases:
- **atom**: Both sides reduce to `v w p` (domain condition is trivially True)
- **bot**: Both sides are False
- **imp**: Both sides are material implication of sub-cases
- **box**: `truthAt M Omega tau_w 0 (box phi'.toBimodal)` = `forall sigma in Omega, truthAt M Omega sigma 0 phi'.toBimodal` = `forall w' with r w w', truthAt M Omega tau_{w'} 0 phi'.toBimodal` which by IH = `forall w' with r w w', Satisfies m w' phi'` = `Satisfies m w (box phi')`.

The box case requires that:
1. Omega = `{ tau_{w'} | r w w' }` so quantifying over Omega = quantifying over r-accessible worlds
2. Each `tau_{w'} in Omega` has `truthAt` matching `Satisfies m w' ...`
3. The Omega used for INNER evaluations (inside the box) must be the SAME Omega -- this works because in S5, the accessibility relation is an equivalence, so the equivalence class of any accessible world is the same as the equivalence class of w.

Point 3 is the crucial S5 requirement: if `r w w'` and `r` is an equivalence relation, then `{ u | r w u } = { u | r w' u }`. This ensures `Omega` is stable under the semantics.

**Step 3: S5 Completeness** -- Apply `s5_completeness` (from `Modal/Metalogic/Systems/S5/Completeness.lean`) to get `Derivable ModalAxiom phi`.

### 3.3 Construction Details and Challenges

**ShiftClosed requirement**: TM soundness requires `ShiftClosed Omega`. This needs `Omega` to be closed under time shifts. The construction `tau_{w'}.timeShift s` should produce another history in Omega. Since each `tau_{w'}` has constant state `w'` at all times, `tau_{w'}.timeShift s` would also have constant state `w'`, so it equals `tau_{w'}` (up to definitional equality). Thus `Omega` is shift-closed.

**WorldHistory construction**: Each `tau_{w'}` needs:
- `domain := fun _ => True` (all times in domain)
- `convex`: trivial (domain is everything)
- `states t _ := w'` (constant)
- `respects_task`: needs `taskRel w' (t - s) w'` for all s, t with s <= t. This constrains the choice of TaskFrame. Using the trivialFrame (WorldState = Unit) won't work because we need WorldState = World. We need a custom frame where `taskRel w d w` for all `d`.

A suitable TaskFrame:
```lean
def kripkeAdapterFrame (World : Type*) : TaskFrame Z where
  WorldState := World
  taskRel := fun w _ u => w = u  -- only identity tasks
  nullity_identity := ...
  forward_comp := ...
  converse := ...
```

Or more precisely, `taskRel w d u := w = u` (identity for all durations). This satisfies:
- nullity_identity: `w = u <-> w = u` (trivial)
- forward_comp: `w = u -> u = v -> w = v` (transitivity of eq)
- converse: `w = u <-> u = w` (symmetry of eq)

Then `tau_{w'}.respects_task` requires `taskRel w' (t-s) w'` = `w' = w'`, which is trivial.

### 3.4 Alternative: Direct S5 Axiom Matching

An alternative syntactic approach would:
1. Define a function `fromBimodal : Bimodal.Formula Atom -> Option (Modal.Proposition Atom)` that is the partial inverse of `toBimodal`
2. Show that each Bimodal axiom, when applied to modal-fragment formulas, either produces a ModalAxiom instance or is derivable from ModalAxiom
3. Translate the derivation tree step by step

This is more complex because TM derivations can use temporal intermediate formulas (temporal_necessitation, temporal_duality, temporal/interaction axioms). These don't map to Modal formulas. The semantic approach avoids this issue entirely.

## 4. Existing Infrastructure Inventory

| Component | Location | Status |
|-----------|----------|--------|
| `Modal.Proposition.toBimodal` | `Bimodal/Embedding/ModalEmbedding.lean` | Complete |
| `Bimodal.ThDerivable` | `Bimodal/Metalogic/Core/DerivationTree.lean` | Complete |
| TM soundness (`soundness`) | `Bimodal/Metalogic/Soundness/Soundness.lean` | Complete |
| `Modal.Derivable ModalAxiom` | `Modal/Metalogic/DerivationTree.lean` | Complete |
| S5 completeness (`s5_completeness`) | `Modal/Metalogic/Systems/S5/Completeness.lean` | Complete |
| `ShiftClosed`, `Set.univ_shift_closed` | `Bimodal/Semantics/Truth.lean` | Complete |
| `WorldHistory.trivial` | `Bimodal/Semantics/WorldHistory.lean` | Complete |
| `TaskFrame.trivialFrame` | `Bimodal/Semantics/TaskFrame.lean` | Complete |
| Semantic bridge (modal) | -- | **Needs construction** |
| Kripke adapter task frame | -- | **Needs construction** |

## 5. Recommended File Location

Following the pattern of `PropositionalConservativity.lean` and `Modal/Metalogic/Systems/K/ConservativeExtension.lean`:

**New file**: `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ModalConservativity.lean`

This file would contain:
1. `kripkeAdapterFrame`: TaskFrame with WorldState = World, identity-only tasks
2. `kripkeAdapterHistory`: WorldHistory constructor for constant-state histories
3. `bimodal_truthAt_toBimodal_iff_satisfies`: Semantic bridge lemma
4. `bimodal_conservative_over_s5`: Main conservativity theorem

## 6. Dependencies

Imports needed:
- `Cslib.Logics.Bimodal.Embedding.ModalEmbedding`
- `Cslib.Logics.Bimodal.Metalogic.Soundness.Soundness`
- `Cslib.Logics.Modal.Metalogic.Systems.S5.Completeness`
- `Mathlib.Algebra.Order.Group.Int`
- `Mathlib.Data.Int.Basic`

## 7. Risk Assessment

| Risk | Level | Mitigation |
|------|-------|------------|
| Box case in semantic bridge requires S5 closure | Medium | Omega = equivalence class is self-stable under S5 |
| ShiftClosed for non-trivial Omega | Medium | Constant-state histories are shift-invariant |
| Universe constraints (S5 completeness needs `Type u`) | Low | Standard universe polymorphism |
| Task frame construction validity | Low | Identity task relation satisfies all frame axioms |

## 8. Recommendation

**TASK DESCRIPTION NEEDS CORRECTION**: The task description should be updated to:

> Prove that Bimodal TM is conservative over Modal S5 for the modal fragment:
> if phi.toBimodal is TM-derivable then phi is S5-derivable.

The proof is achievable with moderate effort. The semantic bridge approach (matching PropositionalConservativity.lean) is recommended. All required components exist in the codebase; only the adapter construction and bridge lemma need to be written.

Estimated implementation complexity: ~150-250 lines of Lean code, primarily:
- ~30 lines: Kripke adapter frame + history construction
- ~60-80 lines: Semantic bridge lemma (induction on phi, 4 cases)
- ~30 lines: Main theorem (compose soundness + bridge + completeness)
- ~30-50 lines: Supporting lemmas (ShiftClosed, domain membership, etc.)
