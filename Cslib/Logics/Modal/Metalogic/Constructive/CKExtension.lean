/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Constructive.CKTruthLemma

/-! # Frame-Condition-Parametrized Extensions of the Segment Canonical Model

This module is the shared scaffold for task 501 (constructive modal extensions `CT`/`CS4`/`CS5`
of `CK`, over the Wijesekera-style fallible-world segment semantics). It generalizes the task-493
segment canonical-model framework (`CKValid`, `ck_completeness`, `CKTruthLemma.lean`) to
validity/completeness over a restricted *class* of fallible-world models, cut out by an arbitrary
frame condition `FC` on the modal relation `r`. This lets each per-system file (`CT.lean`,
`CS4.lean`, `CS5.lean`) bolt its frame condition onto validity/completeness without touching any
task-493 asset.

Unlike task 494's birelational `Extension.lean` (which is **not** reused here — bare `CK` is
incomplete for the birelational `BForces` semantics; see `CK.lean`'s module docstring), this
scaffold is segment-based: the sound-and-complete semantics for every `CK` extension is
`CKForces`/`CKValid` (the ∀∃ diamond, no `F1`/`F2` confluence) restricted to frames whose modal
relation additionally satisfies `FC`.

**The completeness scaffold is deliberately abstract over the canonical `World` type** (not
pinned to `CKSegment Axioms`): the primary implementation challenge of task 501 is that the frame
conditions `ctFC`/`cs4FC`/`cs5FC` do **not** hold globally on raw `CKSegment Axioms` (a
consistent-head segment with tail `{Set.univ}` is well-formed but not `cmreach`-reflexive, e.g.).
Each per-system file therefore builds its canonical model over a **restricted world subtype**
(e.g. `CTSegment`) carrying the frame condition as an invariant, and supplies
`ckvalidFC_completeness` with a `realize` witness transported along the subtype's `.seg`
projection — the truth lemma itself (`ck_truth_lemma`) is reused unchanged on `CKSegment Axioms`.

## Main Definitions

- `CKValidFC`: frame-condition-parametrized segment validity — a copy of `CKValid`
  (`Forcing.lean:159`) with one extra hypothesis `FC r`. `CKValid` itself is untouched;
  `CKValid` is the special case `FC := fun _ => True` (`ckValid_iff_ckValidFC_true`).
- `ctFC`/`cs4FC`/`cs5FC`: the ≤-composed ("order-saturated") frame-condition predicates for `T`,
  `S4`, and `S5`. Because `CKValid` frames carry no `F1`/`F2` confluence, the box-form axioms
  (`tBox`/`fourBox`/`bBox`) need the ≤-saturated clause; the diamond-form axioms
  (`tDia`/`fourDia`/`bDia`) need only the plain clause, which the ≤-composed one implies via
  `le_refl`. Defined locally over `[Preorder World]` — **not** Mathlib's deprecated
  `Reflexive`/`Transitive`/`Symmetric`.
- `ckvalidFC_completeness`: a segment analogue of `ivalidFC_completeness`
  (`Intuitionistic/Extension.lean:97`), abstracted over an arbitrary canonical `World` type
  (rather than committed to `CKSegment Axioms`) so that it can be instantiated over a world
  subtype. Takes `h_canonFC : FC r` and a `realize` witness (any underivable formula is refuted
  at some world of the model) and concludes derivability from `CKValidFC FC`-validity.
- `axiom_mem_head`: a one-line helper (`Axioms φ → φ ∈ s.head` for a `CKSegment Axioms`) used by
  every per-extension canonical-closure proof, the segment analogue of task 494's `axiom_mem`.

## References

* [D. Wijesekera, *Constructive modal logics I*][Wijesekera1990], Definition 1.1.4.
* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (the frame classes for `T`/`S4`/`S5`, mirrored here in ≤-composed form).
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

variable {Atom : Type u}

/-! ## Frame-Condition-Parametrized Segment Validity -/

/-- A formula is `FC`-frame-valid (`CKValidFC`) if it is `CKForces`-forced at every world in
every fallible-world model whose modal relation `r` additionally satisfies the frame condition
`FC` (e.g. `ctFC`, `cs4FC`, `cs5FC`), on top of the usual upward-closure and explosion
conditions of `CKValid` (`Forcing.lean:159`). `CKValid` itself is the special case
`FC := fun _ => True` (`ckValid_iff_ckValidFC_true`); it is left untouched, and `CKValidFC`/
`CKValid` coexist. -/
def CKValidFC (FC : {World : Type v} → [Preorder World] → (World → World → Prop) → Prop)
    (φ : Proposition Atom) : Prop :=
  ∀ (World : Type v) [Preorder World] (r : World → World → Prop) (_fc : FC r)
    (val : World → Atom → Prop) (botForces : World → Prop),
    (∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p) →
    (∀ {w w' : World}, w ≤ w' → botForces w → botForces w') →
    (∀ {w : World} (p : Atom), botForces w → val w p) →
    (∀ {w u : World}, botForces w → r w u → botForces u) →
    (∀ {w : World}, botForces w → ∃ u, r w u ∧ botForces u) →
    ∀ w, CKForces r val botForces w φ

/-- `CKValid` is the special case of `CKValidFC` with the trivial frame condition
`fun _ => True`: both sides quantify over exactly the same models, `CKValidFC`'s extra `FC r`
hypothesis being trivially dischargeable. -/
theorem ckValid_iff_ckValidFC_true {φ : Proposition Atom} :
    CKValid.{u, v} φ ↔ CKValidFC.{u, v} (fun {_} [Preorder _] _ => True) φ := by
  constructor
  · intro h World _ r _ val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
    exact h World r val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  · intro h World _ r val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
    exact h World r trivial val botForces v_uc bf_uc bf_val bf_r bf_r_wit w

/-! ## ≤-Composed Frame Conditions -/

/-- The `CT` frame condition: reflexivity of the modal relation `r`. Both `tBox` (`□A → A`) and
`tDia` (`A → ◇A`) need only the plain clause `∀ w, r w w` (no `≤`-saturation is needed for
reflexivity itself). Defined locally over `[Preorder World]` rather than Mathlib's deprecated
`Reflexive`. -/
def ctFC {World : Type*} [Preorder World] (r : World → World → Prop) : Prop :=
  ∀ w, r w w

/-- The `CS4` frame condition: reflexivity **and** ≤-composed ("order-saturated") transitivity
of the modal relation `r`. `fourDia` (`◇◇A → ◇A`) needs only plain transitivity (the `u' := u`
specialization, via `le_refl`); `fourBox` (`□A → □□A`) needs the full ≤-composed clause
`r w u → u ≤ u' → r u' t → r w t`, which absorbs the role `F2` plays in the birelational
(`IS4`) setting. Defined locally — not Mathlib's deprecated `Transitive`. -/
def cs4FC {World : Type*} [Preorder World] (r : World → World → Prop) : Prop :=
  (∀ w, r w w) ∧ (∀ {w u u' t}, r w u → u ≤ u' → r u' t → r w t)

/-- The `CS5` frame condition: reflexivity, ≤-composed transitivity, **and** ≤-composed
("order-saturated") symmetry of the modal relation `r`. `bDia` (`◇□A → A`) needs only plain
symmetry (the `u' := u` specialization); `bBox` (`A → □◇A`) needs the full ≤-composed clause
`r w u → u ≤ u' → r u' w`. Axiomatized via `B` (symmetry), **not** the classical euclidean/`5`
axiom (see `CS5.lean`'s module docstring for the adversarial finding carried over from task
494). Defined locally — not Mathlib's deprecated `Symmetric`. -/
def cs5FC {World : Type*} [Preorder World] (r : World → World → Prop) : Prop :=
  (∀ w, r w w)
    ∧ (∀ {w u u' t}, r w u → u ≤ u' → r u' t → r w t)
    ∧ (∀ {w u u'}, r w u → u ≤ u' → r u' w)

/-! ## Parametric Completeness over `FC`-Frames -/

section ParametricFCCompleteness

variable {Axioms : Proposition Atom → Prop}

/-- **Parametric completeness over `FC`-frames**: any formula `φ` that is `CKValidFC FC`
(forced at every world of every fallible-world model whose relation satisfies `FC`) is derivable
from `Axioms`, given that the canonical model `(World, r, val, botForces)` itself satisfies `FC`
(`h_canonFC`) and admits a `realize` witness: every `Axioms`-underivable formula is refuted
(fails to be `CKForces`-forced) at some world of the model.

Deliberately abstracted over an arbitrary `World`/`r`/`val`/`botForces` (rather than committed
to `CKSegment Axioms`/`cmreach`/`cval`/`cbotForces` as `ck_completeness` is) so that each
per-system file can instantiate it over a **restricted world subtype** carrying its frame
condition as an invariant (report D3.4): the subtype supplies its own `r`/`val`/`botForces`
(projected from the segment structure) and its own `realize` (segment realization transported
along the subtype's `.seg` projection and the reused `ck_truth_lemma`).

The proof itself is the ~2-line contrapositive shared with `ck_completeness`
(`CK.lean:240-257`)/`ivalidFC_completeness` (`Intuitionistic/Extension.lean:97`): assume `φ` is
not derivable, obtain a refuting world from `realize`, and contradict it with the forcing
`h_valid` supplies at that world. -/
theorem ckvalidFC_completeness
    (FC : {World : Type u} → [Preorder World] → (World → World → Prop) → Prop)
    {World : Type u} [Preorder World]
    (r : World → World → Prop) (val : World → Atom → Prop) (botForces : World → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    (bf_val : ∀ {w : World} (p : Atom), botForces w → val w p)
    (bf_r : ∀ {w u : World}, botForces w → r w u → botForces u)
    (bf_r_wit : ∀ {w : World}, botForces w → ∃ u, r w u ∧ botForces u)
    (h_canonFC : FC r)
    (realize : ∀ {φ : Proposition Atom}, ¬ Derivable Axioms φ →
      ∃ w : World, ¬ CKForces r val botForces w φ)
    {φ : Proposition Atom} (h_valid : CKValidFC.{u, u} FC φ) :
    Derivable Axioms φ := by
  by_contra h_nd
  obtain ⟨w, hw⟩ := realize h_nd
  exact hw (h_valid World r h_canonFC val botForces v_uc bf_uc bf_val bf_r bf_r_wit w)

end ParametricFCCompleteness

/-! ## Axiom Membership Helper -/

section AxiomMemHead

variable {Axioms : Proposition Atom → Prop}

/-- **Axiom membership** (segment analogue of task 494's `axiom_mem`): any axiom instance
`Axioms φ` belongs to the head of every `CKSegment Axioms`. Used by every per-extension
canonical-closure proof (`CT`/`CS4`/`CS5`) to place an axiom instance (e.g. `tBox`, `fourDia`,
`bBox`) into a segment's head, via `mem_of_axiom` and the head's deductive closure. -/
theorem axiom_mem_head {s : CKSegment Axioms} {φ : Proposition Atom} (h : Axioms φ) :
    φ ∈ s.head :=
  mem_of_axiom s.head_qprime.closed h

end AxiomMemHead

end Cslib.Logic.Modal
