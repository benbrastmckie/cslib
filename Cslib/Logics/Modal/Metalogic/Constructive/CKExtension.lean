/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Constructive.CKTruthLemma

/-! # Frame-Condition-Parametrized Extensions of the Segment Canonical Model

This module is the shared scaffold for constructive modal extensions `CT`/`CS4`/`CS5`
of `CK`, over the Wijesekera-style fallible-world segment semantics. It generalizes the
segment canonical-model framework (`CKValid`, `ck_completeness`, `CKTruthLemma.lean`) to
validity/completeness over a restricted *class* of fallible-world models, cut out by an arbitrary
frame condition `FC` on the modal relation `r`. This lets each per-system file (`CT.lean`,
`CS4.lean`, `CS5.lean`) bolt its frame condition onto validity/completeness without touching any
of that segment canonical-model framework's assets.

Unlike the birelational `Extension.lean` (which is **not** reused here — bare `CK` is
incomplete for the birelational `BForces` semantics; see `CK.lean`'s module docstring), this
scaffold is segment-based: the sound-and-complete semantics for every `CK` extension is
`CKForces`/`CKValid` (the ∀∃ diamond, no `F1`/`F2` confluence) restricted to frames whose modal
relation additionally satisfies `FC`.

**The completeness scaffold is deliberately abstract over the canonical `World` type** (not
pinned to `CKSegment Axioms`): the primary implementation challenge here is that the frame
conditions `ctFC`/`cs4FC`/`cs4FC'`/`cs5FC` do **not** hold globally on raw `CKSegment Axioms` (a
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
- `cs4FC'`: a **weakened** `CS4` frame condition, replacing `cs4FC`'s blanket
  ≤-composed transitivity with two existential clauses. `cs4FC_implies_cs4FC'` witnesses that
  every `cs4FC`-frame is a `cs4FC'`-frame. Validity over the weaker `cs4FC'` is what makes `CS4`
  canonical completeness go through (see `CS4.lean`); `cs4FC` is retained unchanged for its
  existing soundness theorems and downstream users in `ConstructiveLatticeMonotonicity.lean`.
- `ckvalidFC_completeness`: a segment analogue of `ivalidFC_completeness`
  (`Intuitionistic/Extension.lean:97`), abstracted over an arbitrary canonical `World` type
  (rather than committed to `CKSegment Axioms`) so that it can be instantiated over a world
  subtype. Takes `h_canonFC : FC r` and a `realize` witness (any underivable formula is refuted
  at some world of the model) and concludes derivability from `CKValidFC FC`-validity.
- `axiom_mem_head`: a one-line helper (`Axioms φ → φ ∈ s.head` for a `CKSegment Axioms`) used by
  every per-extension canonical-closure proof, the segment analogue of the birelational
  development's `axiom_mem`.

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
`Reflexive`. The `[Preorder World]` instance is unused (plain reflexivity needs no `≤`) but is
required to match `CKValidFC`'s shared `FC` shape (`cs4FC`/`cs5FC` do use `≤`). -/
@[nolint unusedArguments]
def ctFC {World : Type*} [Preorder World] (r : World → World → Prop) : Prop :=
  ∀ w, r w w

/-- The `CS4` frame condition: reflexivity **and** ≤-composed ("order-saturated") transitivity
of the modal relation `r`. `fourDia` (`◇◇A → ◇A`) needs only plain transitivity (the `u' := u`
specialization, via `le_refl`); `fourBox` (`□A → □□A`) needs the full ≤-composed clause
`r w u → u ≤ u' → r u' t → r w t`, which absorbs the role `F2` plays in the birelational
(`IS4`) setting. Defined locally — not Mathlib's deprecated `Transitive`. -/
def cs4FC {World : Type*} [Preorder World] (r : World → World → Prop) : Prop :=
  (∀ w, r w w) ∧ (∀ {w u u' t}, r w u → u ≤ u' → r u' t → r w t)

/-- The **weakened** `CS4` frame condition: reflexivity plus two existential
clauses replacing `cs4FC`'s blanket ≤-composed transitivity. `fourBox` (`□A → □□A`) is
discharged at a *re-based* world `v ≥ w''` rather than at `w''` itself, since `□A@w'`
quantifies over all `z ≥ w'` (so any `v ≥ w''` still forces `A` there). `fourDia`
(`◇◇A → ◇A`) needs a genuine `r`-successor of `w''`, but may unfold `◇A@u` at any
`u' ≥ u` — the frame condition supplies a good `u'` for which every `r`-successor `t`
of `u'` is already an `r`-successor of `w''` directly. Validity over `cs4FC'` is a
**stronger** statement than validity over `cs4FC` (the class of `cs4FC'`-frames is larger,
so soundness is *harder* to prove but completeness is *easier* to prove) — this is exactly
what makes canonical completeness for `CS4` go through (see `CS4.lean`). -/
def cs4FC' {World : Type*} [Preorder World] (r : World → World → Prop) : Prop :=
  (∀ w, r w w)
    ∧ (∀ {w u u' t}, r w u → u ≤ u' → r u' t → ∃ v, w ≤ v ∧ r v t)
    ∧ (∀ {w u}, r w u → ∃ u', u ≤ u' ∧ ∀ t, r u' t → r w t)

/-- **`cs4FC'` genuinely weakens `cs4FC`**: every `cs4FC`-frame is a `cs4FC'`-frame,
witnessed by the trivial choices `v := w` (for the first existential clause) and `u' := u`
(for the second). Used to re-derive `CS4.lean`'s existing `cs4FC`-soundness theorems as
corollaries of the (stronger) `cs4FC'`-soundness theorems, and to compose with
`cs5FC_implies_cs4FC` in `ConstructiveLatticeMonotonicity.lean`. -/
theorem cs4FC_implies_cs4FC' {World : Type*} [Preorder World] {r : World → World → Prop}
    (h : cs4FC r) : cs4FC' r :=
  ⟨h.1,
   fun hwu hle hu't => ⟨_, le_refl _, h.2 hwu hle hu't⟩,
   fun hwu => ⟨_, le_refl _, fun _ hut => h.2 hwu (le_refl _) hut⟩⟩

/-- The `CS5` frame condition: reflexivity, ≤-composed transitivity, **and** ≤-composed
("order-saturated") symmetry of the modal relation `r`. `bDia` (`◇□A → A`) needs only plain
symmetry (the `u' := u` specialization); `bBox` (`A → □◇A`) needs the full ≤-composed clause
`r w u → u ≤ u' → r u' w`. Axiomatized via `B` (symmetry), **not** the classical euclidean/`5`
axiom (see `CS5.lean`'s module docstring for the finding). Defined locally — not Mathlib's
deprecated `Symmetric`. -/
def cs5FC {World : Type*} [Preorder World] (r : World → World → Prop) : Prop :=
  (∀ w, r w w)
    ∧ (∀ {w u u' t}, r w u → u ≤ u' → r u' t → r w t)
    ∧ (∀ {w u u'}, r w u → u ≤ u' → r u' w)

/-- **The weakened `CS5` frame condition**: reflexivity, *plain* transitivity, *plain*
symmetry, the `cs4FC'` re-basing clause (`fourBox`), and the weakened ≤-composed symmetry
`FCsym_box` (`bBox`). Per-clause axiom correspondence: `∀ w, r w w` validates `tBox`/`tDia`;
plain transitivity `r w u → r u t → r w t` validates `fourDia`; plain symmetry
`r w u → r u w` validates `bDia`; the `cs4FC'` re-basing clause
`r w u → u ≤ u' → r u' t → ∃ v, w ≤ v ∧ r v t` validates `fourBox`; and `FCsym_box`
`r w u → u ≤ u' → ∃ t, r u' t ∧ w ≤ t` validates `bBox`.

**`cs5FC''` is not `cs5FCweak` corrected by relabelling — it fixes a genuine soundness gap.**
An earlier `cs5FCweak` is `cs5FC''` *minus* plain symmetry and *minus* plain transitivity; that
omission, not any real obstruction, is why `bDia` was unsound over `cs5FCweak`
(`bDia_not_valid_over_cs5FCweak`). That countermodel's relation `wr'` is itself not plainly
symmetric (`Cslib.Logic.Modal.wr'_not_symm`), so it says nothing about `cs5FC''`. All 17 `CS5`
axioms are sound over `cs5FC''`
(`Cslib.Logic.Modal.cs5_axiom_sound''`, `CS5.lean`) — see that theorem for the mechanized
soundness proof. Validity over `cs5FC''` is a genuine weakening of validity over `cs5FC`
(`cs5FC_implies_cs5FC''`), the same direction that makes `CS4` canonical completeness go
through for `cs4FC'`. -/
def cs5FC'' {World : Type*} [Preorder World] (r : World → World → Prop) : Prop :=
  (∀ w, r w w)
    ∧ (∀ {w u t}, r w u → r u t → r w t)
    ∧ (∀ {w u}, r w u → r u w)
    ∧ (∀ {w u u' t}, r w u → u ≤ u' → r u' t → ∃ v, w ≤ v ∧ r v t)
    ∧ (∀ {w u u'}, r w u → u ≤ u' → ∃ t, r u' t ∧ w ≤ t)

/-- **`cs5FC''` genuinely weakens `cs5FC`**: every `cs5FC`-frame is a `cs5FC''`-frame, witnessed
by specializing each ≤-composed clause at `u' := u` (or, for `FCsym_box`, at `t := w`). Validity
over the weaker `cs5FC''` is therefore a *stronger* statement than validity over `cs5FC`:
soundness is harder to prove (`cs5_axiom_sound''`) but completeness is easier — mirrors
`cs4FC_implies_cs4FC'`. -/
theorem cs5FC_implies_cs5FC'' {World : Type*} [Preorder World] {r : World → World → Prop}
    (h : cs5FC r) : cs5FC'' r :=
  ⟨h.1,
   fun hwu hut => h.2.1 hwu (le_refl _) hut,
   fun hwu => h.2.2 hwu (le_refl _),
   fun hwu hle hu't => ⟨_, le_refl _, h.2.1 hwu hle hu't⟩,
   fun hwu hle => ⟨_, h.2.2 hwu hle, le_refl _⟩⟩

/-- **A hub connected to two `cs5FC''`-related worlds forces those two worlds to be related to
each other.** Plain symmetry (`r w u → r u w`) plus plain transitivity (`r w u → r u t → r w t`)
— both required by `cs5FC''` — mean any relation `r` satisfying `cs5FC''` cannot support a
"hub-and-spoke" shape (one designated world related to several otherwise-unrelated "spoke"
worlds): `r w0 T1` and `r w0 T2` already force `r T1 T2` (via `r T1 w0` from symmetry, then
`r T1 w0 → r w0 T2 → r T1 T2` from transitivity). Consequence for canonical-model design: any
`cs5FC''`-frame with a designated world reachable from two or more "auxiliary" worlds collapses
those auxiliary worlds into a single fully-connected cluster with the designated world itself —
there is no way to keep a hub's spokes semantically independent of one another while satisfying
`cs5FC''`. This rules out a class of hand-built multi-world separating models for combined/
two-sorted systems (e.g. a designated `L`-world connected to many independent `R`-witness
worlds intended to stay mutually unrelated): the frame condition itself forces them into one
cluster, so any compound (in particular boxed) formula's truth at a spoke world is entangled
with the hub's own valuation and with every other spoke, not just with that spoke's local
theory. -/
theorem cs5FC''_hub_forces_spoke_connectivity {World : Type*} [Preorder World]
    {r : World → World → Prop} (hFC : cs5FC'' r) {w0 T1 T2 : World}
    (h1 : r w0 T1) (h2 : r w0 T2) : r T1 T2 :=
  hFC.2.1 (hFC.2.2.1 h1) h2

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

/-- **Axiom membership** (segment analogue of the birelational development's `axiom_mem`): any
axiom instance
`Axioms φ` belongs to the head of every `CKSegment Axioms`. Used by every per-extension
canonical-closure proof (`CT`/`CS4`/`CS5`) to place an axiom instance (e.g. `tBox`, `fourDia`,
`bBox`) into a segment's head, via `mem_of_axiom` and the head's deductive closure. -/
theorem axiom_mem_head {s : CKSegment Axioms} {φ : Proposition Atom} (h : Axioms φ) :
    φ ∈ s.head :=
  mem_of_axiom s.head_qprime.closed h

end AxiomMemHead

end Cslib.Logic.Modal
