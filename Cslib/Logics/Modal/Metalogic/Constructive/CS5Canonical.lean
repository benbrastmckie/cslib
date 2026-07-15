/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Constructive.CS5

/-! # `CS5` Birelational Canonical Model (Task 512 Pivot)

This module is being rebuilt as the **birelational canonical model** for `CS5` (Božić–Došen
1984 / Došen 1985 IS5 / Simpson 1994 / Alechina–Mendler–de Paiva–Ritter 2001), replacing the
abandoned doubled-atom `CS5Combined` atom-sum scaffold (task 512 plan 01, DISCARDED this phase
— see `specs/512_cs5_box_backward_atom_sum_completeness/plans/02_birelational-pivot.md`, Phase
2). The doubled-atom approach attempted to close `CS5`'s box-backward truth-lemma case via a
simultaneous-pair construction over `Atom ⊕ Atom`; five dispatches confirmed this re-enters
Pacheco's unsound negation-completeness move (`cs5Combined_seed_excludes`, never closed — see
git history for the removed content).

The birelational pivot makes the canonical relation **one-sided** (`Γ R Δ ⟺ boxInv Γ ⊆ Δ`,
Simpson's `{B | □B ∈ X} ⊆ Y`), dissolving box-backward to the plain one-sided prime lemma
(`box_refuting_theory`, `SegmentLindenbaum.lean`) — confirmed negation-completeness-free at the
Phase 1 gate
(`specs/512_cs5_box_backward_atom_sum_completeness/probes/phase1-onesided-box-backward-gate.lean`,
`cs5_box_backward_onesided`). Symmetry becomes a global ≤-mediated **incestuality** frame
condition (Marin–Morales–Straßburger 2021 Thm 7.1) instead of a per-world back-inclusion baked
into `cs5Tail` (`CS5.lean:632`).

## Status (Phase 2 of the pivot: scaffold discard)

This phase removes the `CS5Combined` doubled-atom machinery (`CS5Combined`, `cs5_axiom_relabel`,
`τL`/`τR`, `cs5Combined_necTransfer`, `cs5CombinedTail`/`cs5CombinedSeg`/`CS5CombinedSegment`/
`cs5CombinedMreach`, and every port of `CS5.lean`'s canonical-model machinery over the doubled
atom space) as dead code — none of it survives the pivot, and nothing else in `Cslib/` referenced
it (confirmed by grep before removal). `Proposition.map` — the one still-useful primitive from
plan 01 — already lives in `Cslib/Logics/Modal/Basic.lean`, not here, so no file-split action was
needed this phase.

The two general negative results the pivot's research explicitly retains stay in their original
files, untouched by this discard:
- `cs5_symmetric_tail_box_gap` (`CS5.lean:712`) — the mechanized diagnosis of why the two-sided
  `cs5Tail` back-inclusion is the box-backward wall.
- `cs5FC''_hub_forces_spoke_connectivity` (`CKExtension.lean:220`) — the general fact that plain
  symmetry + plain transitivity force hub-and-spoke collapse (irrelevant as an obstruction to the
  new incestuality-based design, but a documented fact in its own right).

## Status (Phase 3 of the pivot: birelational frame class)

This phase defines the one-sided canonical relation `cs5OnesidedR`, the one-sided canonical
world type (`cs5CanonTail`/`cs5CanonSeg`/`CS5CanonSegment`/`cs5CanonMreach`, mirroring
`CS4.lean`'s one-sided-`R` `cs4Tail`/`cs4Seg`/`CS4Segment`/`cs4Mreach` template rather than the
discarded two-sided `cs5Tail`/`CS5Segment`), and the ≤-mediated S5 **incestuality** frame
condition (`cs5Incest`, bundled into `cs5FCIncest`) that REPLACES `cs5FC''`'s plain-symmetry +
plain-transitivity conjuncts (`CKExtension.lean:184`, task 509, left untouched — this phase adds
a new definition alongside it, per the plan's rollback note, rather than editing it in place).

**Deliberately NOT done this phase** (each is a separately-scoped later phase): soundness of the
17 `CS5ModalAxiom` cases over `cs5FCIncest` (Phase 4); proving the canonical model
(`cs5CanonMreach`) actually SATISFIES `cs5FCIncest`'s re-basing/incestuality clauses (Phase 5,
beyond the free reflexivity fact `cs5CanonRefl` landed here); the real `cs5_box_backward` in
`Cslib/` (Phase 6, already scaffolded sorry-free in the Phase 1 probe); the truth lemma and
`cs5_completeness` (Phase 7).

The birelational frame class (one-sided `R` + incestuality condition) is added in Phase 3;
soundness, canonical verification, box-backward, and the truth lemma follow in Phases 4-7. See
the plan file for the full phase breakdown.

## References

* [D. Božić and K. Došen, *Models for Normal Intuitionistic Modal Logics*][BozicDosen1984]
* [K. Došen, *Models for Stronger Normal Intuitionistic Modal Logics*][Dosen1985]
* [A. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994]
* [N. Alechina, M. Mendler, V. de Paiva and E. Ritter, *Categorical and Kripke Semantics for
  Constructive S4 Modal Logic*][AlechinaMendlerdePaivaRitter2001]
* [S. Marin, D. Morales and L. Straßburger, *A Fully Labelled Proof System for Intuitionistic
  Modal Logics*][MarinMoralesStrassburger2021]
* [L. Pacheco, *Collapsing Constructive and Intuitionistic Modal Logics*][Pacheco2024]
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u

variable {Atom : Type u}

/-! ## The One-Sided Canonical Relation

Simpson's `{B | □B ∈ X} ⊆ Y` (`Simpson1994`, corpus chunk `682e04d443e7bbd7`): the modal clause
with **no** "back" clause baked in, replacing the discarded two-sided `cs5Tail`
(`CS5.lean:632`, `boxInv H ⊆ t ∧ boxInv t ⊆ H`) that was the box-backward wall
(`cs5_symmetric_tail_box_gap`, `CS5.lean:712`). Verified negation-completeness-free at Phase 1
(`specs/512_cs5_box_backward_atom_sum_completeness/probes/phase1-onesided-box-backward-gate.lean`,
`cs5_box_backward_onesided`) — landed here with the identical signature so Phase 6 can restate
that probe's theorem directly in `Cslib/`. -/

/-- **The one-sided `CS5` canonical relation.** `Γ R Δ` iff `boxInv Γ ⊆ Δ`. Symmetry is NOT a
per-world clause of this relation; it is the global ≤-mediated incestuality frame condition
(`cs5Incest`/`cs5FCIncest` below). -/
def cs5OnesidedR (Γ Δ : Set (Proposition Atom)) : Prop :=
  boxInv Γ ⊆ Δ

/-! ## The One-Sided Canonical World Type

Mirrors `CS4.lean`'s one-sided-`R` template (`cs4Tail`/`cs4Seg`/`CS4Segment`/`cs4Mreach`,
`CS4.lean:341-386`) rather than the discarded two-sided `cs5Tail`/`CS5Segment`/`cs5Mreach`
(`CS5.lean:632-994`). Unlike `CS4Segment`, no excluded-diamond field is threaded through the
world type: the Phase 1 gate showed the one-sided box-backward case needs no hereditary
invariant beyond the plain prime lemma, so `cs5CanonSeg`'s tail is exactly the GENERIC maximal
tail `CKSegment.ofHead` already builds for any axiom system (`Segment.lean:142-150`) — this
section names it `cs5CanonTail`/`cs5CanonSeg` for module-local readability and to expose the
`tail_eq` invariant `CS5CanonSegment` needs, not because the construction differs from
`CKSegment.ofHead`. -/

/-- **The one-sided canonical tail.** Definitionally the maximal tail
`{t | QuasiPrime CS5ModalAxiom t ∧ boxInv H ⊆ t}` that `CKSegment.ofHead` already builds
generically; named here (rather than reused anonymously) so `CS5CanonSegment.tail_eq` can pin
every canonical world to this exact formula. -/
def cs5CanonTail (H : Set (Proposition Atom)) : Set (Set (Proposition Atom)) :=
  {t | QuasiPrime (@CS5ModalAxiom Atom) t ∧ cs5OnesidedR H t}

/-- The `CS5` canonical segment at head `H`: the maximal one-sided tail. Diamonds are witnessed
by the exploding theory `Set.univ` (always in `cs5CanonTail H`) — the box-BACKWARD direction
that needs a genuine Lindenbaum witness omitting a specific formula is `cs5_box_backward`
(Phase 6), not a `CKSegment` field. -/
def cs5CanonSeg {H : Set (Proposition Atom)} (hH : QuasiPrime (@CS5ModalAxiom Atom) H) :
    CKSegment (@CS5ModalAxiom Atom) where
  head := H
  tail := cs5CanonTail H
  head_qprime := hH
  tail_qprime := fun _ ht => ht.1
  box_reflect := fun _ hB _ ht => ht.2 hB
  diam_witness := fun _ _ => ⟨Set.univ, ⟨quasiPrime_univ, Set.subset_univ _⟩, Set.mem_univ _⟩

/-- `CS5` canonical worlds (birelational pivot): segments whose tail is exactly the one-sided
`cs5CanonTail` of their head. Port of the discarded two-sided `CS5Segment` (`CS5.lean:985`),
with `cs5CanonTail` (one-sided) replacing `cs5Tail` (two-sided). -/
structure CS5CanonSegment (Atom : Type u) where
  /-- The underlying segment. -/
  seg : CKSegment (@CS5ModalAxiom Atom)
  /-- The tail is exactly the one-sided canonical tail of the head. -/
  tail_eq : seg.tail = cs5CanonTail seg.head

instance : Preorder (CS5CanonSegment Atom) :=
  Preorder.lift (fun s : CS5CanonSegment Atom => s.seg)

/-- Canonical accessibility for the birelational `CS5` model. Port of `cs5Mreach`. -/
def cs5CanonMreach (P Q : CS5CanonSegment Atom) : Prop := cmreach P.seg Q.seg

/-- The canonical `CS5` world at head `H` (maximal one-sided tail). Port of
`CS5Segment.ofHead`. -/
def CS5CanonSegment.ofHead {H : Set (Proposition Atom)}
    (hH : QuasiPrime (@CS5ModalAxiom Atom) H) : CS5CanonSegment Atom where
  seg := cs5CanonSeg hH
  tail_eq := rfl

/-- `cs5CanonMreach` is reflexive: `boxInv H ⊆ H` is axiom `T` (`cs5_boxInv_subset`,
`CS5.lean:621`). Free from the axioms — no separate `refl` invariant is threaded through the
world type, matching `cs4_refl`/`cs5_refl`. The REMAINING frame-condition clauses
(re-basing/incestuality) are Phase 5's obligation, not proved here. -/
theorem cs5CanonRefl (P : CS5CanonSegment Atom) : cs5CanonMreach P P := by
  change P.seg.head ∈ P.seg.tail
  rw [P.tail_eq]
  exact ⟨P.seg.head_qprime, cs5_boxInv_subset P.seg.head_qprime⟩

/-- Canonical valuation on the birelational `CS5` model. Port of `cs5Val`. -/
def cs5CanonVal (s : CS5CanonSegment Atom) (p : Atom) : Prop := cval s.seg p

/-- Canonical fallibility on the birelational `CS5` model. Port of `cs5Bot`. -/
def cs5CanonBot (s : CS5CanonSegment Atom) : Prop := cbotForces s.seg

/-! ## The ≤-Mediated S5 Incestuality Frame Condition

Marin–Morales–Straßburger Thm 7.1 (Plotkin–Stirling 1986 frame correspondence): an
intuitionistic modal frame `⟨W, R, ≤⟩` validates the Scott–Lemmon path axiom
`◇ᵏ□ˡA ⊃ □ᵐ◇ⁿA` iff `wRᵏu ∧ wRᵐv ⟹ ∃u′. u ≤ u′ ∧ ∃x. u′Rˡx ∧ vRⁿx`. CS5's `B` axiom
(`A → □◇A`, `bBox`) is the instance `k = l = 0`, `m = n = 1` (`◇⁰□⁰A ⊃ □¹◇¹A`, since `◇⁰□⁰A`
is just `A`): `R⁰` is the identity relation, so `wR⁰u`/`u′R⁰x` collapse to `u = w`/`x = u′`, and
`R¹` is plain `r`. Substituting: `r w v ⟹ ∃u′ ≥ w, r v u′`. -/

/-- **The ≤-mediated S5 incestuality condition** (Marin Thm 7.1, specialized to CS5's `B`
instance `k = l = 0`, `m = n = 1` — see the section docstring for the derivation). **This is
NOT the naive classical symmetry condition `r w v → r v w`**: Marin Remark 7.3 explicitly flags
that the naive form is wrong intuitionistically (the exact error CSLib's discarded two-sided
`cs5Tail` made). Here `v` need only reach some world `u′` *above* `w` (`w ≤ u′`), not `w`
itself — the `≤`-mediation is the whole point. Cross-checked against Simpson's F1/F2
forward/backward confluence (`≤∘R ⊆ R∘≤`, `R∘≤ ⊆ ≤∘R`, corpus `Simpson1994`): those are the
general birelational monotonicity conditions any `CKForces`-style model already satisfies
structurally (via `box_reflect`'s upward closure through `≤`); `cs5Incest` is the ADDITIONAL
S5-specific ingredient on top. Proving the canonical model (`cs5CanonMreach`) satisfies this is
Phase 5's obligation, NOT this phase's. -/
def cs5Incest {World : Type*} [Preorder World] (r : World → World → Prop) : Prop :=
  ∀ {w v : World}, r w v → ∃ u', w ≤ u' ∧ r v u'

/-- **The birelational `CS5` incestuality frame condition** (task 512 pivot). Mirrors
`cs5FC''`'s bundling style (`CKExtension.lean:184`, task 509) exactly, but swaps the bundled
conjuncts per the plan's Phase 3 task: reflexivity, the `cs4FC'`-style `fourBox` re-basing
clause, and the `FCsym_box`-style `bBox` clause are KEPT verbatim from `cs5FC''`; `cs5FC''`'s
plain transitivity (`fourDia`) and plain symmetry (`bDia`) conjuncts are DROPPED and replaced by
`cs5Incest`. Per report 04 Q3, `cs5FC''_hub_forces_spoke_connectivity`'s hub-and-spoke
obstruction (derived from exactly the two dropped conjuncts) does not apply to frames satisfying
this bundle instead — dropping those two conjuncts is precisely what dissolves it as a
constraint on canonical-model design. Soundness of the 17 `CS5ModalAxiom` cases over this
bundle — in particular the genuinely new incestuality-mediated soundness argument for
`bDia`/`fourDia` — is Phase 4's obligation, NOT proved here; this definition is pure syntax. -/
def cs5FCIncest {World : Type*} [Preorder World] (r : World → World → Prop) : Prop :=
  (∀ w, r w w)
    ∧ (∀ {w u u' t}, r w u → u ≤ u' → r u' t → ∃ v, w ≤ v ∧ r v t)
    ∧ (∀ {w u u'}, r w u → u ≤ u' → ∃ t, r u' t ∧ w ≤ t)
    ∧ cs5Incest r

/-! ## `CKForces` Clauses Remain Served (Confirmation, Phase 3 Task 4)

`CKForces` (`Forcing.lean:67`) is generic over any `World`/`r`/`val`/`botForces`, independent of
which frame condition `r` happens to satisfy: the propositional cases (atom/bot/and/or/imp) and
the box-forward/diamond-both cases depend only on `≤`, `cmreach`-style `r`, `box_reflect`, and
`diam_witness` — all of which `cs5CanonSeg`/`CS5CanonSegment`/`cs5CanonMreach` above supply,
exactly matching `CS4.lean`'s one-sided-`R` template (`cs4_truth_lemma`, `CS4.lean:457`). Only
the truth lemma's box-BACKWARD case (`□A ∈ head → CKForces (□A)`) needs anything beyond this
generic machinery — the plain one-sided prime lemma (`cs5_box_backward`, Phase 6) — and nothing
about `cs5FCIncest` is needed for that case either (the Phase 1 gate's whole point: box-backward
is frame-condition-independent). Landing the actual truth lemma is Phase 7's obligation. -/

end Cslib.Logic.Modal

end
