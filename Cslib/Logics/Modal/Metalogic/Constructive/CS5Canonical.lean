/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Constructive.CS5

/-! # `CS5` Birelational Canonical Model

This module defines the **birelational canonical model** for `CS5` (Božić–Došen 1984 / Došen
1985 IS5 / Simpson 1994 / Alechina–Mendler–de Paiva–Ritter 2001). It replaces an earlier
doubled-atom `CS5Combined` atom-sum scaffold that attempted to close `CS5`'s box-backward
truth-lemma case via a simultaneous-pair construction over `Atom ⊕ Atom`; that approach
re-entered Pacheco's unsound negation-completeness move (`cs5Combined_seed_excludes`, never
closed — see git history for the removed content) and was discarded.

The birelational approach makes the canonical relation **one-sided** (`Γ R Δ ⟺ boxInv Γ ⊆ Δ`,
Simpson's `{B | □B ∈ X} ⊆ Y`), dissolving box-backward to the plain one-sided prime lemma
(`box_refuting_theory`, `SegmentLindenbaum.lean`) — confirmed negation-completeness-free
(`cs5_box_backward_onesided`). Symmetry becomes a global ≤-mediated **incestuality** frame
condition (Marin–Morales–Straßburger 2021 Thm 7.1) instead of a per-world back-inclusion baked
into `cs5Tail` (`CS5.lean:632`).

## Scaffold discard

The `CS5Combined` doubled-atom machinery (`CS5Combined`, `cs5_axiom_relabel`, `τL`/`τR`,
`cs5Combined_necTransfer`, `cs5CombinedTail`/`cs5CombinedSeg`/`CS5CombinedSegment`/
`cs5CombinedMreach`, and every port of `CS5.lean`'s canonical-model machinery over the doubled
atom space) has been removed as dead code — none of it survives the birelational approach, and
nothing else in `Cslib/` references it. `Proposition.map` — the one still-useful primitive from
that earlier approach — lives in `Cslib/Logics/Modal/Basic.lean`, not here.

The two general negative results retained from that investigation stay in their original files:
- `cs5_symmetric_tail_box_gap` (`CS5.lean:712`) — the mechanized diagnosis of why the two-sided
  `cs5Tail` back-inclusion is the box-backward wall.
- `cs5FC''_hub_forces_spoke_connectivity` (`CKExtension.lean:220`) — the general fact that plain
  symmetry + plain transitivity force hub-and-spoke collapse (irrelevant as an obstruction to the
  incestuality-based design, but a documented fact in its own right).

## Birelational frame class

This module defines the one-sided canonical relation `cs5OnesidedR`, the one-sided canonical
world type (`cs5CanonTail`/`cs5CanonSeg`/`CS5CanonSegment`/`cs5CanonMreach`, mirroring
`CS4.lean`'s one-sided-`R` `cs4Tail`/`cs4Seg`/`CS4Segment`/`cs4Mreach` template rather than the
discarded two-sided `cs5Tail`/`CS5Segment`), and the ≤-mediated S5 **incestuality** frame
condition (`cs5Incest`, bundled into `cs5FCIncest`) that REPLACES `cs5FC''`'s plain-symmetry +
plain-transitivity conjuncts (`CKExtension.lean:184`, left untouched — this module adds a new
definition alongside it rather than editing it in place).

## Soundness over `cs5FCIncest`

This module also re-proves `CS5` soundness (all 17 `CS5ModalAxiom` cases,
`cs5_axiom_sound_incest`/`cs5_soundness_incest`/`cs5_soundness_derivable_incest`) over
`cs5FCIncest`. Along the way it CORRECTS two aspects of the birelational frame class's initial
definitions (both `cs5Incest` and `cs5FCIncest` retain their names, unconsumed by anything
outside this file, so revising their statements is safe and non-regressive — see each
definition's docstring for the full derivation):

- `cs5Incest` was mis-instantiated at first: derived as the `bBox` instance of Marin Thm 7.1
  (`k=l=0,m=n=1`), which turns out to coincide with the already-kept `FCsym_box` clause and so
  contributes nothing new. The genuinely new `B`-soundness content is the OTHER instance,
  `bDia` (`k=l=1,m=n=0`); `cs5Incest` is corrected to that shape.
- `cs5FCIncest` had dropped BOTH plain transitivity (`fourDia`) and plain symmetry (`bDia`).
  `fourDia`'s truth-lemma goal is a "point" fact with no `≤`-room (exactly like `bDia`'s), so no
  `≤`-mediated substitute can weaken transitivity for it the way `cs4FC'`/`FCsym_box` weakens
  `fourBox`'s composition — plain transitivity is added BACK. Only plain symmetry (`bDia`) is
  actually replaced by (corrected) `cs5Incest`.

`cs5FCIncest` is therefore `cs5FC''` with ONLY its plain-symmetry conjunct replaced —
`cs5FC''` itself (`CKExtension.lean`) is left completely untouched; this module adds the
reworked soundness theorems alongside it.

**Deliberately not done here**: proving the canonical model (`cs5CanonMreach`) actually
SATISFIES `cs5FCIncest`'s re-basing/incestuality clauses (beyond the free reflexivity fact
`cs5CanonRefl` landed above). The real `cs5_box_backward` is scaffolded sorry-free but not yet
landed in `Cslib/`; the truth lemma and `cs5_completeness` are likewise still outstanding.

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
(`cs5_symmetric_tail_box_gap`, `CS5.lean:712`). Verified negation-completeness-free
(`cs5_box_backward_onesided`) — landed here with the identical signature so `cs5_box_backward`
can eventually restate that theorem directly in `Cslib/`. -/

/-- **The one-sided `CS5` canonical relation.** `Γ R Δ` iff `boxInv Γ ⊆ Δ`. Symmetry is NOT a
per-world clause of this relation; it is the global ≤-mediated incestuality frame condition
(`cs5Incest`/`cs5FCIncest` below). -/
def cs5OnesidedR (Γ Δ : Set (Proposition Atom)) : Prop :=
  boxInv Γ ⊆ Δ

/-! ## The One-Sided Canonical World Type

Mirrors `CS4.lean`'s one-sided-`R` template (`cs4Tail`/`cs4Seg`/`CS4Segment`/`cs4Mreach`,
`CS4.lean:341-386`) rather than the discarded two-sided `cs5Tail`/`CS5Segment`/`cs5Mreach`
(`CS5.lean:632-994`). Unlike `CS4Segment`, no excluded-diamond field is threaded through the
world type: the one-sided box-backward case needs no hereditary invariant beyond the plain prime
lemma, so `cs5CanonSeg`'s tail is exactly the GENERIC maximal
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
that needs a genuine Lindenbaum witness omitting a specific formula is `cs5_box_backward`,
still outstanding, not a `CKSegment` field. -/
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
(re-basing/incestuality) are not proved here. -/
theorem cs5CanonRefl (P : CS5CanonSegment Atom) : cs5CanonMreach P P := by
  change P.seg.head ∈ P.seg.tail
  rw [P.tail_eq]
  exact ⟨P.seg.head_qprime, cs5_boxInv_subset P.seg.head_qprime⟩

/-- Canonical valuation on the birelational `CS5` model. Port of `cs5Val`. -/
def cs5CanonVal (s : CS5CanonSegment Atom) (p : Atom) : Prop := cval s.seg p

/-- Canonical fallibility on the birelational `CS5` model. Port of `cs5Bot`. -/
def cs5CanonBot (s : CS5CanonSegment Atom) : Prop := cbotForces s.seg

/-! ## The ≤-Mediated S5 Incestuality Frame Condition

Marin–Morales–Straßburger Thm 7.1 (`marinmoralesstrassburger_2021...`, chunk `0043`, verbatim):
an intuitionistic modal frame `⟨W, R, ≤⟩` validates the Scott–Lemmon path axiom
`◇ᵏ□ˡA ⊃ □ᵐ◇ⁿA` iff `wRᵏu ∧ wRᵐv ⟹ ∃u′. u ≤ u′ ∧ ∃x. u′Rˡx ∧ vRⁿx`.

`CS5`'s `B` axiom has TWO forms, and they are DIFFERENT instances of this schema (the definition
below is unchanged in its final form, but its derivation was initially mis-attributed): `bBox`
is `k = l = 0, m = n = 1` (`◇⁰□⁰A ⊃ □¹◇¹A`, since
`◇⁰□⁰A` is just `A`): `R⁰` is the identity, so `wR⁰u`/`u′R⁰x` collapse to `u = w`/`x = u′`,
giving `r w v ⟹ ∃u′ ≥ w, r v u′` — but this is *exactly* the `u′ := u` (`le_refl`)
specialization of `cs5FC''`'s `FCsym_box` clause (kept verbatim below, third conjunct of
`cs5FCIncest`), so it contributes no soundness content beyond what `FCsym_box` already
supplies, and `bBox`'s soundness case is UNCHANGED from `cs5_axiom_sound''`. The genuinely new
incestuality content is the OTHER `B` instance: `bDia` (`◇□A → A`) is `k = l = 1, m = n = 0`
(antecedent `◇¹□¹A`, consequent `□⁰◇⁰A = A`); substituting (`wR⁰v` collapses to `v = w`,
`vR⁰x` to `x = v = w`): `r w u ⟹ ∃u′ ≥ u, r u′ w`. **This** is `cs5Incest` below, replacing
`cs5FC''`'s dropped PLAIN symmetry conjunct (`r w u → r u w`, the `u′ := u` degenerate case of
this). -/

/-- **The ≤-mediated `bDia`-instance of the S5 incestuality condition** (Marin Thm 7.1,
`k = l = 1`, `m = n = 0` — see the section docstring for the derivation and why this, not the
`bBox` instance, is the genuinely new soundness content). **This is NOT the naive classical
symmetry condition `r w u → r u w`**: Marin Remark 7.3 explicitly flags that the naive form is
wrong intuitionistically (the exact error CSLib's discarded two-sided `cs5Tail` made). Here the
witness `u′` need only be *above* `u` (`u ≤ u′`) — the relation still lands back at `w` exactly
(no `≤`-slack on that side, unlike `FCsym_box`'s landing side: `bDia`'s truth-lemma goal is a
"point" fact with no `≤`-room to spare, whereas `bBox`'s nested-quantifier goal tolerates
`≤`-slack on ITS landing side instead — the two `B`-instances trade off which side gets the
slack). Cross-checked against Simpson's F1/F2 forward/backward confluence (`≤∘R ⊆ R∘≤`,
`R∘≤ ⊆ ≤∘R`, corpus `Simpson1994`): those are the general birelational monotonicity conditions
any `CKForces`-style model already satisfies structurally (via `box_reflect`'s upward closure
through `≤`); `cs5Incest` is the ADDITIONAL S5-specific ingredient on top. Proving the canonical
model (`cs5CanonMreach`) satisfies this remains outstanding. -/
def cs5Incest {World : Type*} [Preorder World] (r : World → World → Prop) : Prop :=
  ∀ {w u : World}, r w u → ∃ u', u ≤ u' ∧ r u' w

/-- **The birelational `CS5` incestuality frame condition.** Mirrors `cs5FC''`'s bundling style
(`CKExtension.lean:184`) exactly, but swaps ONE bundled conjunct (dropping BOTH plain
transitivity and plain symmetry breaks `fourDia`'s soundness — its truth-lemma goal is also a
"point" fact with no `≤`-room, so no `≤`-mediated substitute can replace EXACT transitivity the
way `cs4FC'`/`FCsym_box` could weaken `fourBox`'s composition; see `cs5_axiom_sound_incest`'s
`fourDia` case, verbatim from `cs5_axiom_sound''`). Reflexivity, PLAIN transitivity (`fourDia`,
kept — NOT weakenable, see above), the `cs4FC'`-style `fourBox` re-basing clause, and the
`FCsym_box`-style `bBox` clause are all KEPT verbatim from `cs5FC''`; ONLY `cs5FC''`'s plain
symmetry (`bDia`) conjunct is DROPPED and replaced by `cs5Incest` (the `bDia`-specific Marin
instance `k=l=1,m=n=0`, genuinely distinct from the `bBox`-specific instance `FCsym_box` already
covers — see the section docstring). `cs5FC''_hub_forces_spoke_connectivity`'s hub-and-spoke
obstruction (derived from PLAIN transitivity + PLAIN symmetry JOINTLY) no longer applies once
EITHER conjunct is dropped; dropping plain symmetry alone already dissolves it as a
canonical-model design constraint, so keeping plain transitivity is safe. Soundness of the 17
`CS5ModalAxiom` cases over this bundle — in particular the genuinely new incestuality-mediated
soundness argument for `bDia` — is `cs5_axiom_sound_incest` below. -/
def cs5FCIncest {World : Type*} [Preorder World] (r : World → World → Prop) : Prop :=
  (∀ w, r w w)
    ∧ (∀ {w u t}, r w u → r u t → r w t)
    ∧ (∀ {w u u' t}, r w u → u ≤ u' → r u' t → ∃ v, w ≤ v ∧ r v t)
    ∧ (∀ {w u u'}, r w u → u ≤ u' → ∃ t, r u' t ∧ w ≤ t)
    ∧ cs5Incest r

/-! ## Soundness over `cs5FCIncest`

Ports `cs5_axiom_sound''`'s 15 non-`B` cases and the `fourBox`/`bBox` cases VERBATIM
(`CS5.lean:366`) — none of them touch the conjunct that changed. Only the `bDia` case
is genuinely new: it discharges via `cs5Incest` (the corrected `bDia`-instance of Marin Thm 7.1,
`k=l=1,m=n=0`) instead of `cs5FC''`'s plain symmetry conjunct. -/

/-- **Every `CS5ModalAxiom` instance is `CKValidFC cs5FCIncest`.** Identical to
`cs5_axiom_sound''` (`CS5.lean:366`) in 16 of its 17 cases (`fourDia` still uses PLAIN
transitivity, `fourBox`/`bBox` still use the re-basing clauses — `cs5FCIncest` kept those three
conjuncts verbatim from `cs5FC''`); only `bDia` (`◇□A → A`) changes: at `w'` (`le_refl`), get
`u` with `r w' u ∧ □A@u`; `cs5Incest hru` (the `bDia`-instance of Marin Thm 7.1) gives `u' ≥ u`
with `r u' w'`; instantiate `□A@u` at `u'` (via `hru' : u ≤ u'`) and `w'` (via `r u' w'`) to
conclude `A@w'` directly — no `≤`-padding needed beyond what `cs5Incest` itself supplies, and no
negation-completeness step anywhere (Marin Thm 7.2's soundness direction: purely a semantic
unfolding of the incestuality condition against `CKForces`'s clauses). -/
theorem cs5_axiom_sound_incest {φ : Proposition Atom} (h_ax : CS5ModalAxiom φ) :
    CKValidFC.{u, v} cs5FCIncest φ := by
  intro World _ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  obtain ⟨hrefl, htrans, hfour, hsymbox, hincest⟩ := hfc
  cases h_ax with
  | implyK φ ψ =>
    intro w' _ hφ w'' hw' _
    exact ckforces_persistence v_uc bf_uc hw' hφ
  | implyS φ ψ χ =>
    intro w₁ hw₁ h_pqr w₂ hw₂ h_pq w₃ hw₃ h_p
    have h₁₃ : w₁ ≤ w₃ := le_trans hw₂ hw₃
    exact h_pqr w₃ h₁₃ h_p w₃ (le_refl w₃) (h_pq w₃ hw₃ h_p)
  | efq φ =>
    intro w' _ hbot
    exact ckforces_of_exploding bf_uc bf_val bf_r bf_r_wit hbot φ
  | andI φ ψ =>
    intro w₁ _ hφ w₂ hw₂ hψ
    exact ⟨ckforces_persistence v_uc bf_uc hw₂ hφ, hψ⟩
  | andE1 φ ψ => intro _ _ h; exact h.1
  | andE2 φ ψ => intro _ _ h; exact h.2
  | orI1 φ ψ => intro _ _ h; exact Or.inl h
  | orI2 φ ψ => intro _ _ h; exact Or.inr h
  | orE φ ψ χ =>
    intro w₁ _ h_pq w₂ hw₂ h_rq w₃ hw₃ h_pr
    have hw₁₃ : w₁ ≤ w₃ := le_trans hw₂ hw₃
    exact h_pr.elim (fun hp => h_pq w₃ hw₁₃ hp) (fun hr => h_rq w₃ hw₃ hr)
  | k φ ψ =>
    intro w' _ hbox_imp w'' hw' hbox_phi w1 hw1 u hru
    exact hbox_imp w1 (le_trans hw' hw1) u hru u (le_refl u) (hbox_phi w1 hw1 u hru)
  | kdia φ ψ =>
    intro w' _ hbox_imp w'' hw' hdia_phi w₃ hw₃
    obtain ⟨u, hru, hφu⟩ := hdia_phi w₃ hw₃
    exact ⟨u, hru, hbox_imp w₃ (le_trans hw' hw₃) u hru u (le_refl u) hφu⟩
  | tBox φ =>
    intro w' _ hbox
    exact hbox w' (le_refl w') w' (hrefl w')
  | tDia φ =>
    intro w' _ hφ w'' hw''
    exact ⟨w'', hrefl w'', ckforces_persistence v_uc bf_uc hw'' hφ⟩
  | fourDia φ =>
    intro w' _ hdidia w'' hw''
    obtain ⟨u, hru, hdia_u⟩ := hdidia w'' hw''
    obtain ⟨t, hut, hφt⟩ := hdia_u u (le_refl u)
    exact ⟨t, htrans hru hut, hφt⟩
  | fourBox φ =>
    intro w' _ hbox w'' hw'' u hru u' hu' t hrt
    obtain ⟨v, hwv, hrvt⟩ := hfour hru hu' hrt
    exact hbox v (le_trans hw'' hwv) t hrvt
  | bDia φ =>
    intro w' _ hdia
    obtain ⟨u, hru, hboxA⟩ := hdia w' (le_refl w')
    obtain ⟨u', hu', hru'w'⟩ := hincest hru
    exact hboxA u' hu' w' hru'w'
  | bBox φ =>
    intro w' _ hφ w'' hw'' u hru u' hu'
    obtain ⟨t, hru't, hw''t⟩ := hsymbox hru hu'
    exact ⟨t, hru't, ckforces_persistence v_uc bf_uc (le_trans hw'' hw''t) hφ⟩

/-- **Soundness over `cs5FCIncest`**: if `DerivationTree CS5ModalAxiom Γ φ`, then in any
fallible-world model whose modal relation satisfies `cs5FCIncest`, at any world `w` where all
formulas in `Γ` are forced, `φ` is also forced. Structural analogue of `cs5_soundness''`
(`CS5.lean:427`), threading `hfc` through unused except at the `.ax` case. -/
theorem cs5_soundness_incest
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree CS5ModalAxiom Γ φ)
    {World : Type v} [Preorder World]
    (r : World → World → Prop) (hfc : cs5FCIncest r)
    (val : World → Atom → Prop) (botForces : World → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    (bf_val : ∀ {w : World} (p : Atom), botForces w → val w p)
    (bf_r : ∀ {w u : World}, botForces w → r w u → botForces u)
    (bf_r_wit : ∀ {w : World}, botForces w → ∃ u, r w u ∧ botForces u)
    (w : World)
    (h_ctx : ∀ ψ, ψ ∈ Γ → CKForces r val botForces w ψ) :
    CKForces r val botForces w φ := by
  match d with
  | .ax _ ψ h_ax =>
    exact cs5_axiom_sound_incest h_ax World r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact cs5_soundness_incest d₁ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w h_ctx
      w (le_refl w)
      (cs5_soundness_incest d₂ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w h_ctx)
  | .necessitation ψ d' =>
    intro w' _hle u _hru
    exact cs5_soundness_incest d' r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit u
      (fun _ h => nomatch h)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact cs5_soundness_incest d' r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Soundness for derivable formulas over `cs5FCIncest`**: if `Derivable CS5ModalAxiom φ`,
then `φ` is `CKValidFC cs5FCIncest`. -/
theorem cs5_soundness_derivable_incest {φ : Proposition Atom}
    (h : Derivable CS5ModalAxiom φ) : CKValidFC.{u, v} cs5FCIncest φ := by
  intro World _ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  obtain ⟨d⟩ := h
  exact cs5_soundness_incest d r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
    (fun _ h => nomatch h)

/-! ## `CKForces` Clauses Remain Served

`CKForces` (`Forcing.lean:67`) is generic over any `World`/`r`/`val`/`botForces`, independent of
which frame condition `r` happens to satisfy: the propositional cases (atom/bot/and/or/imp) and
the box-forward/diamond-both cases depend only on `≤`, `cmreach`-style `r`, `box_reflect`, and
`diam_witness` — all of which `cs5CanonSeg`/`CS5CanonSegment`/`cs5CanonMreach` above supply,
exactly matching `CS4.lean`'s one-sided-`R` template (`cs4_truth_lemma`, `CS4.lean:457`). Only
the truth lemma's box-BACKWARD case (`□A ∈ head → CKForces (□A)`) needs anything beyond this
generic machinery — the plain one-sided prime lemma (`cs5_box_backward`, still outstanding) —
and nothing about `cs5FCIncest` is needed for that case either (box-backward is
frame-condition-independent). Landing the actual truth lemma remains outstanding. -/

/-! ## Adversarial Verification: `cs5Incest` Fails on `CS5CanonSegment`

Proving `cs5Incest (@cs5CanonMreach Atom)` — that the canonical model literally satisfies the
≤-mediated incestuality condition — is **mathematically false**, for a reason independent of
negation-completeness: `boxInv` is monotone in its argument, so for `cs5Incest`'s witness
`u' ≥ u` (i.e. `u.head ⊆ u'.head`) to satisfy `r u' w` (`boxInv u'.head ⊆ w.head`), it is
*necessary* that `boxInv u.head ⊆ w.head` already holds (any `□C ∈ u.head` persists into
`u'.head`, and `w.head` is untouched by the choice of `u'`) — extending `u` can never help
satisfy the goal, so only `u' := u` (up to the ≤-order) is ever a candidate. So `cs5Incest
cs5CanonMreach` is equivalent, on this world type, to *plain* symmetry of `cs5CanonMreach` —
exactly the naive two-sided condition Marin Remark 7.3 says is wrong intuitionistically.

The counterexample: the exploding world `Ω` (head `Set.univ`) is `cs5CanonMreach`-reachable
from **every** canonical world `P` (`boxInv P.head ⊆ Set.univ` trivially), yet `Ω` cannot reach
back to any non-exploding `P` (`Ω`'s head is already maximal, so `Ω' = Ω` is forced, and
`boxInv Set.univ = Set.univ ⊆ P.head` forces `P.head = Set.univ`). Combined with the fact that
`CS5` is consistent (witnessed below via a one-point model), this produces an outright `False`
from `cs5Incest (@cs5CanonMreach Atom)` — **not a proof-search failure, a genuine
counterexample**. Design options this opens up: restrict to a hereditary world subtype, à la
`CS4Segment`'s `excl` invariant; or weaken `cs5Incest` to an existential clause excluding the
exploding case, à la `cs4FC'`. -/

/-- The exploding canonical world is reachable from every canonical world: `boxInv P.head ⊆
Set.univ` trivially. -/
theorem cs5CanonMreach_to_univ (P : CS5CanonSegment Atom) :
    cs5CanonMreach P (CS5CanonSegment.ofHead (@quasiPrime_univ Atom (@CS5ModalAxiom Atom))) := by
  change (Set.univ : Set (Proposition Atom)) ∈ P.seg.tail
  rw [P.tail_eq]
  exact ⟨quasiPrime_univ, Set.subset_univ _⟩

/-- **If `cs5Incest cs5CanonMreach` held, every canonical world would be the exploding one.**
Applying `cs5Incest` at `(P, Ω)` (`Ω` the exploding world, always `cs5CanonMreach`-reachable from
`P` by `cs5CanonMreach_to_univ`) forces the mediating witness `Ω' ≥ Ω` to equal `Ω` (its head is
already `Set.univ`, the top of the subset order), and then `cs5CanonMreach Ω' P` forces
`P.head = Set.univ` too. -/
theorem cs5Incest_cs5CanonMreach_forces_univ
    (hincest : cs5Incest (@cs5CanonMreach Atom)) (P : CS5CanonSegment Atom) :
    P.seg.head = Set.univ := by
  obtain ⟨Ω', hΩΩ', hΩ'P⟩ := hincest (cs5CanonMreach_to_univ P)
  have hΩ'univ : Ω'.seg.head = Set.univ :=
    Set.Subset.antisymm (Set.subset_univ _) hΩΩ'
  have hmem : P.seg.head ∈ cs5CanonTail Ω'.seg.head := Ω'.tail_eq ▸ hΩ'P
  rw [hΩ'univ] at hmem
  exact Set.Subset.antisymm (Set.subset_univ _) (fun x _ => hmem.2 (Set.mem_univ _))

/-- **`CS5` is consistent**: `⊥` is not derivable. Witnessed by the trivial one-point model
(`World := Unit`, `r`/`val` always `True`, `botForces` always `False`) — `cs5FCIncest` holds
vacuously on this model (every clause's conclusion is trivially available since `r` is always
`True`), so `cs5_soundness_derivable_incest` would force `botForces Unit.unit` (i.e. `False`)
from a hypothetical derivation of `⊥`. -/
theorem cs5_consistent_incest : ¬ Derivable (@CS5ModalAxiom Atom) Proposition.bot := by
  intro h
  have hfc : cs5FCIncest (World := Unit) (fun _ _ => True) := by
    refine ⟨fun _ => trivial, fun _ _ => trivial, ?_, ?_, ?_⟩
    · intro w u u' t hwu hle hu't; exact ⟨Unit.unit, trivial, trivial⟩
    · intro w u u' hwu hle; exact ⟨Unit.unit, trivial, trivial⟩
    · intro w u hwu; exact ⟨Unit.unit, trivial, trivial⟩
  exact cs5_soundness_derivable_incest h Unit (fun _ _ => True) hfc
    (fun _ _ => True) (fun _ => False)
    (fun _ _ _ => trivial) (fun _ h => h.elim) (fun _ h => h.elim)
    (fun h _ => h.elim) (fun h => h.elim) Unit.unit

/-- **`cs5Incest` FAILS for `cs5CanonMreach` (mechanized).** Combines
`cs5Incest_cs5CanonMreach_forces_univ` (if incestuality held, every canonical world would be
exploding) with `cs5_consistent_incest` (there is a non-exploding canonical world, realized via
`quasi_head_realization` at the underivable `⊥`) for an outright contradiction. This is **not**
the negation-completeness wall — it is a distinct, purely set-theoretic obstruction
(monotonicity of `boxInv` against a fixed target, defeated by the universally reachable
exploding world) specific to verifying frame conditions on the *unrestricted* `CS5CanonSegment`
world type landed above. -/
theorem cs5Incest_cs5CanonMreach_false : ¬ cs5Incest (@cs5CanonMreach Atom) := by
  intro hincest
  obtain ⟨T, hT, hbotT⟩ := quasi_head_realization
    (fun φ ψ => CS5ModalAxiom.implyK φ ψ) (fun φ ψ χ => CS5ModalAxiom.implyS φ ψ χ)
    (fun A B χ => CS5ModalAxiom.orE A B χ) cs5_consistent_incest
  have huniv := cs5Incest_cs5CanonMreach_forces_univ hincest (CS5CanonSegment.ofHead hT)
  have huniv' : T = Set.univ := huniv
  exact hbotT (huniv' ▸ Set.mem_univ _)

/-! ## Simpson's Two-Sided Canonical Relation

Restores the diamond clause `{◇A | A ∈ Δ} ⊆ Γ` (Simpson 1994, corpus chunk `682e04d443e7bbd7`)
alongside the box clause `boxInv Γ ⊆ Δ` kept from `cs5OnesidedR` above. -/

/-- **Simpson's two-sided `CS5` canonical relation**: `Γ R Δ` iff `boxInv Γ ⊆ Δ` (the box clause,
Simpson's `{B | □B ∈ Γ} ⊆ Δ`, kept from `cs5OnesidedR`) AND `Δ ⊆ diaInv Γ` (the diamond clause,
Simpson's `{◇A | A ∈ Δ} ⊆ Γ`, i.e. `∀ A, A ∈ Δ → (◇A) ∈ Γ`, restored here). This uses the
textually-correct Simpson clause (quantifying over `A ∈ Δ`, not `◇A ∈ Δ`), cross-checked directly
against `cs5_boxInv_subset_iff` (`CS5.lean:589`) below. -/
def cs5TwoSidedR (Γ Δ : Set (Proposition Atom)) : Prop :=
  boxInv Γ ⊆ Δ ∧ Δ ⊆ diaInv Γ

/-- **Decisive structural fact.** For quasi-prime `Γ`, `Δ`, `cs5TwoSidedR Γ Δ` is EXTENSIONALLY
THE SAME RELATION as `Δ ∈ cs5Tail Γ` (`CS5.lean:632`, the discarded "old wall" two-sided
box-BOTH-directions relation `boxInv Γ ⊆ Δ ∧ boxInv Δ ⊆ Γ`). Proof: `cs5_boxInv_subset_iff`
(`CS5.lean:589`, `boxInv T ⊆ H ↔ T ⊆ diaInv H`, already landed, axiom-free) instantiated at
`H := Γ, T := Δ` reads `boxInv Δ ⊆ Γ ↔ Δ ⊆ diaInv Γ` — i.e. Simpson's diamond clause
`Δ ⊆ diaInv Γ` is LITERALLY EQUIVALENT (an `↔`, not a one-way implication) to the reverse box
clause `boxInv Δ ⊆ Γ`, for ANY pair of quasi-prime `CS5`-theories. This holds because `CS5`'s
`B` axiom (`bBox` + `bDia`, both `CS5ModalAxiom` constructors) makes diamond-membership and
reverse-box-non-membership dual at the level of every individual quasi-prime theory —
independent of which accessibility relation is under discussion, independent of `Ω`-exclusion,
independent of any world-type engineering.

**This shows restoring the diamond clause is NOT restoring independent information** (contrary
to the natural expectation that routing the witness through the diamond clause, rather than
through `boxInv` directly, would sidestep the `boxInv`-monotonicity problem): for `CS5`
specifically, it is restoring EXACTLY the `cs5Tail` relation replaced above, in disguise. See
`cs5Incest_forces_symm` and `cs5Incest_cs5PrimeMreach_false` below for the mechanized
consequence: verifying `cs5Incest` on any one-sided-tail world type forces every tail member
into `cs5Tail`-shape, which `cs5_symmetric_tail_box_gap` (`CS5.lean:712`, already mechanized)
shows cannot admit the box-refuting witness box-backward needs. -/
theorem cs5TwoSidedR_iff_cs5Tail {Γ Δ : Set (Proposition Atom)}
    (hΓ : QuasiPrime (@CS5ModalAxiom Atom) Γ) (hΔ : QuasiPrime (@CS5ModalAxiom Atom) Δ) :
    cs5TwoSidedR Γ Δ ↔ Δ ∈ cs5Tail Γ := by
  unfold cs5TwoSidedR cs5Tail
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hΔ, h1, (cs5_boxInv_subset_iff hΓ hΔ).mpr h2⟩
  · rintro ⟨_, h1, h2⟩
    exact ⟨h1, (cs5_boxInv_subset_iff hΓ hΔ).mp h2⟩

/-- **Corollary: `cs5TwoSidedR` is symmetric** on quasi-prime theories (immediate from
`cs5TwoSidedR_iff_cs5Tail` plus the already-landed `cs5Tail_symm`, `CS5.lean:645`). So at the
THEORY level (before any world-type/segment machinery), `cs5Incest`'s witness for `cs5TwoSidedR`
is always just `u' := u` (`le_refl`) — no `dia_refuting_theory` construction can do better, since
`cs5TwoSidedR` carries no more incestuality content than plain symmetry already does. -/
theorem cs5TwoSidedR_symm {Γ Δ : Set (Proposition Atom)}
    (hΓ : QuasiPrime (@CS5ModalAxiom Atom) Γ) (hΔ : QuasiPrime (@CS5ModalAxiom Atom) Δ)
    (h : cs5TwoSidedR Γ Δ) : cs5TwoSidedR Δ Γ :=
  (cs5TwoSidedR_iff_cs5Tail hΔ hΓ).mpr
    (cs5Tail_symm hΓ ((cs5TwoSidedR_iff_cs5Tail hΓ hΔ).mp h))

/-! ## The `Ω`-Excluding One-Sided World Type (`CS5PrimeSegment`)

Clones `CS4Segment`'s `excl`/`excl_head` hereditary-invariant pattern (`CS4.lean:373-403`) onto
`cs5OnesidedR`'s one-sided box tail, giving a world type carrying a hereditary excluded-diamond
invariant. Built ALONGSIDE `CS5CanonSegment` and `cs5TwoSidedR` above; nothing here edits
either's declarations. -/

/-- `4`-diamond contrapositive for `CS5`: `◇A ∉ H → ◇◇A ∉ H`. The hereditary closure step (CS4
precedent `cs4_not_dia_dia`, `CS4.lean:317`, using `fourDia` here instead) that lets an
excluded-diamond invariant propagate through the transitive closure of the one-sided tail. -/
theorem cs5_not_dia_dia {H : Set (Proposition Atom)} (hH : QuasiPrime (@CS5ModalAxiom Atom) H)
    {A : Proposition Atom} (h_not : (◇A) ∉ H) : (◇(◇A)) ∉ H :=
  fun h => h_not (mem_head_mp hH.closed (mem_of_axiom hH.closed (CS5ModalAxiom.fourDia A)) h)

/-- Tail determined by head `H` and an optional excluded diamond `E`, over `cs5OnesidedR` (NOT
`cs5Tail`) — mirrors `cs4Tail` (`CS4.lean:341`). -/
def cs5PrimeTail (H : Set (Proposition Atom)) (E : Option (Proposition Atom)) :
    Set (Set (Proposition Atom)) :=
  {t | QuasiPrime (@CS5ModalAxiom Atom) t ∧ cs5OnesidedR H t ∧ ∀ A, E = some A → (◇A) ∉ t}

/-- The `◇`-exclusion `CS5` canonical segment at head `H` excluding diamond `E`. Mirrors `cs4Seg`
(`CS4.lean:348`) exactly: `diam_witness` for `E = some A` needs `◇◇A ∉ H`, supplied by `fourDia`
via `cs5_not_dia_dia`, so the hereditary exclusion propagates to the witness theory. -/
def cs5PrimeSeg {H : Set (Proposition Atom)} (hH : QuasiPrime (@CS5ModalAxiom Atom) H)
    (E : Option (Proposition Atom)) (hE : ∀ A, E = some A → (◇A) ∉ H) :
    CKSegment (@CS5ModalAxiom Atom) where
  head := H
  tail := cs5PrimeTail H E
  head_qprime := hH
  tail_qprime := fun _ ht => ht.1
  box_reflect := fun _ hB _ ht => ht.2.1 hB
  diam_witness := fun B hB => by
    cases hE_eq : E with
    | none =>
      refine ⟨Set.univ, ⟨quasiPrime_univ, Set.subset_univ _, ?_⟩, Set.mem_univ _⟩
      rintro A ⟨⟩
    | some A =>
      obtain ⟨T, hsub, hT, hBT, hAT⟩ :=
        dia_refuting_theory (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
          (fun A B χ => .orE A B χ) (fun φ ψ => .k φ ψ) (fun φ ψ => .kdia φ ψ)
          hH hB (cs5_not_dia_dia hH (hE A hE_eq))
      refine ⟨T, ⟨hT, hsub, ?_⟩, hBT⟩
      rintro A' ⟨rfl⟩
      exact hAT

/-- `CS5` canonical worlds carrying a hereditary excluded-diamond invariant (mirrors
`CS4Segment`, `CS4.lean:373`). **Note (see `cs5Incest_cs5PrimeMreach_false` below): worlds with
`excl := none` (e.g. `.ofHead`) do NOT exclude the exploding world `Ω` from their tail** — the
`E = some A` exclusion clause is vacuous when `E = none`, exactly mirroring `CS4Segment` (which
never needed to banish `Ω`, since `CS4`'s frame condition has no incestuality-style clause). This
is the CS4-template's blind spot for `CS5`, diagnosed precisely below. -/
structure CS5PrimeSegment (Atom : Type u) where
  /-- The underlying segment. -/
  seg : CKSegment (@CS5ModalAxiom Atom)
  /-- The optional excluded diamond. -/
  excl : Option (Proposition Atom)
  /-- The excluded diamond is absent from the head (hereditary invariant). -/
  excl_head : ∀ A, excl = some A → (◇A) ∉ seg.head
  /-- The tail is exactly the `◇`-exclusion one-sided tail. -/
  tail_eq : seg.tail = cs5PrimeTail seg.head excl

instance : Preorder (CS5PrimeSegment Atom) :=
  Preorder.lift (fun s : CS5PrimeSegment Atom => s.seg)

/-- Canonical accessibility for the `◇`-exclusion one-sided model. -/
def cs5PrimeMreach (P Q : CS5PrimeSegment Atom) : Prop := cmreach P.seg Q.seg

/-- Maximal-tail world (no excluded diamond). -/
def CS5PrimeSegment.ofHead {H : Set (Proposition Atom)}
    (hH : QuasiPrime (@CS5ModalAxiom Atom) H) : CS5PrimeSegment Atom where
  seg := cs5PrimeSeg hH none (by rintro A ⟨⟩)
  excl := none
  excl_head := by rintro A ⟨⟩
  tail_eq := rfl

/-- The hereditary diamond-refuting world: excludes `A` from every world in its transitive
closure (via `cs5_not_dia_dia`), unlike a one-step `A`-exclusion. -/
def CS5PrimeSegment.diaRefuting
    {H : Set (Proposition Atom)} (hH : QuasiPrime (@CS5ModalAxiom Atom) H)
    {A : Proposition Atom} (h_not : (◇A) ∉ H) : CS5PrimeSegment Atom where
  seg := cs5PrimeSeg hH (some A) (by rintro A' ⟨rfl⟩; exact h_not)
  excl := some A
  excl_head := by rintro A' ⟨rfl⟩; exact h_not
  tail_eq := rfl

/-- `cs5PrimeMreach` is reflexive: `boxInv H ⊆ H` is axiom `T` (`cs5_boxInv_subset`) plus
`excl_head`. This comes for free from the axioms — no separate `refl` invariant is threaded
through the world type. -/
theorem cs5Prime_refl (P : CS5PrimeSegment Atom) : cs5PrimeMreach P P := by
  change P.seg.head ∈ P.seg.tail
  rw [P.tail_eq]
  exact ⟨P.seg.head_qprime, cs5_boxInv_subset P.seg.head_qprime, P.excl_head⟩

/-! ## `cs5Incest` on the Redesigned Frame

Attempts to verify the UNCHANGED `cs5Incest` (`:234`) on the `◇`-exclusion one-sided relation
`cs5PrimeMreach`, mirroring `cs4FC'_cs4Mreach`'s diamond-side technique
(`CS4.lean:441`). **RESULT: FAILURE**, mechanized below (`cs5Incest_cs5PrimeMreach_false`)
via TWO independent, sorry-free arguments — a general one (`cs5Incest_forces_symm`, tied to
`cs5TwoSidedR_iff_cs5Tail` above) and a concrete one (Ω remains reachable from `.ofHead`-built
worlds, exactly as with `cs5CanonMreach` above). -/

/-- **General monotonicity collapse** (generalizes the `cs5CanonMreach`-specific argument above
to ANY box-based canonical relation on ANY `CKSegment`-style world type, independent of
`Ω`-exclusion or world-type engineering). `≤` is head-inclusion on every `CKSegment`-lifted
`Preorder` in this file (`CKSegment.le_iff`, `Segment.lean:167`); if `r` implies the forward box
clause whenever `r w u`, `cs5Incest r` forces the witness to be `u' := u` itself: enlarging `u`
(`u ≤ u'` unfolds to `head u ⊆ head u'`) only ADDS to `boxInv (head u')` (`boxInv` is monotone
under `⊆`), so `boxInv (head u') ⊆ head w` can hold only if `boxInv (head u) ⊆ head w` ALREADY
does — no clever choice of `u'` escapes this, since it is unconditional set theory, not a fact
about any specific construction. -/
theorem cs5Incest_forces_symm
    {World : Type*} [Preorder World] (head : World → Set (Proposition Atom))
    (hmono : ∀ {w w' : World}, w ≤ w' → head w ⊆ head w')
    (r : World → World → Prop) (hbox : ∀ {w u : World}, r w u → boxInv (head w) ⊆ head u)
    (hincest : cs5Incest r) {w u : World} (hru : r w u) :
    boxInv (head u) ⊆ head w := by
  obtain ⟨u', hle, hru'w⟩ := hincest hru
  exact fun B hB => hbox hru'w (hmono hle hB)

/-- `Ω` (the exploding world, wrapped via `.ofHead` with no excluded diamond) is
`cs5PrimeMreach`-reachable from EVERY `.ofHead`-built canonical world — the `E := none` exclusion
clause is vacuous, exactly mirroring `cs4Seg`'s `none` case (which also admits `Set.univ`
unconditionally). This is the concrete instance of the note on `CS5PrimeSegment` above: the
CS4-style per-tail exclusion does not banish `Ω` from the type, only from tails explicitly built
with `excl := some _`. -/
theorem cs5PrimeMreach_ofHead_to_univ {H : Set (Proposition Atom)}
    (hH : QuasiPrime (@CS5ModalAxiom Atom) H) :
    cs5PrimeMreach (CS5PrimeSegment.ofHead hH)
      (CS5PrimeSegment.ofHead (@quasiPrime_univ Atom (@CS5ModalAxiom Atom))) := by
  change (Set.univ : Set (Proposition Atom)) ∈ cs5PrimeTail H none
  exact ⟨quasiPrime_univ, Set.subset_univ _, by rintro A ⟨⟩⟩

/-- **`cs5Incest` FAILS for `cs5PrimeMreach` (mechanized).** Two independent routes combine here:
1. `cs5Incest_forces_symm` shows that IF `cs5Incest cs5PrimeMreach` held, THEN
   `boxInv (head u) ⊆ head w` whenever `cs5PrimeMreach w u` — in particular at
   `w := .ofHead hT` (`T` realizing an underivable formula, hence non-exploding) and
   `u := .ofHead quasiPrime_univ` (`Ω`, reachable from `w` by `cs5PrimeMreach_ofHead_to_univ`),
   giving `boxInv Set.univ ⊆ T`.
2. `boxInv Set.univ = Set.univ` (every formula is trivially boxed inside `Set.univ`), so this
   forces `Set.univ ⊆ T`, i.e. `T = Set.univ` — contradicting `T`'s non-explosion (`⊥ ∉ T`,
   witnessed via `quasi_head_realization` at the underivable `⊥`, `cs5_consistent_incest`).

This is the SAME shape of contradiction as `cs5Incest_cs5CanonMreach_false` above (`Ω`
universally reachable, no witness can route back to a non-exploding world) — showing the
two-sided-R redesign's `Ω`-exclusion mechanism (CS4's per-tail `excl` field) does not actually
solve the problem it was built for: it excludes `Ω` only from tails explicitly constructed with
`excl := some _`, never from the base `.ofHead` worlds `cs5Incest` must quantify over. Combined
with `cs5TwoSidedR_iff_cs5Tail` above (Simpson's diamond clause is, for `CS5`, PROVABLY THE SAME
relation as the old two-sided `cs5Tail` wall), this is not a fixable implementation gap: any
world type whose reachability relation genuinely carries Simpson's diamond clause is forced into
`cs5Tail`-shape, which `cs5_symmetric_tail_box_gap` (`CS5.lean:712`, already mechanized) shows
cannot admit the box-refuting witness (omitting a specific formula) that box-backward needs.
**This confirms a genuine structural wall for the two-sided-R redesign as well, not merely a
fixable implementation gap.** -/
theorem cs5Incest_cs5PrimeMreach_false : ¬ cs5Incest (@cs5PrimeMreach Atom) := by
  intro hincest
  obtain ⟨T, hT, hbotT⟩ := quasi_head_realization
    (fun φ ψ => CS5ModalAxiom.implyK φ ψ) (fun φ ψ χ => CS5ModalAxiom.implyS φ ψ χ)
    (fun A B χ => CS5ModalAxiom.orE A B χ) (@cs5_consistent_incest Atom)
  have hru := cs5PrimeMreach_ofHead_to_univ hT
  have hsub : boxInv (Set.univ : Set (Proposition Atom)) ⊆ T :=
    cs5Incest_forces_symm (fun s : CS5PrimeSegment Atom => s.seg.head) (fun h => h)
      cs5PrimeMreach
      (fun {w u} hwu => (w.tail_eq ▸ hwu : u.seg.head ∈ cs5PrimeTail w.seg.head w.excl).2.1)
      hincest hru
  have huniv_sub : (Set.univ : Set (Proposition Atom)) ⊆ boxInv Set.univ :=
    fun x _ => Set.mem_univ (Proposition.box x)
  exact hbotT (hsub (huniv_sub (Set.mem_univ _)))

end Cslib.Logic.Modal

end
