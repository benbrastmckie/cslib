/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Constructive.CKExtension

/-! # CS4: Constructive Modal Logic S4 (Soundness and Completeness)

This module instantiates the frame-condition-parametrized segment scaffold
(`CKExtension.lean`) at the constructive analogue of `S4`: `CS4` = `CT` (`CT.lean`) plus the two
`4` schemata `fourBox : □A → □□A` and `fourDia : ◇◇A → ◇A`.

`CS4` is sound for `CKValidFC cs4FC` — Wijesekera-style fallible-world validity restricted to
frames whose modal relation `r` is reflexive and ≤-composed-transitive (`cs4FC`,
`CKExtension.lean`) — and **sound and complete for `CKValidFC cs4FC'`**, a **weakened** frame
condition (`cs4FC'`, `CKExtension.lean`) that replaces `cs4FC`'s blanket ≤-composed transitivity
with two existential clauses.

## Completeness

`ck_completeness`'s canonical model needs the diamond-backward truth-lemma case to refute an
unwarranted `◇A` via a *restricted*-tail witness segment (`diamRefutingSegment`,
`CKTruthLemma.lean`) whose tail excludes `A`. That exclusion is a *one-step* property (`A ∉ t`
for `t` a *direct* tail member) that does not propagate through the further ≤-composed-transitive
successors `cs4FC` universally quantifies over — nothing in the one-step construction prevents a
further successor from being (or extending to) the exploding theory `Set.univ`, which always
contains `A`. This is a real obstruction, but it is an obstruction **to `cs4FC` specifically**
(the frame condition, held fixed as `cs4FC`), not an inherent obstruction to `CS4`
completeness — the frame condition is the free parameter.

This is resolved with two changes:

1. **Weaken the frame condition** to `cs4FC'` (`CKExtension.lean`), replacing blanket
   ≤-composed transitivity with two existential clauses that the canonical model can actually
   satisfy. `cs4FC_implies_cs4FC'` witnesses that `cs4FC'` is a genuine weakening, so every
   `cs4FC`-sound theorem still holds (as a corollary via this bridge).
2. **Make the diamond-refuting exclusion hereditary**: `cs4Tail`/`CS4Segment` carry the excluded
   diamond `A` as an invariant (`excl_head`) that propagates through the *entire* transitive
   closure of the tail, not just one step. The key closure fact, `cs4_not_dia_dia`
   (`◇A ∉ H → ◇◇A ∉ H`, via `fourDia` contraposition), is what makes the hereditary exclusion
   self-propagate: `dia_refuting_theory` is reused **unchanged** at `A := ◇A₀`.

With these two changes, `cs4FC'_cs4Mreach` shows the canonical model satisfies `cs4FC'`, and
`cs4_truth_lemma` + `ckvalidFC_completeness` (`CKExtension.lean`) yield `cs4_completeness` and
the soundness-completeness biconditional `cs4_soundness_completeness`. `CT.lean`, `CK.lean`,
`Segment.lean`, `SegmentLindenbaum.lean`, and `CKTruthLemma.lean` are untouched by this
technique — no new foundational abstraction was needed.

**`CS5` cannot be closed by this same technique** — see `CS5.lean`'s module docstring for the
mechanized negative result (`bDia` fails soundness over the natural `CS5` analogue of `cs4FC'`).

## Main Definitions

- `CS4ModalAxiom`: `CTModalAxiom`'s constructors verbatim plus `fourBox`/`fourDia`.
- `cs4_axiom_sound`/`cs4_soundness`/`cs4_soundness_derivable`: soundness for `CKValidFC cs4FC`
  (corollaries of the primed versions below, retained for the
  `ConstructiveLatticeMonotonicity` frame-condition inclusion chain).
- `cs4_axiom_sound'`/`cs4_soundness'`/`cs4_soundness_derivable'`: soundness for the weakened
  `CKValidFC cs4FC'` (the primary proofs).
- `cs4Tail`/`cs4Seg`/`CS4Segment`/`cs4Mreach`: the hereditary `◇`-exclusion canonical world type
  and its accessibility relation.
- `cs4Val`/`cs4Bot`: canonical valuation and fallibility on `CS4Segment`.
- `cs4_truth_lemma`: `CKForces` agrees with head membership on the canonical model.
- `cs4_completeness`/`cs4_soundness_completeness`: **completeness** and the full
  soundness-completeness biconditional for `CKValidFC cs4FC'`.

## Main Results

- `cs4_axiom_sound`, `cs4_soundness`, `cs4_soundness_derivable` (over `cs4FC`).
- `cs4_axiom_sound'`, `cs4_soundness'`, `cs4_soundness_derivable'` (over the weaker `cs4FC'`).
- `cs4FC'_cs4Mreach`: the canonical model satisfies `cs4FC'`.
- `cs4_truth_lemma`: the truth lemma for the `CS4` canonical model.
- `cs4_completeness`: **completeness** for `CKValidFC cs4FC'`.
- `cs4_soundness_completeness`: the soundness-completeness biconditional for `CKValidFC cs4FC'`.

## References

* [D. Wijesekera, *Constructive modal logics I*][Wijesekera1990], §2 and Definition 1.1.4.
* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (the birelational `IS4`, the structural template for the box/diamond axiom pairing).
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

variable {Atom : Type u}

/-! ## The `CS4` Axiom Schemata -/

/-- Axiom schemata for constructive modal logic `CS4`: the 13 `CTModalAxiom` constructors
verbatim, plus the two `4` schemata `fourBox`/`fourDia`. Both box and diamond forms are required
since `◇` is primitive (not `□`-definable) in this framework's `Proposition` datatype (mirroring
`IS4.lean`'s `IS4` extension of `IT`). -/
inductive CS4ModalAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)`. -/
  | implyK (φ ψ : Proposition Atom) :
      CS4ModalAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`. -/
  | implyS (φ ψ χ : Proposition Atom) :
      CS4ModalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Ex falso quodlibet: `⊥ → φ`. -/
  | efq (φ : Proposition Atom) :
      CS4ModalAxiom (Proposition.bot.imp φ)
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)`. -/
  | andI (φ ψ : Proposition Atom) :
      CS4ModalAxiom (Cslib.Logic.Axioms.AndI φ ψ)
  /-- Left conjunction elimination: `φ ∧ ψ → φ`. -/
  | andE1 (φ ψ : Proposition Atom) :
      CS4ModalAxiom (Cslib.Logic.Axioms.AndE1 φ ψ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ`. -/
  | andE2 (φ ψ : Proposition Atom) :
      CS4ModalAxiom (Cslib.Logic.Axioms.AndE2 φ ψ)
  /-- Left disjunction introduction: `φ → φ ∨ ψ`. -/
  | orI1 (φ ψ : Proposition Atom) :
      CS4ModalAxiom (Cslib.Logic.Axioms.OrI1 φ ψ)
  /-- Right disjunction introduction: `ψ → φ ∨ ψ`. -/
  | orI2 (φ ψ : Proposition Atom) :
      CS4ModalAxiom (Cslib.Logic.Axioms.OrI2 φ ψ)
  /-- Disjunction elimination: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))`. -/
  | orE (φ ψ χ : Proposition Atom) :
      CS4ModalAxiom (Cslib.Logic.Axioms.OrE φ ψ χ)
  /-- Kb: `□(φ → ψ) → (□φ → □ψ)`. -/
  | k (φ ψ : Proposition Atom) :
      CS4ModalAxiom
        ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ)))
  /-- Kd: `□(φ → ψ) → (◇φ → ◇ψ)`. -/
  | kdia (φ ψ : Proposition Atom) :
      CS4ModalAxiom ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ)))
  /-- `T` box form: `□A → A`. -/
  | tBox (φ : Proposition Atom) :
      CS4ModalAxiom ((Proposition.box φ).imp φ)
  /-- `T` diamond form: `A → ◇A`. -/
  | tDia (φ : Proposition Atom) :
      CS4ModalAxiom (φ.imp (◇φ))
  /-- `4` box form: `□A → □□A`. -/
  | fourBox (φ : Proposition Atom) :
      CS4ModalAxiom ((Proposition.box φ).imp (Proposition.box (Proposition.box φ)))
  /-- `4` diamond form: `◇◇A → ◇A`. -/
  | fourDia (φ : Proposition Atom) :
      CS4ModalAxiom ((◇◇φ).imp (◇φ))

/-! ## Soundness -/

/-- Every `CS4ModalAxiom` instance is `CKValidFC cs4FC'` (Wijesekera-style fallible-world
validity over frames satisfying the **weakened** `CS4` frame condition `cs4FC'`). The 13 non-`4`
cases are `ct_axiom_sound`'s cases verbatim (`CT.lean`), with the `cs4FC'` components of `hfc`
threaded through unused. The two new cases:
- `fourDia` (`◇◇A → ◇A`): the ∀∃ diamond clause introduces `w'' ≥ w'`; unfolding `◇◇A@w''` at
  `w''` (`le_refl`) gives a witness `u` with `r w'' u ∧ (◇A)@u`; `hfcdia` on `r w'' u` supplies
  `u' ≥ u` such that every `r`-successor of `u'` is an `r`-successor of `w''`; unfolding `◇A@u`
  at `u'` gives `t` with `r u t ∧ A@t`, and `hprop t hu't` transports the `r`-edge to `w''`.
- `fourBox` (`□A → □□A`): the nested box goal introduces `w'' ≥ w'`, `u` with `r w'' u`,
  `u' ≥ u`, `t` with `r u' t`; `hfc4` on `r w'' u`, `u ≤ u'`, `r u' t` supplies a re-based world
  `v ≥ w''` with `r v t`; supply `A@t` from `□A@w'` at `v` (`≥ w'`, by transitivity of `≤`) and
  `t`. This is *harder* than the plain-`cs4FC` case (needs the existential re-basing), which is
  exactly the soundness cost of the weakened frame condition — see `cs4FC'`'s docstring
  (`CKExtension.lean`). -/
theorem cs4_axiom_sound' {φ : Proposition Atom} (h_ax : CS4ModalAxiom φ) :
    CKValidFC.{u, v} cs4FC' φ := by
  intro World _ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  obtain ⟨hrefl, hfc4, hfcdia⟩ := hfc
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
    obtain ⟨u', hle, hprop⟩ := hfcdia hru
    obtain ⟨t, hu't, hφt⟩ := hdia_u u' hle
    exact ⟨t, hprop t hu't, hφt⟩
  | fourBox φ =>
    intro w' _ hbox w'' hw'' u hru u' hu' t hrt
    obtain ⟨v, hwv, hvt⟩ := hfc4 hru hu' hrt
    exact hbox v (le_trans hw'' hwv) t hvt

/-- **Soundness for `cs4FC`** (corollary of `cs4_axiom_sound'` via `cs4FC_implies_cs4FC'`):
every `CS4ModalAxiom` instance is `CKValidFC cs4FC` — Wijesekera-style fallible-world validity
over the stronger frame class `cs4FC` (reflexive, ≤-composed-transitive). Retained for the
`ConstructiveLatticeMonotonicity` inclusion chain (`cs5FC_implies_cs4FC`, `cs4FC_implies_ctFC`);
the primed `cs4_axiom_sound'` is the primary proof since `cs4FC'`-validity is a stronger
statement (soundness over more frames). -/
theorem cs4_axiom_sound {φ : Proposition Atom} (h_ax : CS4ModalAxiom φ) :
    CKValidFC.{u, v} cs4FC φ := by
  intro World _ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  exact cs4_axiom_sound' h_ax World r (cs4FC_implies_cs4FC' hfc) val botForces v_uc bf_uc bf_val
    bf_r bf_r_wit w

/-- **Soundness for `cs4FC'`**: if `DerivationTree CS4ModalAxiom Γ φ`, then in any fallible-world
model satisfying the weakened frame condition `cs4FC'`, at any world `w` where all formulas in
`Γ` are forced, `φ` is also forced. Structural analogue of `ct_soundness` (`CT.lean`), threading
`hfc` through unused except at the `.ax` case. -/
theorem cs4_soundness'
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree CS4ModalAxiom Γ φ)
    {World : Type v} [Preorder World]
    (r : World → World → Prop) (hfc : cs4FC' r)
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
    exact cs4_axiom_sound' h_ax World r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  | .assumption _ ψ h_mem => exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact cs4_soundness' d₁ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w h_ctx
      w (le_refl w)
      (cs4_soundness' d₂ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w h_ctx)
  | .necessitation ψ d' =>
    intro w' _hle u _hru
    exact cs4_soundness' d' r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit u
      (fun _ h => nomatch h)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact cs4_soundness' d' r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Soundness for `cs4FC`** (corollary of `cs4_soundness'` via `cs4FC_implies_cs4FC'`):
if `DerivationTree CS4ModalAxiom Γ φ`, then in any fallible-world model whose modal relation is
reflexive and ≤-composed-transitive (`cs4FC`), at any world `w` where all formulas in `Γ` are
forced, `φ` is also forced. Retained for the `ConstructiveLatticeMonotonicity` inclusion chain. -/
theorem cs4_soundness
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree CS4ModalAxiom Γ φ)
    {World : Type v} [Preorder World]
    (r : World → World → Prop) (hfc : cs4FC r)
    (val : World → Atom → Prop) (botForces : World → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    (bf_val : ∀ {w : World} (p : Atom), botForces w → val w p)
    (bf_r : ∀ {w u : World}, botForces w → r w u → botForces u)
    (bf_r_wit : ∀ {w : World}, botForces w → ∃ u, r w u ∧ botForces u)
    (w : World)
    (h_ctx : ∀ ψ, ψ ∈ Γ → CKForces r val botForces w ψ) :
    CKForces r val botForces w φ :=
  cs4_soundness' d r (cs4FC_implies_cs4FC' hfc) val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
    h_ctx

/-- **Soundness for derivable formulas over `cs4FC'`**: if `Derivable CS4ModalAxiom φ`, then `φ`
is `CKValidFC cs4FC'`. -/
theorem cs4_soundness_derivable' {φ : Proposition Atom}
    (h : Derivable CS4ModalAxiom φ) : CKValidFC.{u, v} cs4FC' φ := by
  intro World _ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  obtain ⟨d⟩ := h
  exact cs4_soundness' d r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
    (fun _ h => nomatch h)

/-- **Soundness for derivable formulas over `cs4FC`** (corollary of `cs4_soundness_derivable'`
via `cs4FC_implies_cs4FC'`): if `Derivable CS4ModalAxiom φ`, then `φ` is `CKValidFC cs4FC`.
Retained for the `ConstructiveLatticeMonotonicity` inclusion chain. -/
theorem cs4_soundness_derivable {φ : Proposition Atom}
    (h : Derivable CS4ModalAxiom φ) : CKValidFC.{u, v} cs4FC φ := by
  intro World _ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  exact cs4_soundness_derivable' h World r (cs4FC_implies_cs4FC' hfc) val botForces v_uc bf_uc
    bf_val bf_r bf_r_wit w

/-! ## Canonical Model -/

/-! ### Part A: head-theory closure facts from the CS4 axioms -/

/-- `4`-box closure: `□B ∈ H → □□B ∈ H`. -/
theorem cs4_box_four {H : Set (Proposition Atom)} (hH : QuasiPrime CS4ModalAxiom H)
    {B : Proposition Atom} (hB : Proposition.box B ∈ H) :
    Proposition.box (Proposition.box B) ∈ H :=
  mem_head_mp hH.closed (axiom_mem_head (s := CKSegment.ofHead hH) (.fourBox B)) hB

/-- `4`-diamond contrapositive: `◇A ∉ H → ◇◇A ∉ H`. THE hereditary step that makes the
diamond-refuting construction below propagate through the transitive closure of the tail
(unlike a one-step `A`-exclusion, which does not propagate — see the module docstring). -/
theorem cs4_not_dia_dia {H : Set (Proposition Atom)} (hH : QuasiPrime CS4ModalAxiom H)
    {A : Proposition Atom} (h_not : (◇A) ∉ H) : (◇(◇A)) ∉ H :=
  fun h =>
    h_not (mem_head_mp hH.closed (axiom_mem_head (s := CKSegment.ofHead hH) (.fourDia A)) h)

/-- `T`-diamond: `A ∈ H → ◇A ∈ H`. -/
theorem cs4_dia_of_mem {H : Set (Proposition Atom)} (hH : QuasiPrime CS4ModalAxiom H)
    {A : Proposition Atom} (hA : A ∈ H) : (◇A) ∈ H :=
  mem_head_mp hH.closed (axiom_mem_head (s := CKSegment.ofHead hH) (.tDia A)) hA

/-- `T`-box: `boxInv H ⊆ H`. -/
theorem cs4_boxInv_subset {H : Set (Proposition Atom)} (hH : QuasiPrime CS4ModalAxiom H) :
    boxInv H ⊆ H :=
  fun _ hB => mem_head_mp hH.closed (axiom_mem_head (s := CKSegment.ofHead hH) (.tBox _)) hB

/-- The `4`-transfer chain used by every frame-condition proof: `boxInv` propagates through
two composed inclusions via one application of `4`-box closure. -/
theorem cs4_boxInv_trans {H K t : Set (Proposition Atom)} (hH : QuasiPrime CS4ModalAxiom H)
    (h1 : boxInv H ⊆ K) (h2 : boxInv K ⊆ t) : boxInv H ⊆ t :=
  fun _ hB => h2 (h1 (cs4_box_four hH hB))

/-! ### Part B: the `◇`-exclusion tail and its segment -/

/-- Tail determined by head `H` and an optional excluded diamond `E`. -/
def cs4Tail (H : Set (Proposition Atom)) (E : Option (Proposition Atom)) :
    Set (Set (Proposition Atom)) :=
  {t | QuasiPrime CS4ModalAxiom t ∧ boxInv H ⊆ t ∧ ∀ A, E = some A → (◇A) ∉ t}

/-- The `CS4` canonical segment at head `H` excluding the diamond `E`.
KEY: `diam_witness` for `E = some A` needs `◇◇A ∉ H`, supplied by `fourDia` via
`cs4_not_dia_dia`, so the hereditary exclusion propagates to the witness theory `T`. -/
def cs4Seg {H : Set (Proposition Atom)} (hH : QuasiPrime CS4ModalAxiom H)
    (E : Option (Proposition Atom)) (hE : ∀ A, E = some A → (◇A) ∉ H) :
    CKSegment (@CS4ModalAxiom Atom) where
  head := H
  tail := cs4Tail H E
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
          hH hB (cs4_not_dia_dia hH (hE A hE_eq))
      refine ⟨T, ⟨hT, hsub, ?_⟩, hBT⟩
      rintro A' ⟨rfl⟩
      exact hAT

/-! ### Part C: the `CS4` world type -/

/-- `CS4` canonical worlds: `◇`-exclusion-shaped segments. -/
structure CS4Segment (Atom : Type u) where
  /-- The underlying segment. -/
  seg : CKSegment (@CS4ModalAxiom Atom)
  /-- The optional excluded diamond. -/
  excl : Option (Proposition Atom)
  /-- The excluded diamond is absent from the head (hereditary invariant). -/
  excl_head : ∀ A, excl = some A → (◇A) ∉ seg.head
  /-- The tail is exactly the `◇`-exclusion tail. -/
  tail_eq : seg.tail = cs4Tail seg.head excl

instance : Preorder (CS4Segment Atom) := Preorder.lift (fun s : CS4Segment Atom => s.seg)

/-- Canonical accessibility. -/
def cs4Mreach (P Q : CS4Segment Atom) : Prop := cmreach P.seg Q.seg

/-- Maximal-tail world (no excluded diamond). -/
def CS4Segment.ofHead {H : Set (Proposition Atom)} (hH : QuasiPrime CS4ModalAxiom H) :
    CS4Segment Atom where
  seg := cs4Seg hH none (by rintro A ⟨⟩)
  excl := none
  excl_head := by rintro A ⟨⟩
  tail_eq := rfl

/-- The hereditary diamond-refuting world: excludes `A` from every world in its transitive
closure (via `cs4_not_dia_dia`), unlike a one-step `A`-exclusion. -/
def CS4Segment.diaRefuting {H : Set (Proposition Atom)} (hH : QuasiPrime CS4ModalAxiom H)
    {A : Proposition Atom} (h_not : (◇A) ∉ H) : CS4Segment Atom where
  seg := cs4Seg hH (some A) (by rintro A' ⟨rfl⟩; exact h_not)
  excl := some A
  excl_head := by rintro A' ⟨rfl⟩; exact h_not
  tail_eq := rfl

/-! ### Part D: the weakened frame condition and its canonical verification -/

/-- `cs4Mreach` is reflexive: derived from `boxInv H ⊆ H` (`tBox`, via `cs4_boxInv_subset`)
plus `excl_head`. This T-invariant comes for free from the axioms, so unlike `CTSegment`,
`CS4Segment` needs no separate `refl` field. -/
theorem cs4_refl (P : CS4Segment Atom) : cs4Mreach P P := by
  change P.seg.head ∈ P.seg.tail
  rw [P.tail_eq]
  exact ⟨P.seg.head_qprime, cs4_boxInv_subset P.seg.head_qprime, P.excl_head⟩

/-- The canonical model satisfies `cs4FC'`'s first (transitivity-style) existential clause.
Discharges its `boxInv` obligation via `cs4_boxInv_trans`. -/
theorem cs4_fc4 {w u u' t : CS4Segment Atom} (hwu : cs4Mreach w u) (hle : u ≤ u')
    (hu't : cs4Mreach u' t) : ∃ v : CS4Segment Atom, w ≤ v ∧ cs4Mreach v t := by
  refine ⟨CS4Segment.ofHead w.seg.head_qprime, Set.Subset.refl _, ?_⟩
  change t.seg.head ∈ cs4Tail w.seg.head none
  refine ⟨t.seg.head_qprime, ?_, by rintro A ⟨⟩⟩
  refine cs4_boxInv_trans (K := u'.seg.head) w.seg.head_qprime ?_ ?_
  · exact fun B hB => hle (w.seg.box_reflect B hB u.seg.head hwu)
  · exact fun B hB => u'.seg.box_reflect B hB t.seg.head hu't

/-- The canonical model satisfies `cs4FC'`'s second (fourDia-style) existential clause.
Discharges its `boxInv` obligation via `cs4_boxInv_trans`. -/
theorem cs4_fcdia {w u : CS4Segment Atom} (hwu : cs4Mreach w u) :
    ∃ u' : CS4Segment Atom, u ≤ u' ∧ ∀ t : CS4Segment Atom, cs4Mreach u' t → cs4Mreach w t := by
  have hmem : u.seg.head ∈ cs4Tail w.seg.head w.excl := w.tail_eq ▸ hwu
  refine ⟨⟨cs4Seg u.seg.head_qprime w.excl hmem.2.2, w.excl, hmem.2.2, rfl⟩,
    Set.Subset.refl _, ?_⟩
  intro t hu't
  have hu't' : t.seg.head ∈ cs4Tail u.seg.head w.excl := hu't
  change t.seg.head ∈ w.seg.tail
  rw [w.tail_eq]
  exact ⟨t.seg.head_qprime,
    cs4_boxInv_trans w.seg.head_qprime hmem.2.1 hu't'.2.1, hu't'.2.2⟩

/-- **The canonical CS4 model satisfies the weakened frame condition.** -/
theorem cs4FC'_cs4Mreach : cs4FC' (@cs4Mreach Atom) :=
  ⟨cs4_refl, fun h1 h2 h3 => cs4_fc4 h1 h2 h3, fun h => cs4_fcdia h⟩

/-! ### Part F: the truth lemma on the CS4 world type -/

/-- Canonical valuation. -/
def cs4Val (s : CS4Segment Atom) (p : Atom) : Prop := cval s.seg p

/-- Canonical fallibility. -/
def cs4Bot (s : CS4Segment Atom) : Prop := cbotForces s.seg

/-- The truth lemma for the `CS4` canonical model: `CKForces` at a world `s` agrees with head
membership. The diamond-backward case (`φ ∈ s.seg.head → CKForces (◇φ) s`) is the one the whole
`cs4Tail`/`CS4Segment` technique exists for: it uses `CS4Segment.diaRefuting` to build the
hereditary `◇φ`-refuting witness world, and closes via `cs4_dia_of_mem` (`tDia`) against the
hereditary `◇A`-exclusion invariant carried by that world. -/
theorem cs4_truth_lemma (s : CS4Segment Atom) (φ : Proposition Atom) :
    CKForces cs4Mreach cs4Val cs4Bot s φ ↔ φ ∈ s.seg.head := by
  induction φ generalizing s with
  | atom p => exact Iff.rfl
  | bot => exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    constructor
    · intro hf
      by_contra h_not
      obtain ⟨T, hHT, hT, hφT, hψT⟩ :=
        imp_refuting_theory (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
          (fun A B χ => .orE A B χ) s.seg.head_qprime h_not
      exact hψT ((ihψ (CS4Segment.ofHead hT)).mp
        (hf (CS4Segment.ofHead hT) hHT ((ihφ (CS4Segment.ofHead hT)).mpr hφT)))
    · intro hmem s' hle hfφ
      exact (ihψ s').mpr
        (mem_head_mp s'.seg.head_qprime.closed (hle hmem) ((ihφ s').mp hfφ))
  | and φ ψ ihφ ihψ =>
    constructor
    · rintro ⟨hfφ, hfψ⟩
      exact mem_head_mp s.seg.head_qprime.closed
        (mem_head_mp s.seg.head_qprime.closed
          (mem_of_axiom s.seg.head_qprime.closed (CS4ModalAxiom.andI φ ψ))
          ((ihφ s).mp hfφ))
        ((ihψ s).mp hfψ)
    · intro hmem
      exact ⟨(ihφ s).mpr (mem_head_mp s.seg.head_qprime.closed
                (mem_of_axiom s.seg.head_qprime.closed (CS4ModalAxiom.andE1 φ ψ)) hmem),
             (ihψ s).mpr (mem_head_mp s.seg.head_qprime.closed
                (mem_of_axiom s.seg.head_qprime.closed (CS4ModalAxiom.andE2 φ ψ)) hmem)⟩
  | or φ ψ ihφ ihψ =>
    constructor
    · rintro (hfφ | hfψ)
      · exact mem_head_mp s.seg.head_qprime.closed
          (mem_of_axiom s.seg.head_qprime.closed (CS4ModalAxiom.orI1 φ ψ)) ((ihφ s).mp hfφ)
      · exact mem_head_mp s.seg.head_qprime.closed
          (mem_of_axiom s.seg.head_qprime.closed (CS4ModalAxiom.orI2 φ ψ)) ((ihψ s).mp hfψ)
    · intro hmem
      rcases s.seg.head_qprime.disj hmem with h | h
      · exact Or.inl ((ihφ s).mpr h)
      · exact Or.inr ((ihψ s).mpr h)
  | box φ ihφ =>
    constructor
    · intro hf
      by_contra h_not
      obtain ⟨T, hsub, hT, hAT⟩ :=
        box_refuting_theory (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
          (fun A B χ => .orE A B χ) (fun φ ψ => .k φ ψ) s.seg.head_qprime h_not
      have hr : cs4Mreach (CS4Segment.ofHead s.seg.head_qprime) (CS4Segment.ofHead hT) :=
        ⟨hT, hsub, by rintro A ⟨⟩⟩
      exact hAT ((ihφ (CS4Segment.ofHead hT)).mp
        (hf (CS4Segment.ofHead s.seg.head_qprime) (Set.Subset.refl _)
          (CS4Segment.ofHead hT) hr))
    · intro hmem s' hle Q hr
      exact (ihφ Q).mpr (s'.seg.box_reflect φ (hle hmem) Q.seg.head hr)
  | diamond φ ihφ =>
    constructor
    · intro hf
      by_contra h_not
      obtain ⟨Q, hr, hfQ⟩ :=
        hf (CS4Segment.diaRefuting s.seg.head_qprime h_not) (Set.Subset.refl _)
      exact hr.2.2 φ rfl (cs4_dia_of_mem Q.seg.head_qprime ((ihφ Q).mp hfQ))
    · intro hmem s' hle
      obtain ⟨t, ht_mem, hφt⟩ := s'.seg.diam_witness φ (hle hmem)
      exact ⟨CS4Segment.ofHead (s'.seg.tail_qprime t ht_mem), ht_mem, (ihφ _).mpr hφt⟩

/-! ### Part G: full CS4 completeness -/

/-- `cs4Val` is upward-closed (segment analogue of `cval_upward_closed`). -/
theorem cs4Val_upward_closed {w w' : CS4Segment Atom} (p : Atom) (h : w ≤ w')
    (hv : cs4Val w p) : cs4Val w' p := cval_upward_closed p h hv

/-- `cs4Bot` is upward-closed (segment analogue of `cbotForces_upward_closed`). -/
theorem cs4Bot_upward_closed {w w' : CS4Segment Atom} (h : w ≤ w') (hb : cs4Bot w) :
    cs4Bot w' := cbotForces_upward_closed h hb

/-- Every atom is forced at an exploding world. -/
theorem cs4Bot_val {w : CS4Segment Atom} (p : Atom) (hb : cs4Bot w) : cs4Val w p :=
  cbotForces_val (fun φ => .efq φ) p hb

/-- `cs4Bot` propagates along `cs4Mreach`. -/
theorem cs4Bot_mreach {w u : CS4Segment Atom} (hb : cs4Bot w) (hr : cs4Mreach w u) :
    cs4Bot u := cbotForces_mreach (fun φ => .efq φ) hb hr

/-- Every exploding world has an exploding `cs4Mreach`-successor. -/
theorem cs4Bot_mreach_wit {w : CS4Segment Atom} (hb : cs4Bot w) :
    ∃ u : CS4Segment Atom, cs4Mreach w u ∧ cs4Bot u := by
  obtain ⟨t, ht_mem, ht_bot⟩ :=
    w.seg.diam_witness _ (mem_of_bot_mem (fun φ => .efq φ) w.seg.head_qprime.closed hb
      (◇Proposition.bot))
  exact ⟨CS4Segment.ofHead (w.seg.tail_qprime t ht_mem), ht_mem, ht_bot⟩

/-- **COMPLETENESS FOR CS4** over the weakened frame condition `cs4FC'`: every `cs4FC'`-valid
formula is derivable. -/
theorem cs4_completeness {φ : Proposition Atom} (h_valid : CKValidFC.{u, u} cs4FC' φ) :
    Derivable CS4ModalAxiom φ :=
  ckvalidFC_completeness cs4FC' cs4Mreach cs4Val cs4Bot
    cs4Val_upward_closed cs4Bot_upward_closed cs4Bot_val cs4Bot_mreach cs4Bot_mreach_wit
    cs4FC'_cs4Mreach
    (fun {φ} h_nd => by
      obtain ⟨T, hT, hφT⟩ := quasi_head_realization (fun φ ψ => .implyK φ ψ)
        (fun φ ψ χ => .implyS φ ψ χ) (fun A B χ => .orE A B χ) h_nd
      exact ⟨CS4Segment.ofHead hT,
        fun hf => hφT ((cs4_truth_lemma (CS4Segment.ofHead hT) φ).mp hf)⟩)
    h_valid

/-- **SOUNDNESS-COMPLETENESS BICONDITIONAL FOR CS4** over the weakened frame condition `cs4FC'`:
`φ` is derivable iff `φ` is `CKValidFC cs4FC'`. -/
theorem cs4_soundness_completeness {φ : Proposition Atom} :
    Derivable CS4ModalAxiom φ ↔ CKValidFC.{u, u} cs4FC' φ :=
  ⟨cs4_soundness_derivable', cs4_completeness⟩

end Cslib.Logic.Modal
