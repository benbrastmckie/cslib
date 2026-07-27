/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Constructive.CKExtension

/-! # CT: Constructive Modal Logic T (Soundness + Completeness)

This module instantiates the frame-condition-parametrized segment scaffold
(`CKExtension.lean`) at the constructive analogue of `T`: `CT` = bare `CK` (`CK.lean`) plus the
two `T` schemata `tBox : □A → A` and `tDia : A → ◇A`. As in the birelational `IT`/`IS4`/`IS5`
family (`Intuitionistic/IT.lean`), **both** a box-form and a diamond-form schema are required
because `◇` is primitive (not `□`-definable) in this framework's `Proposition` datatype.

`CT` is sound and complete for `CKValidFC ctFC` — Wijesekera-style fallible-world validity
restricted to frames whose modal relation `r` is reflexive (`ctFC`, `CKExtension.lean`). The
canonical model is built over `CTSegment`, a restricted subtype of `CKSegment CTModalAxiom`
carrying reflexivity of the canonical accessibility (`cmreach`) as an invariant — this port is
necessitated because `ctFC` does **not** hold globally on raw `CKSegment CTModalAxiom` (a
consistent-head segment with tail `{Set.univ}` is well-formed but not `cmreach`-reflexive).

## Main Definitions

- `CTModalAxiom`: bare `CKModalAxiom`'s 11 constructors verbatim plus `tBox`/`tDia`.
- `ct_axiom_sound`/`ct_soundness`/`ct_soundness_derivable`: soundness for `CKValidFC ctFC`.
- `CTSegment`: the `CT` canonical world subtype (`CKSegment CTModalAxiom` with the invariant
  `seg.head ∈ seg.tail`, i.e. `cmreach seg seg`), with its lifted `Preorder` and projected
  accessibility/valuation/fallibility (`ctMreach`/`ctVal`/`ctBot`).
- `ct_completeness`/`ct_consistent`/`ct_soundness_completeness`: completeness (via
  `ckvalidFC_completeness` instantiated over `CTSegment`), consistency, and the biconditional.

## References

* [D. Wijesekera, *Constructive modal logics I*][Wijesekera1990], §2 and Definition 1.1.4.
* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (the birelational `IT`, the structural template for the box/diamond axiom pairing).
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

variable {Atom : Type u}

/-! ## The `CT` Axiom Schemata -/

/-- Axiom schemata for constructive modal logic `CT`: the 11 `CKModalAxiom` constructors
verbatim, plus the two `T` schemata `tBox`/`tDia`. Both box and diamond forms are required
since `◇` is primitive (not `□`-definable) in this framework's `Proposition` datatype
(mirroring `IT.lean`'s `IT` extension of `IK`). -/
inductive CTModalAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)`. -/
  | implyK (φ ψ : Proposition Atom) :
      CTModalAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`. -/
  | implyS (φ ψ χ : Proposition Atom) :
      CTModalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Ex falso quodlibet: `⊥ → φ`. -/
  | efq (φ : Proposition Atom) :
      CTModalAxiom (Proposition.bot.imp φ)
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)`. -/
  | andI (φ ψ : Proposition Atom) :
      CTModalAxiom (Cslib.Logic.Axioms.AndI φ ψ)
  /-- Left conjunction elimination: `φ ∧ ψ → φ`. -/
  | andE1 (φ ψ : Proposition Atom) :
      CTModalAxiom (Cslib.Logic.Axioms.AndE1 φ ψ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ`. -/
  | andE2 (φ ψ : Proposition Atom) :
      CTModalAxiom (Cslib.Logic.Axioms.AndE2 φ ψ)
  /-- Left disjunction introduction: `φ → φ ∨ ψ`. -/
  | orI1 (φ ψ : Proposition Atom) :
      CTModalAxiom (Cslib.Logic.Axioms.OrI1 φ ψ)
  /-- Right disjunction introduction: `ψ → φ ∨ ψ`. -/
  | orI2 (φ ψ : Proposition Atom) :
      CTModalAxiom (Cslib.Logic.Axioms.OrI2 φ ψ)
  /-- Disjunction elimination: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))`. -/
  | orE (φ ψ χ : Proposition Atom) :
      CTModalAxiom (Cslib.Logic.Axioms.OrE φ ψ χ)
  /-- Kb: `□(φ → ψ) → (□φ → □ψ)`. -/
  | k (φ ψ : Proposition Atom) :
      CTModalAxiom
        ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ)))
  /-- Kd: `□(φ → ψ) → (◇φ → ◇ψ)`. -/
  | kdia (φ ψ : Proposition Atom) :
      CTModalAxiom ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ)))
  /-- `T` box form: `□A → A`. -/
  | tBox (φ : Proposition Atom) :
      CTModalAxiom ((Proposition.box φ).imp φ)
  /-- `T` diamond form: `A → ◇A`. -/
  | tDia (φ : Proposition Atom) :
      CTModalAxiom (φ.imp (◇φ))

/-! ## Soundness -/

/-- Every `CTModalAxiom` instance is `CKValidFC ctFC` (Wijesekera-style fallible-world validity
over reflexive frames). The 11 non-`T` cases are `ck_axiom_sound`'s cases verbatim
(`CK.lean:149-183`), with the reflexivity hypothesis `hfc` threaded through unused. The two new
cases:
- `tBox` (`□A → A`): plain reflexivity — instantiate the box hypothesis at `w'` (`le_refl`) and
  successor `w'` (`hfc w'`).
- `tDia` (`A → ◇A`): the ∀∃ diamond clause introduces `w'' ≥ w'`; witness `w''` itself via
  `hfc w''`, with `A@w''` by persistence from `A@w'` (`w' ≤ w''`). -/
theorem ct_axiom_sound {φ : Proposition Atom} (h_ax : CTModalAxiom φ) :
    CKValidFC.{u, v} ctFC φ := by
  intro World _ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
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
  | andE1 φ ψ =>
    intro _ _ h; exact h.1
  | andE2 φ ψ =>
    intro _ _ h; exact h.2
  | orI1 φ ψ =>
    intro _ _ h; exact Or.inl h
  | orI2 φ ψ =>
    intro _ _ h; exact Or.inr h
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
    exact hbox w' (le_refl w') w' (hfc w')
  | tDia φ =>
    intro w' _ hφ w'' hw''
    exact ⟨w'', hfc w'', ckforces_persistence v_uc bf_uc hw'' hφ⟩

/-- **Soundness**: if `DerivationTree CTModalAxiom Γ φ`, then in any fallible-world model whose
modal relation is reflexive (`ctFC`), at any world `w` where all formulas in `Γ` are forced, `φ`
is also forced. Structural analogue of `ck_soundness` (`CK.lean:189`), threading the
reflexivity hypothesis `hfc` through unused except at the `.ax` case. -/
theorem ct_soundness
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree CTModalAxiom Γ φ)
    {World : Type v} [Preorder World]
    (r : World → World → Prop) (hfc : ctFC r)
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
    exact ct_axiom_sound h_ax World r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact ct_soundness d₁ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w h_ctx
      w (le_refl w)
      (ct_soundness d₂ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w h_ctx)
  | .necessitation ψ d' =>
    intro w' _hle u _hru
    exact ct_soundness d' r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit u
      (fun _ h => nomatch h)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact ct_soundness d' r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Soundness for derivable formulas**: if `Derivable CTModalAxiom φ`, then `φ` is
`CKValidFC ctFC`. -/
theorem ct_soundness_derivable {φ : Proposition Atom}
    (h : Derivable CTModalAxiom φ) : CKValidFC.{u, v} ctFC φ := by
  intro World _ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  obtain ⟨d⟩ := h
  exact ct_soundness d r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
    (fun _ h => nomatch h)

/-! ## The `CT` World Subtype -/

/-- **`CT` canonical worlds**: segments whose head is a modal successor of itself — the
`T`-invariant `seg.head ∈ seg.tail`, i.e. `cmreach seg seg`. Restricting to this subtype is
necessary because `ctFC` does **not** hold on raw `CKSegment CTModalAxiom` (a segment with a
consistent head and tail `{Set.univ}` is well-formed but not `cmreach`-reflexive). -/
structure CTSegment (Atom : Type u) where
  /-- The underlying `CT` segment. -/
  seg : CKSegment (@CTModalAxiom Atom)
  /-- The `T`-invariant: the segment's head is one of its own modal successors. -/
  refl : seg.head ∈ seg.tail

/-- The canonical preorder on `CTSegment Atom`, lifted along `.seg` from `CKSegment`'s
head-inclusion preorder: `P ≤ Q ↔ P.seg.head ⊆ Q.seg.head`. -/
instance : Preorder (CTSegment Atom) := Preorder.lift (fun s : CTSegment Atom => s.seg)

/-- `≤` on `CTSegment Atom` agrees with `≤` on the underlying segment (definitional unfolding
lemma for the lifted preorder). -/
theorem CTSegment.le_iff {P Q : CTSegment Atom} : P ≤ Q ↔ P.seg ≤ Q.seg := Iff.rfl

/-- The `CT` canonical modal accessibility, projected from `cmreach` along `.seg`. -/
def ctMreach (P Q : CTSegment Atom) : Prop := cmreach P.seg Q.seg

/-- The `CT` canonical valuation, projected from `cval` along `.seg`. -/
def ctVal (s : CTSegment Atom) (p : Atom) : Prop := cval s.seg p

/-- The `CT` canonical fallibility predicate, projected from `cbotForces` along `.seg`. -/
def ctBot (s : CTSegment Atom) : Prop := cbotForces s.seg

/-- The `CT` canonical accessibility is reflexive: immediate from the `refl` field
(`ctMreach P P = cmreach P.seg P.seg = P.seg.head ∈ P.seg.tail = P.refl`). -/
theorem ctFC_ctMreach : ctFC (@ctMreach Atom) := fun P => P.refl

/-! ## Invariant Discharge -/

/-- **`ofHead` satisfies the `T`-invariant**: for any quasi-prime `H` closed under `boxInv`
(`boxInv H ⊆ H` — deductively closed, `tBox`-closed via MP: `□B ∈ H ⇒ (□B → B) ∈ H ⇒ B ∈ H`),
the segment `CKSegment.ofHead hH` (maximal tail `{t | QuasiPrime t ∧ boxInv H ⊆ t}`) has its
own head as a tail member. -/
theorem ct_ofHead_refl {H : Set (Proposition Atom)} (hH : QuasiPrime CTModalAxiom H)
    (h_boxInv : boxInv H ⊆ H) :
    (CKSegment.ofHead hH).head ∈ (CKSegment.ofHead hH).tail :=
  ⟨hH, h_boxInv⟩

/-- Every quasi-prime theory over `CTModalAxiom` is closed under `boxInv`: `□B ∈ H` gives
`(□B → B) ∈ H` by `tBox`, so `B ∈ H` by modus ponens (`mem_head_mp`/`axiom_mem_head`). -/
theorem ct_boxInv_subset {H : Set (Proposition Atom)} (hH : QuasiPrime CTModalAxiom H) :
    boxInv H ⊆ H := by
  intro B hB
  exact mem_head_mp hH.closed (axiom_mem_head (s := CKSegment.ofHead hH) (.tBox B)) hB

/-- The `CT`-realizing segment for `CKSegment.ofHead`, bundled with its `T`-invariant proof. -/
def CTSegment.ofHead {H : Set (Proposition Atom)} (hH : QuasiPrime CTModalAxiom H) :
    CTSegment Atom where
  seg := CKSegment.ofHead hH
  refl := ct_ofHead_refl hH (ct_boxInv_subset hH)

@[simp] theorem CTSegment.ofHead_head {H : Set (Proposition Atom)}
    (hH : QuasiPrime CTModalAxiom H) : (CTSegment.ofHead hH).seg.head = H := rfl

/-- **The diamond-refuting segment satisfies the `T`-invariant**: `diamRefutingSegment s h_not`
(head `= s.head`, tail restricted to quasi-prime supersets of `boxInv s.head` omitting `A`) has
its own head as a tail member, since `boxInv s.head ⊆ s.head` (by `ct_boxInv_subset`) and
`A ∉ s.head` (from `◇A ∉ s.head` via `tDia`: `A ∈ s.head ⇒ ◇A ∈ s.head`, contrapositive). -/
theorem ct_diamRefutingSegment_refl (s : CKSegment CTModalAxiom) {A : Proposition Atom}
    (h_not : (◇A) ∉ s.head) :
    s.head ∈
      (diamRefutingSegment (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
        (fun A B χ => .orE A B χ) (fun φ ψ => .k φ ψ) (fun φ ψ => .kdia φ ψ) s h_not).tail := by
  refine ⟨s.head_qprime, ct_boxInv_subset s.head_qprime, ?_⟩
  intro hA
  exact h_not (mem_head_mp s.head_qprime.closed (axiom_mem_head (s := s) (.tDia A)) hA)

/-- The exploding segment satisfies the `T`-invariant: `Set.univ` is trivially a member of the
singleton tail `{Set.univ}`. -/
theorem ct_cexpl_refl {Atom : Type u} :
    (cexpl (Axioms := @CTModalAxiom Atom)).head ∈ (cexpl (Axioms := @CTModalAxiom Atom)).tail :=
  Set.mem_singleton _

/-- **The diamond-refuting segment, realized as a `CTSegment`** (bundling
`ct_diamRefutingSegment_refl`, using that `diamRefutingSegment`'s head is definitionally `s.head`
so the invariant proof transfers without rewriting). -/
def CTSegment.diamRefuting (s : CKSegment CTModalAxiom) {A : Proposition Atom}
    (h_not : (◇A) ∉ s.head) : CTSegment Atom where
  seg := diamRefutingSegment (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    (fun A B χ => .orE A B χ) (fun φ ψ => .k φ ψ) (fun φ ψ => .kdia φ ψ) s h_not
  refl := ct_diamRefutingSegment_refl s h_not

/-! ## Truth-Lemma Transport -/

/-- **Truth lemma for `CTSegment`** (report D3.4 obligation 2, the truth-lemma port): `CKForces`
over `ctMreach`/`ctVal`/`ctBot` coincides with head membership in the underlying segment. The
proof structurally mirrors `ck_truth_lemma` (`CKTruthLemma.lean:133`), with every
`CKSegment.ofHead`/`diamRefutingSegment` witness replaced by its `CTSegment` realization
(`CTSegment.ofHead`/`CTSegment.diamRefuting`, both proven to satisfy the `T`-invariant above) —
the port is possible precisely because every witness construction the original proof needs stays
within the restricted subtype. -/
theorem ct_truth_lemma (s : CTSegment Atom) (φ : Proposition Atom) :
    CKForces ctMreach ctVal ctBot s φ ↔ φ ∈ s.seg.head := by
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
      exact hψT ((ihψ (CTSegment.ofHead hT)).mp
        (hf (CTSegment.ofHead hT) hHT ((ihφ (CTSegment.ofHead hT)).mpr hφT)))
    · intro hmem s' hle hfφ
      exact (ihψ s').mpr
        (mem_head_mp s'.seg.head_qprime.closed (hle hmem) ((ihφ s').mp hfφ))
  | and φ ψ ihφ ihψ =>
    constructor
    · rintro ⟨hfφ, hfψ⟩
      exact mem_head_mp s.seg.head_qprime.closed
        (mem_head_mp s.seg.head_qprime.closed
          (mem_of_axiom s.seg.head_qprime.closed (CTModalAxiom.andI φ ψ))
          ((ihφ s).mp hfφ))
        ((ihψ s).mp hfψ)
    · intro hmem
      exact ⟨(ihφ s).mpr (mem_head_mp s.seg.head_qprime.closed
                (mem_of_axiom s.seg.head_qprime.closed (CTModalAxiom.andE1 φ ψ)) hmem),
             (ihψ s).mpr (mem_head_mp s.seg.head_qprime.closed
                (mem_of_axiom s.seg.head_qprime.closed (CTModalAxiom.andE2 φ ψ)) hmem)⟩
  | or φ ψ ihφ ihψ =>
    constructor
    · rintro (hfφ | hfψ)
      · exact mem_head_mp s.seg.head_qprime.closed
          (mem_of_axiom s.seg.head_qprime.closed (CTModalAxiom.orI1 φ ψ)) ((ihφ s).mp hfφ)
      · exact mem_head_mp s.seg.head_qprime.closed
          (mem_of_axiom s.seg.head_qprime.closed (CTModalAxiom.orI2 φ ψ)) ((ihψ s).mp hfψ)
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
      have hr : ctMreach (CTSegment.ofHead s.seg.head_qprime) (CTSegment.ofHead hT) :=
        ⟨hT, hsub⟩
      exact hAT ((ihφ (CTSegment.ofHead hT)).mp
        (hf (CTSegment.ofHead s.seg.head_qprime) (Set.Subset.refl _)
          (CTSegment.ofHead hT) hr))
    · intro hmem s' hle Q hr
      exact (ihφ Q).mpr (s'.seg.box_reflect φ (hle hmem) Q.seg.head hr)
  | diamond φ ihφ =>
    constructor
    · intro hf
      by_contra h_not
      obtain ⟨Q, hr, hfQ⟩ :=
        hf (CTSegment.diamRefuting s.seg h_not) (Set.Subset.refl _)
      exact hr.2.2 ((ihφ Q).mp hfQ)
    · intro hmem s' hle
      obtain ⟨t, ht_mem, hφt⟩ := s'.seg.diam_witness φ (hle hmem)
      exact ⟨CTSegment.ofHead (s'.seg.tail_qprime t ht_mem), ht_mem, (ihφ _).mpr hφt⟩

/-! ## Completeness and Consistency -/

/-- The `CT` canonical valuation is upward-closed under `ctMreach`'s preorder. -/
theorem ctVal_upward_closed {w w' : CTSegment Atom} (p : Atom) (h : w ≤ w') (hv : ctVal w p) :
    ctVal w' p :=
  cval_upward_closed p h hv

/-- The `CT` canonical fallibility predicate is upward-closed. -/
theorem ctBot_upward_closed {w w' : CTSegment Atom} (h : w ≤ w') (hb : ctBot w) : ctBot w' :=
  cbotForces_upward_closed h hb

/-- Exploding `CTSegment`s force all atoms. -/
theorem ctBot_val {w : CTSegment Atom} (p : Atom) (hb : ctBot w) : ctVal w p :=
  cbotForces_val (fun φ => .efq φ) p hb

/-- Modal successors of exploding `CTSegment`s explode. -/
theorem ctBot_mreach {w u : CTSegment Atom} (hb : ctBot w) (hr : ctMreach w u) : ctBot u :=
  cbotForces_mreach (fun φ => .efq φ) hb hr

/-- Every exploding `CTSegment` has an exploding modal successor, realized within the
subtype via `CTSegment.ofHead` (the same construction `cbotForces_mreach_wit` uses on raw
segments, re-derived here so the witness carries the `T`-invariant). -/
theorem ctBot_mreach_wit {w : CTSegment Atom} (hb : ctBot w) :
    ∃ u : CTSegment Atom, ctMreach w u ∧ ctBot u := by
  obtain ⟨t, ht_mem, ht_bot⟩ :=
    w.seg.diam_witness _ (mem_of_bot_mem (fun φ => .efq φ) w.seg.head_qprime.closed hb
      (◇Proposition.bot))
  exact ⟨CTSegment.ofHead (w.seg.tail_qprime t ht_mem), ht_mem, ht_bot⟩

/-- **Completeness for `CT`**: any formula that is `CKValidFC ctFC` (forced at every world of
every reflexive fallible-world model) is derivable from `CTModalAxiom`. Instantiation of
`CKExtension.lean`'s parametric `ckvalidFC_completeness` over the `CTSegment` canonical
model, with `realize` built from `quasi_head_realization` (segment analogue of
`segment_realization`, exposing the
witnessing quasi-prime theory directly so it can be wrapped via `CTSegment.ofHead`) and
`ct_truth_lemma`. -/
theorem ct_completeness {φ : Proposition Atom} (h_valid : CKValidFC.{u, u} ctFC φ) :
    Derivable CTModalAxiom φ :=
  ckvalidFC_completeness ctFC ctMreach ctVal ctBot
    ctVal_upward_closed ctBot_upward_closed ctBot_val ctBot_mreach ctBot_mreach_wit
    ctFC_ctMreach
    (fun {φ} h_nd => by
      obtain ⟨T, hT, hφT⟩ := quasi_head_realization (fun φ ψ => .implyK φ ψ)
        (fun φ ψ χ => .implyS φ ψ χ) (fun A B χ => .orE A B χ) h_nd
      exact ⟨CTSegment.ofHead hT, fun hf => hφT ((ct_truth_lemma (CTSegment.ofHead hT) φ).mp hf)⟩)
    h_valid

/-- **Consistency of `CT`**: `⊥` is not derivable from `CTModalAxiom`. Corollary of soundness, via
the trivial reflexive one-point fallible-world model (`botForces := fun _ => False` satisfies the
explosion conditions vacuously; the everywhere-`True` relation on `Unit` is trivially reflexive). -/
theorem ct_consistent : ¬ Derivable CTModalAxiom (Proposition.bot : Proposition Atom) := by
  intro h
  exact ct_soundness_derivable h Unit (fun _ _ => True) (fun _ => trivial)
    (fun _ _ => False) (fun _ => False)
    (fun _ _ hv => hv) (fun _ hb => hb) (fun _ hb => hb.elim) (fun hb _ => hb)
    (fun hb => hb.elim) ()

/-- **Soundness-completeness biconditional for `CT`**: `φ` is derivable from `CTModalAxiom` iff
`φ` is `CKValidFC ctFC`. -/
theorem ct_soundness_completeness {φ : Proposition Atom} :
    Derivable CTModalAxiom φ ↔ CKValidFC.{u, u} ctFC φ :=
  ⟨ct_soundness_derivable, ct_completeness⟩

end Cslib.Logic.Modal
