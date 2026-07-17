import Cslib.Logics.Modal.Metalogic.Constructive.CS5

/-! Probe for task 509: locating the real CS5 obstruction.

C1: task 508's `cs5FCweak` countermodel relation is NOT plainly symmetric, so the 508
    countermodel does not refute a frame condition that includes plain symmetry.
C2: `cs5FC''` — refl + plain trans + plain symm + FC4' + FCsym_box — validates all 17
    CS5 axioms (so the CS4-style weakening DOES extend to CS5, contra 508 §5.2).
C3: `cs5FC → cs5FC''`, so `cs5FC''` is a genuine weakening.
-/

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

variable {Atom : Type u}

/-! ## C1: task 508's countermodel relation is not symmetric -/

/-- Task 508's countermodel relation (`probes/cs5-obstruction-verified.lean`, `wr`). -/
def wr' (a b : Bool) : Prop := a = false ∨ b = true

/-- **The 508 countermodel is not plainly symmetric.** `wr' false true` holds but
`wr' true false` does not. Hence `cs5FCweak` (which contains only the *weakened* symmetry
`FCsym_box`, never plain symmetry `r w u → r u w`) is not a frame condition that any
symmetric canonical model would have to satisfy — and `bDia_not_valid_over_cs5FCweak`
therefore does NOT rule out the frame condition `cs5FC''` below. -/
theorem wr'_not_symm : ¬ (∀ {a b : Bool}, wr' a b → wr' b a) := by
  intro h
  have := h (a := false) (b := true) (Or.inl rfl)
  simp [wr'] at this

/-! ## C2: the weakened CS5 frame condition -/

/-- **Weakened `CS5` frame condition.** Reflexivity + *plain* transitivity (`fourDia`) +
*plain* symmetry (`bDia`) + `cs4FC'`'s re-basing clause (`fourBox`) + weakened symmetry
(`bBox`). Compare task 508's `cs5FCweak`, which omitted plain symmetry and plain
transitivity — that omission, not any real obstruction, is what made `bDia` unsound there. -/
def cs5FC'' {World : Type*} [Preorder World] (r : World → World → Prop) : Prop :=
  (∀ w, r w w)
    ∧ (∀ {w u t}, r w u → r u t → r w t)
    ∧ (∀ {w u}, r w u → r u w)
    ∧ (∀ {w u u' t}, r w u → u ≤ u' → r u' t → ∃ v, w ≤ v ∧ r v t)
    ∧ (∀ {w u u'}, r w u → u ≤ u' → ∃ t, r u' t ∧ w ≤ t)

/-- **C3: `cs5FC''` genuinely weakens `cs5FC`.** So validity over `cs5FC''` is a *stronger*
statement than validity over `cs5FC`: soundness is harder, completeness easier. -/
theorem cs5FC_implies_cs5FC'' {World : Type*} [Preorder World] {r : World → World → Prop}
    (h : cs5FC r) : cs5FC'' r :=
  ⟨h.1,
   fun hwu hut => h.2.1 hwu (le_refl _) hut,
   fun hwu => h.2.2 hwu (le_refl _),
   fun hwu hle hu't => ⟨_, le_refl _, h.2.1 hwu hle hu't⟩,
   fun hwu hle => ⟨_, h.2.2 hwu hle, le_refl _⟩⟩

/-- **C2: all 17 `CS5` axioms are sound over `cs5FC''`.** This is the half task 508 declared
impossible. `bDia` uses plain symmetry; `bBox` uses the weakened symmetry `FCsym_box`;
`fourBox` uses the `cs4FC'` re-basing clause; `fourDia` uses plain transitivity. -/
theorem cs5_axiom_sound'' {φ : Proposition Atom} (h_ax : CS5ModalAxiom φ) :
    CKValidFC.{u, v} cs5FC'' φ := by
  intro World _ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  obtain ⟨hrefl, htrans, hsymm, hfour, hsymbox⟩ := hfc
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
    exact hboxA u (le_refl u) w' (hsymm hru)
  | bBox φ =>
    intro w' _ hφ w'' hw'' u hru u' hu'
    obtain ⟨t, hru't, hw''t⟩ := hsymbox hru hu'
    exact ⟨t, hru't, ckforces_persistence v_uc bf_uc (le_trans hw'' hw''t) hφ⟩

end Cslib.Logic.Modal

#print axioms Cslib.Logic.Modal.wr'_not_symm
#print axioms Cslib.Logic.Modal.cs5FC_implies_cs5FC''
#print axioms Cslib.Logic.Modal.cs5_axiom_sound''
