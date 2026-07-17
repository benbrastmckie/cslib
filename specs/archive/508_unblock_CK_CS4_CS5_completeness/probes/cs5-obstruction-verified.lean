import Cslib.Logics.Modal.Metalogic.Constructive.CS5

/-! Probe B for task 508: CS5 reframing facts and the bDia obstruction. -/

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

variable {Atom : Type u}

/-! ## B1: CS5 proves `◇⊥ → ⊥` (unlike CK / CT / CS4) -/

/-- **CS5 ⊢ ◇⊥ → ⊥.** Derivation: `efq` gives `⊥ → □⊥`; necessitation gives `□(⊥ → □⊥)`;
`Kd` gives `◇⊥ → ◇□⊥`; `bDia` at `⊥` gives `◇□⊥ → ⊥`. -/
theorem cs5_dia_bot_imp_bot :
    Derivable (@CS5ModalAxiom Atom)
      ((◇(Proposition.bot : Proposition Atom)).imp Proposition.bot) := by
  have d1 : DerivationTree (@CS5ModalAxiom Atom) []
      ((Proposition.bot : Proposition Atom).imp (Proposition.box Proposition.bot)) :=
    .ax [] _ (.efq (Proposition.box Proposition.bot))
  have d2 : DerivationTree (@CS5ModalAxiom Atom) []
      (Proposition.box ((Proposition.bot : Proposition Atom).imp
        (Proposition.box Proposition.bot))) :=
    .necessitation _ d1
  have d3 : DerivationTree (@CS5ModalAxiom Atom) []
      ((Proposition.box ((Proposition.bot : Proposition Atom).imp
        (Proposition.box Proposition.bot))).imp
        ((◇(Proposition.bot : Proposition Atom)).imp
          (◇(Proposition.box (Proposition.bot : Proposition Atom))))) :=
    .ax [] _ (.kdia Proposition.bot (Proposition.box Proposition.bot))
  have d4 : DerivationTree (@CS5ModalAxiom Atom) []
      ((◇(Proposition.bot : Proposition Atom)).imp
        (◇(Proposition.box (Proposition.bot : Proposition Atom)))) :=
    .modus_ponens _ _ _ d3 d2
  have d5 : DerivationTree (@CS5ModalAxiom Atom) []
      ((◇(Proposition.box (Proposition.bot : Proposition Atom))).imp Proposition.bot) :=
    .ax [] _ (.bDia Proposition.bot)
  have hctx : DerivationTree (@CS5ModalAxiom Atom) [◇(Proposition.bot : Proposition Atom)]
      (Proposition.bot : Proposition Atom) := by
    have a0 : DerivationTree (@CS5ModalAxiom Atom) [◇(Proposition.bot : Proposition Atom)]
        (◇(Proposition.bot : Proposition Atom)) :=
      .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
    have w4 := DerivationTree.weakening [] [◇(Proposition.bot : Proposition Atom)] _ d4
      (fun _ h => nomatch h)
    have w5 := DerivationTree.weakening [] [◇(Proposition.bot : Proposition Atom)] _ d5
      (fun _ h => nomatch h)
    exact .modus_ponens _ _ _ w5 (.modus_ponens _ _ _ w4 a0)
  exact ⟨deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ) []
    (◇(Proposition.bot : Proposition Atom)) Proposition.bot hctx⟩

/-! ## B2: bDia is NOT sound over the CS4-style weakened FC + weakened symmetry -/

/-- Reflexivity + weakened transitivity (FC4') + weakened dia-transitivity (FCdia4)
+ weakened symmetry (FCsym_box) — the natural extension of the verified CS4 technique. -/
def cs5FCweak {World : Type*} [Preorder World] (r : World → World → Prop) : Prop :=
  (∀ w, r w w)
    ∧ (∀ {w u u' t}, r w u → u ≤ u' → r u' t → ∃ v, w ≤ v ∧ r v t)
    ∧ (∀ {w u}, r w u → ∃ u', u ≤ u' ∧ ∀ t, r u' t → r w t)
    ∧ (∀ {w u u'}, r w u → u ≤ u' → ∃ t, r u' t ∧ w ≤ t)

/-- Two-world countermodel: `false` (consistent) and `true` (exploding). -/
def wr (a b : Bool) : Prop := a = false ∨ b = true

/-- Valuation: only the exploding world satisfies the atom. -/
def wval (a : Bool) (_p : Unit) : Prop := a = true

/-- Fallibility: only `true` explodes. -/
def wbot (a : Bool) : Prop := a = true

theorem wr_fc : cs5FCweak wr := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w; cases w <;> simp [wr]
  · intro w u u' t h1 h2 h3
    exact ⟨w, le_refl w, by cases w <;> cases u <;> cases u' <;> cases t <;>
      simp_all [wr, Bool.le_iff_imp]⟩
  · intro w u h1
    refine ⟨u, le_refl u, ?_⟩
    intro t h2
    cases w <;> cases u <;> cases t <;> simp_all [wr]
  · intro w u u' h1 h2
    exact ⟨true, by cases u' <;> simp [wr], by cases w <;> simp⟩

/-- **bDia (`◇□p → p`) is NOT valid over `cs5FCweak`.** -/
theorem bDia_not_valid_over_cs5FCweak :
    ¬ CKValidFC.{0, 0} cs5FCweak
      (((◇(Proposition.box (Proposition.atom ()))).imp (Proposition.atom ()))
        : Proposition Unit) := by
  intro h
  have hf := h Bool wr wr_fc wval wbot
    (by intro a b p hle hv; cases a <;> cases b <;> simp_all [wval, Bool.le_iff_imp])
    (by intro a b hle hb; cases a <;> cases b <;> simp_all [wbot, Bool.le_iff_imp])
    (by intro a p hb; exact hb)
    (by intro a u hb hr; cases a <;> cases u <;> simp_all [wbot, wr])
    (by intro a hb; exact ⟨true, by cases a <;> simp [wr], rfl⟩)
    false
  -- hf : CKForces wr wval wbot false ((◇□p) → p)
  have hdia : CKForces wr wval wbot false (◇(Proposition.box (Proposition.atom ()))) := by
    intro z _
    refine ⟨true, by cases z <;> simp [wr], ?_⟩
    intro z' hz' t hrt
    cases z' <;> cases t <;> simp_all [wr, wval, Bool.le_iff_imp]
  have : wval false () := hf false (le_refl _) hdia
  exact absurd this (by simp [wval])


end Cslib.Logic.Modal

#print axioms Cslib.Logic.Modal.cs5_dia_bot_imp_bot
#print axioms Cslib.Logic.Modal.bDia_not_valid_over_cs5FCweak
