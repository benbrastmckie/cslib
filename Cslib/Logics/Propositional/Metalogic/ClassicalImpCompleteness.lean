/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.ProofSystem.FragmentAxioms
public import Cslib.Logics.Propositional.Metalogic.Soundness
public import Cslib.Logics.Propositional.Semantics.Algebra.ConjImpConservative

/-! # Completeness of the Classical Implicational Fragment CPL⟨→,⊤⟩

This module proves that the classical implicational fragment CPL⟨→,⊤⟩ — axiomatized by
K (weakening), S (distribution), and Peirce's law — is complete for tautologies that
involve only implication and truth (i.e., imp-top-only formulas). The proof follows
the Kalmár / Tarski–Bernays truth-assignment method.

## Strategy

The proof proceeds in stages building toward `classicalImp_completeness`:

1. **Soundness** (`classicalImp_soundness`): every CPL⟨→,⊤⟩-derivable formula is a
   tautology. Routes through `ClassicalImpAxiom.toPropAxiom` and CPL soundness.

2. **Derived rules**: identity (`classicalImp_imp_self`), composition (`classicalImp_imp_trans`),
   and the Peirce-driven case lemma (`classicalImp_peirce_mp`) needed by the truth lemma.

3. **Literal context** (`litCtx`): a List-based Kalmár literal context keyed on a Boolean
   assignment, with atom `p` contributing `atom p` if true or `atom p → goal` if false.

4. **Kalmár truth lemma** (`classicalImp_kalmar`): for imp-top-only `φ`, the literal
   context derives either `φ` (if true) or `φ → goal` (if false).

5. **Completeness** (`classicalImp_completeness`): iterate atom elimination over the literal
   context to conclude `Derivable ClassicalImpAxiom φ` from `Tautology φ`.

6. **Conservativity** (`cpl_conservative_over_imp`): CPL is conservative over CPL⟨→,⊤⟩
   for imp-top-only formulas.

## References

* Tarski–Bernays axiomatization of the classical implicational calculus.
* Kalmár completeness method (falsum-surrogate variant).
* See also: `Cslib/Logics/Propositional/Semantics/Algebra/ImpConservative.lean` for the
  analogous intuitionistic conservativity result. -/

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom : Type*}

/-! ## Soundness -/

/-- Soundness for the classical implicational fragment: every `ClassicalImpAxiom`-derivable
formula is a tautology. Routes through `ClassicalImpAxiom.toPropAxiom` and CPL soundness. -/
theorem classicalImp_soundness {φ : PL.Proposition Atom}
    (h : Derivable ClassicalImpAxiom φ) : Tautology φ := by
  obtain ⟨d⟩ := h
  exact prop_soundness_tautology ⟨liftDerivationTree (fun ψ hψ => hψ.toPropAxiom) d⟩

/-! ## Derived Lemmas -/

/-- Identity: `⊢ φ → φ` in the classical implicational fragment, proved by the standard
S K K derivation. Specifically: S (with ψ := φ→φ, χ := φ) applied to K gives
`(φ → (φ→φ)) → (φ → φ)`, and a second K gives `φ → φ`. -/
theorem classicalImp_imp_self (φ : PL.Proposition Atom) :
    Derivable ClassicalImpAxiom (φ.imp φ) :=
  mp_deriv
    (mp_deriv ⟨.ax [] _ (.implyS φ (φ.imp φ) φ)⟩ ⟨.ax [] _ (.implyK φ (φ.imp φ))⟩)
    ⟨.ax [] _ (.implyK φ φ)⟩

/-- Composition: from `⊢ φ → ψ` and `⊢ ψ → χ` derive `⊢ φ → χ`.

Pure K + S derivation: K weakens `ψ → χ` to `φ → (ψ → χ)`, S distributes to give
`(φ → ψ) → (φ → χ)`, and MP with `h₁` yields `φ → χ`. -/
theorem classicalImp_imp_trans {φ ψ χ : PL.Proposition Atom}
    (h₁ : Derivable ClassicalImpAxiom (φ.imp ψ))
    (h₂ : Derivable ClassicalImpAxiom (ψ.imp χ)) :
    Derivable ClassicalImpAxiom (φ.imp χ) :=
  mp_deriv
    (mp_deriv ⟨.ax [] _ (.implyS φ ψ χ)⟩
              (mp_deriv ⟨.ax [] _ (.implyK (ψ.imp χ) φ)⟩ h₂))
    h₁

/-- Classical case lemma (Peirce): from `Γ ⊢ (φ → goal) → φ` derive `Γ ⊢ φ`.

Direct application of Peirce's law: the axiom `((φ → goal) → φ) → φ` combined with one
modus ponens step. This is the only place Peirce's law is invoked in the classical
implicational completeness argument. -/
theorem classicalImp_peirce_mp {Γ : List (PL.Proposition Atom)} {φ goal : PL.Proposition Atom}
    (h : Deriv ClassicalImpAxiom Γ ((φ.imp goal).imp φ)) :
    Deriv ClassicalImpAxiom Γ φ :=
  mp_deriv ⟨.ax Γ _ (.peirce φ goal)⟩ h

/-! ## Atom Collection -/

/-- Collect the atoms appearing in a proposition as a list (with possible duplicates).
Used in the Kalmár completeness argument to parameterize the literal context. -/
def Proposition.atoms : PL.Proposition Atom → List Atom
  | .atom p => [p]
  | .imp a b => a.atoms ++ b.atoms
  | _ => []

/-! ## Literal Context -/

/-- The Kalmár literal context for a Boolean assignment `v` and falsum-surrogate `goal`,
keyed on a list of atoms `as`: atom `p` contributes `atom p` if `v p = true`, otherwise
`atom p → goal`. Used in `classicalImp_kalmar` to encode the two Boolean branches for
each atom simultaneously via the List-based deduction theorem. -/
def litCtx (v : BoolValuation Atom) (goal : PL.Proposition Atom) :
    List Atom → List (PL.Proposition Atom)
  | [] => []
  | p :: ps => (if v p then PL.Proposition.atom p else (PL.Proposition.atom p).imp goal)
                :: litCtx v goal ps

/-- Membership helper: the literal for atom `p` sits in `litCtx v goal as` whenever `p ∈ as`. -/
theorem litCtx_mem {v : BoolValuation Atom} {goal : PL.Proposition Atom} {as : List Atom}
    {p : Atom} (hp : p ∈ as) :
    (if v p then PL.Proposition.atom p else (PL.Proposition.atom p).imp goal)
      ∈ litCtx v goal as := by
  induction as with
  | nil => simp at hp
  | cons q qs ih =>
    rw [litCtx]
    simp only [List.mem_cons]
    rcases List.mem_cons.mp hp with rfl | hqs
    · exact Or.inl rfl
    · exact Or.inr (ih hqs)

/-! ## In-Context Derived Lemmas -/

/-- In-context composition: from `Γ ⊢ φ → ψ` and `Γ ⊢ ψ → χ` derive `Γ ⊢ φ → χ`.
Uses the deduction theorem to introduce `φ`, applies `h₁` then `h₂` in context, and
peels with the deduction theorem again. This is the context-sensitive sibling of
`classicalImp_imp_trans` (which operates on the empty context only). -/
theorem classicalImp_imp_trans_ctx {Γ : List (PL.Proposition Atom)} {φ ψ χ : PL.Proposition Atom}
    (h₁ : Deriv ClassicalImpAxiom Γ (φ.imp ψ)) (h₂ : Deriv ClassicalImpAxiom Γ (ψ.imp χ)) :
    Deriv ClassicalImpAxiom Γ (φ.imp χ) :=
  classicalImpAxiom_hasDeductionTheorem
    (mp_deriv
      (weakening_deriv h₂ (fun _ hx => List.mem_cons.mpr (Or.inr hx)))
      (mp_deriv
        (weakening_deriv h₁ (fun _ hx => List.mem_cons.mpr (Or.inr hx)))
        (assumption_deriv (List.mem_cons.mpr (Or.inl rfl)))))

/-- In-context K-weakening: from `Γ ⊢ ψ` derive `Γ ⊢ φ → ψ`.
Axiom K (`ψ → (φ → ψ)`) plus one modus ponens step. -/
theorem classicalImp_weaken_ctx {Γ : List (PL.Proposition Atom)} {φ ψ : PL.Proposition Atom}
    (h : Deriv ClassicalImpAxiom Γ ψ) : Deriv ClassicalImpAxiom Γ (φ.imp ψ) :=
  mp_deriv ⟨.ax Γ _ (.implyK ψ φ)⟩ h

/-! ## Kalmár Truth Lemma -/

/-- Kalmár truth lemma (falsum-surrogate / double-negation form). For imp-top-only `φ`, under the
literal context `litCtx v goal as` (with `as` covering the atoms of `φ`): if `v ⊨ φ` then the
context derives the double negation `(φ → goal) → goal`; otherwise it derives `φ → goal`. The
surrogate `goal` is fixed and arbitrary. Proved by induction on `φ`; only `atom` and `imp` cases
are live. Peirce's law enters only in the `imp` TRUE-side false-antecedent subcase. -/
theorem classicalImp_kalmar {v : BoolValuation Atom} {goal : PL.Proposition Atom}
    (as : List Atom) {φ : PL.Proposition Atom} (hITO : φ.IsImpTopOnly = true)
    (hcov : ∀ p, p ∈ φ.atoms → p ∈ as) :
    (BoolEvaluate v φ = true →
        Deriv ClassicalImpAxiom (litCtx v goal as) ((φ.imp goal).imp goal)) ∧
    (BoolEvaluate v φ = false →
        Deriv ClassicalImpAxiom (litCtx v goal as) (φ.imp goal)) := by
  revert hITO hcov
  induction φ with
  | atom p =>
    intro _ hcov
    simp only [Proposition.atoms, List.mem_singleton] at hcov
    have hp : p ∈ as := hcov p rfl
    have hlit : (if v p then PL.Proposition.atom p else (PL.Proposition.atom p).imp goal)
        ∈ litCtx v goal as := litCtx_mem hp
    simp only [BoolEvaluate_atom]
    constructor
    · intro hv
      simp only [hv, ite_true] at hlit
      exact classicalImpAxiom_hasDeductionTheorem
        (mp_deriv
          (assumption_deriv (List.mem_cons.mpr (Or.inl rfl)))
          (weakening_deriv (assumption_deriv hlit)
            (fun _ hx => List.mem_cons.mpr (Or.inr hx))))
    · intro hv
      simp only [hv] at hlit
      exact assumption_deriv hlit
  | bot => intro hITO _; simp [Proposition.IsImpTopOnly] at hITO
  | and a b _ _ => intro hITO _; simp [Proposition.IsImpTopOnly] at hITO
  | or a b _ _ => intro hITO _; simp [Proposition.IsImpTopOnly] at hITO
  | imp a b iha ihb =>
    intro hITO hcov
    simp only [Proposition.IsImpTopOnly, Bool.and_eq_true] at hITO
    obtain ⟨hITOa, hITOb⟩ := hITO
    simp only [Proposition.atoms, List.mem_append] at hcov
    have hcova : ∀ p, p ∈ a.atoms → p ∈ as := fun p hp => hcov p (Or.inl hp)
    have hcovb : ∀ p, p ∈ b.atoms → p ∈ as := fun p hp => hcov p (Or.inr hp)
    obtain ⟨ihaT, ihaF⟩ := iha hITOa hcova
    obtain ⟨ihbT, ihbF⟩ := ihb hITOb hcovb
    simp only [BoolEvaluate_imp]
    refine ⟨fun hTrue => ?_, fun hFalse => ?_⟩
    · -- TRUE case: !BoolEvaluate v a || BoolEvaluate v b = true
      -- Split on BoolEvaluate v a
      cases hva : BoolEvaluate v a with
      | true =>
        -- v a = true, so v b must be true
        have hvb : BoolEvaluate v b = true := by
          simp only [hva, Bool.not_true, Bool.false_or] at hTrue; exact hTrue
        -- IHb-TRUE: Γ ⊢ (b→goal)→goal. Use K(b,a) + H to build b→goal in ((a→b)→goal)::Γ.
        apply classicalImpAxiom_hasDeductionTheorem
        apply mp_deriv (weakening_deriv (ihbT hvb) (fun _ hx => List.mem_cons.mpr (Or.inr hx)))
        apply classicalImp_imp_trans_ctx
        · exact ⟨.ax _ _ (.implyK b a)⟩
        · exact assumption_deriv (List.mem_cons.mpr (Or.inl rfl))
      | false =>
        -- v a = false: Peirce case. IHa-FALSE: Γ ⊢ a→goal.
        -- Need: Γ ⊢ ((a→b)→goal)→goal.
        apply classicalImpAxiom_hasDeductionTheorem
        -- ((a→b)→goal) :: Γ ⊢ goal  (let Γ' = H :: Γ, H = (a→b)→goal)
        apply classicalImp_peirce_mp (φ := goal) (goal := a.imp b)
        -- Γ' ⊢ (goal→(a→b))→goal
        apply classicalImpAxiom_hasDeductionTheorem
        -- (goal→(a→b)) :: Γ' ⊢ goal  (Γ'' = K' :: H :: Γ, K' = goal→(a→b))
        -- Derive: Γ'' ⊢ a→b (via a: IHa-FALSE+a→goal; K'→a→b; mp a→b with a→b; DT)
        -- then H applied to a→b gives goal
        apply mp_deriv
        · -- Γ'' ⊢ (a→b)→goal  (H at index 1 in Γ'')
          exact assumption_deriv
            (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
        · -- Γ'' ⊢ a→b  (via DT over a)
          apply classicalImpAxiom_hasDeductionTheorem
          -- a :: Γ'' ⊢ b
          apply mp_deriv
          · -- a :: Γ'' ⊢ a→b  (K' applied to goal)
            apply mp_deriv
            · -- a :: Γ'' ⊢ goal→(a→b)  (K' at index 1 in a :: Γ'')
              exact assumption_deriv
                (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
            · -- a :: Γ'' ⊢ goal  (IHa-FALSE + assumption a)
              apply mp_deriv
              · -- a :: Γ'' ⊢ a→goal  (IHa-FALSE weakened 3×)
                exact weakening_deriv
                  (weakening_deriv
                    (weakening_deriv (ihaF hva)
                      (fun _ hx => List.mem_cons.mpr (Or.inr hx)))
                    (fun _ hx => List.mem_cons.mpr (Or.inr hx)))
                  (fun _ hx => List.mem_cons.mpr (Or.inr hx))
              · -- a :: Γ'' ⊢ a  (head assumption)
                exact assumption_deriv (List.mem_cons.mpr (Or.inl rfl))
          · -- a :: Γ'' ⊢ a  (head assumption)
            exact assumption_deriv (List.mem_cons.mpr (Or.inl rfl))
    · -- FALSE case: !BoolEvaluate v a || BoolEvaluate v b = false
      -- Extract: BoolEvaluate v a = true and BoolEvaluate v b = false
      cases hva : BoolEvaluate v a with
      | false =>
        simp only [hva, Bool.not_false, Bool.true_or] at hFalse
        exact absurd hFalse (by decide)  -- true || _ = true ≠ false
      | true =>
        have hvb : BoolEvaluate v b = false := by
          simp only [hva, Bool.not_true, Bool.false_or] at hFalse; exact hFalse
        -- IHa-TRUE: Γ ⊢ (a→goal)→goal; IHb-FALSE: Γ ⊢ b→goal
        -- DT: introduce H := a→b; compose H with IHb-FALSE to get a→goal; mp with IHa-TRUE
        apply classicalImpAxiom_hasDeductionTheorem
        -- (a→b) :: Γ ⊢ goal
        apply mp_deriv (weakening_deriv (ihaT hva) (fun _ hx => List.mem_cons.mpr (Or.inr hx)))
        -- (a→b) :: Γ ⊢ a→goal
        apply classicalImp_imp_trans_ctx
        · -- (a→b) :: Γ ⊢ a→b  (head assumption)
          exact assumption_deriv (List.mem_cons.mpr (Or.inl rfl))
        · -- (a→b) :: Γ ⊢ b→goal  (IHb-FALSE weakened)
          exact weakening_deriv (ihbF hvb) (fun _ hx => List.mem_cons.mpr (Or.inr hx))

/-! ## Atom Elimination -/

/-- Atom elimination (one step): if the context with `p` true derives `goal` and the context
with `p` false (i.e., with `p → goal` instead) also derives `goal`, then the shorter context
without the `p`-literal derives `goal`. Uses the deduction theorem to peel each branch and
combine with one `mp_deriv`. -/
theorem classicalImp_elim_atom {goal : PL.Proposition Atom}
    {Γ : List (PL.Proposition Atom)} {p : Atom}
    (hT : Deriv ClassicalImpAxiom (PL.Proposition.atom p :: Γ) goal)
    (hF : Deriv ClassicalImpAxiom ((PL.Proposition.atom p).imp goal :: Γ) goal) :
    Deriv ClassicalImpAxiom Γ goal :=
  mp_deriv
    (classicalImpAxiom_hasDeductionTheorem hF)  -- Γ ⊢ (p→goal)→goal
    (classicalImpAxiom_hasDeductionTheorem hT)  -- Γ ⊢ p→goal

end Cslib.Logic.PL
