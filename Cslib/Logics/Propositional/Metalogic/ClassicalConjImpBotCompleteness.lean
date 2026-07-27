/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Metalogic.ClassicalConjImpCompleteness

/-! # Completeness of the Classical ⟨∧,→,⊥,⊤⟩ Fragment CPL⟨∧,→,⊥,⊤⟩

This module proves that the classical conjunctive-implicational-bot fragment CPL⟨∧,→,⊥,⊤⟩ —
axiomatized by K, S, Peirce's law, the three conjunction axioms (andI, andE1, andE2), and
ex falso quodlibet (efq) — is complete for tautologies that involve only conjunction,
implication, falsum, and atoms (i.e., or-free formulas). The proof extends the Kalmár /
Tarski–Bernays truth-assignment method from the conjunction-implication case (see
`ClassicalConjImpCompleteness.lean`)
with a new `bot` case.

## Strategy

The proof extends `classicalConjImp_completeness` (from
`ClassicalConjImpCompleteness.lean`), mirroring its
phase structure but widening the predicate from `IsOrBotFree` to `IsOrFree` and adding the
`bot` case to the truth lemma:

1. **Soundness** (`classicalConjImpBot_soundness`): every `ClassicalConjImpBotAxiom`-derivable
   formula is a tautology, via `ClassicalConjImpBotAxiom.toPropAxiom` and CPL soundness.

2. **Derived rules**: identity (`classicalConjImpBot_imp_self`), composition
   (`classicalConjImpBot_imp_trans`), the Peirce case lemma (`classicalConjImpBot_peirce_mp`),
   in-context helpers (`classicalConjImpBot_imp_trans_ctx`, `classicalConjImpBot_weaken_ctx`),
   and the new EFQ helper (`classicalConjImpBot_exfalso`).

3. **Kalmár truth lemma** (`classicalConjImpBot_kalmar`): for or-free `φ`, the literal
   context derives either `(φ → goal) → goal` (if `v ⊨ φ`) or `φ → goal` (otherwise). The
   `atom`, `imp`, and `and` cases are transcribed from `classicalConjImp_kalmar`;
   the `bot` case is new and trivial: the TRUE side is vacuous (⊥ is never true), and the
   FALSE side is immediate via the EFQ axiom.

4. **Completeness** (`classicalConjImpBot_completeness`): iterate atom elimination over the
   literal context to conclude `Derivable ClassicalConjImpBotAxiom φ`.

5. **Conservativity** (`cpl_conservative_over_classicalConjImpBot`): CPL is conservative over
   CPL⟨∧,→,⊥,⊤⟩ for or-free formulas.

## Key Design Choice

The proof uses the falsum-surrogate / double-negation method, not an algebraic route.
Classical fragments are not Heyting-complete, so algebraic approaches fail here. The real `⊥`
in the fragment enters only in the `bot` FALSE case of the truth lemma, where the EFQ axiom
(`⊥ → goal`) directly closes the goal. This is the one genuine extension over the
conjunction-implication case.

Peirce's law enters only in the `imp` TRUE-side false-antecedent subcase, exactly as in
the implicational and conjunction-implication cases.

## References

* Tarski–Bernays axiomatization of the classical implicational calculus.
* Kalmár completeness method (falsum-surrogate variant).
* `Cslib/Logics/Propositional/Metalogic/ClassicalImpCompleteness.lean` —
  the original template; `litCtx`, `litCtx_mem`, `Proposition.atoms` reused by import.
* `Cslib/Logics/Propositional/Metalogic/ClassicalConjImpCompleteness.lean` —
  the ∧-extension this module builds on; atom/imp/and cases transcribed from there;
  `Proposition.atomsConjImp` reused by import. -/

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom : Type*}

/-! ## Soundness -/

/-- Soundness for the classical conjunctive-implicational-bot fragment: every
`ClassicalConjImpBotAxiom`-derivable formula is a tautology. Routes through
`ClassicalConjImpBotAxiom.toPropAxiom` and CPL soundness. -/
theorem classicalConjImpBot_soundness {φ : PL.Proposition Atom}
    (h : Derivable ClassicalConjImpBotAxiom φ) : Tautology φ := by
  obtain ⟨d⟩ := h
  exact prop_soundness_tautology ⟨liftDerivationTree (fun ψ hψ => hψ.toPropAxiom) d⟩

/-! ## Derived Lemmas -/

/-- Identity: `⊢ φ → φ` in the classical conjunctive-implicational-bot fragment, proved by
the standard S K K derivation. Specifically: S (with ψ := φ→φ, χ := φ) applied to K gives
`(φ → (φ→φ)) → (φ → φ)`, and a second K gives `φ → φ`. -/
theorem classicalConjImpBot_imp_self (φ : PL.Proposition Atom) :
    Derivable ClassicalConjImpBotAxiom (φ.imp φ) :=
  mp_deriv
    (mp_deriv ⟨.ax [] _ (.implyS φ (φ.imp φ) φ)⟩ ⟨.ax [] _ (.implyK φ (φ.imp φ))⟩)
    ⟨.ax [] _ (.implyK φ φ)⟩

/-- Composition: from `⊢ φ → ψ` and `⊢ ψ → χ` derive `⊢ φ → χ`.

Pure K + S derivation: K weakens `ψ → χ` to `φ → (ψ → χ)`, S distributes to give
`(φ → ψ) → (φ → χ)`, and MP with `h₁` yields `φ → χ`. -/
theorem classicalConjImpBot_imp_trans {φ ψ χ : PL.Proposition Atom}
    (h₁ : Derivable ClassicalConjImpBotAxiom (φ.imp ψ))
    (h₂ : Derivable ClassicalConjImpBotAxiom (ψ.imp χ)) :
    Derivable ClassicalConjImpBotAxiom (φ.imp χ) :=
  mp_deriv
    (mp_deriv ⟨.ax [] _ (.implyS φ ψ χ)⟩
              (mp_deriv ⟨.ax [] _ (.implyK (ψ.imp χ) φ)⟩ h₂))
    h₁

/-- Classical case lemma (Peirce): from `Γ ⊢ (φ → goal) → φ` derive `Γ ⊢ φ`.

Direct application of Peirce's law: the axiom `((φ → goal) → φ) → φ` combined with one
modus ponens step. This is the only place Peirce's law is invoked in the classical
conjunctive-implicational-bot completeness argument. -/
theorem classicalConjImpBot_peirce_mp
    {Γ : List (PL.Proposition Atom)} {φ goal : PL.Proposition Atom}
    (h : Deriv ClassicalConjImpBotAxiom Γ ((φ.imp goal).imp φ)) :
    Deriv ClassicalConjImpBotAxiom Γ φ :=
  mp_deriv ⟨.ax Γ _ (.peirce φ goal)⟩ h

/-! ## In-Context Derived Lemmas -/

/-- In-context composition: from `Γ ⊢ φ → ψ` and `Γ ⊢ ψ → χ` derive `Γ ⊢ φ → χ`.
Uses the deduction theorem to introduce `φ`, applies `h₁` then `h₂` in context, and
peels with the deduction theorem again. -/
theorem classicalConjImpBot_imp_trans_ctx
    {Γ : List (PL.Proposition Atom)} {φ ψ χ : PL.Proposition Atom}
    (h₁ : Deriv ClassicalConjImpBotAxiom Γ (φ.imp ψ))
    (h₂ : Deriv ClassicalConjImpBotAxiom Γ (ψ.imp χ)) :
    Deriv ClassicalConjImpBotAxiom Γ (φ.imp χ) :=
  classicalConjImpBotAxiom_hasDeductionTheorem
    (mp_deriv
      (weakening_deriv h₂ (fun _ hx => List.mem_cons.mpr (Or.inr hx)))
      (mp_deriv
        (weakening_deriv h₁ (fun _ hx => List.mem_cons.mpr (Or.inr hx)))
        (assumption_deriv (List.mem_cons.mpr (Or.inl rfl)))))

/-- In-context K-weakening: from `Γ ⊢ ψ` derive `Γ ⊢ φ → ψ`.
Axiom K (`ψ → (φ → ψ)`) plus one modus ponens step. -/
theorem classicalConjImpBot_weaken_ctx
    {Γ : List (PL.Proposition Atom)} {φ ψ : PL.Proposition Atom}
    (h : Deriv ClassicalConjImpBotAxiom Γ ψ) :
    Deriv ClassicalConjImpBotAxiom Γ (φ.imp ψ) :=
  mp_deriv ⟨.ax Γ _ (.implyK ψ φ)⟩ h

/-- Ex falso: the falsum axiom gives `Γ ⊢ ⊥ → φ` for any `φ` and any context `Γ`.
Consumed by the `bot` FALSE side of the Kalmár truth lemma, where `⊥ → goal` is the
direct EFQ axiom instance. -/
theorem classicalConjImpBot_exfalso
    {Γ : List (PL.Proposition Atom)} {goal : PL.Proposition Atom} :
    Deriv ClassicalConjImpBotAxiom Γ (Proposition.bot.imp goal) :=
  ⟨.ax Γ _ (.efq goal)⟩

/-! ## Literal Context Congruence (local copy) -/

/-- Valuation congruence for literal contexts: if `v` and `w` agree on every atom in `as`,
then `litCtx v goal as = litCtx w goal as`. Used in `classicalConjImpBot_collapse` to reconcile
Boolean-updated valuations when eliminating an atom not present in the remaining tail.
(Local copy of the private lemma from `ClassicalConjImpCompleteness`; `litCtx` itself is
reused by import from `ClassicalImpCompleteness`.) -/
private lemma litCtx_congr' {goal : PL.Proposition Atom} {as : List Atom}
    {v w : BoolValuation Atom} (h : ∀ q ∈ as, v q = w q) :
    litCtx v goal as = litCtx w goal as := by
  induction as with
  | nil => rfl
  | cons p ps ih =>
    simp only [litCtx]
    congr 1
    · rw [h p (List.mem_cons.mpr (Or.inl rfl))]
    · exact ih (fun q hq => h q (List.mem_cons.mpr (Or.inr hq)))

/-! ## Kalmár Truth Lemma -/

/-- Kalmár truth lemma for the classical conjunctive-implicational-bot fragment
(falsum-surrogate / double-negation form). For or-free `φ`, under the literal context
`litCtx v goal as` (with `as` covering the atoms of `φ` under `atomsConjImp`): if `v ⊨ φ`
then the context derives the double negation `(φ → goal) → goal`; otherwise it derives
`φ → goal`. The surrogate `goal` is fixed and arbitrary.

Proved by induction on `φ`; the `or` case is excluded by `IsOrFree`. The `atom`, `imp`, and
`and` cases are transcribed from `classicalConjImp_kalmar`, retargeted to
`ClassicalConjImpBotAxiom`. The `bot` case is the new content: the TRUE side is vacuous
(`⊥` is never true, so the hypothesis `false = true` is contradictory), and the FALSE side
uses `classicalConjImpBot_exfalso` to immediately supply `Γ ⊢ ⊥ → goal`. Peirce's law
enters only in the `imp` TRUE-side false-antecedent subcase, as in the implicational and
conjunction-implication cases. -/
theorem classicalConjImpBot_kalmar {v : BoolValuation Atom} {goal : PL.Proposition Atom}
    (as : List Atom) {φ : PL.Proposition Atom} (hOF : φ.IsOrFree = true)
    (hcov : ∀ p, p ∈ φ.atomsConjImp → p ∈ as) :
    (BoolEvaluate v φ = true →
        Deriv ClassicalConjImpBotAxiom (litCtx v goal as) ((φ.imp goal).imp goal)) ∧
    (BoolEvaluate v φ = false →
        Deriv ClassicalConjImpBotAxiom (litCtx v goal as) (φ.imp goal)) := by
  revert hOF hcov
  induction φ with
  | atom p =>
    intro _ hcov
    simp only [Proposition.atomsConjImp, List.mem_singleton] at hcov
    have hp : p ∈ as := hcov p rfl
    have hlit : (if v p then PL.Proposition.atom p else (PL.Proposition.atom p).imp goal)
        ∈ litCtx v goal as := litCtx_mem hp
    simp only [BoolEvaluate_atom]
    constructor
    · intro hv
      simp only [hv, ite_true] at hlit
      exact classicalConjImpBotAxiom_hasDeductionTheorem
        (mp_deriv
          (assumption_deriv (List.mem_cons.mpr (Or.inl rfl)))
          (weakening_deriv (assumption_deriv hlit)
            (fun _ hx => List.mem_cons.mpr (Or.inr hx))))
    · intro hv
      simp only [hv] at hlit
      exact assumption_deriv hlit
  | bot =>
    -- ⊥ is never true under any Boolean assignment; TRUE side is vacuous, FALSE side is EFQ.
    intro _ _
    simp only [BoolEvaluate_bot]
    constructor
    · intro hv
      exact absurd hv (by decide)
    · intro _
      exact classicalConjImpBot_exfalso
  | or a b _ _ => intro hOF _; simp [Proposition.IsOrFree] at hOF
  | imp a b iha ihb =>
    intro hOF hcov
    simp only [Proposition.IsOrFree, Bool.and_eq_true] at hOF
    obtain ⟨hOFa, hOFb⟩ := hOF
    simp only [Proposition.atomsConjImp, List.mem_append] at hcov
    have hcova : ∀ p, p ∈ a.atomsConjImp → p ∈ as := fun p hp => hcov p (Or.inl hp)
    have hcovb : ∀ p, p ∈ b.atomsConjImp → p ∈ as := fun p hp => hcov p (Or.inr hp)
    obtain ⟨ihaT, ihaF⟩ := iha hOFa hcova
    obtain ⟨ihbT, ihbF⟩ := ihb hOFb hcovb
    simp only [BoolEvaluate_imp]
    refine ⟨fun hTrue => ?_, fun hFalse => ?_⟩
    · -- TRUE case: !BoolEvaluate v a || BoolEvaluate v b = true
      cases hva : BoolEvaluate v a with
      | true =>
        -- v a = true, so v b must be true
        have hvb : BoolEvaluate v b = true := by
          simp only [hva, Bool.not_true, Bool.false_or] at hTrue; exact hTrue
        -- IHb-TRUE: Γ ⊢ (b→goal)→goal. Use K(b,a) + H to build b→goal in ((a→b)→goal)::Γ.
        apply classicalConjImpBotAxiom_hasDeductionTheorem
        apply mp_deriv (weakening_deriv (ihbT hvb) (fun _ hx => List.mem_cons.mpr (Or.inr hx)))
        apply classicalConjImpBot_imp_trans_ctx
        · exact ⟨.ax _ _ (.implyK b a)⟩
        · exact assumption_deriv (List.mem_cons.mpr (Or.inl rfl))
      | false =>
        -- v a = false: Peirce case. IHa-FALSE: Γ ⊢ a→goal.
        -- Need: Γ ⊢ ((a→b)→goal)→goal.
        apply classicalConjImpBotAxiom_hasDeductionTheorem
        -- ((a→b)→goal) :: Γ ⊢ goal
        apply classicalConjImpBot_peirce_mp (φ := goal) (goal := a.imp b)
        -- Γ' ⊢ (goal→(a→b))→goal
        apply classicalConjImpBotAxiom_hasDeductionTheorem
        -- (goal→(a→b)) :: Γ' ⊢ goal
        apply mp_deriv
        · -- Γ'' ⊢ (a→b)→goal  (H at index 1)
          exact assumption_deriv
            (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
        · -- Γ'' ⊢ a→b  (via DT over a)
          apply classicalConjImpBotAxiom_hasDeductionTheorem
          -- a :: Γ'' ⊢ b
          apply mp_deriv
          · -- a :: Γ'' ⊢ a→b  (K' applied to goal)
            apply mp_deriv
            · -- a :: Γ'' ⊢ goal→(a→b)
              exact assumption_deriv
                (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
            · -- a :: Γ'' ⊢ goal  (IHa-FALSE + assumption a)
              apply mp_deriv
              · exact weakening_deriv
                    (weakening_deriv
                      (weakening_deriv (ihaF hva)
                        (fun _ hx => List.mem_cons.mpr (Or.inr hx)))
                      (fun _ hx => List.mem_cons.mpr (Or.inr hx)))
                    (fun _ hx => List.mem_cons.mpr (Or.inr hx))
              · exact assumption_deriv (List.mem_cons.mpr (Or.inl rfl))
          · exact assumption_deriv (List.mem_cons.mpr (Or.inl rfl))
    · -- FALSE case: !BoolEvaluate v a || BoolEvaluate v b = false
      cases hva : BoolEvaluate v a with
      | false =>
        simp only [hva, Bool.not_false, Bool.true_or] at hFalse
        exact absurd hFalse (by decide)
      | true =>
        have hvb : BoolEvaluate v b = false := by
          simp only [hva, Bool.not_true, Bool.false_or] at hFalse; exact hFalse
        apply classicalConjImpBotAxiom_hasDeductionTheorem
        apply mp_deriv (weakening_deriv (ihaT hva) (fun _ hx => List.mem_cons.mpr (Or.inr hx)))
        apply classicalConjImpBot_imp_trans_ctx
        · exact assumption_deriv (List.mem_cons.mpr (Or.inl rfl))
        · exact weakening_deriv (ihbF hvb) (fun _ hx => List.mem_cons.mpr (Or.inr hx))
  | and a b iha ihb =>
    intro hOF hcov
    simp only [Proposition.IsOrFree, Bool.and_eq_true] at hOF
    obtain ⟨hOFa, hOFb⟩ := hOF
    simp only [Proposition.atomsConjImp, List.mem_append] at hcov
    have hcova : ∀ p, p ∈ a.atomsConjImp → p ∈ as := fun p hp => hcov p (Or.inl hp)
    have hcovb : ∀ p, p ∈ b.atomsConjImp → p ∈ as := fun p hp => hcov p (Or.inr hp)
    obtain ⟨ihaT, ihaF⟩ := iha hOFa hcova
    obtain ⟨ihbT, ihbF⟩ := ihb hOFb hcovb
    simp only [BoolEvaluate_and]
    refine ⟨fun hTrue => ?_, fun hFalse => ?_⟩
    · -- TRUE case: (BoolEvaluate v a && BoolEvaluate v b) = true
      -- Extract: v a = true and v b = true
      simp only [Bool.and_eq_true] at hTrue
      obtain ⟨hva, hvb⟩ := hTrue
      -- Goal: Γ ⊢ ((a ∧ b → goal) → goal)
      -- DT: introduce H := (a ∧ b) → goal; need H :: Γ ⊢ goal
      apply classicalConjImpBotAxiom_hasDeductionTheorem
      -- Step 1: Build H :: Γ ⊢ a → (b → goal)
      -- Strategy: under a and b, andI gives a ∧ b, H gives goal.
      have hab_to_goal :
          Deriv ClassicalConjImpBotAxiom
            ((a.and b).imp goal :: litCtx v goal as) (a.imp (b.imp goal)) :=
        classicalConjImpBotAxiom_hasDeductionTheorem
          (classicalConjImpBotAxiom_hasDeductionTheorem
            -- b :: a :: H :: Γ ⊢ goal
            (mp_deriv
              -- b :: a :: H :: Γ ⊢ (a ∧ b) → goal  (H at index 2)
              (assumption_deriv
                (List.mem_cons.mpr
                  (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))
              -- b :: a :: H :: Γ ⊢ a ∧ b
              (mp_deriv
                -- b :: a :: H :: Γ ⊢ b → a ∧ b  (andI a b applied to assumption a)
                (mp_deriv
                  -- b :: a :: H :: Γ ⊢ a → (b → a ∧ b)  (andI axiom)
                  ⟨.ax _ _ (.andI a b)⟩
                  -- b :: a :: H :: Γ ⊢ a  (index 1)
                  (assumption_deriv
                    (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))
                -- b :: a :: H :: Γ ⊢ b  (head, index 0)
                (assumption_deriv (List.mem_cons.mpr (Or.inl rfl))))))
      -- Step 2: Build H :: Γ ⊢ a → goal
      have ha_goal :
          Deriv ClassicalConjImpBotAxiom
            ((a.and b).imp goal :: litCtx v goal as) (a.imp goal) :=
        classicalConjImpBotAxiom_hasDeductionTheorem
          -- a :: H :: Γ ⊢ goal
          (mp_deriv
            -- a :: H :: Γ ⊢ (b → goal) → goal  (IHb-TRUE weakened to a :: H :: Γ)
            (weakening_deriv
              (weakening_deriv (ihbT hvb)
                (fun _ hx => List.mem_cons.mpr (Or.inr hx)))
              (fun _ hx => List.mem_cons.mpr (Or.inr hx)))
            -- a :: H :: Γ ⊢ b → goal  (hab_to_goal weakened + mp with assumption a)
            (mp_deriv
              -- a :: H :: Γ ⊢ a → (b → goal)  (hab_to_goal weakened)
              (weakening_deriv hab_to_goal
                (fun _ hx => List.mem_cons.mpr (Or.inr hx)))
              -- a :: H :: Γ ⊢ a  (head assumption)
              (assumption_deriv (List.mem_cons.mpr (Or.inl rfl)))))
      -- Step 3: Apply IHa-TRUE to a → goal to get goal in H :: Γ
      exact mp_deriv
        -- H :: Γ ⊢ (a → goal) → goal  (IHa-TRUE weakened)
        (weakening_deriv (ihaT hva) (fun _ hx => List.mem_cons.mpr (Or.inr hx)))
        -- H :: Γ ⊢ a → goal
        ha_goal
    · -- FALSE case: (BoolEvaluate v a && BoolEvaluate v b) = false
      -- Goal: Γ ⊢ (a ∧ b) → goal
      -- Split on v a
      cases hva : BoolEvaluate v a with
      | false =>
        -- Left false: compose andE1 with IHa-FALSE
        exact classicalConjImpBot_imp_trans_ctx
          -- Γ ⊢ (a ∧ b) → a  (andE1 axiom)
          ⟨.ax _ _ (.andE1 a b)⟩
          -- Γ ⊢ a → goal  (IHa-FALSE)
          (ihaF hva)
      | true =>
        -- Right false: v b = false
        have hvb : BoolEvaluate v b = false := by
          simp only [hva, Bool.true_and] at hFalse; exact hFalse
        -- Compose andE2 with IHb-FALSE
        exact classicalConjImpBot_imp_trans_ctx
          -- Γ ⊢ (a ∧ b) → b  (andE2 axiom)
          ⟨.ax _ _ (.andE2 a b)⟩
          -- Γ ⊢ b → goal  (IHb-FALSE)
          (ihbF hvb)

/-! ## Atom Elimination -/

/-- Atom elimination (one step): if the context with `p` true derives `goal` and the context
with `p` false (i.e., with `p → goal` instead) also derives `goal`, then the shorter context
without the `p`-literal derives `goal`. Uses the deduction theorem to peel each branch and
combine with one `mp_deriv`. -/
theorem classicalConjImpBot_elim_atom {goal : PL.Proposition Atom}
    {Γ : List (PL.Proposition Atom)} {p : Atom}
    (hT : Deriv ClassicalConjImpBotAxiom (PL.Proposition.atom p :: Γ) goal)
    (hF : Deriv ClassicalConjImpBotAxiom ((PL.Proposition.atom p).imp goal :: Γ) goal) :
    Deriv ClassicalConjImpBotAxiom Γ goal :=
  mp_deriv
    (classicalConjImpBotAxiom_hasDeductionTheorem hF)  -- Γ ⊢ (p → goal) → goal
    (classicalConjImpBotAxiom_hasDeductionTheorem hT)  -- Γ ⊢ p → goal

/-! ## Context Collapse -/

/-- Collapse the full literal context: if for every Boolean assignment the context derives
`goal`, then the empty context derives `goal`. By structural induction on `as`, using
`classicalConjImpBot_elim_atom`.

**Induction step** (`p :: ps`): for each `v`, case-split on `p ∈ ps`:
- `p ∈ ps`: apply the deduction theorem to `h v`; the p-literal already in `litCtx v goal ps`
  (by `litCtx_mem`) provides the `mp_deriv` witness.
- `p ∉ ps`: update `v` to `vT`/`vF` at `p`; since `p ∉ ps`, both tail contexts equal
  `litCtx v goal ps` (by `litCtx_congr'`); `classicalConjImpBot_elim_atom` eliminates `p`. -/
theorem classicalConjImpBot_collapse {goal : PL.Proposition Atom} (as : List Atom)
    (h : ∀ v : BoolValuation Atom, Deriv ClassicalConjImpBotAxiom (litCtx v goal as) goal) :
    Derivable ClassicalConjImpBotAxiom goal := by
  induction as with
  | nil => exact h (fun _ => false)
  | cons p ps ih =>
    apply ih
    intro v
    rcases Classical.em (p ∈ ps) with hp | hp
    · -- p ∈ ps: the p-literal already lies in litCtx v goal ps
      have hlit := litCtx_mem (v := v) (goal := goal) (as := ps) hp
      have hDT := classicalConjImpBotAxiom_hasDeductionTheorem (h v)
      cases hvp : v p with
      | true =>
        simp only [hvp, ite_true] at hlit hDT
        exact mp_deriv hDT (assumption_deriv hlit)
      | false =>
        simp only [hvp] at hlit hDT
        exact mp_deriv hDT (assumption_deriv hlit)
    · -- p ∉ ps: Boolean updates at p leave litCtx v goal ps unchanged
      haveI := Classical.decEq Atom
      have hT : Deriv ClassicalConjImpBotAxiom
          (PL.Proposition.atom p :: litCtx v goal ps) goal := by
        have hTh : Deriv ClassicalConjImpBotAxiom
            (PL.Proposition.atom p :: litCtx (Function.update v p true) goal ps) goal := by
          have h0 := h (Function.update v p true)
          simp only [litCtx, Function.update_self, ite_true] at h0
          exact h0
        rwa [litCtx_congr' (fun q hq =>
          Function.update_of_ne (fun (heq : q = p) => hp (heq ▸ hq)) true v)] at hTh
      have hF : Deriv ClassicalConjImpBotAxiom
          ((PL.Proposition.atom p).imp goal :: litCtx v goal ps) goal := by
        have hFh : Deriv ClassicalConjImpBotAxiom
            ((PL.Proposition.atom p).imp goal ::
              litCtx (Function.update v p false) goal ps) goal := by
          have h0 := h (Function.update v p false)
          simp only [litCtx, Function.update_self] at h0
          exact h0
        rwa [litCtx_congr' (fun q hq =>
          Function.update_of_ne (fun (heq : q = p) => hp (heq ▸ hq)) false v)] at hFh
      exact classicalConjImpBot_elim_atom hT hF

/-! ## Completeness -/

/-- **The Kalmár–Tarski–Bernays completeness theorem for CPL⟨∧,→,⊥,⊤⟩.**
K + S + Peirce + andI + andE1 + andE2 + efq is complete for classical or-free tautologies:
every or-free tautology is derivable in `ClassicalConjImpBotAxiom`.

Proof: for each Boolean assignment `v`, apply `classicalConjImpBot_kalmar` at `goal := φ` to
get `litCtx v φ φ.atomsConjImp ⊢ (φ → φ) → φ` (the TRUE conjunct); weaken
`classicalConjImpBot_imp_self φ` to get `litCtx v φ φ.atomsConjImp ⊢ φ → φ`; apply
`mp_deriv` to obtain `litCtx v φ φ.atomsConjImp ⊢ φ`; then collapse via
`classicalConjImpBot_collapse`. -/
theorem classicalConjImpBot_completeness {φ : PL.Proposition Atom}
    (hOF : φ.IsOrFree = true) (h : Tautology φ) :
    Derivable ClassicalConjImpBotAxiom φ := by
  rw [tautology_iff_boolEvaluate_true] at h
  apply classicalConjImpBot_collapse φ.atomsConjImp
  intro v
  obtain ⟨hkalT, _⟩ :=
    classicalConjImpBot_kalmar (goal := φ) φ.atomsConjImp hOF (fun p hp => hp)
  exact mp_deriv (hkalT (h v))
    (weakening_deriv (classicalConjImpBot_imp_self φ) (fun _ hx => absurd hx List.not_mem_nil))

/-! ## Conservativity and Chain Extension -/

/-- **Classical conservativity (CL-C)**: CPL is conservative over CPL⟨∧,→,⊥,⊤⟩ for
or-free formulas. If an or-free formula is derivable in the full classical propositional
calculus, then it is derivable in the classical conjunctive-implicational-bot fragment
CPL⟨∧,→,⊥,⊤⟩ (K + S + Peirce + andI + andE1 + andE2 + efq). Proof: CPL soundness gives
a tautology; then `classicalConjImpBot_completeness` yields a CPL⟨∧,→,⊥,⊤⟩ derivation.

This completes all three classical conservativity results in the column:
- CL-A: `CPL⟨→,⊤⟩ ⊂ CPL` for imp-top-only formulas
- CL-B: `CPL⟨∧,→,⊤⟩ ⊂ CPL` for or-bot-free formulas
- CL-C: `CPL⟨∧,→,⊥,⊤⟩ ⊂ CPL` for or-free formulas (this theorem) -/
theorem cpl_conservative_over_classicalConjImpBot {φ : PL.Proposition Atom}
    (hOF : φ.IsOrFree = true) (h : Derivable PropositionalAxiom φ) :
    Derivable ClassicalConjImpBotAxiom φ :=
  classicalConjImpBot_completeness hOF (prop_soundness_tautology h)

/-- **Subsumption**: every `ClassicalConjImpBotAxiom`-derivable formula is
`PropositionalAxiom`-derivable. The CPL⟨∧,→,⊥,⊤⟩ axioms K, S, Peirce, andI, andE1, andE2,
and efq are all `PropositionalAxiom`s; lift via `liftDerivationTree` using
`ClassicalConjImpBotAxiom.toPropAxiom`. -/
theorem derivablePropOfDerivableClassicalConjImpBot {φ : PL.Proposition Atom}
    (h : Derivable ClassicalConjImpBotAxiom φ) : Derivable PropositionalAxiom φ := by
  obtain ⟨d⟩ := h
  exact ⟨liftDerivationTree (fun ψ hψ => hψ.toPropAxiom) d⟩

/-- **Biconditional (chain edge CPL⟨∧,→,⊥,⊤⟩ ⊆ CPL)**: for or-free formulas,
CPL⟨∧,→,⊥,⊤⟩ and CPL derivability coincide. Combines
`cpl_conservative_over_classicalConjImpBot` (the completeness direction) with
`derivablePropOfDerivableClassicalConjImpBot` (the axiom-subsumption direction). -/
theorem classicalConjImpBot_iff_chain {φ : PL.Proposition Atom} (hOF : φ.IsOrFree = true) :
    Derivable ClassicalConjImpBotAxiom φ ↔ Derivable PropositionalAxiom φ :=
  ⟨derivablePropOfDerivableClassicalConjImpBot,
    cpl_conservative_over_classicalConjImpBot hOF⟩

end Cslib.Logic.PL
