/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.SequentCalculus.LJ.CutElimination
public import Cslib.Logics.Propositional.SequentCalculus.LJ.Completeness
public import Cslib.Logics.Propositional.ProofSystem.FragmentAxioms

/-! # Conservative Extension: IPL over IPL⟨∨,→,⊤⟩

This module proves that IPL is a conservative extension of the disjunctive-implicational
fragment IPL⟨∨,→,⊤⟩ for and-bot-free formulas.

## Main Results

- `cutFreeLJ_toOrImp`: A cut-free LJ proof of an and-bot-free sequent `Γ ⊢ C` yields an
  OrImp Hilbert derivation of `C` from any list `L` containing all of `Γ`.
- `hilbertIplConservativeOverOrImp`: IPL is a conservative extension of IPL⟨∨,→,⊤⟩ for
  and-bot-free formulas. No `[DecidableEq Atom]` hypothesis. This, together with
  `cutFreeLJ_toOrImp`, is the hard-direction content retained in this file. The generic
  subsumption/biconditional/ND-corollary boilerplate (`derivableOrImpOfDerivableInt`,
  `hilbertIplConservativeOverOrImp_iff`, `ipl_conservative_over_orImp`) is re-homed as a
  `FragmentConservativity` instance in `FragmentConservativityInstances.lean`.

## Proof Strategy

The proof is proof-theoretic, routing through the LJ cut-elimination machinery:
1. `hilbert_iff_lj.mp h` converts `Derivable IntPropAxiom φ` to `Nonempty (LJProof (∅ ⊢ φ))`.
2. `LJProof.cutElim` extracts a `CutFreeLJProof (∅ ⊢ φ)`.
3. `cutFreeLJ_toOrImp` converts the cut-free proof to `Deriv OrImpAxiom [] φ` by structural
   induction on the LJ proof tree. The and-bot-free invariant eliminates the `andL`, `andR`,
   and `botL` cases. The `cut` case is eliminated by cut-freeness.

## References

* [A. S. Troelstra, H. Schwichtenberg, *Basic Proof Theory*][TroelstraSchwichtenberg2000]
* [S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001]
-/

@[expose] public section

noncomputable section

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn

universe u

/-! ## Core Induction Lemma -/

/-- Internal auxiliary lemma for `cutFreeLJ_toOrImp`. All premises are placed inside the
Pi type so that `induction dp` on `dp : LJProof seq` (with `seq` a free variable) succeeds.
This avoids the "index is not a variable" error that occurs when the sequent index is a
concrete pair `(Γ, C)` rather than a fresh variable. -/
private lemma cutFreeLJ_toOrImp_aux {Atom : Type u} [DecidableEq Atom]
    {seq : @Sequent Atom} (dp : LJProof seq) :
    ∀ (_ : LJCutFree dp)
      (_ : ∀ x ∈ seq.1, x.IsAndBotFree = true)
      (_ : seq.2.IsAndBotFree = true)
      (L : List (Proposition Atom))
      (_ : ∀ x ∈ seq.1, x ∈ L),
    Deriv (@OrImpAxiom Atom) L seq.2 := by
  induction dp with
  | ax A _ hA =>
    intro _ _ _ L hL
    exact assumption_deriv (hL A hA)
  | botL _ _ hbot =>
    intro _ hΓ _ _ _
    exact absurd (hΓ _ hbot) (by simp [Proposition.IsAndBotFree])
  | andL A B hAB _ _ =>
    intro _ hΓ _ _ _
    exact absurd (hΓ _ hAB) (by simp [Proposition.IsAndBotFree])
  | andR _ _ _ _ _ _ =>
    intro _ _ hC _ _
    exact absurd hC (by simp [Proposition.IsAndBotFree])
  | orR1 A B _ ih =>
    intro hcf hΓ hC L hL
    simp only [Proposition.IsAndBotFree, Bool.and_eq_true] at hC
    exact hilbertOrI1Deriv (fun φ ψ => .orI1 φ ψ) (ih hcf hΓ hC.1 L hL)
  | orR2 A B _ ih =>
    intro hcf hΓ hC L hL
    simp only [Proposition.IsAndBotFree, Bool.and_eq_true] at hC
    exact hilbertOrI2Deriv (fun φ ψ => .orI2 φ ψ) (ih hcf hΓ hC.2 L hL)
  | orL A B hAB _ _ ih₁ ih₂ =>
    intro ⟨hcf₁, hcf₂⟩ hΓ hC L hL
    have hAorB_abf : (A.or B).IsAndBotFree = true := hΓ _ hAB
    simp only [Proposition.IsAndBotFree, Bool.and_eq_true] at hAorB_abf
    exact hilbertOrEDeriv
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ ψ χ => .orE φ ψ χ)
      (assumption_deriv (hL _ hAB))
      (ih₁ hcf₁
        (fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hxΓ
          · exact hAorB_abf.1
          · exact hΓ x hxΓ)
        hC (A :: L)
        (fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hxΓ
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hL x hxΓ)))
      (ih₂ hcf₂
        (fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hxΓ
          · exact hAorB_abf.2
          · exact hΓ x hxΓ)
        hC (B :: L)
        (fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hxΓ
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hL x hxΓ)))
  | impL A B hAB _ _ ih₁ ih₂ =>
    intro ⟨hcf₁, hcf₂⟩ hΓ hC L hL
    have hAiB_abf : (A.imp B).IsAndBotFree = true := hΓ _ hAB
    simp only [Proposition.IsAndBotFree, Bool.and_eq_true] at hAiB_abf
    -- Derive A from the first IH
    have dA := ih₁ hcf₁ hΓ hAiB_abf.1 L hL
    -- Derive A→B by assumption, then B by modus ponens
    have dB := hilbertImpEDeriv (assumption_deriv (hL _ hAB)) dA
    -- Derive C given B, using deduction theorem and modus ponens
    have dBiC := hilbertImpIDeriv (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
      (ih₂ hcf₂
        (fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hxΓ
          · exact hAiB_abf.2
          · exact hΓ x hxΓ)
        hC (B :: L)
        (fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hxΓ
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hL x hxΓ)))
    exact hilbertImpEDeriv dBiC dB
  | impR A B _ ih =>
    intro hcf hΓ hC L hL
    simp only [Proposition.IsAndBotFree, Bool.and_eq_true] at hC
    exact hilbertImpIDeriv (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
      (ih hcf
        (fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hxΓ
          · exact hC.1
          · exact hΓ x hxΓ)
        hC.2 (A :: L)
        (fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hxΓ
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hL x hxΓ)))
  | weakL _ _ ih =>
    intro hcf hΓ hC L hL
    -- d' : LJProof (Γ ⊢ C), outer context is insert A Γ
    exact ih hcf
      (fun x hx => hΓ x (Finset.mem_insert_of_mem hx))
      hC L
      (fun x hx => hL x (Finset.mem_insert_of_mem hx))
  | cut _ _ _ _ _ =>
    intro hcf _ _ _ _
    exact hcf.elim

/-- **Cut-free LJ to OrImp**: a cut-free LJ proof of an and-bot-free sequent `Γ ⊢ C`
yields an OrImp Hilbert derivation of `C` from any list `L ⊇ Γ`.

The proof is by structural induction on the LJ proof tree (via `cutFreeLJ_toOrImp_aux`):
- `ax`: `A ∈ Γ ⊆ L`, so use the assumption rule.
- `botL`: vacuous — `⊥ ∈ Γ` contradicts `hΓ` (`⊥.IsAndBotFree = false`).
- `andL`: vacuous — `A∧B ∈ Γ` contradicts `hΓ` (`(A∧B).IsAndBotFree = false`).
- `andR`: vacuous — conclusion `A∧B` contradicts `hC` (`(A∧B).IsAndBotFree = false`).
- `orR1`/`orR2`: apply IH then `hilbertOrI1Deriv`/`hilbertOrI2Deriv`.
- `orL`: two IHs + `hilbertOrEDeriv` (with `A∨B` derivable from `L` by assumption).
- `impL`: `hilbertImpEDeriv` + IH(A) gives `B`; IH(C) via deduction theorem + MP.
- `impR`: IH with extended list + `hilbertImpIDeriv` (deduction theorem).
- `weakL`: IH restricted to the smaller context `Γ' ⊂ insert A Γ'`.
- `cut`: vacuous — `d.2 : LJCutFree` eliminates this case (`False`). -/
theorem cutFreeLJ_toOrImp {Atom : Type u} [DecidableEq Atom]
    {Γ : Ctx Atom} {C : Proposition Atom}
    (hΓ : ∀ x ∈ Γ, x.IsAndBotFree = true) (hC : C.IsAndBotFree = true)
    (d : CutFreeLJProof (Γ ⊢ C))
    {L : List (Proposition Atom)} (hL : ∀ x ∈ Γ, x ∈ L) :
    Deriv (@OrImpAxiom Atom) L C :=
  cutFreeLJ_toOrImp_aux d.1 d.2 hΓ hC L hL

/-! ## Public Hilbert-Primary Conservative Extension -/

/-- **Hilbert-primary conservative extension theorem**: IPL is a conservative extension of
IPL⟨∨,→,⊤⟩ for and-bot-free formulas. If `φ` is derivable in the intuitionistic Hilbert
system and `φ` contains no `∧` or `⊥`, then `φ` is already derivable in the
disjunctive-implicational Hilbert system.

The proof routes through LJ cut elimination:
1. `hilbert_iff_lj.mp h` converts `Derivable IntPropAxiom φ` to `Nonempty (LJProof (∅ ⊢ φ))`.
2. `LJProof.cutElim` yields a `CutFreeLJProof (∅ ⊢ φ)`.
3. `cutFreeLJ_toOrImp` converts to `Deriv OrImpAxiom [] φ = Derivable OrImpAxiom φ`.

The public signature omits `[DecidableEq Atom]` (parallel to `hilbertIplConservativeOverConjImp`).
Classical choice is used inside the body to supply the required `DecidableEq` instance. -/
theorem hilbertIplConservativeOverOrImp {Atom : Type u} {φ : PL.Proposition Atom}
    (hABF : φ.IsAndBotFree = true) (h : Derivable (@IntPropAxiom Atom) φ) :
    Derivable (@OrImpAxiom Atom) φ := by
  letI : DecidableEq Atom := Classical.decEq Atom
  -- Convert Derivable to LJProof via hilbert_iff_lj (Γ = ∅, toList ∅ = [])
  rw [Derivable, ← Finset.toList_empty (α := Proposition Atom)] at h
  obtain ⟨d⟩ := (hilbert_iff_lj (Γ := ∅)).mp h
  -- Eliminate cuts
  obtain ⟨dcf⟩ := d.cutElim
  -- Convert cut-free LJ proof to OrImp Hilbert derivation
  exact cutFreeLJ_toOrImp (by simp) hABF dcf (by simp)

/-! ## Completeness Relative to IPL Semantics -/

/-- **OrImp completeness relative to IPL semantics, on the and-bot-free sublanguage.**
For and-bot-free formulas, `IValid` (intuitionistic Kripke validity, the semantic notion IPL
itself is complete for) implies `OrImpAxiom` derivability.

**This is explicitly NOT fragment-matched algebraic completeness.** The other three
intuitionistic fragments with a completeness theorem (`ConjImp`, `Imp`, `ConjImpBot`) are
complete against an algebra class matched to their own signature. `OrImpAxiom`'s meet-free
`⟨∨, →, ⊤⟩` signature gives `→` nothing to residuate against, so no such fragment-matched
algebra has been defined for it (this is the D1-absolute gap, recorded as a follow-up
recommendation rather than attempted here — it needs a new algebra class chosen and defined,
which is definitional infrastructure, not just a proof). What this theorem gives instead is
completeness **relative to full IPL semantics**, restricted to the and-bot-free sublanguage:
any and-bot-free formula valid in every intuitionistic Kripke model has an OrImp Hilbert
derivation. An unqualified "orImp completeness" reading of this theorem would overclaim exactly
the class of defect Phase 1 of this task corrects elsewhere in the tree.

Composes `IValid φ → Derivable IntPropAxiom φ` (via `lj_iff_ivalid` and `hilbert_iff_lj`, the
Kripke-to-LJ-to-Hilbert completeness route already used by `hilbertIplConservativeOverOrImp`'s
own proof) with `hilbertIplConservativeOverOrImp` itself (the hard direction of the
conservative-extension biconditional — `hilbertIplConservativeOverOrImp_iff.mp` in
`FragmentConservativityInstances.lean` reduces to this same function, but that module is not
imported here to avoid a dependency cycle, since it in turn imports this file). -/
theorem orImpCompletenessRelativeToIPL {Atom : Type u} {φ : PL.Proposition Atom}
    (hABF : φ.IsAndBotFree = true) (h : IValid.{u, u} φ) :
    Derivable (@OrImpAxiom Atom) φ := by
  letI : DecidableEq Atom := Classical.decEq Atom
  obtain ⟨d⟩ := lj_iff_ivalid.mp h
  have hderiv : Derivable (@IntPropAxiom Atom) φ := by
    rw [Derivable, ← Finset.toList_empty (α := Proposition Atom)]
    exact hilbert_iff_lj.mpr ⟨d⟩
  exact hilbertIplConservativeOverOrImp hABF hderiv

/-! ## Subsumption / Biconditional / ND Corollary (re-homed)

The generic subsumption, biconditional, and ND-corollary boilerplate for this fragment
(`derivableOrImpOfDerivableInt`, `hilbertIplConservativeOverOrImp_iff`,
`ipl_conservative_over_orImp`) now lives in `FragmentConservativityInstances.lean`, as one-line
consequences of `fragmentConservativityOrImp` applied to the generic `FragmentConservativity`
core (Part B consolidation). -/

end Cslib.Logic.PL

end

end
