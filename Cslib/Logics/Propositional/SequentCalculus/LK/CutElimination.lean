/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.SequentCalculus.LK.Basic

/-! # Cut Elimination for LK (Hauptsatz)

We prove cut admissibility for the classical sequent calculus LK: every sequent provable
in LK is provable by a cut-free LK proof. This is Gentzen's *Hauptsatz*.

## Proof Strategy

Following [TroelstraSchwichtenberg2000] Theorem 4.1.5 and [NegriVonPlato2001] Theorem 3.2.3,
using lexicographic induction on `(sizeOf C, d₁.height + d₂.height)`.

The proof uses five structural helpers with generic-sequent parameters to avoid Finset quotient
equation failures during pattern matching on `LKProof` constructors. Each helper takes
`{Γ Δ : Finset ...} (d : LKProof (Γ ⊢ₛ Δ))` together with subset hypotheses connecting
`Γ` and `Δ` to the desired conclusion sequent.

## References

* [A. S. Troelstra, H. Schwichtenberg,
  *Basic Proof Theory*][TroelstraSchwichtenberg2000], Ch. 4, Theorem 4.1.5
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition LKSequent

variable {Atom : Type u} [DecidableEq Atom]

/-! ## Cut-Freeness Preservation Under Weakening -/

/-- Weakening preserves cut-freeness: if a proof is cut-free, so is any monotone
extension to larger contexts. -/
lemma CutFree.mono {seq : LKSequent Atom} {Γ' Δ' : Finset (Proposition Atom)}
    (d : LKProof seq) (hL : seq.ant ⊆ Γ') (hR : seq.suc ⊆ Δ') (hcf : CutFree d) :
    CutFree (d.mono hL hR) := by
  induction d generalizing Γ' Δ' with
  | ax => simp [LKProof.mono, CutFree]
  | botL => simp [LKProof.mono, CutFree]
  | andL A B hAB d' ih =>
    simp only [LKProof.mono, CutFree]
    exact ih (Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hL)) hR hcf
  | andR A B hAB d₁ d₂ ih₁ ih₂ =>
    simp only [LKProof.mono, CutFree]
    exact ⟨ih₁ hL (Finset.insert_subset_insert _ hR) hcf.1,
           ih₂ hL (Finset.insert_subset_insert _ hR) hcf.2⟩
  | orL A B hAB d₁ d₂ ih₁ ih₂ =>
    simp only [LKProof.mono, CutFree]
    exact ⟨ih₁ (Finset.insert_subset_insert _ hL) hR hcf.1,
           ih₂ (Finset.insert_subset_insert _ hL) hR hcf.2⟩
  | orR A B hAB d' ih =>
    simp only [LKProof.mono, CutFree]
    exact ih hL (Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hR)) hcf
  | impL A B hAB d₁ d₂ ih₁ ih₂ =>
    simp only [LKProof.mono, CutFree]
    exact ⟨ih₁ hL (Finset.insert_subset_insert _ hR) hcf.1,
           ih₂ (Finset.insert_subset_insert _ hL) hR hcf.2⟩
  | impR A B hAB d' ih =>
    simp only [LKProof.mono, CutFree]
    exact ih (Finset.insert_subset_insert _ hL) (Finset.insert_subset_insert _ hR) hcf
  | weakL A d' ih =>
    simp only [LKProof.mono]
    exact ih ((Finset.subset_insert A _).trans hL) hR hcf
  | weakR A d' ih =>
    simp only [LKProof.mono]
    exact ih hL ((Finset.subset_insert A _).trans hR) hcf
  | cut => exact absurd hcf id

/-- Weakening for cut-free LK proofs: if `Γ ⊢ₛ Δ` is cut-free-derivable, so is `Γ' ⊢ₛ Δ'`
for any `Γ' ⊇ Γ` and `Δ' ⊇ Δ`. -/
def CutFreeLKProof.mono {Γ Δ Γ' Δ' : Finset (Proposition Atom)}
    (hL : Γ ⊆ Γ') (hR : Δ ⊆ Δ') (d : CutFreeLKProof (Γ ⊢ₛ Δ)) :
    CutFreeLKProof (Γ' ⊢ₛ Δ') :=
  ⟨d.1.mono hL hR, CutFree.mono d.1 hL hR d.2⟩

/-! ## Cut Admissibility

### Helper type alias -/

/-- The induction hypothesis type for subformula induction in cut admissibility.
For each formula B strictly smaller than C, we can eliminate a cut on B from cut-free proofs. -/
noncomputable abbrev CutIH (C : Proposition Atom) : Type u :=
  ∀ (B : Proposition Atom), sizeOf B < sizeOf C →
    ∀ (Γ Δ : Finset (Proposition Atom)),
    CutFreeLKProof (Γ ⊢ₛ insert B Δ) →
    CutFreeLKProof (insert B Γ ⊢ₛ Δ) →
    CutFreeLKProof (Γ ⊢ₛ Δ)

/-! ### Helper: insert membership branching -/

/-- From `x ∈ insert a s` and `x ≠ a`, extract `x ∈ s`. -/
theorem mem_of_ne_head {α : Type*} [DecidableEq α] {a x : α} {s : Finset α}
    (hx : x ∈ insert a s) (hne : x ≠ a) : x ∈ s :=
  Finset.mem_of_mem_insert_of_ne hx hne

/-! ### Shared Finset subset helpers -/

/-- `s ⊆ insert a (insert b s)` by double application of `Finset.subset_insert`. -/
theorem subset_insert₂ {α : Type*} [DecidableEq α] (a b : α) (s : Finset α) :
    s ⊆ insert a (insert b s) :=
  (Finset.subset_insert b s).trans (Finset.subset_insert a _)

/-- Transport a subset through an outer insert: from `s ⊆ insert c t` derive
`insert a s ⊆ insert c (insert a t)`. -/
theorem insert_subset_swap {α : Type*} [DecidableEq α]
    {c a : α} {s t : Finset α}
    (h : s ⊆ insert c t) : insert a s ⊆ insert c (insert a t) :=
  Finset.insert_subset
    (Finset.mem_insert_of_mem (Finset.mem_insert_self a _))
    (fun _ hx => (Finset.insert_subset_insert c (Finset.subset_insert a _)) (h hx))

/-- Left-side weakening for cut-free proofs: weaken the antecedent while preserving
the succedent unchanged. -/
def CutFreeLKProof.monoL {Γ Δ Γ' : Finset (Proposition Atom)}
    (h : Γ ⊆ Γ') (d : CutFreeLKProof (Γ ⊢ₛ Δ)) :
    CutFreeLKProof (Γ' ⊢ₛ Δ) :=
  d.mono h (Finset.Subset.refl _)

/-- Right-side weakening for cut-free proofs: weaken the succedent while preserving
the antecedent unchanged. -/
def CutFreeLKProof.monoR {Γ Δ Δ' : Finset (Proposition Atom)}
    (h : Δ ⊆ Δ') (d : CutFreeLKProof (Γ ⊢ₛ Δ)) :
    CutFreeLKProof (Γ ⊢ₛ Δ') :=
  d.mono (Finset.Subset.refl _) h

/-! ### Principal-case helpers (self-recursive, extracted from mutual block)

Each helper performs structural recursion on the right proof `d₂` for one specific
connective-principal interaction. They are self-recursive only and do not call
`cutAdmRight` or `cutAdmLeft`, so they can live outside the mutual block. -/

/-- Principal andR/andL case: structural recursion on `d₂` given
`d₁a : Γ₀ ⊢ₛ insert A Δ₀` and `d₁b : Γ₀ ⊢ₛ insert B Δ₀` from the andR side. -/
noncomputable def cutAdmRightAndR
    (A B : Proposition Atom) (Γ₀ Δ₀ : Finset (Proposition Atom))
    (d₁a : CutFreeLKProof (Γ₀ ⊢ₛ insert A Δ₀))
    (d₁b : CutFreeLKProof (Γ₀ ⊢ₛ insert B Δ₀))
    (ih : CutIH (Proposition.and A B))
    {Γ Δ : Finset (Proposition Atom)} (d₂ : LKProof (Γ ⊢ₛ Δ)) (hcf₂ : CutFree d₂)
    (hant : Γ ⊆ insert (A ∧ B) Γ₀) (hsuc : Δ ⊆ Δ₀) :
    CutFreeLKProof (Γ₀ ⊢ₛ Δ₀) :=
  match d₂, hcf₂ with
  | .ax phi _ _ hphiL hphiD, _ =>
    if heq : phi = Proposition.and A B then
      if h : phi ∈ Γ₀ then
        ⟨.ax phi Γ₀ Δ₀ h (hsuc hphiD), trivial⟩
      else
        have hmem_left : phi ∈ insert (A ∧ B) Γ₀ := hant hphiL
        have h_eq_cut : phi = (A ∧ B) := by
          rcases Finset.mem_insert.mp hmem_left with h_eq | h_in
          · exact h_eq
          · exact absurd h_in h
        have hmem : (A ∧ B) ∈ Δ₀ := h_eq_cut ▸ (hsuc hphiD)
        ⟨.andR A B hmem d₁a.1 d₁b.1, ⟨d₁a.2, d₁b.2⟩⟩
    else
      ⟨.ax phi Γ₀ Δ₀ (mem_of_ne_head (hant hphiL) heq) (hsuc hphiD), trivial⟩
  | .botL _ _ hbot, _ =>
    ⟨.botL Γ₀ Δ₀ (mem_of_ne_head (hant hbot)
        (by intro h; cases h)), by unfold CutFree; trivial⟩
  | .andL A' B' hAB d', hcf' =>
    if h1 : A' = A ∧ B' = B then
      -- PRINCIPAL CASE: d₂ = andL A B, C = A ∧ B.
      -- Recurse on d' (structurally smaller) with widened Γ₀, then use ih A, ih B.
      have hA : sizeOf A < sizeOf (Proposition.and A B) := by
        rw [Proposition.and.sizeOf_spec]; omega
      have hB : sizeOf B < sizeOf (Proposition.and A B) := by
        rw [Proposition.and.sizeOf_spec]; omega
      let wk : Γ₀ ⊆ insert A (insert B Γ₀) :=
        (Finset.subset_insert B Γ₀).trans (Finset.subset_insert A _)
      let hant' : insert A' (insert B' Γ) ⊆ insert (A ∧ B) (insert A (insert B Γ₀)) :=
        Finset.insert_subset
          (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl h1.1)))
          (Finset.insert_subset
            (Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl h1.2))))
            (fun x hx => (Finset.insert_subset_insert (A ∧ B) wk) (hant hx)))
      let d₂' := cutAdmRightAndR A B (insert A (insert B Γ₀)) Δ₀
        (d₁a.mono wk (Finset.Subset.refl _))
        (d₁b.mono wk (Finset.Subset.refl _))
        ih d' hcf' hant' hsuc
      let d₁a_w := d₁a.mono (Finset.subset_insert B _) (Finset.Subset.refl _)
      let r₁ := ih A hA (insert B Γ₀) Δ₀ d₁a_w d₂'
      ih B hB Γ₀ Δ₀ d₁b r₁
    else
      let hAB₀ : (A' ∧ B') ∈ Γ₀ := mem_of_ne_head (hant hAB)
        (by intro heq; injection heq with h1a h1b; exact h1 ⟨h1a, h1b⟩)
      let wk2 : Γ₀ ⊆ insert A' (insert B' Γ₀) :=
        (Finset.subset_insert B' Γ₀).trans (Finset.subset_insert A' _)
      let hant' : insert A' (insert B' Γ) ⊆ insert (A ∧ B) (insert A' (insert B' Γ₀)) :=
        Finset.insert_subset
          (Finset.mem_insert_of_mem (Finset.mem_insert_self A' _))
          (Finset.insert_subset
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self B' _)))
            (fun x hx => (Finset.insert_subset_insert _ wk2) (hant hx)))
      let ⟨r, hr⟩ := cutAdmRightAndR A B (insert A' (insert B' Γ₀)) Δ₀
        (d₁a.mono wk2 (Finset.Subset.refl _))
        (d₁b.mono wk2 (Finset.Subset.refl _))
        ih d' hcf' hant' hsuc
      ⟨.andL A' B' hAB₀ r, hr⟩
  | .andR A' B' hAB d₂a d₂b, hcf_ab =>
    let hAB₀ : (A' ∧ B') ∈ Δ₀ := hsuc hAB
    let ⟨ra, hra⟩ := cutAdmRightAndR A B Γ₀ (insert A' Δ₀)
      (d₁a.mono (Finset.Subset.refl _) (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
      (d₁b.mono (Finset.Subset.refl _) (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
      ih d₂a hcf_ab.1 hant
      (Finset.insert_subset_insert _ hsuc)
    let ⟨rb, hrb⟩ := cutAdmRightAndR A B Γ₀ (insert B' Δ₀)
      (d₁a.mono (Finset.Subset.refl _) (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
      (d₁b.mono (Finset.Subset.refl _) (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
      ih d₂b hcf_ab.2 hant
      (Finset.insert_subset_insert _ hsuc)
    ⟨.andR A' B' hAB₀ ra rb, And.intro hra hrb⟩
  | .orL A' B' hAB d₂a d₂b, hcf_ab =>
    let hAB₀ : (A' ∨ B') ∈ Γ₀ := mem_of_ne_head (hant hAB)
      (by intro h; cases h)
    let hant_a : insert A' Γ ⊆ insert (A ∧ B) (insert A' Γ₀) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self A' _))
        (fun x hx => (Finset.insert_subset_insert _ (Finset.subset_insert A' _)) (hant hx))
    let hant_b : insert B' Γ ⊆ insert (A ∧ B) (insert B' Γ₀) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self B' _))
        (fun x hx => (Finset.insert_subset_insert _ (Finset.subset_insert B' _)) (hant hx))
    let ⟨ra, hra⟩ := cutAdmRightAndR A B (insert A' Γ₀) Δ₀
      (d₁a.mono (Finset.subset_insert _ _) (Finset.Subset.refl _))
      (d₁b.mono (Finset.subset_insert _ _) (Finset.Subset.refl _))
      ih d₂a hcf_ab.1 hant_a hsuc
    let ⟨rb, hrb⟩ := cutAdmRightAndR A B (insert B' Γ₀) Δ₀
      (d₁a.mono (Finset.subset_insert _ _) (Finset.Subset.refl _))
      (d₁b.mono (Finset.subset_insert _ _) (Finset.Subset.refl _))
      ih d₂b hcf_ab.2 hant_b hsuc
    ⟨.orL A' B' hAB₀ ra rb, And.intro hra hrb⟩
  | .orR A' B' hAB d', hcf' =>
    let hAB₀ : (A' ∨ B') ∈ Δ₀ := hsuc hAB
    let wkR : Δ₀ ⊆ insert A' (insert B' Δ₀) :=
      (Finset.subset_insert B' _).trans (Finset.subset_insert A' _)
    let ⟨r, hr⟩ := cutAdmRightAndR A B Γ₀ (insert A' (insert B' Δ₀))
      (d₁a.mono (Finset.Subset.refl _)
        (Finset.insert_subset_insert _ wkR))
      (d₁b.mono (Finset.Subset.refl _)
        (Finset.insert_subset_insert _ wkR))
      ih d' hcf' hant
      (Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hsuc))
    ⟨.orR A' B' hAB₀ r, hr⟩
  | .impL A' B' hAB d₂a d₂b, hcf_ab =>
    let hAB₀ : (A' → B') ∈ Γ₀ := mem_of_ne_head (hant hAB)
      (by intro h; cases h)
    let hant_b : insert B' Γ ⊆ insert (A ∧ B) (insert B' Γ₀) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self B' _))
        (fun x hx => (Finset.insert_subset_insert _ (Finset.subset_insert B' _)) (hant hx))
    let ⟨ra, hra⟩ := cutAdmRightAndR A B Γ₀ (insert A' Δ₀)
      (d₁a.mono (Finset.Subset.refl _) (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
      (d₁b.mono (Finset.Subset.refl _) (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
      ih d₂a hcf_ab.1 hant
      (Finset.insert_subset_insert _ hsuc)
    let ⟨rb, hrb⟩ := cutAdmRightAndR A B (insert B' Γ₀) Δ₀
      (d₁a.mono (Finset.subset_insert _ _) (Finset.Subset.refl _))
      (d₁b.mono (Finset.subset_insert _ _) (Finset.Subset.refl _))
      ih d₂b hcf_ab.2 hant_b hsuc
    ⟨.impL A' B' hAB₀ ra rb, And.intro hra hrb⟩
  | .impR A' B' hAB d', hcf' =>
    let hAB₀ : (A' → B') ∈ Δ₀ := hsuc hAB
    let hant' : insert A' Γ ⊆ insert (A ∧ B) (insert A' Γ₀) := insert_subset_swap hant
    let ⟨r, hr⟩ := cutAdmRightAndR A B (insert A' Γ₀) (insert B' Δ₀)
      (d₁a.mono (Finset.subset_insert A' _)
        (Finset.insert_subset_insert _ (Finset.subset_insert B' _)))
      (d₁b.mono (Finset.subset_insert A' _)
        (Finset.insert_subset_insert _ (Finset.subset_insert B' _)))
      ih d' hcf' hant'
      (Finset.insert_subset_insert _ hsuc)
    ⟨.impR A' B' hAB₀ r, hr⟩
  | .weakL A' d', hcf' =>
    cutAdmRightAndR A B Γ₀ Δ₀ d₁a d₁b ih d' hcf'
      (fun x hx => hant (Finset.mem_insert_of_mem hx)) hsuc
  | .weakR A' d', hcf' =>
    cutAdmRightAndR A B Γ₀ Δ₀ d₁a d₁b ih d' hcf' hant ((Finset.subset_insert A' _).trans hsuc)
  | .cut _ _ _, hcf' => absurd hcf' id

/-- Principal orR/orL case: structural recursion on `d₂` given
`d₁' : Γ₀ ⊢ₛ insert A (insert B Δ₀)` from the orR side. -/
noncomputable def cutAdmRightOrR
    (A B : Proposition Atom) (Γ₀ Δ₀ : Finset (Proposition Atom))
    (d₁' : CutFreeLKProof (Γ₀ ⊢ₛ insert A (insert B Δ₀)))
    (ih : CutIH (Proposition.or A B))
    {Γ Δ : Finset (Proposition Atom)} (d₂ : LKProof (Γ ⊢ₛ Δ)) (hcf₂ : CutFree d₂)
    (hant : Γ ⊆ insert (A ∨ B) Γ₀) (hsuc : Δ ⊆ Δ₀) :
    CutFreeLKProof (Γ₀ ⊢ₛ Δ₀) :=
  match d₂, hcf₂ with
  | .ax phi _ _ hphiL hphiD, _ =>
    if heq : phi = Proposition.or A B then
      have hmem : A.or B ∈ Δ₀ := heq ▸ (hsuc hphiD)
      if h : phi ∈ Γ₀ then
        ⟨.ax phi Γ₀ Δ₀ h (hsuc hphiD), trivial⟩
      else
        have : phi = (A ∨ B) := by
          rcases Finset.mem_insert.mp (hant hphiL) with h_eq | h_in
          · exact h_eq
          · exact absurd h_in h
        ⟨.orR A B hmem d₁'.1, d₁'.2⟩
    else
      ⟨.ax phi Γ₀ Δ₀ (mem_of_ne_head (hant hphiL) heq) (hsuc hphiD), trivial⟩
  | .botL _ _ hbot, _ =>
    ⟨.botL Γ₀ Δ₀ (mem_of_ne_head (hant hbot)
        (by intro h; cases h)), by unfold CutFree; trivial⟩
  | .andL A' B' hAB d', hcf' =>
    let hAB₀ : (A' ∧ B') ∈ Γ₀ := mem_of_ne_head (hant hAB)
      (by intro h; cases h)
    let wk2 : Γ₀ ⊆ insert A' (insert B' Γ₀) :=
      (Finset.subset_insert B' Γ₀).trans (Finset.subset_insert A' _)
    let hant' : insert A' (insert B' Γ) ⊆ insert (A ∨ B) (insert A' (insert B' Γ₀)) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self A' _))
        (Finset.insert_subset
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self B' _)))
          (fun x hx => (Finset.insert_subset_insert _ wk2) (hant hx)))
    let ⟨r, hr⟩ := cutAdmRightOrR A B (insert A' (insert B' Γ₀)) Δ₀
      (d₁'.mono wk2 (Finset.Subset.refl _))
      ih d' hcf' hant' hsuc
    ⟨.andL A' B' hAB₀ r, hr⟩
  | .andR A' B' hAB d₂a d₂b, hcf_ab =>
    let hAB₀ : (A' ∧ B') ∈ Δ₀ := hsuc hAB
    let ⟨ra, hra⟩ := cutAdmRightOrR A B Γ₀ (insert A' Δ₀)
      (d₁'.mono (Finset.Subset.refl _)
        (Finset.insert_subset_insert _ (Finset.insert_subset_insert _ (Finset.subset_insert _ _))))
      ih d₂a hcf_ab.1 hant
      (Finset.insert_subset_insert _ hsuc)
    let ⟨rb, hrb⟩ := cutAdmRightOrR A B Γ₀ (insert B' Δ₀)
      (d₁'.mono (Finset.Subset.refl _)
        (Finset.insert_subset_insert _ (Finset.insert_subset_insert _ (Finset.subset_insert _ _))))
      ih d₂b hcf_ab.2 hant
      (Finset.insert_subset_insert _ hsuc)
    ⟨.andR A' B' hAB₀ ra rb, And.intro hra hrb⟩
  | .orL A' B' hAB d₂a d₂b, hcf_ab =>
    if h1 : A' = A ∧ B' = B then
      -- PRINCIPAL CASE: d₂ = orL A B, C = A ∨ B.
      -- Recurse on d₂a, d₂b (structurally smaller), then use ih A, ih B.
      have hA : sizeOf A < sizeOf (Proposition.or A B) := by rw [Proposition.or.sizeOf_spec]; omega
      have hB : sizeOf B < sizeOf (Proposition.or A B) := by rw [Proposition.or.sizeOf_spec]; omega
      let wk_a : Γ₀ ⊆ insert A Γ₀ := Finset.subset_insert A _
      let wk_b : Γ₀ ⊆ insert B Γ₀ := Finset.subset_insert B _
      let hant_a : insert A' Γ ⊆ insert (A ∨ B) (insert A Γ₀) :=
        Finset.insert_subset
          (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl h1.1)))
          (fun x hx => (Finset.insert_subset_insert (A ∨ B) wk_a) (hant hx))
      let hant_b : insert B' Γ ⊆ insert (A ∨ B) (insert B Γ₀) :=
        Finset.insert_subset
          (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl h1.2)))
          (fun x hx => (Finset.insert_subset_insert (A ∨ B) wk_b) (hant hx))
      let d₂a' := cutAdmRightOrR A B (insert A Γ₀) Δ₀
        (d₁'.mono wk_a (Finset.Subset.refl _))
        ih d₂a hcf_ab.1 hant_a hsuc
      let d₂b' := cutAdmRightOrR A B (insert B Γ₀) Δ₀
        (d₁'.mono wk_b (Finset.Subset.refl _))
        ih d₂b hcf_ab.2 hant_b hsuc
      let d₂a_w := d₂a'.mono (Finset.Subset.refl _) (Finset.subset_insert B _)
      let r₁ := ih A hA Γ₀ (insert B Δ₀) d₁' d₂a_w
      ih B hB Γ₀ Δ₀ r₁ d₂b'
    else
      let hAB₀ : (A' ∨ B') ∈ Γ₀ := mem_of_ne_head (hant hAB)
        (by intro heq; injection heq with h1a h1b; exact h1 ⟨h1a, h1b⟩)
      let hant_a : insert A' Γ ⊆ insert (A ∨ B) (insert A' Γ₀) :=
        Finset.insert_subset
          (Finset.mem_insert_of_mem (Finset.mem_insert_self A' _))
          (fun x hx => (Finset.insert_subset_insert _ (Finset.subset_insert A' _)) (hant hx))
      let hant_b : insert B' Γ ⊆ insert (A ∨ B) (insert B' Γ₀) :=
        Finset.insert_subset
          (Finset.mem_insert_of_mem (Finset.mem_insert_self B' _))
          (fun x hx => (Finset.insert_subset_insert _ (Finset.subset_insert B' _)) (hant hx))
      let ⟨ra, hra⟩ := cutAdmRightOrR A B (insert A' Γ₀) Δ₀
        (d₁'.mono (Finset.subset_insert _ _) (Finset.Subset.refl _))
        ih d₂a hcf_ab.1 hant_a hsuc
      let ⟨rb, hrb⟩ := cutAdmRightOrR A B (insert B' Γ₀) Δ₀
        (d₁'.mono (Finset.subset_insert _ _) (Finset.Subset.refl _))
        ih d₂b hcf_ab.2 hant_b hsuc
      ⟨.orL A' B' hAB₀ ra rb, And.intro hra hrb⟩
  | .orR A' B' hAB d', hcf' =>
    let hAB₀ : (A' ∨ B') ∈ Δ₀ := hsuc hAB
    let wkR : Δ₀ ⊆ insert A' (insert B' Δ₀) :=
      (Finset.subset_insert B' _).trans (Finset.subset_insert A' _)
    let ⟨r, hr⟩ := cutAdmRightOrR A B Γ₀ (insert A' (insert B' Δ₀))
      (d₁'.mono (Finset.Subset.refl _)
        (Finset.insert_subset_insert _ (Finset.insert_subset_insert _ wkR)))
      ih d' hcf' hant
      (Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hsuc))
    ⟨.orR A' B' hAB₀ r, hr⟩
  | .impL A' B' hAB d₂a d₂b, hcf_ab =>
    let hAB₀ : (A' → B') ∈ Γ₀ := mem_of_ne_head (hant hAB) (by intro h; cases h)
    let hant_b : insert B' Γ ⊆ insert (A ∨ B) (insert B' Γ₀) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self B' _))
        (fun x hx => (Finset.insert_subset_insert _ (Finset.subset_insert B' _)) (hant hx))
    let wkR_a : insert A (insert B Δ₀) ⊆ insert A (insert B (insert A' Δ₀)) :=
      Finset.insert_subset_insert _ (Finset.insert_subset_insert _ (Finset.subset_insert A' _))
    let ⟨ra, hra⟩ := cutAdmRightOrR A B Γ₀ (insert A' Δ₀)
      (d₁'.mono (Finset.Subset.refl _) wkR_a)
      ih d₂a hcf_ab.1 hant
      (Finset.insert_subset_insert _ hsuc)
    let ⟨rb, hrb⟩ := cutAdmRightOrR A B (insert B' Γ₀) Δ₀
      (d₁'.mono (Finset.subset_insert _ _) (Finset.Subset.refl _))
      ih d₂b hcf_ab.2 hant_b hsuc
    ⟨.impL A' B' hAB₀ ra rb, And.intro hra hrb⟩
  | .impR A' B' hAB d', hcf' =>
    let hAB₀ : (A' → B') ∈ Δ₀ := hsuc hAB
    let hant' : insert A' Γ ⊆ insert (A ∨ B) (insert A' Γ₀) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self A' _))
        (fun x hx => (Finset.insert_subset_insert _ (Finset.subset_insert A' _)) (hant hx))
    let wkR_imp : insert A (insert B Δ₀) ⊆ insert A (insert B (insert B' Δ₀)) :=
      Finset.insert_subset_insert _
        (Finset.insert_subset_insert _ (Finset.subset_insert B' _))
    let ⟨r, hr⟩ := cutAdmRightOrR A B (insert A' Γ₀) (insert B' Δ₀)
      (d₁'.mono (Finset.subset_insert _ _) wkR_imp)
      ih d' hcf' hant'
      (Finset.insert_subset_insert _ hsuc)
    ⟨.impR A' B' hAB₀ r, hr⟩
  | .weakL A' d', hcf' =>
    cutAdmRightOrR A B Γ₀ Δ₀ d₁' ih d' hcf'
      (fun x hx => hant (Finset.mem_insert_of_mem hx)) hsuc
  | .weakR A' d', hcf' =>
    cutAdmRightOrR A B Γ₀ Δ₀ d₁' ih d' hcf' hant ((Finset.subset_insert A' _).trans hsuc)
  | .cut _ _ _, hcf' => absurd hcf' id

/-- Principal impR/impL case: structural recursion on `d₂` given
`d₁' : insert A Γ₀ ⊢ₛ insert B Δ₀` from the impR side. -/
noncomputable def cutAdmRightImpR
    (A B : Proposition Atom) (Γ₀ Δ₀ : Finset (Proposition Atom))
    (d₁' : CutFreeLKProof (insert A Γ₀ ⊢ₛ insert B Δ₀))
    (ih : CutIH (Proposition.imp A B))
    {Γ Δ : Finset (Proposition Atom)} (d₂ : LKProof (Γ ⊢ₛ Δ)) (hcf₂ : CutFree d₂)
    (hant : Γ ⊆ insert (A → B) Γ₀) (hsuc : Δ ⊆ Δ₀) :
    CutFreeLKProof (Γ₀ ⊢ₛ Δ₀) :=
  match d₂, hcf₂ with
  | .ax phi _ _ hphiL hphiD, _ =>
    if heq : phi = Proposition.imp A B then
      if h : phi ∈ Γ₀ then
        ⟨.ax phi Γ₀ Δ₀ h (hsuc hphiD), trivial⟩
      else
        have hmem_left : phi ∈ insert (A → B) Γ₀ := hant hphiL
        have h_eq_cut : phi = (A → B) := by
          rcases Finset.mem_insert.mp hmem_left with h_eq | h_in
          · exact h_eq
          · exact absurd h_in h
        have hmem : (A → B) ∈ Δ₀ := h_eq_cut ▸ (hsuc hphiD)
        ⟨.impR A B hmem d₁'.1, d₁'.2⟩
    else
      ⟨.ax phi Γ₀ Δ₀ (mem_of_ne_head (hant hphiL) heq) (hsuc hphiD), trivial⟩
  | .botL _ _ hbot, _ =>
    ⟨.botL Γ₀ Δ₀ (mem_of_ne_head (hant hbot) nofun), by unfold CutFree; trivial⟩
  | .andL A' B' hAB d', hcf' =>
    let hAB₀ : (A' ∧ B') ∈ Γ₀ := mem_of_ne_head (hant hAB) nofun
    let wk2 : Γ₀ ⊆ insert A' (insert B' Γ₀) :=
      (Finset.subset_insert B' Γ₀).trans (Finset.subset_insert A' _)
    let hant' : insert A' (insert B' Γ) ⊆ insert (A → B) (insert A' (insert B' Γ₀)) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self A' _))
        (Finset.insert_subset
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self B' _)))
          (fun x hx => (Finset.insert_subset_insert (Proposition.imp A B) wk2) (hant hx)))
    let ⟨r, hr⟩ := cutAdmRightImpR A B (insert A' (insert B' Γ₀)) Δ₀
      (d₁'.mono (Finset.insert_subset_insert _ wk2) (Finset.Subset.refl _))
      ih d' hcf' hant' hsuc
    ⟨.andL A' B' hAB₀ r, hr⟩
  | .andR A' B' hAB d₂a d₂b, hcf_ab =>
    let hAB₀ : (A' ∧ B') ∈ Δ₀ := hsuc hAB
    let ⟨ra, hra⟩ := cutAdmRightImpR A B Γ₀ (insert A' Δ₀)
      (d₁'.mono (Finset.Subset.refl _) (Finset.insert_subset_insert _ (Finset.subset_insert A' _)))
      ih d₂a hcf_ab.1 hant
      (Finset.insert_subset_insert _ hsuc)
    let ⟨rb, hrb⟩ := cutAdmRightImpR A B Γ₀ (insert B' Δ₀)
      (d₁'.mono (Finset.Subset.refl _) (Finset.insert_subset_insert _ (Finset.subset_insert B' _)))
      ih d₂b hcf_ab.2 hant
      (Finset.insert_subset_insert _ hsuc)
    ⟨.andR A' B' hAB₀ ra rb, And.intro hra hrb⟩
  | .orL A' B' hAB d₂a d₂b, hcf_ab =>
    let hAB₀ : (A' ∨ B') ∈ Γ₀ := mem_of_ne_head (hant hAB) nofun
    let hant_a : insert A' Γ ⊆ insert (A → B) (insert A' Γ₀) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self A' _))
        (fun x hx => (Finset.insert_subset_insert _ (Finset.subset_insert A' _)) (hant hx))
    let hant_b : insert B' Γ ⊆ insert (A → B) (insert B' Γ₀) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self B' _))
        (fun x hx => (Finset.insert_subset_insert _ (Finset.subset_insert B' _)) (hant hx))
    let ⟨ra, hra⟩ := cutAdmRightImpR A B (insert A' Γ₀) Δ₀
      (d₁'.mono (Finset.insert_subset_insert _ (Finset.subset_insert A' _)) (Finset.Subset.refl _))
      ih d₂a hcf_ab.1 hant_a hsuc
    let ⟨rb, hrb⟩ := cutAdmRightImpR A B (insert B' Γ₀) Δ₀
      (d₁'.mono (Finset.insert_subset_insert _ (Finset.subset_insert B' _)) (Finset.Subset.refl _))
      ih d₂b hcf_ab.2 hant_b hsuc
    ⟨.orL A' B' hAB₀ ra rb, And.intro hra hrb⟩
  | .orR A' B' hAB d', hcf' =>
    let hAB₀ : (A' ∨ B') ∈ Δ₀ := hsuc hAB
    let wkR_or : insert B Δ₀ ⊆ insert B (insert A' (insert B' Δ₀)) :=
      Finset.insert_subset_insert _
        ((Finset.subset_insert B' Δ₀).trans (Finset.subset_insert A' _))
    let ⟨r, hr⟩ := cutAdmRightImpR A B Γ₀ (insert A' (insert B' Δ₀))
      (d₁'.mono (Finset.Subset.refl _) wkR_or)
      ih d' hcf' hant
      (Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hsuc))
    ⟨.orR A' B' hAB₀ r, hr⟩
  | .impR A' B' hAB d', hcf' =>
    let hAB₀ : (A' → B') ∈ Δ₀ := hsuc hAB
    let hant' : insert A' Γ ⊆ insert (A → B) (insert A' Γ₀) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self A' _))
        (fun x hx => (Finset.insert_subset_insert _ (Finset.subset_insert A' _)) (hant hx))
    let wkR_impR : insert B Δ₀ ⊆ insert B (insert B' Δ₀) :=
      Finset.insert_subset_insert _ (Finset.subset_insert B' _)
    let ⟨r, hr⟩ := cutAdmRightImpR A B (insert A' Γ₀) (insert B' Δ₀)
      (d₁'.mono (Finset.insert_subset_insert _ (Finset.subset_insert A' _)) wkR_impR)
      ih d' hcf' hant'
      (Finset.insert_subset_insert _ hsuc)
    ⟨.impR A' B' hAB₀ r, hr⟩
  | .impL A' B' hAB d₂a d₂b, hcf_ab =>
    if h1 : A' = A ∧ B' = B then
      -- PRINCIPAL CASE: d₂ = impL A B, C = A → B.
      -- Recurse on d₂a, d₂b (structurally smaller), then use ih A, ih B.
      have hA : sizeOf A < sizeOf (Proposition.imp A B) := by
        rw [Proposition.imp.sizeOf_spec]; omega
      have hB : sizeOf B < sizeOf (Proposition.imp A B) := by
        rw [Proposition.imp.sizeOf_spec]; omega
      let wk_b : Γ₀ ⊆ insert B Γ₀ := Finset.subset_insert B _
      let hsuc_a : insert A' Δ ⊆ insert A Δ₀ :=
        Finset.insert_subset
          (Finset.mem_insert.mpr (Or.inl h1.1))
          (fun x hx => Finset.mem_insert_of_mem (hsuc hx))
      let d₂a_result := cutAdmRightImpR A B Γ₀ (insert A Δ₀)
        (d₁'.mono (Finset.Subset.refl _)
          (Finset.insert_subset_insert _ (Finset.subset_insert A _)))
        ih d₂a hcf_ab.1 hant hsuc_a
      let hant_b : insert B' Γ ⊆ insert (A → B) (insert B Γ₀) :=
        Finset.insert_subset
          (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl h1.2)))
          (fun x hx => (Finset.insert_subset_insert (A → B) wk_b) (hant hx))
      let d₂b' := cutAdmRightImpR A B (insert B Γ₀) Δ₀
        (d₁'.mono (Finset.insert_subset_insert _ wk_b) (Finset.Subset.refl _))
        ih d₂b hcf_ab.2 hant_b hsuc
      let d₂a_w := d₂a_result.mono (Finset.Subset.refl _)
        (Finset.insert_subset_insert _ (Finset.subset_insert B _))
      let r₁ := ih A hA Γ₀ (insert B Δ₀) d₂a_w d₁'
      ih B hB Γ₀ Δ₀ r₁ d₂b'
    else
      let hAB₀ : (A' → B') ∈ Γ₀ := mem_of_ne_head (hant hAB)
        (by intro heq; injection heq with h1a h1b; exact h1 ⟨h1a, h1b⟩)
      let ⟨ra, hra⟩ := cutAdmRightImpR A B Γ₀ (insert A' Δ₀)
        (d₁'.monoR (Finset.insert_subset_insert _ (Finset.subset_insert A' _)))
        ih d₂a hcf_ab.1 hant
        (Finset.insert_subset_insert _ hsuc)
      let hant_b : insert B' Γ ⊆ insert (A → B) (insert B' Γ₀) :=
        insert_subset_swap hant
      let ⟨rb, hrb⟩ := cutAdmRightImpR A B (insert B' Γ₀) Δ₀
        (d₁'.monoL (Finset.insert_subset_insert _ (Finset.subset_insert B' _)))
        ih d₂b hcf_ab.2 hant_b hsuc
      ⟨.impL A' B' hAB₀ ra rb, And.intro hra hrb⟩
  | .weakL A' d', hcf' =>
    cutAdmRightImpR A B Γ₀ Δ₀ d₁' ih d' hcf'
      (fun x hx => hant (Finset.mem_insert_of_mem hx)) hsuc
  | .weakR A' d', hcf' =>
    cutAdmRightImpR A B Γ₀ Δ₀ d₁' ih d' hcf' hant ((Finset.subset_insert A' _).trans hsuc)
  | .cut _ _ _, hcf' => absurd hcf' id

/-! ### Mutual recursion block

Only `cutAdmRight` and `cutAdmLeft` are mutually recursive. The three principal-case
helpers above are self-recursive and called one-way by `cutAdmLeft`. -/

set_option maxHeartbeats 210000 in
-- The mutual block elaboration cost exceeds the default 200000 heartbeats because
-- Lean re-checks all mutual definitions together; individual definitions are fast.
mutual

/-- General right-side helper: structural recursion on `d₂` for non-principal cases in d₁.
When C appears as ⊥ in d₂, uses cutAdmLeft (mutual recursion). -/
noncomputable def cutAdmRight
    (C : Proposition Atom) (Γ₀ Δ₀ : Finset (Proposition Atom))
    (d₁ : CutFreeLKProof (Γ₀ ⊢ₛ insert C Δ₀)) (ih : CutIH C)
    {Γ Δ : Finset (Proposition Atom)} (d₂ : LKProof (Γ ⊢ₛ Δ)) (hcf₂ : CutFree d₂)
    (hant : Γ ⊆ insert C Γ₀) (hsuc : Δ ⊆ Δ₀) :
    CutFreeLKProof (Γ₀ ⊢ₛ Δ₀) :=
  match d₂, hcf₂ with
  | .ax phi _ _ hphiL hphiD, _ =>
    if heq : phi = C then
      d₁.mono (Finset.Subset.refl _)
              (Finset.insert_subset (heq ▸ hsuc hphiD) (Finset.Subset.refl _))
    else
      ⟨.ax phi Γ₀ Δ₀ (mem_of_ne_head (hant hphiL) heq) (hsuc hphiD), trivial⟩
  | .botL _ _ hbot, _ =>
    if heq : (⊥ : Proposition Atom) = C then
      have hbot₀ : (⊥ : Proposition Atom) ∈ insert C Γ₀ := heq ▸ Finset.mem_insert_self _ _
      cutAdmLeft C Γ₀ Δ₀
        ⟨.botL (insert C Γ₀) Δ₀ hbot₀, by unfold CutFree; trivial⟩
        ih d₁.1 d₁.2 (Finset.Subset.refl _) (Finset.Subset.refl _)
    else
      ⟨.botL Γ₀ Δ₀ (mem_of_ne_head (hant hbot) heq), by unfold CutFree; trivial⟩
  | .andL A B hAB d', hcf' =>
    let wk2 : Γ₀ ⊆ insert A (insert B Γ₀) := subset_insert₂ A B Γ₀
    let hant' : insert A (insert B Γ) ⊆ insert C (insert A (insert B Γ₀)) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self A _))
        (Finset.insert_subset
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self B _)))
          (hant.trans (Finset.insert_subset_insert C wk2)))
    let ⟨r, hr⟩ := cutAdmRight C (insert A (insert B Γ₀)) Δ₀
      (d₁.monoL (subset_insert₂ A B Γ₀))
      ih d' hcf' hant' hsuc
    if heq : Proposition.and A B = C then
      let wk_ab : insert A (insert B Γ₀) ⊆ insert A (insert B (insert (A ∧ B) Γ₀)) :=
        Finset.insert_subset_insert _
          (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
      let d₂_new : CutFreeLKProof (insert (A ∧ B) Γ₀ ⊢ₛ Δ₀) :=
        ⟨.andL A B (Finset.mem_insert_self _ _)
          (r.mono wk_ab (Finset.Subset.refl _)), CutFree.mono r wk_ab (Finset.Subset.refl _) hr⟩
      cutAdmLeft C Γ₀ Δ₀ (heq ▸ d₂_new) ih d₁.1 d₁.2
        (Finset.Subset.refl _) (Finset.Subset.refl _)
    else
      ⟨.andL A B (mem_of_ne_head (hant hAB) heq) r, hr⟩
  | .andR A B hAB d₂a d₂b, hcf_ab =>
    let hAB₀ : (A ∧ B) ∈ Δ₀ := hsuc hAB
    let ⟨ra, hra⟩ := cutAdmRight C Γ₀ (insert A Δ₀)
      (d₁.monoR (Finset.insert_subset_insert C (Finset.subset_insert A _)))
      ih d₂a hcf_ab.1 hant
      (Finset.insert_subset_insert _ hsuc)
    let ⟨rb, hrb⟩ := cutAdmRight C Γ₀ (insert B Δ₀)
      (d₁.monoR (Finset.insert_subset_insert C (Finset.subset_insert B _)))
      ih d₂b hcf_ab.2 hant
      (Finset.insert_subset_insert _ hsuc)
    ⟨.andR A B hAB₀ ra rb, And.intro hra hrb⟩
  | .orL A B hAB d₂a d₂b, hcf_ab =>
    let hant_a : insert A Γ ⊆ insert C (insert A Γ₀) := insert_subset_swap hant
    let hant_b : insert B Γ ⊆ insert C (insert B Γ₀) := insert_subset_swap hant
    let ⟨ra, hra⟩ := cutAdmRight C (insert A Γ₀) Δ₀
      (d₁.monoL (Finset.subset_insert A _))
      ih d₂a hcf_ab.1 hant_a hsuc
    let ⟨rb, hrb⟩ := cutAdmRight C (insert B Γ₀) Δ₀
      (d₁.monoL (Finset.subset_insert B _))
      ih d₂b hcf_ab.2 hant_b hsuc
    if heq : Proposition.or A B = C then
      let wk_a := Finset.insert_subset_insert A (Finset.subset_insert (A ∨ B) Γ₀)
      let wk_b := Finset.insert_subset_insert B (Finset.subset_insert (A ∨ B) Γ₀)
      let d₂_new : CutFreeLKProof (insert (A ∨ B) Γ₀ ⊢ₛ Δ₀) :=
        ⟨.orL A B (Finset.mem_insert_self _ _)
          (ra.mono wk_a (Finset.Subset.refl _))
          (rb.mono wk_b (Finset.Subset.refl _)),
         And.intro (CutFree.mono ra wk_a (Finset.Subset.refl _) hra)
                   (CutFree.mono rb wk_b (Finset.Subset.refl _) hrb)⟩
      cutAdmLeft C Γ₀ Δ₀ (heq ▸ d₂_new) ih d₁.1 d₁.2
        (Finset.Subset.refl _) (Finset.Subset.refl _)
    else
      ⟨.orL A B (mem_of_ne_head (hant hAB) heq) ra rb, And.intro hra hrb⟩
  | .orR A B hAB d', hcf' =>
    let hAB₀ : (A ∨ B) ∈ Δ₀ := hsuc hAB
    let ⟨r, hr⟩ := cutAdmRight C Γ₀ (insert A (insert B Δ₀))
      (d₁.monoR (Finset.insert_subset_insert C (subset_insert₂ A B Δ₀)))
      ih d' hcf' hant
      (Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hsuc))
    ⟨.orR A B hAB₀ r, hr⟩
  | .impL A B hAB d₂a d₂b, hcf_ab =>
    let hant_b : insert B Γ ⊆ insert C (insert B Γ₀) := insert_subset_swap hant
    let ⟨ra, hra⟩ := cutAdmRight C Γ₀ (insert A Δ₀)
      (d₁.monoR (Finset.insert_subset_insert C (Finset.subset_insert A _)))
      ih d₂a hcf_ab.1 hant
      (Finset.insert_subset_insert _ hsuc)
    let ⟨rb, hrb⟩ := cutAdmRight C (insert B Γ₀) Δ₀
      (d₁.monoL (Finset.subset_insert B _))
      ih d₂b hcf_ab.2 hant_b hsuc
    if heq : Proposition.imp A B = C then
      let wk_ra := Finset.subset_insert (Proposition.imp A B) Γ₀
      let wk_rb := Finset.insert_subset_insert B (Finset.subset_insert (Proposition.imp A B) Γ₀)
      let d₂_new : CutFreeLKProof (insert (A → B) Γ₀ ⊢ₛ Δ₀) :=
        ⟨.impL A B (Finset.mem_insert_self _ _)
          (ra.mono wk_ra (Finset.Subset.refl _))
          (rb.mono wk_rb (Finset.Subset.refl _)),
         And.intro (CutFree.mono ra wk_ra (Finset.Subset.refl _) hra)
                   (CutFree.mono rb wk_rb (Finset.Subset.refl _) hrb)⟩
      cutAdmLeft C Γ₀ Δ₀ (heq ▸ d₂_new) ih d₁.1 d₁.2
        (Finset.Subset.refl _) (Finset.Subset.refl _)
    else
      ⟨.impL A B (mem_of_ne_head (hant hAB) heq) ra rb, And.intro hra hrb⟩
  | .impR A B hAB d', hcf' =>
    let hAB₀ : (A → B) ∈ Δ₀ := hsuc hAB
    let hant' : insert A Γ ⊆ insert C (insert A Γ₀) := insert_subset_swap hant
    let ⟨r, hr⟩ := cutAdmRight C (insert A Γ₀) (insert B Δ₀)
      (d₁.mono (Finset.subset_insert A _)
        (Finset.insert_subset_insert C (Finset.subset_insert B _)))
      ih d' hcf' hant'
      (Finset.insert_subset_insert _ hsuc)
    ⟨.impR A B hAB₀ r, hr⟩
  | .weakL A d', hcf' =>
    cutAdmRight C Γ₀ Δ₀ d₁ ih d' hcf' ((Finset.subset_insert A _).trans hant) hsuc
  | .weakR A d', hcf' =>
    cutAdmRight C Γ₀ Δ₀ d₁ ih d' hcf' hant ((Finset.subset_insert A _).trans hsuc)
  | .cut _ _ _, hcf' => absurd hcf' id

/-- Left-side structural recursion on `d₁`: eliminate cut formula C from the left proof.
Non-principal cases push the cut deeper into sub-proofs of d₁.
Principal cases (when d₁ introduces C on the right) first clean up C from d₁'s sub-proof
succedents, then delegate to the appropriate right helper. -/
noncomputable def cutAdmLeft
    (C : Proposition Atom) (Γ₀ Δ₀ : Finset (Proposition Atom))
    (d₂ : CutFreeLKProof (insert C Γ₀ ⊢ₛ Δ₀)) (ih : CutIH C)
    {Γ Δ : Finset (Proposition Atom)} (d₁ : LKProof (Γ ⊢ₛ Δ)) (hcf₁ : CutFree d₁)
    (hant : Γ ⊆ Γ₀) (hsuc : Δ ⊆ insert C Δ₀) :
    CutFreeLKProof (Γ₀ ⊢ₛ Δ₀) :=
  match d₁, hcf₁ with
  | .ax phi _ _ hphiL hphiD, _ =>
    if heq : phi = C then
      d₂.mono (Finset.insert_subset (heq ▸ hant hphiL) (Finset.Subset.refl _))
              (Finset.Subset.refl _)
    else
      ⟨.ax phi Γ₀ Δ₀ (hant hphiL) (mem_of_ne_head (hsuc hphiD) heq), trivial⟩
  | .botL _ _ hbot, _ =>
    ⟨.botL Γ₀ Δ₀ (hant hbot), trivial⟩
  | .andL A B hAB d', hcf' =>
    let d₂' := d₂.monoL (Finset.insert_subset_insert C (subset_insert₂ A B Γ₀))
    let hant' : insert A (insert B Γ) ⊆ insert A (insert B Γ₀) :=
      Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hant)
    let ⟨r, hr⟩ := cutAdmLeft C (insert A (insert B Γ₀)) Δ₀ d₂' ih d' hcf' hant' hsuc
    ⟨.andL A B (hant hAB) r, hr⟩
  | .andR A B hAB d₁a d₁b, hcf_ab =>
    if heq : Proposition.and A B = C then
      -- PRINCIPAL CASE: C = A ∧ B. Clean up C from d₁a and d₁b's succedents.
      let d₁a_clean := cutAdmLeft C Γ₀ (insert A Δ₀)
        (d₂.monoR (Finset.subset_insert A _))
        ih d₁a hcf_ab.1 hant (insert_subset_swap hsuc)
      let d₁b_clean := cutAdmLeft C Γ₀ (insert B Δ₀)
        (d₂.monoR (Finset.subset_insert B _))
        ih d₁b hcf_ab.2 hant (insert_subset_swap hsuc)
      cutAdmRightAndR A B Γ₀ Δ₀ d₁a_clean d₁b_clean
        (heq ▸ ih)
        d₂.1 d₂.2
        (fun x hx => (Proposition.and_def A B).symm.trans heq ▸ hx)
        (Finset.Subset.refl _)
    else
      -- Non-principal: A∧B ≠ C so A∧B ∈ Δ₀.
      have hAB₀ : (A ∧ B) ∈ Δ₀ := mem_of_ne_head (hsuc hAB) heq
      let ⟨ra, hra⟩ := cutAdmLeft C Γ₀ (insert A Δ₀)
        (d₂.monoR (Finset.subset_insert A _)) ih d₁a hcf_ab.1 hant (insert_subset_swap hsuc)
      let ⟨rb, hrb⟩ := cutAdmLeft C Γ₀ (insert B Δ₀)
        (d₂.monoR (Finset.subset_insert B _)) ih d₁b hcf_ab.2 hant (insert_subset_swap hsuc)
      ⟨.andR A B hAB₀ ra rb, And.intro hra hrb⟩
  | .orL A B hAB d₁a d₁b, hcf_ab =>
    let d₂_a := d₂.monoL (Finset.insert_subset_insert C (Finset.subset_insert A _))
    let d₂_b := d₂.monoL (Finset.insert_subset_insert C (Finset.subset_insert B _))
    let ⟨ra, hra⟩ := cutAdmLeft C (insert A Γ₀) Δ₀ d₂_a ih d₁a hcf_ab.1
      (Finset.insert_subset_insert _ hant) hsuc
    let ⟨rb, hrb⟩ := cutAdmLeft C (insert B Γ₀) Δ₀ d₂_b ih d₁b hcf_ab.2
      (Finset.insert_subset_insert _ hant) hsuc
    ⟨.orL A B (hant hAB) ra rb, And.intro hra hrb⟩
  | .orR A B hAB d', hcf' =>
    let hR' : insert A (insert B Δ) ⊆ insert C (insert A (insert B Δ₀)) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self A _))
        (Finset.insert_subset
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self B _)))
          (hsuc.trans (Finset.insert_subset_insert C (subset_insert₂ A B Δ₀))))
    if heq : Proposition.or A B = C then
      -- PRINCIPAL CASE: C = A ∨ B. Clean up C from d''s succedent.
      let d₁'_clean := cutAdmLeft C Γ₀ (insert A (insert B Δ₀))
        (d₂.monoR (subset_insert₂ A B Δ₀))
        ih d' hcf' hant hR'
      cutAdmRightOrR A B Γ₀ Δ₀ d₁'_clean
        (heq ▸ ih)
        d₂.1 d₂.2
        (fun x hx => (Proposition.or_def A B).symm.trans heq ▸ hx)
        (Finset.Subset.refl _)
    else
      -- Non-principal: A∨B ≠ C so A∨B ∈ Δ₀.
      have hAB₀ : (A ∨ B) ∈ Δ₀ := mem_of_ne_head (hsuc hAB) heq
      let ⟨r, hr⟩ := cutAdmLeft C Γ₀ (insert A (insert B Δ₀))
        (d₂.monoR (subset_insert₂ A B Δ₀)) ih d' hcf' hant hR'
      ⟨.orR A B hAB₀ r, hr⟩
  | .impL A B hAB d₁a d₁b, hcf_ab =>
    let ⟨ra, hra⟩ := cutAdmLeft C Γ₀ (insert A Δ₀)
      (d₂.monoR (Finset.subset_insert A _)) ih d₁a hcf_ab.1 hant (insert_subset_swap hsuc)
    let ⟨rb, hrb⟩ := cutAdmLeft C (insert B Γ₀) Δ₀
      (d₂.monoL (Finset.insert_subset_insert C (Finset.subset_insert B _)))
      ih d₁b hcf_ab.2 (Finset.insert_subset_insert _ hant) hsuc
    ⟨.impL A B (hant hAB) ra rb, And.intro hra hrb⟩
  | .impR A B hAB d', hcf' =>
    let hR' : insert B Δ ⊆ insert C (insert B Δ₀) := insert_subset_swap hsuc
    let d₂' := d₂.mono (Finset.insert_subset_insert C (Finset.subset_insert A _))
                       (Finset.subset_insert B _)
    if heq : Proposition.imp A B = C then
      -- PRINCIPAL CASE: C = A → B. Clean up C from d''s succedent.
      let d₁'_clean := cutAdmLeft C (insert A Γ₀) (insert B Δ₀) d₂'
        ih d' hcf' (Finset.insert_subset_insert _ hant) hR'
      cutAdmRightImpR A B Γ₀ Δ₀ d₁'_clean
        (heq ▸ ih)
        d₂.1 d₂.2
        (fun x hx => (Proposition.imp_def A B).symm.trans heq ▸ hx)
        (Finset.Subset.refl _)
    else
      -- Non-principal: A→B ≠ C so A→B ∈ Δ₀.
      have hAB₀ : (A → B) ∈ Δ₀ := mem_of_ne_head (hsuc hAB) heq
      let ⟨r, hr⟩ := cutAdmLeft C (insert A Γ₀) (insert B Δ₀) d₂'
        ih d' hcf' (Finset.insert_subset_insert _ hant) hR'
      ⟨.impR A B hAB₀ r, hr⟩
  | .weakL A d', hcf' =>
    cutAdmLeft C Γ₀ Δ₀ d₂ ih d' hcf' ((Finset.subset_insert A _).trans hant) hsuc
  | .weakR A d', hcf' =>
    cutAdmLeft C Γ₀ Δ₀ d₂ ih d' hcf' hant ((Finset.subset_insert A _).trans hsuc)
  | .cut _ _ _, hcf' => absurd hcf' id

end -- mutual

/-! ## Top-Level Cut Admissibility and Cut Elimination -/

/-- Cut admissibility: a cut on formula C can be eliminated from cut-free proofs.
Defined by well-founded recursion on `sizeOf C`.
Following [TroelstraSchwichtenberg2000] Theorem 4.1.5. -/
noncomputable def cutAdmissibility
    (C : Proposition Atom) (Γ Δ : Finset (Proposition Atom))
    (d₁ : CutFreeLKProof (Γ ⊢ₛ insert C Δ))
    (d₂ : CutFreeLKProof (insert C Γ ⊢ₛ Δ)) :
    CutFreeLKProof (Γ ⊢ₛ Δ) :=
  cutAdmLeft C Γ Δ d₂
    (fun B _ Γ' Δ' d₁' d₂' => cutAdmissibility B Γ' Δ' d₁' d₂')
    d₁.1 d₁.2 (Finset.Subset.refl _) (Finset.Subset.refl _)
termination_by sizeOf C

/-! ## Cut Elimination -/

/-- Every LK proof can be transformed into a cut-free LK proof (Gentzen's Hauptsatz).
By structural induction; cut steps use `cutAdmissibility` on their sub-proofs. -/
theorem LKProof.cutElim {seq : LKSequent Atom} (d : LKProof seq) :
    Nonempty (CutFreeLKProof seq) :=
  match d with
  | .ax phi Γ Δ hL hR => ⟨⟨.ax phi Γ Δ hL hR, trivial⟩⟩
  | .botL Γ Δ hbot => ⟨⟨.botL Γ Δ hbot, trivial⟩⟩
  | .andL A B hAB d' =>
    let ⟨⟨r, hr⟩⟩ := d'.cutElim
    ⟨⟨.andL A B hAB r, hr⟩⟩
  | .andR A B hAB d₁ d₂ =>
    let ⟨⟨r₁, hr₁⟩⟩ := d₁.cutElim
    let ⟨⟨r₂, hr₂⟩⟩ := d₂.cutElim
    ⟨⟨.andR A B hAB r₁ r₂, ⟨hr₁, hr₂⟩⟩⟩
  | .orL A B hAB d₁ d₂ =>
    let ⟨⟨r₁, hr₁⟩⟩ := d₁.cutElim
    let ⟨⟨r₂, hr₂⟩⟩ := d₂.cutElim
    ⟨⟨.orL A B hAB r₁ r₂, ⟨hr₁, hr₂⟩⟩⟩
  | .orR A B hAB d' =>
    let ⟨⟨r, hr⟩⟩ := d'.cutElim
    ⟨⟨.orR A B hAB r, hr⟩⟩
  | .impL A B hAB d₁ d₂ =>
    let ⟨⟨r₁, hr₁⟩⟩ := d₁.cutElim
    let ⟨⟨r₂, hr₂⟩⟩ := d₂.cutElim
    ⟨⟨.impL A B hAB r₁ r₂, ⟨hr₁, hr₂⟩⟩⟩
  | .impR A B hAB d' =>
    let ⟨⟨r, hr⟩⟩ := d'.cutElim
    ⟨⟨.impR A B hAB r, hr⟩⟩
  | .weakL A d' =>
    let ⟨⟨r, hr⟩⟩ := d'.cutElim
    ⟨CutFreeLKProof.mono (Finset.subset_insert A _) (Finset.Subset.refl _) ⟨r, hr⟩⟩
  | .weakR A d' =>
    let ⟨⟨r, hr⟩⟩ := d'.cutElim
    ⟨CutFreeLKProof.mono (Finset.Subset.refl _) (Finset.subset_insert A _) ⟨r, hr⟩⟩
  | .cut A d₁ d₂ =>
    let ⟨d₁'⟩ := d₁.cutElim
    let ⟨d₂'⟩ := d₂.cutElim
    ⟨cutAdmissibility A _ _ d₁' d₂'⟩

end Cslib.Logic.PL
