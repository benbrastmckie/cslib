/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.SequentCalculus.LJ.Basic

/-! # Cut Elimination for LJ (Hauptsatz)

We prove that the cut rule is admissible in LJ: every LJ derivation can be transformed
into a cut-free derivation of the same sequent.

## Main Results

- `LJCutFree.mono`: Cut-freeness is preserved under context weakening (`LJProof.mono`).
- `CutFreeLJProof.mono`: Cut-free proofs are closed under context weakening.
- `ljCutAdmissibility`: From cut-free proofs of `Γ ⊢ A` and `insert A Γ ⊢ C`,
  we can derive a cut-free proof of `Γ ⊢ C`.
- `LJProof.cutElim`: Every LJ-derivable sequent has a cut-free proof.

## Proof Strategy

The key theorem `ljCutAdmissibility` takes **cut-free** inputs and produces a **cut-free**
output. It proceeds by well-founded induction on `sizeOf A` (formula complexity), with
structural recursion on proof trees for the fixed-formula case. The atom and `⊥` base cases
are handled by case analysis on `d₁`. The compound formula cases (`and`, `or`, `imp`) handle
non-principal subcases structurally (decreasing proof size), and handle the principal case
(where `A` is introduced on both sides) using the induction hypothesis for subformulas
(decreasing formula size).

The proof is decomposed following the LK cut elimination architecture:
1. Three standalone self-recursive helpers for principal connective cases
2. A mutual recursion block (`ljCutAdmRight` / `ljCutAdmLeft`)
3. A top-level WF wrapper (`ljCutAdmissibility`)

## References

* [A. S. Troelstra, H. Schwichtenberg, *Basic Proof Theory*][TroelstraSchwichtenberg2000],
  Ch. 4, Theorem 4.1.1
* [S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001], Ch. 2, Thm 2.4.3
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition

variable {Atom : Type u} [DecidableEq Atom]

/-! ## Cut-Freeness Preservation Under Weakening -/

/-- Cut-freeness is preserved under `SeqProof.mono`, generic over the theory `T`. This
inducts on the `SeqProof T` structure itself, which does not depend on which `T` is fixed
throughout, so the proof carries over unchanged from the `LJProof`-only version beyond the
added `{T}` binder. -/
lemma SeqProof.CutFree.mono {T : Theory Atom} {seq : @Sequent Atom} {Γ' : Ctx Atom}
    (hL : seq.1 ⊆ Γ') (d : SeqProof T seq) (hcf : SeqProof.CutFree d) :
    SeqProof.CutFree (d.mono hL) := by
  induction d generalizing Γ' with
  | ax _ _ _ => simp [SeqProof.mono, SeqProof.CutFree]
  | botL _ _ _ => simp [SeqProof.mono, SeqProof.CutFree]
  | andL _ _ _ _ ih =>
    simp only [SeqProof.mono, SeqProof.CutFree] at *; exact ih _ hcf
  | andR _ _ _ _ ih₁ ih₂ =>
    simp only [SeqProof.mono, SeqProof.CutFree] at *
    exact ⟨ih₁ _ hcf.1, ih₂ _ hcf.2⟩
  | orL _ _ _ _ _ ih₁ ih₂ =>
    simp only [SeqProof.mono, SeqProof.CutFree] at *
    exact ⟨ih₁ _ hcf.1, ih₂ _ hcf.2⟩
  | orR1 _ _ _ ih =>
    simp only [SeqProof.mono, SeqProof.CutFree] at *; exact ih _ hcf
  | orR2 _ _ _ ih =>
    simp only [SeqProof.mono, SeqProof.CutFree] at *; exact ih _ hcf
  | impL _ _ _ _ _ ih₁ ih₂ =>
    simp only [SeqProof.mono, SeqProof.CutFree] at *
    exact ⟨ih₁ _ hcf.1, ih₂ _ hcf.2⟩
  | impR _ _ _ ih =>
    simp only [SeqProof.mono, SeqProof.CutFree] at *; exact ih _ hcf
  | weakL _ _ ih =>
    simp only [SeqProof.mono, SeqProof.CutFree] at *; exact ih _ hcf
  | cut _ _ _ => exact absurd hcf id

/-- Cut-freeness is preserved under `LJProof.mono`. Re-export of `SeqProof.CutFree.mono` at
`IPL`. -/
lemma LJCutFree.mono {seq : @Sequent Atom} {Γ' : Ctx Atom}
    (hL : seq.1 ⊆ Γ') (d : LJProof seq) (hcf : LJCutFree d) :
    LJCutFree (d.mono hL) :=
  SeqProof.CutFree.mono hL d hcf

/-- Monotonicity for cut-free `SeqProof T` proofs, generic over the theory `T`. -/
def CutFreeSeqProof.mono {T : Theory Atom} {seq : @Sequent Atom} {Γ' : Ctx Atom}
    (hL : seq.1 ⊆ Γ') (d : CutFreeSeqProof T seq) :
    CutFreeSeqProof T (Γ', seq.2) :=
  ⟨d.1.mono hL, SeqProof.CutFree.mono hL d.1 d.2⟩

/-- Monotonicity for cut-free LJ proofs. Re-export of `CutFreeSeqProof.mono` at `IPL`. -/
@[reducible] def CutFreeLJProof.mono {seq : @Sequent Atom} {Γ' : Ctx Atom}
    (hL : seq.1 ⊆ Γ') (d : CutFreeLJProof seq) :
    CutFreeLJProof (Γ', seq.2) :=
  CutFreeSeqProof.mono hL d

/-! ## Cut Admissibility

### Helper type alias -/

/-- The induction hypothesis type for subformula induction in cut admissibility, generic over
the theory `T`. For each formula `B` strictly smaller than `A`, we can eliminate a cut on `B`
from cut-free proofs. -/
noncomputable abbrev LJCutIH {T : Theory Atom} (A : Proposition Atom) : Type u :=
  ∀ (B : Proposition Atom), sizeOf B < sizeOf A →
    ∀ (Γ : Ctx Atom) (C : Proposition Atom),
    CutFreeSeqProof T (Γ ⊢ B) →
    CutFreeSeqProof T (insert B Γ ⊢ C) →
    CutFreeSeqProof T (Γ ⊢ C)

/-! ### Helper: insert membership branching -/

/-- From `x ∈ insert a s` and `x ≠ a`, extract `x ∈ s`. -/
theorem ljMem_of_ne_head {α : Type*} [DecidableEq α] {a x : α} {s : Finset α}
    (hx : x ∈ insert a s) (hne : x ≠ a) : x ∈ s :=
  Finset.mem_of_mem_insert_of_ne hx hne

/-! ### Standalone self-recursive helpers -/

/-- Principal `andR`/`andL` case: structural recursion on `d₂` given
`d₁p : CutFreeSeqProof T (Γ₀ ⊢ P)` and `d₁q : CutFreeSeqProof T (Γ₀ ⊢ Q)` from the `andR`
side. When `d₂` decomposes `P ∧ Q` via `andL`, the principal case uses `ih` to cut on the
subformulas `P` and `Q`. All other `d₂` cases reconstruct the rule with a recursive call.
Generic over the theory `T`: every rule used (`ax`, `andL`, `andR`, `orL`, `orR1`, `orR2`,
`impL`, `impR`, `weakL`) is in the ungated minimal base, and the `botL` case reconstructs its
stored `[IsIntuitionistic T]` instance via `letI`, following `SeqProof.mono`'s idiom
(`LJ/Basic.lean:184-186`). -/
noncomputable def ljCutAdmPrincipalAndR {T : Theory Atom}
    (P Q : Proposition Atom) (Γ₀ : Ctx Atom)
    (d₁p : CutFreeSeqProof T (Γ₀ ⊢ P))
    (d₁q : CutFreeSeqProof T (Γ₀ ⊢ Q))
    (ih : LJCutIH (T := T) (P ∧ Q))
    {Γ : Ctx Atom} {C : Proposition Atom}
    (d₂ : SeqProof T (Γ ⊢ C)) (hcf₂ : SeqProof.CutFree d₂)
    (hant : Γ ⊆ insert (P ∧ Q) Γ₀) :
    CutFreeSeqProof T (Γ₀ ⊢ C) :=
  match d₂, hcf₂ with
  | .ax phi _ hphiL, _ =>
    if heq : phi = Proposition.and P Q then
      if h : phi ∈ Γ₀ then ⟨.ax phi Γ₀ h, trivial⟩
      else
        (heq ▸ ⟨.andR P Q d₁p.1 d₁q.1, ⟨d₁p.2, d₁q.2⟩⟩ :
          CutFreeSeqProof T (Γ₀ ⊢ phi))
    else ⟨.ax phi Γ₀ (ljMem_of_ne_head (hant hphiL) heq), trivial⟩
  | @SeqProof.botL _ _ _ _ _ inst hbot, _ =>
    letI := inst
    ⟨.botL Γ₀ _ (ljMem_of_ne_head (hant hbot) nofun), trivial⟩
  | .andL A' B' hAB d', hcf' =>
    if h1 : A' = P ∧ B' = Q then
      have hP : sizeOf P < sizeOf (Proposition.and P Q) := by
        rw [Proposition.and.sizeOf_spec]; omega
      have hQ : sizeOf Q < sizeOf (Proposition.and P Q) := by
        rw [Proposition.and.sizeOf_spec]; omega
      let wk : Γ₀ ⊆ insert P (insert Q Γ₀) :=
        (Finset.subset_insert Q Γ₀).trans (Finset.subset_insert P _)
      let hant' : insert A' (insert B' Γ) ⊆ insert (P ∧ Q) (insert P (insert Q Γ₀)) :=
        Finset.insert_subset
          (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl h1.1)))
          (Finset.insert_subset
            (Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl h1.2))))
            (fun x hx => (Finset.insert_subset_insert (P ∧ Q) wk) (hant hx)))
      let d₂' := ljCutAdmPrincipalAndR P Q (insert P (insert Q Γ₀))
        (d₁p.mono wk) (d₁q.mono wk) ih d' hcf' hant'
      let r₁ := ih P hP (insert Q Γ₀) C (d₁p.mono (Finset.subset_insert Q _)) d₂'
      ih Q hQ Γ₀ C d₁q r₁
    else
      let hAB₀ := ljMem_of_ne_head (hant hAB)
        (by intro heq; injection heq with h1a h1b; exact h1 ⟨h1a, h1b⟩)
      let wk2 : Γ₀ ⊆ insert A' (insert B' Γ₀) :=
        (Finset.subset_insert B' Γ₀).trans (Finset.subset_insert A' _)
      let hant' : insert A' (insert B' Γ) ⊆ insert (P ∧ Q) (insert A' (insert B' Γ₀)) :=
        Finset.insert_subset
          (Finset.mem_insert_of_mem (Finset.mem_insert_self A' _))
          (Finset.insert_subset
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self B' _)))
            (fun x hx => (Finset.insert_subset_insert _ wk2) (hant hx)))
      let ⟨r, hr⟩ := ljCutAdmPrincipalAndR P Q (insert A' (insert B' Γ₀))
        (d₁p.mono wk2) (d₁q.mono wk2) ih d' hcf' hant'
      ⟨.andL A' B' hAB₀ r, hr⟩
  | .andR A' B' d₂a d₂b, hcf_ab =>
    let ⟨ra, hra⟩ := ljCutAdmPrincipalAndR P Q Γ₀ d₁p d₁q ih d₂a hcf_ab.1 hant
    let ⟨rb, hrb⟩ := ljCutAdmPrincipalAndR P Q Γ₀ d₁p d₁q ih d₂b hcf_ab.2 hant
    ⟨.andR A' B' ra rb, ⟨hra, hrb⟩⟩
  | .orL A' B' hAB d₂a d₂b, hcf_ab =>
    let hAB₀ := ljMem_of_ne_head (hant hAB) nofun
    let hant_a : insert A' Γ ⊆ insert (P ∧ Q) (insert A' Γ₀) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self A' _))
        (fun x hx => (Finset.insert_subset_insert _ (Finset.subset_insert A' _)) (hant hx))
    let hant_b : insert B' Γ ⊆ insert (P ∧ Q) (insert B' Γ₀) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self B' _))
        (fun x hx => (Finset.insert_subset_insert _ (Finset.subset_insert B' _)) (hant hx))
    let ⟨ra, hra⟩ := ljCutAdmPrincipalAndR P Q (insert A' Γ₀)
      (d₁p.mono (Finset.subset_insert _ _)) (d₁q.mono (Finset.subset_insert _ _))
      ih d₂a hcf_ab.1 hant_a
    let ⟨rb, hrb⟩ := ljCutAdmPrincipalAndR P Q (insert B' Γ₀)
      (d₁p.mono (Finset.subset_insert _ _)) (d₁q.mono (Finset.subset_insert _ _))
      ih d₂b hcf_ab.2 hant_b
    ⟨.orL A' B' hAB₀ ra rb, ⟨hra, hrb⟩⟩
  | .orR1 A' B' d', hcf' =>
    let ⟨r, hr⟩ := ljCutAdmPrincipalAndR P Q Γ₀ d₁p d₁q ih d' hcf' hant
    ⟨.orR1 A' B' r, hr⟩
  | .orR2 A' B' d', hcf' =>
    let ⟨r, hr⟩ := ljCutAdmPrincipalAndR P Q Γ₀ d₁p d₁q ih d' hcf' hant
    ⟨.orR2 A' B' r, hr⟩
  | .impL A' B' hAB d₂a d₂b, hcf_ab =>
    let hAB₀ := ljMem_of_ne_head (hant hAB) nofun
    let hant_b : insert B' Γ ⊆ insert (P ∧ Q) (insert B' Γ₀) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self B' _))
        (fun x hx => (Finset.insert_subset_insert _ (Finset.subset_insert B' _)) (hant hx))
    let ⟨ra, hra⟩ := ljCutAdmPrincipalAndR P Q Γ₀ d₁p d₁q ih d₂a hcf_ab.1 hant
    let ⟨rb, hrb⟩ := ljCutAdmPrincipalAndR P Q (insert B' Γ₀)
      (d₁p.mono (Finset.subset_insert _ _)) (d₁q.mono (Finset.subset_insert _ _))
      ih d₂b hcf_ab.2 hant_b
    ⟨.impL A' B' hAB₀ ra rb, ⟨hra, hrb⟩⟩
  | .impR A' B' d', hcf' =>
    let hant' : insert A' Γ ⊆ insert (P ∧ Q) (insert A' Γ₀) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self A' _))
        (fun x hx => (Finset.insert_subset_insert _ (Finset.subset_insert A' _)) (hant hx))
    let ⟨r, hr⟩ := ljCutAdmPrincipalAndR P Q (insert A' Γ₀)
      (d₁p.mono (Finset.subset_insert _ _)) (d₁q.mono (Finset.subset_insert _ _))
      ih d' hcf' hant'
    ⟨.impR A' B' r, hr⟩
  | .weakL A' d', hcf' =>
    ljCutAdmPrincipalAndR P Q Γ₀ d₁p d₁q ih d' hcf'
      (fun x hx => hant (Finset.mem_insert_of_mem hx))
  | .cut _ _ _, hcf' => absurd hcf' id
termination_by d₂.height
decreasing_by all_goals (simp [SeqProof.height]; try omega)

/-- Principal `orR`/`orL` case: structural recursion on `d₂` given a sub-proof
`d₁sub : CutFreeSeqProof T (Γ₀ ⊢ X)` where `X` is the chosen disjunct. The parameter
`hXeq` certifies `X = P` or `X = Q`, allowing selection of the correct `orL` branch
in the principal case. The `rebuild` function lifts `(Γ' ⊢ X)` to `(Γ' ⊢ P ∨ Q)` for
the `ax` base case. Generic over the theory `T`, following `ljCutAdmPrincipalAndR`'s pattern. -/
noncomputable def ljCutAdmPrincipalOrR {T : Theory Atom}
    (P Q : Proposition Atom) (Γ₀ : Ctx Atom)
    {X : Proposition Atom} (d₁sub : CutFreeSeqProof T (Γ₀ ⊢ X))
    (hXsz : sizeOf X < sizeOf (P ∨ Q))
    (hXeq : X = P ∨ X = Q)
    (rebuild : ∀ {Γ' : Ctx Atom}, CutFreeSeqProof T (Γ' ⊢ X) → CutFreeSeqProof T (Γ' ⊢ P ∨ Q))
    (ih : LJCutIH (T := T) (P ∨ Q))
    {Γ : Ctx Atom} {C : Proposition Atom}
    (d₂ : SeqProof T (Γ ⊢ C)) (hcf₂ : SeqProof.CutFree d₂)
    (hant : Γ ⊆ insert (P ∨ Q) Γ₀) :
    CutFreeSeqProof T (Γ₀ ⊢ C) :=
  match d₂, hcf₂ with
  | .ax phi _ hphiL, _ =>
    if heq : phi = Proposition.or P Q then
      if h : phi ∈ Γ₀ then ⟨.ax phi Γ₀ h, trivial⟩
      else
        (heq ▸ rebuild d₁sub : CutFreeSeqProof T (Γ₀ ⊢ phi))
    else ⟨.ax phi Γ₀ (ljMem_of_ne_head (hant hphiL) heq), trivial⟩
  | @SeqProof.botL _ _ _ _ _ inst hbot, _ =>
    letI := inst
    ⟨.botL Γ₀ _ (ljMem_of_ne_head (hant hbot) nofun), trivial⟩
  | .andL A' B' hAB d', hcf' =>
    let hAB₀ := ljMem_of_ne_head (hant hAB) nofun
    let wk2 : Γ₀ ⊆ insert A' (insert B' Γ₀) :=
      (Finset.subset_insert B' Γ₀).trans (Finset.subset_insert A' _)
    let hant' : insert A' (insert B' Γ) ⊆ insert (P ∨ Q) (insert A' (insert B' Γ₀)) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self A' _))
        (Finset.insert_subset
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self B' _)))
          (fun x hx => (Finset.insert_subset_insert _ wk2) (hant hx)))
    let ⟨r, hr⟩ := ljCutAdmPrincipalOrR P Q (insert A' (insert B' Γ₀))
      (d₁sub.mono wk2) hXsz hXeq rebuild ih d' hcf' hant'
    ⟨.andL A' B' hAB₀ r, hr⟩
  | .andR A' B' d₂a d₂b, hcf_ab =>
    let ⟨ra, hra⟩ := ljCutAdmPrincipalOrR P Q Γ₀ d₁sub hXsz hXeq rebuild
      ih d₂a hcf_ab.1 hant
    let ⟨rb, hrb⟩ := ljCutAdmPrincipalOrR P Q Γ₀ d₁sub hXsz hXeq rebuild
      ih d₂b hcf_ab.2 hant
    ⟨.andR A' B' ra rb, ⟨hra, hrb⟩⟩
  | .orL A' B' hAB d₂a d₂b, hcf_ab =>
    if h1 : A' = P ∧ B' = Q then
      -- PRINCIPAL CASE: d₂ = orL P Q, cut formula = P ∨ Q
      let wk_a : Γ₀ ⊆ insert A' Γ₀ := Finset.subset_insert A' _
      let wk_b : Γ₀ ⊆ insert B' Γ₀ := Finset.subset_insert B' _
      let hant_a : insert A' Γ ⊆ insert (P ∨ Q) (insert A' Γ₀) :=
        Finset.insert_subset
          (Finset.mem_insert_of_mem (Finset.mem_insert_self A' Γ₀))
          (fun x hx => (Finset.insert_subset_insert (P ∨ Q) wk_a) (hant hx))
      let hant_b : insert B' Γ ⊆ insert (P ∨ Q) (insert B' Γ₀) :=
        Finset.insert_subset
          (Finset.mem_insert_of_mem (Finset.mem_insert_self B' Γ₀))
          (fun x hx => (Finset.insert_subset_insert (P ∨ Q) wk_b) (hant hx))
      let d₂a' := ljCutAdmPrincipalOrR P Q (insert A' Γ₀)
        (d₁sub.mono wk_a) hXsz hXeq rebuild ih d₂a hcf_ab.1 hant_a
      let d₂b' := ljCutAdmPrincipalOrR P Q (insert B' Γ₀)
        (d₁sub.mono wk_b) hXsz hXeq rebuild ih d₂b hcf_ab.2 hant_b
      -- Select the branch matching X and cut via ih
      if hxp : X = P then
        have hA' : A' = X := h1.1.symm ▸ hxp.symm
        ih X hXsz Γ₀ C d₁sub (hA' ▸ d₂a')
      else
        have hxq : X = Q := by
          rcases hXeq with h | h
          · exact absurd h hxp
          · exact h
        have hB' : B' = X := h1.2.symm ▸ hxq.symm
        ih X hXsz Γ₀ C d₁sub (hB' ▸ d₂b')
    else
      let hAB₀ := ljMem_of_ne_head (hant hAB)
        (by intro heq; injection heq with h1a h1b; exact h1 ⟨h1a, h1b⟩)
      let hant_a : insert A' Γ ⊆ insert (P ∨ Q) (insert A' Γ₀) :=
        Finset.insert_subset
          (Finset.mem_insert_of_mem (Finset.mem_insert_self A' _))
          (fun x hx => (Finset.insert_subset_insert _ (Finset.subset_insert A' _)) (hant hx))
      let hant_b : insert B' Γ ⊆ insert (P ∨ Q) (insert B' Γ₀) :=
        Finset.insert_subset
          (Finset.mem_insert_of_mem (Finset.mem_insert_self B' _))
          (fun x hx => (Finset.insert_subset_insert _ (Finset.subset_insert B' _)) (hant hx))
      let ⟨ra, hra⟩ := ljCutAdmPrincipalOrR P Q (insert A' Γ₀)
        (d₁sub.mono (Finset.subset_insert _ _)) hXsz hXeq rebuild
        ih d₂a hcf_ab.1 hant_a
      let ⟨rb, hrb⟩ := ljCutAdmPrincipalOrR P Q (insert B' Γ₀)
        (d₁sub.mono (Finset.subset_insert _ _)) hXsz hXeq rebuild
        ih d₂b hcf_ab.2 hant_b
      ⟨.orL A' B' hAB₀ ra rb, ⟨hra, hrb⟩⟩
  | .orR1 A' B' d', hcf' =>
    let ⟨r, hr⟩ := ljCutAdmPrincipalOrR P Q Γ₀ d₁sub hXsz hXeq rebuild
      ih d' hcf' hant
    ⟨.orR1 A' B' r, hr⟩
  | .orR2 A' B' d', hcf' =>
    let ⟨r, hr⟩ := ljCutAdmPrincipalOrR P Q Γ₀ d₁sub hXsz hXeq rebuild
      ih d' hcf' hant
    ⟨.orR2 A' B' r, hr⟩
  | .impL A' B' hAB d₂a d₂b, hcf_ab =>
    let hAB₀ := ljMem_of_ne_head (hant hAB) nofun
    let hant_b : insert B' Γ ⊆ insert (P ∨ Q) (insert B' Γ₀) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self B' _))
        (fun x hx => (Finset.insert_subset_insert _ (Finset.subset_insert B' _)) (hant hx))
    let ⟨ra, hra⟩ := ljCutAdmPrincipalOrR P Q Γ₀ d₁sub hXsz hXeq rebuild
      ih d₂a hcf_ab.1 hant
    let ⟨rb, hrb⟩ := ljCutAdmPrincipalOrR P Q (insert B' Γ₀)
      (d₁sub.mono (Finset.subset_insert _ _)) hXsz hXeq rebuild
      ih d₂b hcf_ab.2 hant_b
    ⟨.impL A' B' hAB₀ ra rb, ⟨hra, hrb⟩⟩
  | .impR A' B' d', hcf' =>
    let hant' : insert A' Γ ⊆ insert (P ∨ Q) (insert A' Γ₀) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self A' _))
        (fun x hx => (Finset.insert_subset_insert _ (Finset.subset_insert A' _)) (hant hx))
    let ⟨r, hr⟩ := ljCutAdmPrincipalOrR P Q (insert A' Γ₀)
      (d₁sub.mono (Finset.subset_insert _ _)) hXsz hXeq rebuild
      ih d' hcf' hant'
    ⟨.impR A' B' r, hr⟩
  | .weakL A' d', hcf' =>
    ljCutAdmPrincipalOrR P Q Γ₀ d₁sub hXsz hXeq rebuild ih d' hcf'
      (fun x hx => hant (Finset.mem_insert_of_mem hx))
  | .cut _ _ _, hcf' => absurd hcf' id
termination_by d₂.height
decreasing_by all_goals (simp [SeqProof.height]; try omega)

/-- Principal `impR`/`impL` case: structural recursion on `d₂` given
`d₁' : CutFreeSeqProof T (insert P Γ₀ ⊢ Q)` from the `impR` side. When `d₂` decomposes
`P → Q` via `impL`, the principal case uses `ih` to cut on `P` and `Q`. Generic over the
theory `T`, following `ljCutAdmPrincipalAndR`'s pattern. -/
noncomputable def ljCutAdmPrincipalImpR {T : Theory Atom}
    (P Q : Proposition Atom) (Γ₀ : Ctx Atom)
    (d₁' : CutFreeSeqProof T (insert P Γ₀ ⊢ Q))
    (ih : LJCutIH (T := T) (P → Q))
    {Γ : Ctx Atom} {C : Proposition Atom}
    (d₂ : SeqProof T (Γ ⊢ C)) (hcf₂ : SeqProof.CutFree d₂)
    (hant : Γ ⊆ insert (P → Q) Γ₀) :
    CutFreeSeqProof T (Γ₀ ⊢ C) :=
  match d₂, hcf₂ with
  | .ax phi _ hphiL, _ =>
    if heq : phi = Proposition.imp P Q then
      if h : phi ∈ Γ₀ then ⟨.ax phi Γ₀ h, trivial⟩
      else
        (heq ▸ ⟨.impR P Q d₁'.1, d₁'.2⟩ : CutFreeSeqProof T (Γ₀ ⊢ phi))
    else ⟨.ax phi Γ₀ (ljMem_of_ne_head (hant hphiL) heq), trivial⟩
  | @SeqProof.botL _ _ _ _ _ inst hbot, _ =>
    letI := inst
    ⟨.botL Γ₀ _ (ljMem_of_ne_head (hant hbot) nofun), trivial⟩
  | .andL A' B' hAB d', hcf' =>
    let hAB₀ := ljMem_of_ne_head (hant hAB) nofun
    let wk2 : Γ₀ ⊆ insert A' (insert B' Γ₀) :=
      (Finset.subset_insert B' Γ₀).trans (Finset.subset_insert A' _)
    let hant' : insert A' (insert B' Γ) ⊆ insert (P → Q) (insert A' (insert B' Γ₀)) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self A' _))
        (Finset.insert_subset
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self B' _)))
          (fun x hx => (Finset.insert_subset_insert _ wk2) (hant hx)))
    let ⟨r, hr⟩ := ljCutAdmPrincipalImpR P Q (insert A' (insert B' Γ₀))
      (d₁'.mono (Finset.insert_subset_insert _ wk2)) ih d' hcf' hant'
    ⟨.andL A' B' hAB₀ r, hr⟩
  | .andR A' B' d₂a d₂b, hcf_ab =>
    let ⟨ra, hra⟩ := ljCutAdmPrincipalImpR P Q Γ₀ d₁' ih d₂a hcf_ab.1 hant
    let ⟨rb, hrb⟩ := ljCutAdmPrincipalImpR P Q Γ₀ d₁' ih d₂b hcf_ab.2 hant
    ⟨.andR A' B' ra rb, ⟨hra, hrb⟩⟩
  | .orL A' B' hAB d₂a d₂b, hcf_ab =>
    let hAB₀ := ljMem_of_ne_head (hant hAB) nofun
    let hant_a : insert A' Γ ⊆ insert (P → Q) (insert A' Γ₀) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self A' _))
        (fun x hx => (Finset.insert_subset_insert _ (Finset.subset_insert A' _)) (hant hx))
    let hant_b : insert B' Γ ⊆ insert (P → Q) (insert B' Γ₀) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self B' _))
        (fun x hx => (Finset.insert_subset_insert _ (Finset.subset_insert B' _)) (hant hx))
    let ⟨ra, hra⟩ := ljCutAdmPrincipalImpR P Q (insert A' Γ₀)
      (d₁'.mono (Finset.insert_subset_insert _ (Finset.subset_insert A' _)))
      ih d₂a hcf_ab.1 hant_a
    let ⟨rb, hrb⟩ := ljCutAdmPrincipalImpR P Q (insert B' Γ₀)
      (d₁'.mono (Finset.insert_subset_insert _ (Finset.subset_insert B' _)))
      ih d₂b hcf_ab.2 hant_b
    ⟨.orL A' B' hAB₀ ra rb, ⟨hra, hrb⟩⟩
  | .orR1 A' B' d', hcf' =>
    let ⟨r, hr⟩ := ljCutAdmPrincipalImpR P Q Γ₀ d₁' ih d' hcf' hant
    ⟨.orR1 A' B' r, hr⟩
  | .orR2 A' B' d', hcf' =>
    let ⟨r, hr⟩ := ljCutAdmPrincipalImpR P Q Γ₀ d₁' ih d' hcf' hant
    ⟨.orR2 A' B' r, hr⟩
  | .impL A' B' hAB d₂a d₂b, hcf_ab =>
    if h1 : A' = P ∧ B' = Q then
      -- PRINCIPAL CASE: d₂ = impL P Q, cut formula = P → Q
      have hP : sizeOf P < sizeOf (Proposition.imp P Q) := by
        rw [Proposition.imp.sizeOf_spec]; omega
      have hQ : sizeOf Q < sizeOf (Proposition.imp P Q) := by
        rw [Proposition.imp.sizeOf_spec]; omega
      -- d₂a : (Γ, A') -- recurse to get (Γ₀, A'), then cast A' = P
      let d₂a_result := ljCutAdmPrincipalImpR P Q Γ₀ d₁' ih d₂a hcf_ab.1 hant
      let d₂a_P : CutFreeSeqProof T (Γ₀ ⊢ P) := h1.1 ▸ d₂a_result
      -- d₂b : (insert B' Γ, C) -- recurse to get (insert Q Γ₀, C)
      let wk_b : Γ₀ ⊆ insert B' Γ₀ := Finset.subset_insert B' _
      let hant_b : insert B' Γ ⊆ insert (P → Q) (insert B' Γ₀) :=
        Finset.insert_subset
          (Finset.mem_insert_of_mem (Finset.mem_insert_self B' Γ₀))
          (fun x hx => (Finset.insert_subset_insert (P → Q) wk_b) (hant hx))
      let d₂b' := ljCutAdmPrincipalImpR P Q (insert B' Γ₀)
        (d₁'.mono (Finset.insert_subset_insert _ wk_b)) ih d₂b hcf_ab.2 hant_b
      let d₂b_Q : CutFreeSeqProof T (insert Q Γ₀ ⊢ C) := h1.2 ▸ d₂b'
      -- Cut on P: d₂a_P : (Γ₀, P), d₁' : (insert P Γ₀, Q) → (Γ₀, Q) via ih P
      let r₁ := ih P hP Γ₀ Q d₂a_P d₁'
      -- Cut on Q: r₁ : (Γ₀, Q), d₂b_Q : (insert Q Γ₀, C) → (Γ₀, C) via ih Q
      ih Q hQ Γ₀ C r₁ d₂b_Q
    else
      let hAB₀ := ljMem_of_ne_head (hant hAB)
        (by intro heq; injection heq with h1a h1b; exact h1 ⟨h1a, h1b⟩)
      let hant_b : insert B' Γ ⊆ insert (P → Q) (insert B' Γ₀) :=
        Finset.insert_subset
          (Finset.mem_insert_of_mem (Finset.mem_insert_self B' _))
          (fun x hx => (Finset.insert_subset_insert _ (Finset.subset_insert B' _)) (hant hx))
      let ⟨ra, hra⟩ := ljCutAdmPrincipalImpR P Q Γ₀ d₁' ih d₂a hcf_ab.1 hant
      let ⟨rb, hrb⟩ := ljCutAdmPrincipalImpR P Q (insert B' Γ₀)
        (d₁'.mono (Finset.insert_subset_insert _ (Finset.subset_insert B' _)))
        ih d₂b hcf_ab.2 hant_b
      ⟨.impL A' B' hAB₀ ra rb, ⟨hra, hrb⟩⟩
  | .impR A' B' d', hcf' =>
    let hant' : insert A' Γ ⊆ insert (P → Q) (insert A' Γ₀) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self A' _))
        (fun x hx => (Finset.insert_subset_insert _ (Finset.subset_insert A' _)) (hant hx))
    let ⟨r, hr⟩ := ljCutAdmPrincipalImpR P Q (insert A' Γ₀)
      (d₁'.mono (Finset.insert_subset_insert _ (Finset.subset_insert A' _)))
      ih d' hcf' hant'
    ⟨.impR A' B' r, hr⟩
  | .weakL A' d', hcf' =>
    ljCutAdmPrincipalImpR P Q Γ₀ d₁' ih d' hcf'
      (fun x hx => hant (Finset.mem_insert_of_mem hx))
  | .cut _ _ _, hcf' => absurd hcf' id
termination_by d₂.height
decreasing_by all_goals (simp [SeqProof.height]; try omega)

/-! ### ljCutAdmLeft: structural recursion on d₁ -/

/-- Left-side structural recursion on `d₁`: eliminate the cut formula `A` from the left
proof. Non-principal cases push the cut deeper. Principal cases (where `d₁` introduces `A`
on the right) delegate to the appropriate standalone helper. Generic over the theory `T`,
following `ljCutAdmPrincipalAndR`'s pattern. -/
noncomputable def ljCutAdmLeft {T : Theory Atom}
    (A : Proposition Atom) (Γ₀ : Ctx Atom) (C₀ : Proposition Atom)
    (d₂ : CutFreeSeqProof T (insert A Γ₀ ⊢ C₀)) (ih : LJCutIH (T := T) A)
    {Γ : Ctx Atom}
    (d₁ : SeqProof T (Γ ⊢ A)) (hcf₁ : SeqProof.CutFree d₁)
    (hant : Γ ⊆ Γ₀) :
    CutFreeSeqProof T (Γ₀ ⊢ C₀) :=
  match d₁, hcf₁ with
  | .ax _ _ hphiL, _ =>
    d₂.mono (Finset.insert_subset (hant hphiL) (Finset.Subset.refl _))
  | @SeqProof.botL _ _ _ _ _ inst hbot, _ =>
    letI := inst
    ⟨.botL Γ₀ C₀ (hant hbot), trivial⟩
  | .andL A' B' hAB d', hcf' =>
    let d₂' := d₂.mono
      (Finset.insert_subset_insert A
        ((Finset.subset_insert B' Γ₀).trans (Finset.subset_insert A' _)))
    let hant' : insert A' (insert B' Γ) ⊆ insert A' (insert B' Γ₀) :=
      Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hant)
    let ⟨r, hr⟩ := ljCutAdmLeft A (insert A' (insert B' Γ₀)) C₀ d₂' ih d' hcf' hant'
    ⟨.andL A' B' (hant hAB) r, hr⟩
  | .andR P Q d₁a d₁b, hcf_ab =>
    -- PRINCIPAL: A = P ∧ Q, delegate to ljCutAdmPrincipalAndR
    let d₁p : CutFreeSeqProof T (Γ₀ ⊢ P) :=
      ⟨d₁a.mono hant, SeqProof.CutFree.mono hant d₁a hcf_ab.1⟩
    let d₁q : CutFreeSeqProof T (Γ₀ ⊢ Q) :=
      ⟨d₁b.mono hant, SeqProof.CutFree.mono hant d₁b hcf_ab.2⟩
    ljCutAdmPrincipalAndR P Q Γ₀ d₁p d₁q (by exact ih)
      d₂.1 d₂.2 (fun x hx => hx)
  | .orL A' B' hAB d₁a d₁b, hcf_ab =>
    let d₂_a := d₂.mono (Finset.insert_subset_insert A (Finset.subset_insert A' _))
    let d₂_b := d₂.mono (Finset.insert_subset_insert A (Finset.subset_insert B' _))
    let ⟨ra, hra⟩ := ljCutAdmLeft A (insert A' Γ₀) C₀ d₂_a ih d₁a hcf_ab.1
      (Finset.insert_subset_insert _ hant)
    let ⟨rb, hrb⟩ := ljCutAdmLeft A (insert B' Γ₀) C₀ d₂_b ih d₁b hcf_ab.2
      (Finset.insert_subset_insert _ hant)
    ⟨.orL A' B' (hant hAB) ra rb, ⟨hra, hrb⟩⟩
  | .orR1 P Q d', hcf' =>
    -- PRINCIPAL: A = P ∨ Q, d' : (Γ, P). Delegate to ljCutAdmPrincipalOrR.
    let d₁sub : CutFreeSeqProof T (Γ₀ ⊢ P) :=
      ⟨d'.mono hant, SeqProof.CutFree.mono hant d' hcf'⟩
    have hPsz : sizeOf P < sizeOf (Proposition.or P Q) := by
      rw [Proposition.or.sizeOf_spec]; omega
    ljCutAdmPrincipalOrR P Q Γ₀ d₁sub hPsz (Or.inl rfl)
      (fun d => ⟨.orR1 P Q d.1, d.2⟩) (by exact ih)
      d₂.1 d₂.2 (fun x hx => hx)
  | .orR2 P Q d', hcf' =>
    -- PRINCIPAL: A = P ∨ Q, d' : (Γ, Q). Delegate to ljCutAdmPrincipalOrR.
    let d₁sub : CutFreeSeqProof T (Γ₀ ⊢ Q) :=
      ⟨d'.mono hant, SeqProof.CutFree.mono hant d' hcf'⟩
    have hQsz : sizeOf Q < sizeOf (Proposition.or P Q) := by
      rw [Proposition.or.sizeOf_spec]; omega
    ljCutAdmPrincipalOrR P Q Γ₀ d₁sub hQsz (Or.inr rfl)
      (fun d => ⟨.orR2 P Q d.1, d.2⟩) (by exact ih)
      d₂.1 d₂.2 (fun x hx => hx)
  | .impL A' B' hAB d₁a d₁b, hcf_ab =>
    -- Non-principal left rule: impL. d₁a : (Γ, A'), d₁b : (insert B' Γ, A)
    let d₂_b := d₂.mono (Finset.insert_subset_insert A (Finset.subset_insert B' _))
    let ⟨rb, hrb⟩ := ljCutAdmLeft A (insert B' Γ₀) C₀ d₂_b ih d₁b hcf_ab.2
      (Finset.insert_subset_insert _ hant)
    let ra : CutFreeSeqProof T (Γ₀ ⊢ A') :=
      ⟨d₁a.mono hant, SeqProof.CutFree.mono hant d₁a hcf_ab.1⟩
    ⟨.impL A' B' (hant hAB) ra.1 rb, ⟨ra.2, hrb⟩⟩
  | .impR P Q d', hcf' =>
    -- PRINCIPAL: A = P → Q. d' : (insert P Γ, Q). Delegate to ljCutAdmPrincipalImpR.
    let d₁' : CutFreeSeqProof T (insert P Γ₀ ⊢ Q) :=
      ⟨d'.mono (Finset.insert_subset_insert _ hant),
       SeqProof.CutFree.mono (Finset.insert_subset_insert _ hant) d' hcf'⟩
    ljCutAdmPrincipalImpR P Q Γ₀ d₁' (by exact ih)
      d₂.1 d₂.2 (fun x hx => hx)
  | .weakL A' d', hcf' =>
    ljCutAdmLeft A Γ₀ C₀ d₂ ih d' hcf' ((Finset.subset_insert A' _).trans hant)
  | .cut _ _ _, hcf' => absurd hcf' id
termination_by d₁.height
decreasing_by all_goals (simp [SeqProof.height]; try omega)

/-! ### ljCutAdmRight: structural recursion on d₂ -/

set_option maxHeartbeats 400000 in
-- The right-side helper has many cases with Finset subset obligations.
/-- Right-side structural recursion on `d₂`: eliminate the cut formula `A` from a proof
whose context contains `A`. For left-rule cases where `A` is the decomposed formula,
builds a reconstructed `d₂_new` and delegates to `ljCutAdmLeft`. Generic over the theory `T`,
following `ljCutAdmPrincipalAndR`'s pattern. -/
noncomputable def ljCutAdmRight {T : Theory Atom}
    (A : Proposition Atom) (Γ₀ : Ctx Atom)
    (d₁ : CutFreeSeqProof T (Γ₀ ⊢ A)) (ih : LJCutIH (T := T) A)
    {Γ : Ctx Atom} {C : Proposition Atom}
    (d₂ : SeqProof T (Γ ⊢ C)) (hcf₂ : SeqProof.CutFree d₂)
    (hant : Γ ⊆ insert A Γ₀) :
    CutFreeSeqProof T (Γ₀ ⊢ C) :=
  match d₂, hcf₂ with
  | .ax phi _ hphiL, _ =>
    if heq : phi = A then
      (heq ▸ d₁ : CutFreeSeqProof T (Γ₀ ⊢ phi))
    else ⟨.ax phi Γ₀ (ljMem_of_ne_head (hant hphiL) heq), trivial⟩
  | @SeqProof.botL _ _ _ _ _ inst hbot, _ =>
    letI := inst
    if heq : (⊥ : Proposition Atom) = A then
      ljCutAdmLeft A Γ₀ _
        ⟨.botL (insert A Γ₀) _ (heq ▸ Finset.mem_insert_self _ _), trivial⟩
        ih d₁.1 d₁.2 (Finset.Subset.refl _)
    else ⟨.botL Γ₀ _ (ljMem_of_ne_head (hant hbot) heq), trivial⟩
  | .andL A' B' hAB d', hcf' =>
    let wk2 : Γ₀ ⊆ insert A' (insert B' Γ₀) :=
      (Finset.subset_insert B' Γ₀).trans (Finset.subset_insert A' _)
    let hant' : insert A' (insert B' Γ) ⊆ insert A (insert A' (insert B' Γ₀)) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self A' _))
        (Finset.insert_subset
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self B' _)))
          (fun x hx => (Finset.insert_subset_insert A wk2) (hant hx)))
    let ⟨r, hr⟩ := ljCutAdmRight A (insert A' (insert B' Γ₀))
      (d₁.mono wk2) ih d' hcf' hant'
    if heq : Proposition.and A' B' = A then
      let wk_ab : insert A' (insert B' Γ₀) ⊆ insert A' (insert B' (insert (A' ∧ B') Γ₀)) :=
        Finset.insert_subset_insert _
          (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
      let d₂_new : CutFreeSeqProof T (insert (A' ∧ B') Γ₀ ⊢ C) :=
        ⟨.andL A' B' (Finset.mem_insert_self _ _) (r.mono wk_ab),
         SeqProof.CutFree.mono wk_ab r hr⟩
      ljCutAdmLeft A Γ₀ C (heq ▸ d₂_new) ih d₁.1 d₁.2 (Finset.Subset.refl _)
    else ⟨.andL A' B' (ljMem_of_ne_head (hant hAB) heq) r, hr⟩
  | .andR A' B' d₂a d₂b, hcf_ab =>
    let ⟨ra, hra⟩ := ljCutAdmRight A Γ₀ d₁ ih d₂a hcf_ab.1 hant
    let ⟨rb, hrb⟩ := ljCutAdmRight A Γ₀ d₁ ih d₂b hcf_ab.2 hant
    ⟨.andR A' B' ra rb, ⟨hra, hrb⟩⟩
  | .orL A' B' hAB d₂a d₂b, hcf_ab =>
    let hant_a : insert A' Γ ⊆ insert A (insert A' Γ₀) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self A' _))
        (fun x hx => (Finset.insert_subset_insert A (Finset.subset_insert A' _)) (hant hx))
    let hant_b : insert B' Γ ⊆ insert A (insert B' Γ₀) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self B' _))
        (fun x hx => (Finset.insert_subset_insert A (Finset.subset_insert B' _)) (hant hx))
    let ⟨ra, hra⟩ := ljCutAdmRight A (insert A' Γ₀)
      (d₁.mono (Finset.subset_insert _ _)) ih d₂a hcf_ab.1 hant_a
    let ⟨rb, hrb⟩ := ljCutAdmRight A (insert B' Γ₀)
      (d₁.mono (Finset.subset_insert _ _)) ih d₂b hcf_ab.2 hant_b
    if heq : Proposition.or A' B' = A then
      let wk_a := Finset.insert_subset_insert A' (Finset.subset_insert (A' ∨ B') Γ₀)
      let wk_b := Finset.insert_subset_insert B' (Finset.subset_insert (A' ∨ B') Γ₀)
      let d₂_new : CutFreeSeqProof T (insert (A' ∨ B') Γ₀ ⊢ C) :=
        ⟨.orL A' B' (Finset.mem_insert_self _ _) (ra.mono wk_a) (rb.mono wk_b),
         ⟨SeqProof.CutFree.mono wk_a ra hra, SeqProof.CutFree.mono wk_b rb hrb⟩⟩
      ljCutAdmLeft A Γ₀ C (heq ▸ d₂_new) ih d₁.1 d₁.2 (Finset.Subset.refl _)
    else ⟨.orL A' B' (ljMem_of_ne_head (hant hAB) heq) ra rb, ⟨hra, hrb⟩⟩
  | .orR1 A' B' d', hcf' =>
    let ⟨r, hr⟩ := ljCutAdmRight A Γ₀ d₁ ih d' hcf' hant
    ⟨.orR1 A' B' r, hr⟩
  | .orR2 A' B' d', hcf' =>
    let ⟨r, hr⟩ := ljCutAdmRight A Γ₀ d₁ ih d' hcf' hant
    ⟨.orR2 A' B' r, hr⟩
  | .impL A' B' hAB d₂a d₂b, hcf_ab =>
    let hant_b : insert B' Γ ⊆ insert A (insert B' Γ₀) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self B' _))
        (fun x hx => (Finset.insert_subset_insert A (Finset.subset_insert B' _)) (hant hx))
    let ⟨ra, hra⟩ := ljCutAdmRight A Γ₀ d₁ ih d₂a hcf_ab.1 hant
    let ⟨rb, hrb⟩ := ljCutAdmRight A (insert B' Γ₀)
      (d₁.mono (Finset.subset_insert _ _)) ih d₂b hcf_ab.2 hant_b
    if heq : Proposition.imp A' B' = A then
      let wk_ra := Finset.subset_insert (Proposition.imp A' B') Γ₀
      let wk_rb := Finset.insert_subset_insert B'
        (Finset.subset_insert (Proposition.imp A' B') Γ₀)
      let d₂_new : CutFreeSeqProof T (insert (A' → B') Γ₀ ⊢ C) :=
        ⟨.impL A' B' (Finset.mem_insert_self _ _) (ra.mono wk_ra) (rb.mono wk_rb),
         ⟨SeqProof.CutFree.mono wk_ra ra hra, SeqProof.CutFree.mono wk_rb rb hrb⟩⟩
      ljCutAdmLeft A Γ₀ C (heq ▸ d₂_new) ih d₁.1 d₁.2 (Finset.Subset.refl _)
    else ⟨.impL A' B' (ljMem_of_ne_head (hant hAB) heq) ra rb, ⟨hra, hrb⟩⟩
  | .impR A' B' d', hcf' =>
    let hant' : insert A' Γ ⊆ insert A (insert A' Γ₀) :=
      Finset.insert_subset
        (Finset.mem_insert_of_mem (Finset.mem_insert_self A' _))
        (fun x hx => (Finset.insert_subset_insert A (Finset.subset_insert A' _)) (hant hx))
    let ⟨r, hr⟩ := ljCutAdmRight A (insert A' Γ₀)
      (d₁.mono (Finset.subset_insert _ _)) ih d' hcf' hant'
    ⟨.impR A' B' r, hr⟩
  | .weakL A' d', hcf' =>
    ljCutAdmRight A Γ₀ d₁ ih d' hcf'
      (fun x hx => hant (Finset.mem_insert_of_mem hx))
  | .cut _ _ _, hcf' => absurd hcf' id
termination_by d₂.height
decreasing_by all_goals (simp [SeqProof.height]; try omega)

/-! ## Top-Level Cut Admissibility and Cut Elimination -/

/-- Cut admissibility (Hauptsatz), generic over the theory `T`: from cut-free proofs of
`Γ ⊢ A` and `insert A Γ ⊢ C`, we can derive a cut-free proof of `Γ ⊢ C`.

The proof uses well-founded induction on formula complexity (`sizeOf A`).
Following [TroelstraSchwichtenberg2000] Theorem 4.1.1 and
[NegriVonPlato2001] Theorem 2.4.3. -/
noncomputable def ljCutAdmissibility {T : Theory Atom} (A : Proposition Atom) (Γ : Ctx Atom)
    (C : Proposition Atom)
    (d₁ : CutFreeSeqProof T (Γ ⊢ A))
    (d₂ : CutFreeSeqProof T (insert A Γ ⊢ C)) :
    CutFreeSeqProof T (Γ ⊢ C) :=
  ljCutAdmLeft A Γ C d₂
    (fun B _hB Γ' C' d₁' d₂' => ljCutAdmissibility B Γ' C' d₁' d₂')
    d₁.1 d₁.2 (Finset.Subset.refl _)
termination_by sizeOf A

/-! ## Cut Elimination -/

/-- Cut-free provability: every LJ proof can be transformed into a cut-free proof.

This is a corollary of `ljCutAdmissibility` applied to eliminate all cut steps.
The proof proceeds by structural induction on the LJ proof tree. Each non-cut
constructor is preserved directly. The cut case eliminates the cut step using
`ljCutAdmissibility`, which requires both sub-proofs to be cut-free (provided
inductively) and produces a cut-free result. -/
theorem LJProof.cutElim {seq : @Sequent Atom} (d : LJProof seq) :
    Nonempty (CutFreeLJProof seq) := by
  induction d with
  | ax A Γ hA => exact ⟨⟨.ax A Γ hA, trivial⟩⟩
  | botL Γ C hbot => exact ⟨⟨.botL Γ C hbot, trivial⟩⟩
  | andL A B hAB _ ih =>
      obtain ⟨⟨d', hd'⟩⟩ := ih
      exact ⟨⟨.andL A B hAB d', hd'⟩⟩
  | andR A B _ _ ih₁ ih₂ =>
      obtain ⟨⟨d₁', hd₁'⟩⟩ := ih₁
      obtain ⟨⟨d₂', hd₂'⟩⟩ := ih₂
      exact ⟨⟨.andR A B d₁' d₂', ⟨hd₁', hd₂'⟩⟩⟩
  | orL A B hAB _ _ ih₁ ih₂ =>
      obtain ⟨⟨d₁', hd₁'⟩⟩ := ih₁
      obtain ⟨⟨d₂', hd₂'⟩⟩ := ih₂
      exact ⟨⟨.orL A B hAB d₁' d₂', ⟨hd₁', hd₂'⟩⟩⟩
  | orR1 A B _ ih =>
      obtain ⟨⟨d', hd'⟩⟩ := ih
      exact ⟨⟨.orR1 A B d', hd'⟩⟩
  | orR2 A B _ ih =>
      obtain ⟨⟨d', hd'⟩⟩ := ih
      exact ⟨⟨.orR2 A B d', hd'⟩⟩
  | impL A B hAB _ _ ih₁ ih₂ =>
      obtain ⟨⟨d₁', hd₁'⟩⟩ := ih₁
      obtain ⟨⟨d₂', hd₂'⟩⟩ := ih₂
      exact ⟨⟨.impL A B hAB d₁' d₂', ⟨hd₁', hd₂'⟩⟩⟩
  | impR A B _ ih =>
      obtain ⟨⟨d', hd'⟩⟩ := ih
      exact ⟨⟨.impR A B d', hd'⟩⟩
  | weakL A _ ih =>
      obtain ⟨⟨d', hd'⟩⟩ := ih
      exact ⟨⟨.weakL A d', hd'⟩⟩
  | cut A _ _ ih₁ ih₂ =>
      obtain ⟨d₁'⟩ := ih₁
      obtain ⟨d₂'⟩ := ih₂
      exact ⟨ljCutAdmissibility A _ _ d₁' d₂'⟩

end Cslib.Logic.PL
