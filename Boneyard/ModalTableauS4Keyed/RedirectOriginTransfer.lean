import Cslib.Logics.Modal.Tableau.LoopChecking

/-!
# ARCHIVED (Boneyard)

This file archives two declarations excised from
`Cslib/Logics/Modal/Tableau/LoopChecking.lean`:

- `blockedRedirect_boxctx_mem_of_boxOrigin`
- `blockedRedirect_diaNeg_mem_of_diaOrigin`

Both are sorry-free and proven. They were archived as zero-consumer: a word-boundary grep of
each full name over `Cslib/`, `CslibTests/`, `scripts/`, and `Cslib.lean` returned zero code
consumers at the time of archival. See `../README.md` for the Boneyard convention and
`README.md` in this directory for why these particular declarations were archived.

Do not import from live code.
-/

#exit

/-- **Case-(b) derivation, box-context shape.** Given an already-recorded edge `u → wBlock` and
`T(□ψ)@u ∈ b`, mint-readiness (`modalNonMintCandidates φ₀ keys b e acc = []`) forces
`T(□ψ)@wBlock ∈ b`. Proof: otherwise `modalFourBoxProp b acc ψ u` is non-empty (it contains
`T(□ψ)@wBlock`, since the edge is recorded and the formula is absent), so
`modalApplyOneS4Keyed φ₀ keys` is applicable at `T(□ψ)@u` (`_,_`-catch-all reduction to
`modalApplyOneS4Rules`, since `T(□ψ)@u` is neither of the two keyed-guard shapes); `T(□ψ)@u` is
not a mint shape, so `modalNonMintCandidates`'s emptiness forces it into the expanded set `e` --
but `S4KeyedHintikkaInv.eBoxOnlyNeg` (`sf ∈ e, sf.formula = .box _ → sf.sign = .neg`) rules that
out for a POSITIVE box formula. This lemma lands regardless of how the witness gate below
resolves -- it is the load-bearing half either way. -/
lemma blockedRedirect_boxctx_mem_of_boxOrigin (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (u wBlock : WorldIndex) (ψ : Proposition Atom)
    (hedge : acc.hasEdge u wBlock = true)
    (hbox : (⟨.pos, .box ψ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (heBoxOnlyNeg : ∀ sf ∈ e, ∀ ψ', sf.formula = .box ψ' → sf.sign = .neg)
    (hmint : modalNonMintCandidates φ₀ keys b e acc = []) :
    (⟨.pos, .box ψ, wBlock⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  by_contra hcontra
  have hne_any : b.any (· == (⟨.pos, .box ψ, wBlock⟩ :
      SignedFormula (Proposition Atom) WorldIndex)) = false := by
    by_contra hne
    rw [Bool.not_eq_false, List.any_eq_true] at hne
    obtain ⟨x, hxmem, hxeq⟩ := hne
    rw [beq_iff_eq] at hxeq
    exact hcontra (hxeq ▸ hxmem)
  have hfourmem : (⟨.pos, .box ψ, wBlock⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalFourBoxProp b acc ψ u := by
    unfold modalFourBoxProp
    rw [List.mem_filterMap]
    refine ⟨wBlock, hasEdge_mem_successorsOf hedge, ?_⟩
    rw [if_neg (by simp [hne_any])]
  have hfourne : modalFourBoxProp b acc ψ u ≠ [] := List.ne_nil_of_mem hfourmem
  have hnotapp : (modalApplyOneS4Keyed φ₀ keys
      (⟨.pos, .box ψ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).1
      ≠ .notApplicable := by
    rw [modalApplyOneS4Keyed_boxPos_eq_S4Rules]
    exact modalApplyOneS4Rules_boxPos_not_notApplicable_of_fourBoxProp_ne_nil b acc ψ u hfourne
  have hcand := (modalNonMintCandidates_eq_nil_iff φ₀ keys b e acc).mp hmint
    (⟨.pos, .box ψ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) hbox
  rcases hcand with hshape | he | hna
  · exact absurd hshape (by simp [modalMintShape])
  · exact absurd (heBoxOnlyNeg _ he ψ rfl) (by simp)
  · exact hnotapp hna

/-- **Case-(b) derivation, diamond-context shape** (dual of
`blockedRedirect_boxctx_mem_of_boxOrigin`). Given an already-recorded edge `u → wBlock` and
`F(◇ψ)@u ∈ b`, mint-readiness forces `F(◇ψ)@wBlock ∈ b`, via `modalFourDiaNegProp` and
`S4KeyedHintikkaInv.eDiamondOnlyPos`. -/
lemma blockedRedirect_diaNeg_mem_of_diaOrigin (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (u wBlock : WorldIndex) (ψ : Proposition Atom)
    (hedge : acc.hasEdge u wBlock = true)
    (hdia : (⟨.neg, .diamond ψ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (heDiamondOnlyPos : ∀ sf ∈ e, ∀ ψ', sf.formula = .diamond ψ' → sf.sign = .pos)
    (hmint : modalNonMintCandidates φ₀ keys b e acc = []) :
    (⟨.neg, .diamond ψ, wBlock⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  by_contra hcontra
  have hne_any : b.any (· == (⟨.neg, .diamond ψ, wBlock⟩ :
      SignedFormula (Proposition Atom) WorldIndex)) = false := by
    by_contra hne
    rw [Bool.not_eq_false, List.any_eq_true] at hne
    obtain ⟨x, hxmem, hxeq⟩ := hne
    rw [beq_iff_eq] at hxeq
    exact hcontra (hxeq ▸ hxmem)
  have hfourmem : (⟨.neg, .diamond ψ, wBlock⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalFourDiaNegProp b acc ψ u := by
    unfold modalFourDiaNegProp
    rw [List.mem_filterMap]
    refine ⟨wBlock, hasEdge_mem_successorsOf hedge, ?_⟩
    rw [if_neg (by simp [hne_any])]
  have hfourne : modalFourDiaNegProp b acc ψ u ≠ [] := List.ne_nil_of_mem hfourmem
  have hnotapp : (modalApplyOneS4Keyed φ₀ keys
      (⟨.neg, .diamond ψ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).1
      ≠ .notApplicable := by
    rw [modalApplyOneS4Keyed_diaNeg_eq_S4Rules]
    exact modalApplyOneS4Rules_diaNeg_not_notApplicable_of_fourDiaNegProp_ne_nil b acc ψ u hfourne
  have hcand := (modalNonMintCandidates_eq_nil_iff φ₀ keys b e acc).mp hmint
    (⟨.neg, .diamond ψ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) hdia
  rcases hcand with hshape | he | hna
  · exact absurd hshape (by simp [modalMintShape])
  · exact absurd (heDiamondOnlyPos _ he ψ rfl) (by simp)
  · exact hnotapp hna
