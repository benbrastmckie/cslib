/-
ARCHIVE -- NOT BUILT, NOT IMPORTED.

This file is archival: it is not in the `Cslib/` tree, carries no `import Cslib.Init`, is
not listed in `Cslib.lean`, and is never seen by `lake build` / `checkInitImports` /
`mk_all`. The blocks below will NOT compile as lifted out of context (they depend on the
surrounding file's variables, imports, and `omit` scopes); that is expected for an archive.
Each block's provenance header carries the `git` coordinates that recover a compiling version.
-/

-- Retired cluster 02: the UNKEYED minting guard and the guarded rule `modalApplyOneS5g`.

-- ARCHIVED from Cslib/Logics/Modal/Tableau/S5Simplification.lean:1260-1423
-- Retired: 2026-07-16, task 515 phase 14 (plan v4)
-- Superseded by: `modalApplyOneS5w` + `witnessWorldS5` (`S5Simplification.lean`) -- witness REUSE rather than mint-blocking
-- Why retired: the unkeyed guard compares a prospective successor's birth content against every known world's CURRENT (live) relevant set, so a world born with key `k` can later grow its live set past `k` and stop blocking a later mint computing the same `k`. Superseded first by the keyed redesign (cluster 03) and ultimately by witness reuse, which needs no guard at all. No driver ever ran `modalApplyOneS5g`.
-- Status at retirement: CI-green, sorry-free, zero axioms beyond propext/Classical.choice/Quot.sound
-- Recover a compiling version at: git show af59318098f7ed0eceb7a33634d072babb45b603 -- Cslib/Logics/Modal/Tableau/S5Simplification.lean

/-! ## S5 Minting Guard (task 515 Phase 2)

The termination machinery's minting guard: `successorBirthContentS5`/`blockingWorldS5` mirror
`successorBirthContent`/`blockingWorldS4` (`LoopChecking.lean:374/391`) exactly. Both are
already `φ₀`-parametric and rule-independent (they only inspect the branch `b`'s box-context at
the trigger world `w`, never any S4-specific rule), so the S5 versions reuse the S4
declarations verbatim under new names, matching the plan's Phase 2 artifact list and keeping
S4/S5 development decoupled. -/

/-- The prospective birth content of the successor that would be minted for the modal-minting
call at `⟨s, φ, w⟩` (the two K minting shapes `F(□φ)@w`/`T(◇φ)@w`, `s` the witness's sign) at
branch `b`. Reuses `successorBirthContent` (`LoopChecking.lean:374`) verbatim -- the
computation is purely a function of what is already on `b` at `w`, independent of which
system's tableau triggered the mint. -/
def successorBirthContentS5 (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex) : Finset (Sign × Proposition Atom) :=
  successorBirthContent φ₀ b s φ w

/-- The S5 minting guard: the least world `w' ∈ modalKnownWorlds b` whose CURRENT relevant set
(`relevantSetFinset`) already equals the PROSPECTIVE successor's birth content
(`successorBirthContentS5`), if any exists. Mirrors `blockingWorldS4`
(`LoopChecking.lean:391`) exactly, with `successorBirthContentS5` swapped in. `none` means no
blocking world exists (the underlying rule should mint a fresh world); `some wBlock` means the
prospective successor should be loop-backed to `wBlock` instead. -/
def blockingWorldS5 (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex) : Option WorldIndex :=
  ((modalKnownWorlds b).filter
    (fun w' => decide (relevantSetFinset φ₀ b w' = successorBirthContentS5 φ₀ b s φ w))).min?

omit [Hashable Atom] in
/-- If `blockingWorldS5` returns a world, it is a known world of the branch. Mirrors
`blockingWorldS4_mem_modalKnownWorlds` (`LoopChecking.lean:399`). -/
lemma blockingWorldS5_mem_modalKnownWorlds (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (s : Sign) (φ : Proposition Atom)
    (w wBlock : WorldIndex) (h : blockingWorldS5 φ₀ b s φ w = some wBlock) :
    wBlock ∈ modalKnownWorlds b := by
  have hmem := List.min?_mem h
  exact (List.mem_filter.mp hmem).1

omit [Hashable Atom] in
/-- **The guard contract**: if `blockingWorldS5` returns a world, that world's CURRENT relevant
set equals the prospective successor's birth content. Mirrors `blockingWorldS4_eq_birthContent`
(`LoopChecking.lean:413`). -/
lemma blockingWorldS5_eq_birthContent (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (s : Sign) (φ : Proposition Atom)
    (w wBlock : WorldIndex) (h : blockingWorldS5 φ₀ b s φ w = some wBlock) :
    relevantSetFinset φ₀ b wBlock = successorBirthContentS5 φ₀ b s φ w := by
  have hmem := List.min?_mem h
  have hpred := (List.mem_filter.mp hmem).2
  exact of_decide_eq_true hpred

omit [Hashable Atom] in
/-- **The guard's freshness contract**: if `blockingWorldS5` returns `none`, the prospective
successor's birth content differs from every existing known world's CURRENT relevant set.
Mirrors `blockingWorldS4_none_fresh` (`LoopChecking.lean:426`). -/
lemma blockingWorldS5_none_fresh (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (s : Sign) (φ : Proposition Atom)
    (w : WorldIndex) (h : blockingWorldS5 φ₀ b s φ w = none) :
    ∀ w' ∈ modalKnownWorlds b, relevantSetFinset φ₀ b w' ≠ successorBirthContentS5 φ₀ b s φ w := by
  unfold blockingWorldS5 at h
  rw [List.min?_eq_none_iff, List.filter_eq_nil_iff] at h
  intro w' hw' heq
  exact absurd (decide_eq_true heq) (by simpa using h w' hw')

/-! ## S5 Guarded Rule Application (task 515 Phase 2)

`modalApplyOneS5g` routes the two K minting shapes (`F(□φ)@w`, `T(◇φ)@w` -- disjoint from the
S5 universal-propagation shapes `T(□φ)@w`/`F(◇φ)@w`) through `blockingWorldS5`, mirroring
`modalApplyOneS4` (`LoopChecking.lean:461`); every other shape (including both S5 universal
arms) falls through unchanged to `modalApplyOneS5`. Unlike S4 (which falls through to
`modalApplyOneS4Rules`, an extra K+T+4 dispatch layer), S5 has no intermediate rule layer, so
the unblocked/agreement lemmas below are direct, not chained through a T-style rule stack. -/

/-- The guarded S5 rule-application function (Decision D2's replacement for the abandoned
`RuleApplicationSpec modalApplyOneS5` route): at the two K minting shapes, consult
`blockingWorldS5` before minting; everywhere else (including the S5 universal arms), reduce to
`modalApplyOneS5` unchanged. Mirrors `modalApplyOneS4` (`LoopChecking.lean:461`). -/
def modalApplyOneS5g (φ₀ : Proposition Atom) : RuleApply Atom :=
  fun sf b acc =>
    match sf.sign, sf.formula with
    | .neg, .box φ =>
      match blockingWorldS5 φ₀ b .neg φ sf.label with
      | some wBlock => (.linear [], acc.addEdge sf.label wBlock)
      | none => modalApplyOneS5 sf b acc
    | .pos, .diamond φ =>
      match blockingWorldS5 φ₀ b .pos φ sf.label with
      | some wBlock => (.linear [], acc.addEdge sf.label wBlock)
      | none => modalApplyOneS5 sf b acc
    | _, _ => modalApplyOneS5 sf b acc

/-- Guard spec (a), box-negative shape: `modalApplyOneS5g φ₀` at `F(□φ)@w` blocks -- adding
exactly one loop-back edge to an existing known world and minting no new world -- when the
guard fires. Mirrors `modalApplyOneS4_boxNeg_blocked_eq` (`LoopChecking.lean:479`). -/
lemma modalApplyOneS5g_boxNeg_blocked_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w wBlock : WorldIndex)
    (hblock : blockingWorldS5 φ₀ b .neg φ w = some wBlock) :
    modalApplyOneS5g φ₀ ⟨.neg, .box φ, w⟩ b acc = (.linear [], acc.addEdge w wBlock) := by
  unfold modalApplyOneS5g
  simp [hblock]

/-- Guard spec (b), box-negative shape, unblocked case: `modalApplyOneS5g φ₀` reduces to
`modalApplyOneS5` directly (no intermediate rule layer, unlike S4's `modalApplyOneS4Rules`
chain). Mirrors `modalApplyOneS4_boxNeg_unblocked_eq` (`LoopChecking.lean:488`). -/
lemma modalApplyOneS5g_boxNeg_unblocked_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) (hblock : blockingWorldS5 φ₀ b .neg φ w = none) :
    modalApplyOneS5g φ₀ ⟨.neg, .box φ, w⟩ b acc = modalApplyOneS5 ⟨.neg, .box φ, w⟩ b acc := by
  unfold modalApplyOneS5g
  simp [hblock]

/-- Guard spec (a), diamond-positive shape (dual of the box-negative pair): blocked case adds
exactly one loop-back edge and mints no new world. Mirrors `modalApplyOneS4_diaPos_blocked_eq`
(`LoopChecking.lean:500`). -/
lemma modalApplyOneS5g_diaPos_blocked_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w wBlock : WorldIndex)
    (hblock : blockingWorldS5 φ₀ b .pos φ w = some wBlock) :
    modalApplyOneS5g φ₀ ⟨.pos, .diamond φ, w⟩ b acc = (.linear [], acc.addEdge w wBlock) := by
  unfold modalApplyOneS5g
  simp [hblock]

/-- Guard spec (b), diamond-positive shape, unblocked case: reduces to `modalApplyOneS5`
directly. Mirrors `modalApplyOneS4_diaPos_unblocked_eq` (`LoopChecking.lean:510`). -/
lemma modalApplyOneS5g_diaPos_unblocked_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) (hblock : blockingWorldS5 φ₀ b .pos φ w = none) :
    modalApplyOneS5g φ₀ ⟨.pos, .diamond φ, w⟩ b acc =
      modalApplyOneS5 ⟨.pos, .diamond φ, w⟩ b acc := by
  unfold modalApplyOneS5g
  simp [hblock]

/-- `modalApplyOneS5g` agrees with `modalApplyOneS5` outside the two K minting shapes: the
guard only ever intervenes at `F(□φ)@w`/`T(◇φ)@w`. Mirrors
`modalApplyOneS4_eq_of_not_boxNeg_diaPos` (`LoopChecking.lean:522`). -/
lemma modalApplyOneS5g_eq_of_not_boxNeg_diaPos
    (φ₀ : Proposition Atom) (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)) :
    modalApplyOneS5g φ₀ sf b acc = modalApplyOneS5 sf b acc := by
  obtain ⟨h1, h2⟩ := h
  unfold modalApplyOneS5g
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
    simp_all

/-- `modalApplyOneS5g` agrees with K's `modalApplyOne` outside **all four** of the shapes
either the guard or the S5 universal arms touch (the two K minting shapes AND the two S5
universal-propagation shapes): composes `modalApplyOneS5g_eq_of_not_boxNeg_diaPos` with
`modalApplyOneS5_eq_of_not_boxPos_diaNeg` (`S5Simplification.lean:243`), the reuse the plan's
Phase 2 task calls for. -/
lemma modalApplyOneS5g_eq_of_not_minting_not_universal
    (φ₀ : Proposition Atom) (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hmint : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
             ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ))
    (huniv : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
             ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    modalApplyOneS5g φ₀ sf b acc = modalApplyOne sf b acc := by
  rw [modalApplyOneS5g_eq_of_not_boxNeg_diaPos φ₀ sf b acc hmint,
    modalApplyOneS5_eq_of_not_boxPos_diaNeg sf b acc huniv]

