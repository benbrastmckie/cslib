/-
ARCHIVE -- NOT BUILT, NOT IMPORTED.

This file is archival: it is not in the `Cslib/` tree, carries no `import Cslib.Init`, is
not listed in `Cslib.lean`, and is never seen by `lake build` / `checkInitImports` /
`mk_all`. The blocks below will NOT compile as lifted out of context (they depend on the
surrounding file's variables, imports, and `omit` scopes); that is expected for an archive.
Each block's provenance header carries the `git` coordinates that recover a compiling version.
-/

-- Retired cluster 03: the KEYED minting guard and the key-threaded stepper.

-- ARCHIVED from Cslib/Logics/Modal/Tableau/S5Simplification.lean:2540-2665
-- Retired: 2026-07-16, task 515 phase 14 (plan v4)
-- Superseded by: `modalApplyOneS5w` + `modalMaxWorld_lt_worldBound_of_S5w` (`S5Simplification.lean`)
-- Why retired: correct (0/700 differential errors) but **no driver runs it**, and `modalExpMeasure_step_lt_gen` is stated for `modalStepBranchGen`, so a keyed driver could consume neither the measure engine nor `modalExpandBranchesGen_hintikka`. **Retired on cost, not correctness.**
-- Status at retirement: CI-green, sorry-free, zero axioms beyond propext/Classical.choice/Quot.sound
-- Recover a compiling version at: git show af59318098f7ed0eceb7a33634d072babb45b603 -- Cslib/Logics/Modal/Tableau/S5Simplification.lean

/-! ## Keys-Aware Guard Redesign (task 515 Phase 3, v2)

`blockingWorldS5` (Phase 2) compares the prospective successor's birth content against every
known world's CURRENT (live) relevant set. Task 511's S4 development hit the identical guard-vs-
live-set obstruction: a world born with key `k` can later grow its live relevant set past `k`,
so a *different* freshly-minted world computing the *same* birth content `k` is not blocked by
the live-set guard (its own live set has already grown away from `k`), yet `keysDistinct`
demands the two worlds' *birth keys* differ. The v2 fix (task 511's documented resolution,
adopted verbatim in shape): compare the prospective birth content against the threaded
**stored keys** list directly. Keys are fixed at minting time and never change, so this
comparison is exact and the resulting `_none_fresh` contract is precisely the birth-key
invariant `keysDistinct` (Phase 5) needs. -/

/-- The keys-aware S5 minting guard (v2, supersedes `blockingWorldS5` for the minting decision):
the least *stored* world `w'` among `keys` whose STORED birth key already equals the PROSPECTIVE
successor's birth content (`successorBirthContentS5`), if any exists. Mirrors the *intent* of
`blockingWorldS4`/`blockingWorldS5` but keys the comparison on the threaded `keys` list, per task
511's documented fix (511 summary "Next Steps"; report Section 4 Option A2). `none` means no
blocking world exists (mint fresh); `some wBlock` means loop-back to `wBlock`. -/
def blockingWorldS5Keyed (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex) : Option WorldIndex :=
  ((keys.filter
    (fun p => decide (p.2 = successorBirthContentS5 φ₀ b s φ w))).map Prod.fst).min?

omit [Hashable Atom] in
/-- **The keyed guard contract**: if `blockingWorldS5Keyed` returns a world, that world's
STORED birth key equals the prospective successor's birth content. Mirrors
`blockingWorldS5_eq_birthContent`, keyed on `keys` rather than the live relevant set. -/
lemma blockingWorldS5Keyed_eq_birthContent (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (s : Sign) (φ : Proposition Atom)
    (w wBlock : WorldIndex) (h : blockingWorldS5Keyed φ₀ keys b s φ w = some wBlock) :
    (wBlock, successorBirthContentS5 φ₀ b s φ w) ∈ keys := by
  unfold blockingWorldS5Keyed at h
  have hmem := List.min?_mem h
  obtain ⟨p, hp, hpfst⟩ := List.mem_map.mp hmem
  obtain ⟨hpmem, hpdec⟩ := List.mem_filter.mp hp
  have hpeq : p.2 = successorBirthContentS5 φ₀ b s φ w := of_decide_eq_true hpdec
  obtain ⟨pw, pk⟩ := p
  simp only at hpfst hpeq
  subst hpfst
  subst hpeq
  exact hpmem

omit [Hashable Atom] in
/-- **The keyed guard's freshness contract**: if `blockingWorldS5Keyed` returns `none`, the
prospective successor's birth content differs from EVERY stored key in `keys`. **This is the
birth-key invariant that makes `keysDistinct` a genuine per-step invariant** (directly discharges
the new-vs-old case in Phase 5). Mirrors `blockingWorldS5_none_fresh`/`blockingWorldS4_none_fresh`,
keyed on `keys`. -/
lemma blockingWorldS5Keyed_none_fresh (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (s : Sign) (φ : Proposition Atom)
    (w : WorldIndex) (h : blockingWorldS5Keyed φ₀ keys b s φ w = none) :
    ∀ w' k, (w', k) ∈ keys → k ≠ successorBirthContentS5 φ₀ b s φ w := by
  unfold blockingWorldS5Keyed at h
  rw [List.min?_eq_none_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff] at h
  intro w' k hmem heq
  exact absurd (decide_eq_true heq) (by simpa using h (w', k) hmem)

/-! ## Key-Threaded S5 Guarded Step (task 515 Phase 3, v2)

Mirrors `LoopChecking.lean`'s `modalStepBranchS4Keyed` (task 511 Phase 4): threads a stable
per-world birth-key list `keys` alongside `(b, e, acc)`, gaining an entry exactly when the guard
is unblocked at one of the two K minting shapes. **v2 crux change**: the block/mint decision is
now computed here directly via `blockingWorldS5Keyed` (the keys-aware guard), bypassing
`modalApplyOneS5g`'s live-set dispatch on the two minting shapes entirely (R2: "keys-aware bypass
inside a redesigned stepper"). Every other shape (including both S5 universal-propagation arms)
still delegates to `modalApplyOneS5` unchanged, so the non-minting agreement lemmas
(`modalApplyOneS5g_eq_of_not_boxNeg_diaPos`, Phase 2) remain valid, undisturbed reference
material even though this stepper no longer calls `modalApplyOneS5g` on the minting shapes. -/

/-- The S5-specific keyed one-step branch expansion (v2): mirrors `modalStepBranchS4Keyed`
(`LoopChecking.lean:582`) for the `(newBranches, newExpandedSets, newAcc)` triple, additionally
threading `keys`. At the two K minting shapes, the keyed guard `blockingWorldS5Keyed` decides
block (loop-back edge to the stored world, no new formulas) vs. mint (delegate to
`modalApplyOneS5` -- equal to K's `modalApplyOne` here since minting shapes are disjoint from
the S5 universal shapes, `modalApplyOneS5_eq_of_not_boxPos_diaNeg`), appending the fresh key to
`keys` on an unblocked mint. Every other shape delegates to `modalApplyOneS5` with `keys`
unchanged. -/
def modalStepBranchS5gKeyed (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) :
    Option (List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            Accessibility ×
            List (WorldIndex × Finset (Sign × Proposition Atom))) :=
  b.findSome? fun sf =>
    if e.any (· == sf) then none
    else
      match sf.sign, sf.formula with
      | .neg, .box φ =>
        match blockingWorldS5Keyed φ₀ keys b .neg φ sf.label with
        | some wBlock => some ([b], [e ++ [sf]], acc.addEdge sf.label wBlock, keys)
        | none =>
          let (result, newAcc) := modalApplyOneS5 sf b acc
          let keys' := keys ++ [(modalNextWorld b, successorBirthContentS5 φ₀ b .neg φ sf.label)]
          match result with
          | .linear newForms => some ([newForms ++ b], [e ++ [sf]], newAcc, keys')
          | .branching branches =>
            some (branches.map (· ++ b), branches.map (fun _ => e ++ [sf]), newAcc, keys')
          | .persistent newForms => some ([newForms ++ b], [e], newAcc, keys')
          | .notApplicable => none
      | .pos, .diamond φ =>
        match blockingWorldS5Keyed φ₀ keys b .pos φ sf.label with
        | some wBlock => some ([b], [e ++ [sf]], acc.addEdge sf.label wBlock, keys)
        | none =>
          let (result, newAcc) := modalApplyOneS5 sf b acc
          let keys' := keys ++ [(modalNextWorld b, successorBirthContentS5 φ₀ b .pos φ sf.label)]
          match result with
          | .linear newForms => some ([newForms ++ b], [e ++ [sf]], newAcc, keys')
          | .branching branches =>
            some (branches.map (· ++ b), branches.map (fun _ => e ++ [sf]), newAcc, keys')
          | .persistent newForms => some ([newForms ++ b], [e], newAcc, keys')
          | .notApplicable => none
      | _, _ =>
        let (result, newAcc) := modalApplyOneS5 sf b acc
        match result with
        | .linear newForms => some ([newForms ++ b], [e ++ [sf]], newAcc, keys)
        | .branching branches =>
          some (branches.map (· ++ b), branches.map (fun _ => e ++ [sf]), newAcc, keys)
        | .persistent newForms => some ([newForms ++ b], [e], newAcc, keys)
        | .notApplicable => none

