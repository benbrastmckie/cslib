/-
ARCHIVE -- NOT BUILT, NOT IMPORTED.

This file is archival: it is not in the `Cslib/` tree, carries no `import Cslib.Init`, is
not listed in `Cslib.lean`, and is never seen by `lake build` / `checkInitImports` /
`mk_all`. The blocks below will NOT compile as lifted out of context (they depend on the
surrounding file's variables, imports, and `omit` scopes); that is expected for an archive.
Each block's provenance header carries the `git` coordinates that recover a compiling version.
-/

-- Retired cluster 04: the `S5LoopInv` twelve-field loop invariant, its world-contiguity
-- bookkeeping support, and the ~11 `modalStepBranchS5g_preserves_*` field-preservation
-- lemmas. Three blocks, in original file order.

-- ARCHIVED from Cslib/Logics/Modal/Tableau/S5Simplification.lean:2303-2539
-- Retired: 2026-07-16, task 515 phase 14 (plan v4)
-- Superseded by: no replacement needed -- the witness-rule chain (`S5wTagInv`/`S5wWorldInv`) never needs world contiguity
-- Why retired: `worldsContiguous` support for the retired `S5LoopInv`: it bridged Phase 6's known-world COUNT bound to the fresh label's VALUE bound. The tag-counting bound is stated directly on `modalMaxWorld`, so no such bridge is needed.
-- Status at retirement: CI-green, sorry-free, zero axioms beyond propext/Classical.choice/Quot.sound
-- Recover a compiling version at: git show af59318098f7ed0eceb7a33634d072babb45b603 -- Cslib/Logics/Modal/Tableau/S5Simplification.lean

/-! ## World-Contiguity Bookkeeping (task 515 Phase 4, 12th `S5LoopInv` field)

Local re-derivations of `FmpMeasure.lean`'s private `modalMaxWorld_append_*`/known-worlds-length
facts (unavailable across files), needed to prove the 12th `S5LoopInv` field `worldsContiguous`
(`modalMaxWorld b + 1 = (modalKnownWorlds b).length`) is preserved across a
`modalStepBranchS5gKeyed` step. See `specs/515_.../handoffs/02_phase4-bclosure-contiguity-gap.md`
for why this field is needed: Phase 6's pigeonhole bound
(`modalKnownWorlds_length_le_worldBoundS5`) bounds the known-world *count*, but `bClosure`'s
mint-case obligation needs a bound on the fresh label's *value*
(`modalNextWorld b ≤ modalWorldBoundS5 φ₀`); contiguity is exactly the bridge between the two. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma modalMaxWorld_foldl_le`. -/
private lemma modalMaxWorld_foldl_le_S5
    (l : List (SignedFormula (Proposition Atom) WorldIndex)) (c M : Nat) (hc : c ≤ M)
    (h : ∀ sf ∈ l, sf.label ≤ M) :
    l.foldl (fun mx sf => max mx sf.label) c ≤ M := by
  induction l generalizing c with
  | nil => simpa using hc
  | cons sf rest ih =>
    simp only [List.foldl_cons]
    exact ih (max c sf.label) (max_le hc (h sf List.mem_cons_self))
      (fun x hx => h x (List.mem_cons_of_mem _ hx))

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma modalMaxWorld_le_of_forall_le`. -/
private lemma modalMaxWorld_le_of_forall_le_S5
    (l : List (SignedFormula (Proposition Atom) WorldIndex)) (M : Nat)
    (h : ∀ sf ∈ l, sf.label ≤ M) : modalMaxWorld l ≤ M :=
  modalMaxWorld_foldl_le_S5 l 0 M (Nat.zero_le _) h

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma modalMaxWorld_append_eq_of_forall_le`
(unavailable across files): if every label of `xs` is already `≤ modalMaxWorld b`, appending `xs`
doesn't change `modalMaxWorld`. -/
private lemma modalMaxWorld_append_eq_of_forall_le_S5
    (xs b : List (SignedFormula (Proposition Atom) WorldIndex))
    (h : ∀ sf ∈ xs, sf.label ≤ modalMaxWorld b) :
    modalMaxWorld (xs ++ b) = modalMaxWorld b := by
  apply le_antisymm
  · apply modalMaxWorld_le_of_forall_le_S5
    intro sf hsf
    rcases List.mem_append.mp hsf with hxs | hb
    · exact h sf hxs
    · exact label_le_modalMaxWorld hb
  · exact modalMaxWorld_le_append xs b

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma modalMaxWorld_append_single`
(unavailable across files): if `xs` is nonempty and all its labels equal a fresh world `w'`
strictly greater than `modalMaxWorld b`, appending `xs` sets `modalMaxWorld` to exactly `w'`. -/
private lemma modalMaxWorld_append_single_S5
    (xs b : List (SignedFormula (Proposition Atom) WorldIndex)) (w' : WorldIndex)
    (hxsne : xs ≠ []) (hxs : ∀ sf ∈ xs, sf.label = w') (hgt : modalMaxWorld b < w') :
    modalMaxWorld (xs ++ b) = w' := by
  apply le_antisymm
  · apply modalMaxWorld_le_of_forall_le_S5
    intro sf hsf
    rcases List.mem_append.mp hsf with hxs' | hb
    · exact le_of_eq (hxs sf hxs')
    · exact le_of_lt (lt_of_le_of_lt (label_le_modalMaxWorld hb) hgt)
  · obtain ⟨sf0, hsf0⟩ := List.exists_mem_of_ne_nil xs hxsne
    have := label_le_modalMaxWorld (List.mem_append_left b hsf0)
    rwa [hxs sf0 hsf0] at this

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s
`private lemma modalNextWorld_not_mem_modalKnownWorlds` (unavailable across files): the fresh
world is never already known. -/
private lemma modalNextWorld_not_mem_modalKnownWorlds_S5
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) :
    modalNextWorld b ∉ modalKnownWorlds b := by
  intro hmem
  rw [mem_modalKnownWorlds_S5] at hmem
  obtain ⟨sf, hsf, hsflab⟩ := hmem
  exact absurd hsflab (Nat.ne_of_lt (modalNextWorld_gt b sf hsf))

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma modalKnownWorlds_toFinset_append`
(unavailable across files): the known-worlds `Finset` under append splits as a union. -/
private lemma modalKnownWorlds_toFinset_append_S5
    (xs b : List (SignedFormula (Proposition Atom) WorldIndex)) :
    (modalKnownWorlds (xs ++ b)).toFinset =
      (xs.map SignedFormula.label).toFinset ∪ (modalKnownWorlds b).toFinset := by
  ext x
  simp only [Finset.mem_union, List.mem_toFinset, mem_modalKnownWorlds_S5, List.mem_append,
    List.mem_map]
  constructor
  · rintro ⟨sf, hsf | hsf, rfl⟩
    · exact Or.inl ⟨sf, hsf, rfl⟩
    · exact Or.inr ⟨sf, hsf, rfl⟩
  · rintro (⟨sf, hsf, rfl⟩ | ⟨sf, hsf, rfl⟩)
    · exact ⟨sf, Or.inl hsf, rfl⟩
    · exact ⟨sf, Or.inr hsf, rfl⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- If every label of `xs` is already a known world of `b`, appending `xs` doesn't change the
known-worlds COUNT (mirrors `FmpMeasure.lean`'s private `modalKnownWorlds_perm_append_of_subset`,
stated at the length level rather than up to `Perm`). -/
private lemma modalKnownWorlds_length_append_of_known_S5
    (xs b : List (SignedFormula (Proposition Atom) WorldIndex))
    (h : ∀ sf ∈ xs, sf.label ∈ modalKnownWorlds b) :
    (modalKnownWorlds (xs ++ b)).length = (modalKnownWorlds b).length := by
  rw [← List.toFinset_card_of_nodup (modalKnownWorlds_nodup_S5 (xs ++ b)),
    ← List.toFinset_card_of_nodup (modalKnownWorlds_nodup_S5 b),
    modalKnownWorlds_toFinset_append_S5]
  have hsub : (xs.map SignedFormula.label).toFinset ⊆ (modalKnownWorlds b).toFinset := by
    intro x hx
    simp only [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨sf, hsf, rfl⟩ := hx
    simpa using h sf hsf
  rw [Finset.union_eq_right.mpr hsub]

omit [DecidableEq Atom] [Hashable Atom] in
/-- If `xs` is nonempty and all its labels equal a fresh world `w'` not already known, appending
`xs` grows the known-worlds COUNT by exactly 1 (mirrors `FmpMeasure.lean`'s private
`modalKnownWorlds_perm_append_single`, stated at the length level). -/
private lemma modalKnownWorlds_length_append_single_S5
    (xs b : List (SignedFormula (Proposition Atom) WorldIndex)) (w' : WorldIndex)
    (hxsne : xs ≠ []) (hxs : ∀ sf ∈ xs, sf.label = w') (hw' : w' ∉ modalKnownWorlds b) :
    (modalKnownWorlds (xs ++ b)).length = (modalKnownWorlds b).length + 1 := by
  rw [← List.toFinset_card_of_nodup (modalKnownWorlds_nodup_S5 (xs ++ b)),
    ← List.toFinset_card_of_nodup (modalKnownWorlds_nodup_S5 b),
    modalKnownWorlds_toFinset_append_S5]
  have hxseq : (xs.map SignedFormula.label).toFinset = {w'} := by
    ext x
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_singleton]
    constructor
    · rintro ⟨sf, hsf, rfl⟩; exact hxs sf hsf
    · intro hxeq
      obtain ⟨sf, hsf⟩ := List.exists_mem_of_ne_nil xs hxsne
      exact ⟨sf, hsf, hxeq ▸ (hxs sf hsf)⟩
  rw [hxseq, Finset.singleton_union, Finset.card_insert_of_notMem (by simpa using hw')]

/-- **`bClosure` support**: every signed formula emitted by `modalApplyOneS5 sf b acc` (NOT just
K's own `modalApplyOne`) stays inside `U_{S5}(φ₀)`. At the two S5-relevant shapes, combines K's
own closure (`modalApplyOne_outputs_subset_S5`) for the `boxPropagation`/`diamondNeg`-sourced
formulas with a direct bound for the S5-merged `modalS5BoxAll`/`modalS5DiaNegAll` formulas
(same formula `φ` as the box/diamond body, subformula-closed via `modalSubfmls_trans_S5`; label a
known world of `b`, hence `≤ modalMaxWorld b < modalWorldBoundS5 φ₀`). At every other shape,
`modalApplyOneS5` agrees with `modalApplyOne` exactly
(`modalApplyOneS5_eq_of_not_boxPos_diaNeg`), so `modalApplyOne_outputs_subset_S5` transfers
directly. -/
lemma modalApplyOneS5_outputs_subset
    (φ₀ : Proposition Atom) (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS5 φ₀) (hsf : sf ∈ b)
    (hInv : accFreshInv b acc)
    (hW : modalMaxWorld b < modalWorldBoundS5 φ₀) :
    (match (modalApplyOneS5 sf b acc).fst with
      | .linear formulas => ∀ x ∈ formulas, x ∈ modalUniverseS5 φ₀
      | .branching branches => ∀ x ∈ branches.flatten, x ∈ modalUniverseS5 φ₀
      | .persistent formulas => ∀ x ∈ formulas, x ∈ modalUniverseS5 φ₀
      | .notApplicable => True) := by
  by_cases hbd : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hbd with ⟨hs, φ, hf⟩ | ⟨hs, φ, hf⟩
    · obtain ⟨s, ff, l⟩ := sf
      simp only at hs hf
      subst hs; subst hf
      have hKsub := modalApplyOne_outputs_subset_S5 φ₀
        (⟨.pos, .box φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hb hsf hInv hW
      have hKeq := modalApplyOne_boxPos_eq
        (⟨.pos, .box φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
      have hsrc : (Proposition.box φ) ∈ modalSubfmls φ₀ := modalUniverseS5_mem_formula (hb _ hsf)
      have hφmem : φ ∈ modalSubfmls (Proposition.box φ) :=
        List.mem_cons_of_mem _ (modalSubfmls_self_mem_S5 φ)
      have hφsub : φ ∈ modalSubfmls φ₀ := modalSubfmls_trans_S5 hφmem hsrc
      have hallNewSub : ∀ x ∈ modalS5BoxAll b φ l, x ∈ modalUniverseS5 φ₀ := by
        intro x hx
        obtain ⟨hxeq, hxknown, -⟩ := modalS5BoxAll_mem hx
        rw [hxeq]
        refine mem_modalUniverseS5_of ?_ hφsub
        obtain ⟨sf0, hsf0, hlab⟩ := (mem_modalKnownWorlds_S5 b x.label).mp hxknown
        calc x.label ≤ modalMaxWorld b := hlab ▸ label_le_modalMaxWorld hsf0
          _ ≤ modalWorldBoundS5 φ₀ := le_of_lt hW
      unfold modalApplyOneS5
      rcases hp : modalApplyOne
          (⟨.pos, .box φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
          with ⟨kResult, kAcc⟩
      rw [hp] at hKsub hKeq
      dsimp only at hKsub
      simp only at hKeq
      rcases hKeq with hKeq | ⟨out0, hKeq⟩ <;> subst hKeq
      · dsimp only
        split_ifs with hemp
        · trivial
        · exact fun x hx => hallNewSub x hx
      · dsimp only
        intro x hx
        simp only [List.mem_append, List.mem_filter] at hx
        rcases hx with hx | ⟨hx, -⟩
        · exact hKsub x hx
        · exact hallNewSub x hx
    · obtain ⟨s, ff, l⟩ := sf
      simp only at hs hf
      subst hs; subst hf
      have hKsub := modalApplyOne_outputs_subset_S5 φ₀
        (⟨.neg, .diamond φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hb hsf hInv hW
      have hKeq := modalApplyOne_diamondNeg_eq
        (⟨.neg, .diamond φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
      have hsrc : (Proposition.diamond φ) ∈ modalSubfmls φ₀ :=
        modalUniverseS5_mem_formula (hb _ hsf)
      have hφmem : φ ∈ modalSubfmls (Proposition.diamond φ) :=
        List.mem_cons_of_mem _ (modalSubfmls_self_mem_S5 φ)
      have hφsub : φ ∈ modalSubfmls φ₀ := modalSubfmls_trans_S5 hφmem hsrc
      have hallNewSub : ∀ x ∈ modalS5DiaNegAll b φ l, x ∈ modalUniverseS5 φ₀ := by
        intro x hx
        obtain ⟨hxeq, hxknown, -⟩ := modalS5DiaNegAll_mem hx
        rw [hxeq]
        refine mem_modalUniverseS5_of ?_ hφsub
        obtain ⟨sf0, hsf0, hlab⟩ := (mem_modalKnownWorlds_S5 b x.label).mp hxknown
        calc x.label ≤ modalMaxWorld b := hlab ▸ label_le_modalMaxWorld hsf0
          _ ≤ modalWorldBoundS5 φ₀ := le_of_lt hW
      unfold modalApplyOneS5
      rcases hp : modalApplyOne
          (⟨.neg, .diamond φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
          with ⟨kResult, kAcc⟩
      rw [hp] at hKsub hKeq
      dsimp only at hKsub
      simp only at hKeq
      rcases hKeq with hKeq | ⟨out0, hKeq⟩ <;> subst hKeq
      · dsimp only
        split_ifs with hemp
        · trivial
        · exact fun x hx => hallNewSub x hx
      · dsimp only
        intro x hx
        simp only [List.mem_append, List.mem_filter] at hx
        rcases hx with hx | ⟨hx, -⟩
        · exact hKsub x hx
        · exact hallNewSub x hx
  · have hnbox : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) := fun hc => hbd (Or.inl hc)
    have hndia : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) := fun hc => hbd (Or.inr hc)
    rw [modalApplyOneS5_eq_of_not_boxPos_diaNeg sf b acc ⟨hnbox, hndia⟩]
    exact modalApplyOne_outputs_subset_S5 φ₀ sf b acc hb hsf hInv hW


-- ARCHIVED from Cslib/Logics/Modal/Tableau/S5Simplification.lean:2666-3839
-- Retired: 2026-07-16, task 515 phase 14 (plan v4)
-- Superseded by: `ModalLoopInvHintikka` at `Aux := ModalLoopAuxS5w` (`CompletenessLoop.lean`), whose `aux` field is just `S5wTagInv φ₀ b ∧ S5wWorldInv φ₀ b`
-- Why retired: an invariant of the KEYED stepper `modalStepBranchS5gKeyed` (cluster 03), which no driver runs, and whose twelve fields were needed only to feed the powerset pigeonhole. The parametric Hintikka lift takes an opaque `Aux`, and S5w's instantiation discharges in two lines with no rank map.
-- Status at retirement: CI-green, sorry-free, zero axioms beyond propext/Classical.choice/Quot.sound
-- Recover a compiling version at: git show af59318098f7ed0eceb7a33634d072babb45b603 -- Cslib/Logics/Modal/Tableau/S5Simplification.lean

/-! ## The S5 Loop Invariant `S5LoopInv` (task 515 Phase 3, v2: extended to ten fields)

**v2 crux change**: extends the v1 four-field `S5LoopInv` to the full ten-field shape mirroring
the landed `S4LoopInv` (`LoopChecking.lean:1127`), adding the six generic driver-bookkeeping
fields (`bClosure`/`eNodup`/`eClosure`/`accFresh`/`accKnown`/`outDegEq`) the v1 four-field
structure lacked. `accKnown` (= `accTargetsKnown`) is the exact standing hypothesis
`modalApplyOne_knownWorlds_step` (`FmpMeasure.lean:2042`) demands; `bClosure` (⊆
`modalUniverseS5 φ₀`) supplies the subformula-closure fact needed to place a newly-inserted
birth-key pair inside `signedSubfmls φ₀`. The four birth-key fields are carried unchanged from
v1 (same statements), but `keysDistinct` is now discharged by the keys-aware guard
(`blockingWorldS5Keyed_none_fresh`) rather than resisting as in the v1 live-set design. -/

/-- **v2 extended structure**: `S5LoopInv` mirrors `S4LoopInv`'s ten fields
(`LoopChecking.lean:1127`) exactly, `S4` swapped for `S5` throughout (`modalUniverseS4` ->
`modalUniverseS5`), stated over the threaded `keys` list (`modalStepBranchS5gKeyed`) rather than
the live branch for the four birth-key fields. -/
structure S5LoopInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) : Prop where
  /-- Every branch formula is a member of the fixed finite S5 universe `U_{S5}(φ₀)`. -/
  bClosure : ∀ x ∈ b, x ∈ modalUniverseS5 φ₀
  /-- The expanded set has no duplicate entries. -/
  eNodup : e.Nodup
  /-- Every expanded-set formula is a member of `U_{S5}(φ₀)`. -/
  eClosure : ∀ x ∈ e, x ∈ modalUniverseS5 φ₀
  /-- All of `acc`'s recorded worlds are `< modalNextWorld b`. -/
  accFresh : accFreshInv b acc
  /-- Every `acc`-edge target is a label already appearing on the branch. -/
  accKnown : accTargetsKnown b acc
  /-- `outDeg` exactly counts the minting-shaped formulas in `e` at each world. -/
  outDegEq : ∀ w, outDeg acc w = (e.filter (fun x => x.label == w && isMintingShaped x)).length
  /-- Every known world has a recorded birth key. -/
  keysTotal : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys
  /-- A world's recorded birth key is a LOWER BOUND on its live relevant set: monotone-stable,
  since birth keys never change after a world is born and live relevant sets only grow
  (`relevantSetFinset_mono`). -/
  keyLowerBd : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w
  /-- Distinct worlds have DISTINCT birth keys: the hypothesis the pigeonhole argument
  (`modalKnownWorlds_length_le_worldBoundS5`, Phase 6) consumes. Now discharged via the
  keys-aware guard (`blockingWorldS5Keyed_none_fresh`), not live-set reasoning. -/
  keysDistinct : ∀ w w' k k', (w, k) ∈ keys → (w', k') ∈ keys → w ≠ w' → k ≠ k'
  /-- Birth keys are drawn from the powerset of the finite signed-subformula codomain
  `signedSubfmls φ₀`: the pigeonhole argument's injection target (Phase 6). -/
  keysInUniverse : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀
  /-- Every recorded key's world is a known world of the branch: the fact
  `blockingWorldS5Keyed`'s stored-key guard needs (in place of `blockingWorldS5`'s free
  `blockingWorldS5_mem_modalKnownWorlds` corollary of filtering over `modalKnownWorlds b`
  directly) to justify that a loop-back edge to a stored key's world targets a known world
  (feeds `accKnown` preservation, Phase 4). Maintained alongside `keysTotal` as the converse
  membership direction; both grow only by appending a freshly-minted, immediately-known world. -/
  keysKnown : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b
  /-- **12th field (deviation, cycle-3 addition)**: known-world labels form a CONTIGUOUS range
  `{0, ..., modalMaxWorld b}` -- worlds are only ever minted at exactly
  `modalNextWorld b = modalMaxWorld b + 1`, so the known-world COUNT equals `modalMaxWorld b + 1`
  exactly, with no gaps. Needed because Phase 6's pigeonhole bound
  (`modalKnownWorlds_length_le_worldBoundS5`) only bounds the known-world *count*, but
  `bClosure`/`eClosure`'s mint-case obligation needs a bound on the fresh label's *value*
  (`modalNextWorld b ≤ modalWorldBoundS5 φ₀`); contiguity is exactly the bridge (see
  `specs/515_.../handoffs/02_phase4-bclosure-contiguity-gap.md`). -/
  worldsContiguous : modalMaxWorld b + 1 = (modalKnownWorlds b).length

/-! ## Generic-Field Preservation Lemmas (task 515 Phase 4)

Proves that a `modalStepBranchS5gKeyed` step preserves the six generic (rule-independent)
`S5LoopInv` fields. **No template**: the existing generic `_gen` wrappers
(`modalStepBranch_preserves_accTargetsKnown_gen`, `modalStepBranch_knownWorlds_gen`, etc.,
`FmpMeasure.lean`) all presuppose the `hFreshLocal` dichotomy (`acc` unchanged, or exactly one
edge to a genuinely FRESH world) -- but the keyed guard's *blocked* case adds a loop-back edge to
an *existing* (known, non-fresh) world, which fits neither disjunct. So these lemmas are proved
directly by case analysis on `modalStepBranchS5gKeyed`'s own three-way dispatch (blocked / mint /
non-minting), reusing K's own per-call lemmas (`modalApplyOne_knownWorlds_step`,
`modalApplyOne_boxNeg_witness`/`_diamondPos_witness`) on the shapes where the keyed stepper
provably agrees with K, rather than routing through the generic wrappers. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `Soundness.lean`'s `private lemma hasEdge_addEdge_cases`
(unavailable across files): decompose membership of an edge in `acc.addEdge w w'`. Mirrors
`BDriver.lean`'s `hasEdge_addEdge_cases_B`. -/
private lemma hasEdge_addEdge_cases_S5 {acc : Accessibility} {w w' a a' : WorldIndex}
    (h : (acc.addEdge w w').hasEdge a a' = true) :
    (a = w ∧ a' = w') ∨ acc.hasEdge a a' = true := by
  simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq] at h
  tauto

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma outDeg_addEdge_self` (unavailable
across files): `outDeg` under `addEdge` at the matching source extends the successor list by
exactly the new target, incrementing `outDeg` by 1. -/
private lemma outDeg_addEdge_self_S5 (acc : Accessibility) (w wf : WorldIndex) :
    outDeg (acc.addEdge w wf) w = outDeg acc w + 1 := by
  simp [outDeg, Accessibility.successorsOf, Accessibility.addEdge]

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma outDeg_addEdge_ne` (unavailable
across files): `outDeg` under `addEdge` is unchanged at any world other than the edge's
source. -/
private lemma outDeg_addEdge_ne_S5 (acc : Accessibility) (w wf w' : WorldIndex) (h : w' ≠ w) :
    outDeg (acc.addEdge w wf) w' = outDeg acc w' := by
  simp only [outDeg, Accessibility.successorsOf, Accessibility.addEdge, List.filterMap_cons]
  have : (w == w') = false := by simp only [beq_eq_false_iff_ne]; exact fun heq => h heq.symm
  simp [this]

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma filter_minting_append_of_minting_at`
(unavailable across files): appending a minting-shaped formula at label `sf.label` to the
expanded set extends the minting-filtered count at `sf.label` by exactly the singleton `[sf]`. -/
private lemma filter_minting_append_of_minting_at_S5
    (e : List (SignedFormula (Proposition Atom) WorldIndex))
    (sf : SignedFormula (Proposition Atom) WorldIndex) (h : isMintingShaped sf = true) :
    (e ++ [sf]).filter (fun x => x.label == sf.label && isMintingShaped x) =
      e.filter (fun x => x.label == sf.label && isMintingShaped x) ++ [sf] := by
  rw [List.filter_append]
  simp [h]

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma filter_minting_append_of_minting_ne`
(unavailable across files): appending a minting-shaped formula at label `sf.label` to the
expanded set leaves the minting-filtered count at any *other* world `w` unchanged. -/
private lemma filter_minting_append_of_minting_ne_S5
    (e : List (SignedFormula (Proposition Atom) WorldIndex))
    (sf : SignedFormula (Proposition Atom) WorldIndex) (w : WorldIndex) (hw : w ≠ sf.label) :
    (e ++ [sf]).filter (fun x => x.label == w && isMintingShaped x) =
      e.filter (fun x => x.label == w && isMintingShaped x) := by
  rw [List.filter_append]
  have : (sf.label == w) = false := by
    simp only [beq_eq_false_iff_ne]; exact fun h => hw h.symm
  simp [this]

omit [Hashable Atom] in
/-- Characterization of the expanded-set shape a `modalStepBranchS5gKeyed` step can produce:
every child expanded set is either `e ++ [sf]` (linear/blocked-loop-back-shaped) or `e` unchanged
(persistent-shaped), where `sf` is the trigger formula the step fired on and `sf ∉ e`. This is
the one fact all six generic-field preservation lemmas' `e`-component reasoning shares, so it is
factored out once. -/
private lemma modalStepBranchS5gKeyed_expanded_shape (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (newKeys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS5gKeyed φ₀ b e acc keys = some (newBs, newExps, newAcc, newKeys)) :
    ∃ sf ∈ b, sf ∉ e ∧ ∀ e' ∈ newExps, e' = e ++ [sf] ∨ e' = e := by
  unfold modalStepBranchS5gKeyed at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  clear hstep
  by_cases hexp : e.any (· == sf) = true
  · simp only [hexp, if_true] at hsf
    exact absurd hsf (by simp)
  · rw [if_neg (by simpa using hexp)] at hsf
    refine ⟨sf, hsfmem, by simpa using hexp, ?_⟩
    clear hsfmem hexp
    split at hsf <;> repeat' split at hsf
    all_goals try injection hsf
    all_goals
      (rename_i hsf
       simp only [Prod.mk.injEq] at hsf
       intro e' he'
       first
       | (rw [← hsf.2.1] at he'; simp only [List.mem_singleton] at he'; exact Or.inl he')
       | (rw [← hsf.2.1] at he'
          obtain ⟨br, -, rfl⟩ := List.mem_map.mp he'; exact Or.inl rfl)
       | (rw [← hsf.2.1] at he'; simp only [List.mem_singleton] at he'; exact Or.inr he'))

omit [Hashable Atom] in
/-- Characterization of the accessibility/branch-list shape a `modalStepBranchS5gKeyed` step
can produce (mirrors `modalStepBranchS5gKeyed_expanded_shape`'s pattern for the `newAcc`/`newBs`
components instead of `newExps`). Every step is either a **blocked** (loop-back) step --
`newBs = [b]` unchanged, `newAcc = acc.addEdge sf.label wBlock` for a *known* `wBlock` -- or a
step whose accessibility output is exactly `(modalApplyOneS5 sf b acc).snd` (uniformly,
regardless of whether `sf` is one of the two K-minting shapes or any other shape, by
`modalApplyOneS5_snd_eq`), with `newBs` built from `(modalApplyOneS5 sf b acc).fst`'s
`RuleResult` shape the same three ways `modalStepBranchS5gKeyed_expanded_shape` characterizes
`newExps`. Shared case dispatch for the remaining Phase 4 fields
(`accFresh`/`accKnown`/`outDegEq`). -/
private lemma modalStepBranchS5gKeyed_acc_shape (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (newKeys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS5gKeyed φ₀ b e acc keys = some (newBs, newExps, newAcc, newKeys))
    (hkK : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b) :
    ∃ sf ∈ b, sf ∉ e ∧
      ((∃ wBlock, wBlock ∈ modalKnownWorlds b ∧ newAcc = acc.addEdge sf.label wBlock ∧
          newBs = [b] ∧ newExps = [e ++ [sf]] ∧ isMintingShaped sf = true) ∨
       (newAcc = (modalApplyOneS5 sf b acc).snd ∧
        (match (modalApplyOneS5 sf b acc).fst with
          | .linear nf => newBs = [nf ++ b] ∧ newExps = [e ++ [sf]]
          | .branching brs => newBs = brs.map (· ++ b) ∧ newExps = brs.map (fun _ => e ++ [sf])
          | .persistent nf => newBs = [nf ++ b] ∧ newExps = [e]
          | .notApplicable => False))) := by
  unfold modalStepBranchS5gKeyed at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  clear hstep
  by_cases hexp : e.any (· == sf) = true
  · simp only [hexp, if_true] at hsf
    exact absurd hsf (by simp)
  · rw [if_neg (by simpa using hexp)] at hsf
    refine ⟨sf, hsfmem, by simpa using hexp, ?_⟩
    clear hexp
    split at hsf <;> repeat' split at hsf
    all_goals try injection hsf
    all_goals (rename_i hsf; simp only [Prod.mk.injEq] at hsf)
    all_goals first
      | (refine Or.inl ⟨_, ?_, hsf.2.2.1.symm, hsf.1.symm, hsf.2.1.symm, ?_⟩
         · exact hkK _ _
             (blockingWorldS5Keyed_eq_birthContent φ₀ keys b _ _ sf.label _ (by assumption))
         · unfold isMintingShaped; simp_all)
      | (refine Or.inr ⟨?_, ?_⟩
         · rw [show modalApplyOneS5 sf b acc = _ from by assumption]
           exact hsf.2.2.1.symm
         · rw [show modalApplyOneS5 sf b acc = _ from by assumption]
           exact ⟨by simpa using hsf.1.symm, by simpa using hsf.2.1.symm⟩)

omit [Hashable Atom] in
/-- Characterization of the birth-key list shape a `modalStepBranchS5gKeyed` step can produce:
`newKeys` is either `keys` unchanged (blocked step, or any non-minting shape), or `keys` grown
by exactly one fresh entry `(modalNextWorld b, successorBirthContentS5 φ₀ b s φ sf.label)` at
one of the two K-minting shapes (`F(□φ)@w`/`T(◇φ)@w`) when the keyed guard is unblocked. Shared
case dispatch for Phase 5's four birth-key preservation lemmas. -/
private lemma modalStepBranchS5gKeyed_keys_shape (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (newKeys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS5gKeyed φ₀ b e acc keys = some (newBs, newExps, newAcc, newKeys)) :
    ∃ sf ∈ b, sf ∉ e ∧
      (newKeys = keys ∨
        (∃ φ, sf.sign = .neg ∧ sf.formula = .box φ ∧
          blockingWorldS5Keyed φ₀ keys b .neg φ sf.label = none ∧
          newKeys =
            keys ++ [(modalNextWorld b, successorBirthContentS5 φ₀ b .neg φ sf.label)]) ∨
        (∃ φ, sf.sign = .pos ∧ sf.formula = .diamond φ ∧
          blockingWorldS5Keyed φ₀ keys b .pos φ sf.label = none ∧
          newKeys =
            keys ++ [(modalNextWorld b, successorBirthContentS5 φ₀ b .pos φ sf.label)])) := by
  unfold modalStepBranchS5gKeyed at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  clear hstep
  by_cases hexp : e.any (· == sf) = true
  · simp only [hexp, if_true] at hsf
    exact absurd hsf (by simp)
  · rw [if_neg (by simpa using hexp)] at hsf
    refine ⟨sf, hsfmem, by simpa using hexp, ?_⟩
    clear hexp hsfmem
    split at hsf <;> repeat' split at hsf
    all_goals try injection hsf
    all_goals (rename_i hsf; simp only [Prod.mk.injEq] at hsf)
    all_goals first
      | (left; exact hsf.2.2.2.symm)
      | (right; left
         exact ⟨_, by assumption, by assumption, by assumption, hsf.2.2.2.symm⟩)
      | (right; right
         exact ⟨_, by assumption, by assumption, by assumption, hsf.2.2.2.symm⟩)

omit [Hashable Atom] in
/-- Combined characterization of a `modalStepBranchS5gKeyed` step, giving the `newBs`-shape (as
`modalStepBranchS5gKeyed_acc_shape` does) AND the `newKeys`-shape (as
`modalStepBranchS5gKeyed_keys_shape` does) from a SINGLE case split tied to the SAME triggering
`sf`. Needed by `keysTotal`'s preservation proof: `_acc_shape` and `_keys_shape` each
independently eliminate their own existential `sf` witness from `hstep`, so a caller composing
them as black boxes gets two a priori unrelated witnesses with no proof they coincide -- but
`keysTotal` must know that "the branch that grew" and "the key that got appended" belong to the
same step event. The wildcard (non-minting-shape) disjunct additionally records
`(modalApplyOneS5 sf b acc).snd = acc` (via `modalApplyOneS5_snd_eq_acc_of_not_mint_shape`),
which lets callers rule out `modalApplyOneS5_knownWorlds_step`'s mint disjunct on those shapes. -/
private lemma modalStepBranchS5gKeyed_keys_full_shape (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (newKeys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS5gKeyed φ₀ b e acc keys = some (newBs, newExps, newAcc, newKeys)) :
    ∃ sf ∈ b, sf ∉ e ∧
      ((∃ wBlock, newAcc = acc.addEdge sf.label wBlock ∧ newBs = [b] ∧ newKeys = keys) ∨
       (newKeys = keys ∧ (modalApplyOneS5 sf b acc).snd = acc ∧
        (match (modalApplyOneS5 sf b acc).fst with
          | .linear nf => newBs = [nf ++ b]
          | .branching brs => newBs = brs.map (· ++ b)
          | .persistent nf => newBs = [nf ++ b]
          | .notApplicable => False)) ∨
       (∃ φ', sf.sign = .neg ∧ sf.formula = .box φ' ∧
          blockingWorldS5Keyed φ₀ keys b .neg φ' sf.label = none ∧
          newKeys = keys ++ [(modalNextWorld b, successorBirthContentS5 φ₀ b .neg φ' sf.label)] ∧
          (match (modalApplyOneS5 sf b acc).fst with
            | .linear nf => newBs = [nf ++ b]
            | .branching brs => newBs = brs.map (· ++ b)
            | .persistent nf => newBs = [nf ++ b]
            | .notApplicable => False)) ∨
       (∃ φ', sf.sign = .pos ∧ sf.formula = .diamond φ' ∧
          blockingWorldS5Keyed φ₀ keys b .pos φ' sf.label = none ∧
          newKeys = keys ++ [(modalNextWorld b, successorBirthContentS5 φ₀ b .pos φ' sf.label)] ∧
          (match (modalApplyOneS5 sf b acc).fst with
            | .linear nf => newBs = [nf ++ b]
            | .branching brs => newBs = brs.map (· ++ b)
            | .persistent nf => newBs = [nf ++ b]
            | .notApplicable => False))) := by
  unfold modalStepBranchS5gKeyed at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  clear hstep
  by_cases hexp : e.any (· == sf) = true
  · simp only [hexp, if_true] at hsf
    exact absurd hsf (by simp)
  · rw [if_neg (by simpa using hexp)] at hsf
    refine ⟨sf, hsfmem, by simpa using hexp, ?_⟩
    clear hexp hsfmem
    split at hsf <;> repeat' split at hsf
    all_goals try injection hsf
    all_goals (rename_i hsf; simp only [Prod.mk.injEq] at hsf)
    all_goals first
      | (refine Or.inl ⟨_, hsf.2.2.1.symm, hsf.1.symm, hsf.2.2.2.symm⟩)
      | (refine Or.inr (Or.inr (Or.inl
           ⟨_, by assumption, by assumption, by assumption, hsf.2.2.2.symm, ?_⟩))
         rw [show modalApplyOneS5 sf b acc = _ from by assumption]
         simpa using hsf.1.symm)
      | (refine Or.inr (Or.inr (Or.inr
           ⟨_, by assumption, by assumption, by assumption, hsf.2.2.2.symm, ?_⟩))
         rw [show modalApplyOneS5 sf b acc = _ from by assumption]
         simpa using hsf.1.symm)
      | (refine Or.inr (Or.inl ⟨hsf.2.2.2.symm,
           modalApplyOneS5_snd_eq_acc_of_not_mint_shape sf b acc
             ⟨by rintro ⟨hs, ψ, hf⟩; simp_all, by rintro ⟨hs, ψ, hf⟩; simp_all⟩, ?_⟩)
         rw [show modalApplyOneS5 sf b acc = _ from by assumption]
         simpa using hsf.1.symm)

omit [Hashable Atom] in
/-- **Phase 4 field 1/6**: `modalStepBranchS5gKeyed` preserves `e.Nodup`. Rule-agnostic: the
new expanded set is always either `e ++ [sf]` (with `sf ∉ e` from the stepper's own dedup guard)
or `e` unchanged, across all three of the stepper's top-level cases. -/
lemma modalStepBranchS5g_preserves_eNodup (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (newKeys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS5gKeyed φ₀ b e acc keys = some (newBs, newExps, newAcc, newKeys))
    (henodup : e.Nodup) :
    ∀ e' ∈ newExps, e'.Nodup := by
  obtain ⟨sf, -, hsfnotin, hshape⟩ :=
    modalStepBranchS5gKeyed_expanded_shape φ₀ b e acc keys newBs newExps newAcc newKeys hstep
  intro e' he'
  rcases hshape e' he' with rfl | rfl
  · rw [List.nodup_append]
    refine ⟨henodup, List.nodup_singleton sf, ?_⟩
    intro a ha y hy
    simp only [List.mem_singleton] at hy
    subst hy
    intro heq
    subst heq
    exact hsfnotin ha
  · exact henodup

/-- **Phase 4 field 2/6**: `modalStepBranchS5gKeyed` preserves `accFreshInv`. Blocked (loop-back)
steps add an edge to a *known* world (`S5LoopInv.keysKnown`), which is `< modalNextWorld b`
since every known world is some branch formula's label (`modalNextWorld_gt`); non-blocked steps
either leave `acc` unchanged (`modalNextWorld` only grows under branch prepend,
`modalNextWorld_le_append`) or mint a fresh edge to `modalNextWorld b` itself, which becomes
`< modalNextWorld b'` once `b'` contains the freshly-labeled witness formula
(`modalApplyOne_knownWorlds_step`'s mint disjunct, lifted to `modalApplyOneS5` via
`modalApplyOneS5_eq_of_linear`). -/
lemma modalStepBranchS5g_preserves_accFresh (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (newKeys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS5gKeyed φ₀ b e acc keys = some (newBs, newExps, newAcc, newKeys))
    (hkK : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hknown : accTargetsKnown b acc) (hfresh : accFreshInv b acc) :
    ∀ b' ∈ newBs, accFreshInv b' newAcc := by
  obtain ⟨sf, hsfmem, -, hcase⟩ :=
    modalStepBranchS5gKeyed_acc_shape φ₀ b e acc keys newBs newExps newAcc newKeys hstep hkK
  rcases hcase with ⟨wBlock, hwBlock, hnewAcc, hnewBs, -, -⟩ | ⟨hnewAcc, hshape⟩
  · subst hnewAcc
    intro b' hb'
    rw [hnewBs] at hb'
    simp only [List.mem_singleton] at hb'
    rw [hb']
    intro w w' hedge
    rcases hasEdge_addEdge_cases_S5 hedge with ⟨hw1, hw2⟩ | hold
    · rw [hw1, hw2]
      refine ⟨modalNextWorld_gt b sf hsfmem, ?_⟩
      obtain ⟨sfw, hsfw, hsfwl⟩ := (mem_modalKnownWorlds_S5 b wBlock).mp hwBlock
      exact hsfwl ▸ modalNextWorld_gt b sfw hsfw
    · exact hfresh w w' hold
  · have hbb' : ∀ b' ∈ newBs, ∃ xs, b' = xs ++ b := by
      intro b' hb'
      rcases hm : (modalApplyOneS5 sf b acc).fst with nf | brs | nf | -
      · rw [hm] at hshape; rw [hshape.1] at hb'
        simp only [List.mem_singleton] at hb'; exact ⟨nf, hb'⟩
      · rw [hm] at hshape; rw [hshape.1] at hb'
        obtain ⟨br, -, rfl⟩ := List.mem_map.mp hb'; exact ⟨br, rfl⟩
      · rw [hm] at hshape; rw [hshape.1] at hb'
        simp only [List.mem_singleton] at hb'; exact ⟨nf, hb'⟩
      · rw [hm] at hshape; exact absurd hshape (by simp)
    rcases modalApplyOne_knownWorlds_step sf b acc hsfmem hknown with
      ⟨hsndeq, -⟩ | ⟨hsndeq, hmatch⟩
    · rw [hnewAcc, modalApplyOneS5_snd_eq sf b acc, hsndeq]
      intro b' hb' w w' hedge
      obtain ⟨xs, rfl⟩ := hbb' b' hb'
      obtain ⟨hw, hw'⟩ := hfresh w w' hedge
      exact ⟨lt_of_lt_of_le hw (modalNextWorld_le_append xs b),
             lt_of_lt_of_le hw' (modalNextWorld_le_append xs b)⟩
    · rcases hkf : (modalApplyOne sf b acc).fst with formulas | brs | nf | -
      · rw [hkf] at hmatch
        obtain ⟨hne, hlabel⟩ := hmatch
        have heqS5 := modalApplyOneS5_eq_of_linear sf b acc formulas hkf
        rw [hnewAcc, modalApplyOneS5_snd_eq sf b acc, hsndeq]
        intro b' hb'
        have hfst : (modalApplyOneS5 sf b acc).fst = RuleResult.linear formulas := by
          rw [heqS5]; exact hkf
        rw [hfst] at hshape
        rw [hshape.1] at hb'
        simp only [List.mem_singleton] at hb'
        rw [hb']
        cases formulas with
        | nil => exact absurd rfl hne
        | cons x0 rest =>
          have hx0mem : x0 ∈ x0 :: rest := List.mem_cons_self
          have hx0label := hlabel x0 hx0mem
          have hx0memb' : x0 ∈ (x0 :: rest) ++ b := List.mem_append_left b hx0mem
          have hgrow : modalNextWorld b < modalNextWorld ((x0 :: rest) ++ b) := by
            have hh := modalNextWorld_gt ((x0 :: rest) ++ b) x0 hx0memb'
            rwa [hx0label] at hh
          intro w w' hedge
          rcases hasEdge_addEdge_cases_S5 hedge with ⟨rfl, rfl⟩ | hold
          · exact ⟨lt_trans (modalNextWorld_gt b sf hsfmem) hgrow, hgrow⟩
          · obtain ⟨hw, hw'⟩ := hfresh w w' hold
            exact ⟨lt_trans hw hgrow, lt_trans hw' hgrow⟩
      · rw [hkf] at hmatch; exact hmatch.elim
      · rw [hkf] at hmatch; exact hmatch.elim
      · rw [hkf] at hmatch; exact hmatch.elim

/-- **Phase 4 field 3/6**: `modalStepBranchS5gKeyed` preserves `accTargetsKnown`. Blocked
(loop-back) steps add an edge to a known world directly (`S5LoopInv.keysKnown`); non-blocked
steps either leave `acc` unchanged (old targets stay known since the branch only grows,
`modalKnownWorlds_mono_append_S5`) or mint a fresh edge to `modalNextWorld b`, immediately known
on the grown branch since it is the freshly-labeled witness formula's own label. -/
lemma modalStepBranchS5g_preserves_accKnown (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (newKeys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS5gKeyed φ₀ b e acc keys = some (newBs, newExps, newAcc, newKeys))
    (hkK : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hknown : accTargetsKnown b acc) :
    ∀ b' ∈ newBs, accTargetsKnown b' newAcc := by
  obtain ⟨sf, hsfmem, -, hcase⟩ :=
    modalStepBranchS5gKeyed_acc_shape φ₀ b e acc keys newBs newExps newAcc newKeys hstep hkK
  rcases hcase with ⟨wBlock, hwBlock, hnewAcc, hnewBs, -, -⟩ | ⟨hnewAcc, hshape⟩
  · subst hnewAcc
    intro b' hb'
    rw [hnewBs] at hb'
    simp only [List.mem_singleton] at hb'
    rw [hb']
    intro w w' hedge
    rcases hasEdge_addEdge_cases_S5 hedge with ⟨hw1, hw2⟩ | hold
    · rw [hw2]; exact hwBlock
    · exact hknown w w' hold
  · have hbb' : ∀ b' ∈ newBs, ∃ xs, b' = xs ++ b := by
      intro b' hb'
      rcases hm : (modalApplyOneS5 sf b acc).fst with nf | brs | nf | -
      · rw [hm] at hshape; rw [hshape.1] at hb'
        simp only [List.mem_singleton] at hb'; exact ⟨nf, hb'⟩
      · rw [hm] at hshape; rw [hshape.1] at hb'
        obtain ⟨br, -, rfl⟩ := List.mem_map.mp hb'; exact ⟨br, rfl⟩
      · rw [hm] at hshape; rw [hshape.1] at hb'
        simp only [List.mem_singleton] at hb'; exact ⟨nf, hb'⟩
      · rw [hm] at hshape; exact absurd hshape (by simp)
    rcases modalApplyOne_knownWorlds_step sf b acc hsfmem hknown with
      ⟨hsndeq, -⟩ | ⟨hsndeq, hmatch⟩
    · rw [hnewAcc, modalApplyOneS5_snd_eq sf b acc, hsndeq]
      intro b' hb' w w' hedge
      obtain ⟨xs, rfl⟩ := hbb' b' hb'
      exact modalKnownWorlds_mono_append_S5 xs b w' (hknown w w' hedge)
    · rcases hkf : (modalApplyOne sf b acc).fst with formulas | brs | nf | -
      · rw [hkf] at hmatch
        obtain ⟨hne, hlabel⟩ := hmatch
        have heqS5 := modalApplyOneS5_eq_of_linear sf b acc formulas hkf
        rw [hnewAcc, modalApplyOneS5_snd_eq sf b acc, hsndeq]
        intro b' hb'
        have hfst : (modalApplyOneS5 sf b acc).fst = RuleResult.linear formulas := by
          rw [heqS5]; exact hkf
        rw [hfst] at hshape
        rw [hshape.1] at hb'
        simp only [List.mem_singleton] at hb'
        rw [hb']
        cases formulas with
        | nil => exact absurd rfl hne
        | cons x0 rest =>
          have hx0mem : x0 ∈ x0 :: rest := List.mem_cons_self
          have hx0label := hlabel x0 hx0mem
          have hx0memb' : x0 ∈ (x0 :: rest) ++ b := List.mem_append_left b hx0mem
          have hfreshknown : modalNextWorld b ∈ modalKnownWorlds ((x0 :: rest) ++ b) :=
            (mem_modalKnownWorlds_S5 _ _).mpr ⟨x0, hx0memb', hx0label⟩
          intro w w' hedge
          rcases hasEdge_addEdge_cases_S5 hedge with ⟨hw1, hw2⟩ | hold
          · rw [hw2]; exact hfreshknown
          · exact modalKnownWorlds_mono_append_S5 (x0 :: rest) b w' (hknown w w' hold)
      · rw [hkf] at hmatch; exact hmatch.elim
      · rw [hkf] at hmatch; exact hmatch.elim
      · rw [hkf] at hmatch; exact hmatch.elim

omit [Hashable Atom] in
/-- **Phase 4 field 4/6**: `modalStepBranchS5gKeyed` preserves the `outDeg`/expanded-set
minting-count correspondence. Blocked (loop-back) steps add an edge at the (minting-shaped)
trigger's own label, exactly matching the appended `[sf]` in the new expanded set
(`outDeg_addEdge_self`/`filter_minting_append_of_minting_at`); non-blocked steps reduce to K's
own per-call counting obligation (`modalApplyOne_outDeg_step`), whose `e`-growth/unchanged
dichotomy agrees with `modalStepBranchS5gKeyed`'s own (`modalApplyOneS5_eshape_eq`). -/
lemma modalStepBranchS5g_preserves_outDegEq (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (newKeys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS5gKeyed φ₀ b e acc keys = some (newBs, newExps, newAcc, newKeys))
    (hkK : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (houtdeg :
      ∀ w, outDeg acc w = (e.filter (fun x => x.label == w && isMintingShaped x)).length) :
    ∀ e' ∈ newExps, ∀ w, outDeg newAcc w =
      (e'.filter (fun x => x.label == w && isMintingShaped x)).length := by
  obtain ⟨sf, hsfmem, -, hcase⟩ :=
    modalStepBranchS5gKeyed_acc_shape φ₀ b e acc keys newBs newExps newAcc newKeys hstep hkK
  rcases hcase with ⟨wBlock, -, hnewAcc, -, hnewExps, hmint⟩ | ⟨hnewAcc, hshape⟩
  · subst hnewAcc
    intro e' he'
    rw [hnewExps] at he'
    simp only [List.mem_singleton] at he'
    subst he'
    intro w
    by_cases hw : w = sf.label
    · subst hw
      rw [outDeg_addEdge_self_S5, filter_minting_append_of_minting_at_S5 e sf hmint,
        houtdeg sf.label]
      simp
    · rw [outDeg_addEdge_ne_S5 acc sf.label wBlock w hw,
        filter_minting_append_of_minting_ne_S5 e sf w hw, houtdeg w]
  · rw [hnewAcc, modalApplyOneS5_snd_eq sf b acc]
    intro e' he' w
    have hfull : outDeg (modalApplyOne sf b acc).2 w =
        (List.filter (fun x => x.label == w && isMintingShaped x)
          (match (modalApplyOneS5 sf b acc).fst with
            | .linear _ => e ++ [sf]
            | .branching _ => e ++ [sf]
            | .persistent _ => e
            | .notApplicable => e)).length :=
      (modalApplyOne_outDeg_step sf b e acc houtdeg w).trans
        (congrArg (fun l => (List.filter (fun x => x.label == w && isMintingShaped x) l).length)
          (modalApplyOneS5_eshape_eq sf b e acc).symm)
    rw [hfull]
    rcases hm : (modalApplyOneS5 sf b acc).fst with nf | brs | nf | -
    · rw [hm] at hshape
      rw [hshape.2] at he'
      simp only [List.mem_singleton] at he'
      subst he'
      rfl
    · rw [hm] at hshape
      rw [hshape.2] at he'
      obtain ⟨br, -, rfl⟩ := List.mem_map.mp he'
      rfl
    · rw [hm] at hshape
      rw [hshape.2] at he'
      simp only [List.mem_singleton] at he'
      subst he'
      rfl
    · rw [hm] at hshape; exact hshape.elim

/-- **Phase 4 field 5/6 (12th `S5LoopInv` field, cycle-3 addition)**: `modalStepBranchS5gKeyed`
preserves `worldsContiguous` (`modalMaxWorld b + 1 = (modalKnownWorlds b).length`). Blocked
(loop-back) steps leave `b` unchanged, so both sides are trivially stable. Non-blocked steps
consume `modalApplyOneS5_knownWorlds_step`'s dichotomy: the non-mint case appends formulas at
already-known labels, so `modalMaxWorld`/the known-worlds COUNT are both unchanged
(`modalMaxWorld_append_eq_of_forall_le_S5`/`modalKnownWorlds_length_append_of_known_S5`); the
mint case appends a nonempty list of formulas all at exactly `modalNextWorld b`, incrementing
both `modalMaxWorld` and the known-worlds count by exactly 1
(`modalMaxWorld_append_single_S5`/`modalKnownWorlds_length_append_single_S5`). See handoff
`02_phase4-bclosure-contiguity-gap.md` for why this field is the key to unblocking
`bClosure`/`eClosure`. -/
lemma modalStepBranchS5g_preserves_worldsContiguous (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (newKeys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS5gKeyed φ₀ b e acc keys = some (newBs, newExps, newAcc, newKeys))
    (hkK : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hknown : accTargetsKnown b acc)
    (hcontig : modalMaxWorld b + 1 = (modalKnownWorlds b).length) :
    ∀ b' ∈ newBs, modalMaxWorld b' + 1 = (modalKnownWorlds b').length := by
  obtain ⟨sf, hsfmem, -, hcase⟩ :=
    modalStepBranchS5gKeyed_acc_shape φ₀ b e acc keys newBs newExps newAcc newKeys hstep hkK
  rcases hcase with ⟨wBlock, -, -, hnewBs, -, -⟩ | ⟨-, hshape⟩
  · intro b' hb'
    rw [hnewBs] at hb'
    simp only [List.mem_singleton] at hb'
    rw [hb']; exact hcontig
  · have hallxs : ∀ b' ∈ newBs, ∃ xs, b' = xs ++ b ∧
        ((∀ x ∈ xs, x.label ∈ modalKnownWorlds b) ∨
          (xs ≠ [] ∧ ∀ x ∈ xs, x.label = modalNextWorld b)) := by
      intro b' hb'
      rcases modalApplyOneS5_knownWorlds_step sf b acc hsfmem hknown with
        ⟨-, hmatch⟩ | ⟨-, hmatch⟩
      · rcases hm : (modalApplyOneS5 sf b acc).fst with nf | brs | nf | -
        · rw [hm] at hshape hmatch
          rw [hshape.1] at hb'
          simp only [List.mem_singleton] at hb'
          exact ⟨nf, hb', Or.inl hmatch⟩
        · rw [hm] at hshape hmatch
          rw [hshape.1] at hb'
          obtain ⟨br, hbr, rfl⟩ := List.mem_map.mp hb'
          refine ⟨br, rfl, Or.inl ?_⟩
          intro x hx
          exact hmatch x (List.mem_flatten.mpr ⟨br, hbr, hx⟩)
        · rw [hm] at hshape hmatch
          rw [hshape.1] at hb'
          simp only [List.mem_singleton] at hb'
          exact ⟨nf, hb', Or.inl hmatch⟩
        · rw [hm] at hshape; exact absurd hshape (by simp)
      · rcases hm : (modalApplyOneS5 sf b acc).fst with nf | brs | nf | -
        · rw [hm] at hshape hmatch
          rw [hshape.1] at hb'
          simp only [List.mem_singleton] at hb'
          exact ⟨nf, hb', Or.inr hmatch⟩
        · rw [hm] at hmatch; exact hmatch.elim
        · rw [hm] at hmatch; exact hmatch.elim
        · rw [hm] at hmatch; exact hmatch.elim
    intro b' hb'
    obtain ⟨xs, rfl, hxsfact⟩ := hallxs b' hb'
    rcases hxsfact with hknownxs | ⟨hne, hfreshxs⟩
    · have hmaxeq : modalMaxWorld (xs ++ b) = modalMaxWorld b :=
        modalMaxWorld_append_eq_of_forall_le_S5 xs b (fun sf' hsf' => by
          have hk := hknownxs sf' hsf'
          rw [mem_modalKnownWorlds_S5] at hk
          obtain ⟨sf0, hsf0, hlab⟩ := hk
          rw [← hlab]; exact label_le_modalMaxWorld hsf0)
      have hleneq : (modalKnownWorlds (xs ++ b)).length = (modalKnownWorlds b).length :=
        modalKnownWorlds_length_append_of_known_S5 xs b hknownxs
      rw [hmaxeq, hleneq]; exact hcontig
    · have hmaxeq : modalMaxWorld (xs ++ b) = modalNextWorld b :=
        modalMaxWorld_append_single_S5 xs b (modalNextWorld b) hne hfreshxs
          (Nat.lt_succ_self (modalMaxWorld b))
      have hleneq : (modalKnownWorlds (xs ++ b)).length = (modalKnownWorlds b).length + 1 :=
        modalKnownWorlds_length_append_single_S5 xs b (modalNextWorld b) hne hfreshxs
          (modalNextWorld_not_mem_modalKnownWorlds_S5 b)
      have hnext : modalNextWorld b = modalMaxWorld b + 1 := rfl
      rw [hmaxeq, hleneq, hnext, hcontig]

omit [Hashable Atom] in
/-- **Phase 4 field 6/6**: `modalStepBranchS5gKeyed` preserves `eClosure`
(`∀ x ∈ e, x ∈ modalUniverseS5 φ₀`). Easy given `bClosure`: the only formula ever appended to
`e` is the trigger `sf` itself (`modalStepBranchS5gKeyed_expanded_shape`), and `sf ∈ b`, so
`sf ∈ modalUniverseS5 φ₀` follows directly from the ambient `bClosure` hypothesis on `b` -- no
mint-case label-bound reasoning is needed at all (unlike `bClosure`'s own preservation). -/
lemma modalStepBranchS5g_preserves_eClosure (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (newKeys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS5gKeyed φ₀ b e acc keys = some (newBs, newExps, newAcc, newKeys))
    (hbClosure : ∀ x ∈ b, x ∈ modalUniverseS5 φ₀)
    (heClosure : ∀ x ∈ e, x ∈ modalUniverseS5 φ₀) :
    ∀ e' ∈ newExps, ∀ x ∈ e', x ∈ modalUniverseS5 φ₀ := by
  obtain ⟨sf, hsfmem, -, hshape⟩ :=
    modalStepBranchS5gKeyed_expanded_shape φ₀ b e acc keys newBs newExps newAcc newKeys hstep
  intro e' he'
  rcases hshape e' he' with rfl | rfl
  · intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hxeq
    · exact heClosure x hx
    · rw [hxeq]; exact hbClosure sf hsfmem
  · exact heClosure

/-! ## Birth-Key Preservation Lemmas (task 515 Phase 5, the `keysDistinct` crux) -/

omit [Hashable Atom] in
/-- **Phase 5 field 1/4, the crux**: `modalStepBranchS5gKeyed` preserves `keysDistinct`. Keys
never change value once recorded; the blocked/non-minting cases leave `keys` untouched entirely.
The minting case appends exactly one fresh entry, and `blockingWorldS5Keyed_none_fresh`
(Phase 3) directly gives that the fresh key differs from EVERY stored key -- this is the fix for
the v1 design gap (the guard compares against stored keys, not a live relevant set that could
have grown past a stale key). -/
lemma modalStepBranchS5g_preserves_keysDistinct (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (newKeys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS5gKeyed φ₀ b e acc keys = some (newBs, newExps, newAcc, newKeys))
    (hDistinct : ∀ w w' k k', (w, k) ∈ keys → (w', k') ∈ keys → w ≠ w' → k ≠ k') :
    ∀ w w' k k', (w, k) ∈ newKeys → (w', k') ∈ newKeys → w ≠ w' → k ≠ k' := by
  obtain ⟨sf, -, -, hcase⟩ :=
    modalStepBranchS5gKeyed_keys_shape φ₀ b e acc keys newBs newExps newAcc newKeys hstep
  have hmint : ∀ (s : Sign) (φ : Proposition Atom),
      blockingWorldS5Keyed φ₀ keys b s φ sf.label = none →
      newKeys = keys ++ [(modalNextWorld b, successorBirthContentS5 φ₀ b s φ sf.label)] →
      ∀ w w' k k', (w, k) ∈ newKeys → (w', k') ∈ newKeys → w ≠ w' → k ≠ k' := by
    intro s φ hnone hnk w w' k k' hw hw' hne
    rw [hnk] at hw hw'
    simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hw hw'
    rcases hw with hw | ⟨rfl, rfl⟩ <;> rcases hw' with hw' | ⟨rfl, rfl⟩
    · exact hDistinct w w' k k' hw hw' hne
    · exact blockingWorldS5Keyed_none_fresh φ₀ keys b s φ sf.label hnone w k hw
    · exact (blockingWorldS5Keyed_none_fresh φ₀ keys b s φ sf.label hnone w' k' hw').symm
    · exact absurd rfl hne
  rcases hcase with hnk | ⟨φ, -, -, hnone, hnk⟩ | ⟨φ, -, -, hnone, hnk⟩
  · rw [hnk]; exact hDistinct
  · exact hmint .neg φ hnone hnk
  · exact hmint .pos φ hnone hnk

omit [Hashable Atom] in
/-- **Phase 5 field 4/4**: `modalStepBranchS5gKeyed` preserves `keysInUniverse`
(`∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀`). Old keys are unaffected. The fresh key
`successorBirthContentS5 φ₀ b s φ sf.label` is, by construction, `insert (s, φ)` into a
`Finset.filter` over `signedSubfmls φ₀` (hence trivially `⊆ signedSubfmls φ₀` once the witness
pair `(s, φ)` itself is shown to lie in `signedSubfmls φ₀`); the witness's formula-closure
`φ ∈ modalSubfmls φ₀` follows from `bClosure`/`sf ∈ b`/`modalSubfmls_trans_S5`, identical
reasoning to `bClosure`'s own mint-case witness argument. -/
lemma modalStepBranchS5g_preserves_keysInUniverse (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (newKeys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS5gKeyed φ₀ b e acc keys = some (newBs, newExps, newAcc, newKeys))
    (hbClosure : ∀ x ∈ b, x ∈ modalUniverseS5 φ₀)
    (hInUniv : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀) :
    ∀ w k, (w, k) ∈ newKeys → k ⊆ signedSubfmls φ₀ := by
  obtain ⟨sf, hsfmem, -, hcase⟩ :=
    modalStepBranchS5gKeyed_keys_shape φ₀ b e acc keys newBs newExps newAcc newKeys hstep
  have hkinuniv : ∀ (s : Sign) (φ : Proposition Atom), φ ∈ modalSubfmls φ₀ →
      successorBirthContentS5 φ₀ b s φ sf.label ⊆ signedSubfmls φ₀ := by
    intro s φ hφ
    unfold successorBirthContentS5 successorBirthContent
    apply Finset.insert_subset_iff.mpr
    refine ⟨?_, Finset.filter_subset _ _⟩
    simp only [signedSubfmls, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton,
      List.mem_toFinset]
    exact ⟨by cases s <;> simp, hφ⟩
  rcases hcase with hnk | ⟨φ, -, hf, -, hnk⟩ | ⟨φ, -, hf, -, hnk⟩
  · rw [hnk]; exact hInUniv
  · have hsrc : (Proposition.box φ) ∈ modalSubfmls φ₀ := by
      have := modalUniverseS5_mem_formula (hbClosure sf hsfmem)
      rwa [hf] at this
    have hφmem : φ ∈ modalSubfmls (Proposition.box φ) :=
      List.mem_cons_of_mem _ (modalSubfmls_self_mem_S5 φ)
    have hφsub : φ ∈ modalSubfmls φ₀ := modalSubfmls_trans_S5 hφmem hsrc
    intro w k hwk
    rw [hnk] at hwk
    simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hwk
    rcases hwk with hwk | ⟨-, rfl⟩
    · exact hInUniv w k hwk
    · exact hkinuniv .neg φ hφsub
  · have hsrc : (Proposition.diamond φ) ∈ modalSubfmls φ₀ := by
      have := modalUniverseS5_mem_formula (hbClosure sf hsfmem)
      rwa [hf] at this
    have hφmem : φ ∈ modalSubfmls (Proposition.diamond φ) :=
      List.mem_cons_of_mem _ (modalSubfmls_self_mem_S5 φ)
    have hφsub : φ ∈ modalSubfmls φ₀ := modalSubfmls_trans_S5 hφmem hsrc
    intro w k hwk
    rw [hnk] at hwk
    simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hwk
    rcases hwk with hwk | ⟨-, rfl⟩
    · exact hInUniv w k hwk
    · exact hkinuniv .pos φ hφsub

omit [DecidableEq Atom] [Hashable Atom] in
/-- `addEdge` never returns its input unchanged (it conses one edge onto the edge list). Used
by `keysTotal`'s preservation to rule out `modalApplyOneS5_knownWorlds_step`'s mint disjunct at
the keyed stepper's non-minting-shape dispatch, where
`modalStepBranchS5gKeyed_keys_full_shape` guarantees `(modalApplyOneS5 sf b acc).snd = acc`. -/
private lemma addEdge_ne_self_S5 (acc : Accessibility) (w w' : WorldIndex) :
    acc.addEdge w w' ≠ acc := by
  intro h
  have hlen := congrArg (fun a => a.edges.length) h
  simp only [Accessibility.addEdge, List.length_cons] at hlen
  omega

/-- **Phase 5 field 2/4**: `modalStepBranchS5gKeyed` preserves `keysTotal`
(`∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys`). Blocked steps change neither the branch nor
the keys. Non-minting-shape steps only emit formulas at already-known labels
(`modalApplyOneS5_knownWorlds_step`'s non-mint disjunct, selected via
`(modalApplyOneS5 sf b acc).snd = acc` from `modalStepBranchS5gKeyed_keys_full_shape` +
`addEdge_ne_self_S5`), so the old `keysTotal` witness transfers. Minting steps append the fresh
key for the ONE newly-known world `modalNextWorld b` in the SAME step event that grows the
branch -- the correlation `modalStepBranchS5gKeyed_keys_full_shape` exists to provide. -/
lemma modalStepBranchS5g_preserves_keysTotal (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (newKeys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS5gKeyed φ₀ b e acc keys = some (newBs, newExps, newAcc, newKeys))
    (hknown : accTargetsKnown b acc)
    (hTotal : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys) :
    ∀ b' ∈ newBs, ∀ w ∈ modalKnownWorlds b', ∃ k, (w, k) ∈ newKeys := by
  obtain ⟨sf, hsfmem, -, hcase⟩ :=
    modalStepBranchS5gKeyed_keys_full_shape φ₀ b e acc keys newBs newExps newAcc newKeys hstep
  have htrans : ∀ (xs : List (SignedFormula (Proposition Atom) WorldIndex)),
      (∀ x ∈ xs, x.label ∈ modalKnownWorlds b) →
      ∀ w ∈ modalKnownWorlds (xs ++ b), w ∈ modalKnownWorlds b := by
    intro xs hxs w hw
    rw [mem_modalKnownWorlds_S5] at hw
    obtain ⟨sf', hsf', rfl⟩ := hw
    rcases List.mem_append.mp hsf' with hx | hb0
    · exact hxs sf' hx
    · exact (mem_modalKnownWorlds_S5 b sf'.label).mpr ⟨sf', hb0, rfl⟩
  have hmint : ∀ (s : Sign) (φ : Proposition Atom),
      newKeys = keys ++ [(modalNextWorld b, successorBirthContentS5 φ₀ b s φ sf.label)] →
      (match (modalApplyOneS5 sf b acc).fst with
        | .linear nf => newBs = [nf ++ b]
        | .branching brs => newBs = brs.map (· ++ b)
        | .persistent nf => newBs = [nf ++ b]
        | .notApplicable => False) →
      ∀ b' ∈ newBs, ∀ w ∈ modalKnownWorlds b', ∃ k, (w, k) ∈ newKeys := by
    intro s φ hnk hshape b' hb'
    rcases modalApplyOneS5_knownWorlds_step sf b acc hsfmem hknown with
      ⟨-, hmatch⟩ | ⟨-, hmatch⟩
    · rcases hm : (modalApplyOneS5 sf b acc).fst with nf | brs | nf | -
      · rw [hm] at hshape hmatch
        rw [hshape] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        obtain ⟨k, hk⟩ := hTotal w (htrans nf hmatch w hw)
        exact ⟨k, hnk ▸ List.mem_append_left _ hk⟩
      · rw [hm] at hshape hmatch
        rw [hshape] at hb'
        obtain ⟨br, hbr, rfl⟩ := List.mem_map.mp hb'
        intro w hw
        obtain ⟨k, hk⟩ := hTotal w (htrans br
          (fun x hx => hmatch x (List.mem_flatten.mpr ⟨br, hbr, hx⟩)) w hw)
        exact ⟨k, hnk ▸ List.mem_append_left _ hk⟩
      · rw [hm] at hshape hmatch
        rw [hshape] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        obtain ⟨k, hk⟩ := hTotal w (htrans nf hmatch w hw)
        exact ⟨k, hnk ▸ List.mem_append_left _ hk⟩
      · rw [hm] at hshape; exact hshape.elim
    · rcases hm : (modalApplyOneS5 sf b acc).fst with nf | brs | nf | -
      · rw [hm] at hshape hmatch
        rw [hshape] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        rw [mem_modalKnownWorlds_S5] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hx | hb0
        · refine ⟨successorBirthContentS5 φ₀ b s φ sf.label, ?_⟩
          rw [hnk, hmatch.2 sf' hx]
          exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
        · obtain ⟨k, hk⟩ :=
            hTotal sf'.label ((mem_modalKnownWorlds_S5 b sf'.label).mpr ⟨sf', hb0, rfl⟩)
          exact ⟨k, hnk ▸ List.mem_append_left _ hk⟩
      · rw [hm] at hmatch; exact hmatch.elim
      · rw [hm] at hmatch; exact hmatch.elim
      · rw [hm] at hmatch; exact hmatch.elim
  rcases hcase with ⟨wBlock, -, hnewBs, hnk⟩ | ⟨hnk, hsnd, hshape⟩ |
    ⟨φ, -, -, -, hnk, hshape⟩ | ⟨φ, -, -, -, hnk, hshape⟩
  · intro b' hb'
    rw [hnewBs] at hb'
    simp only [List.mem_singleton] at hb'
    subst hb'
    intro w hw
    rw [hnk]
    exact hTotal w hw
  · rcases modalApplyOneS5_knownWorlds_step sf b acc hsfmem hknown with
      ⟨-, hmatch⟩ | ⟨hsndeq, -⟩
    · intro b' hb'
      rcases hm : (modalApplyOneS5 sf b acc).fst with nf | brs | nf | -
      · rw [hm] at hshape hmatch
        rw [hshape] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        rw [hnk]
        exact hTotal w (htrans nf hmatch w hw)
      · rw [hm] at hshape hmatch
        rw [hshape] at hb'
        obtain ⟨br, hbr, rfl⟩ := List.mem_map.mp hb'
        intro w hw
        rw [hnk]
        exact hTotal w (htrans br
          (fun x hx => hmatch x (List.mem_flatten.mpr ⟨br, hbr, hx⟩)) w hw)
      · rw [hm] at hshape hmatch
        rw [hshape] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        rw [hnk]
        exact hTotal w (htrans nf hmatch w hw)
      · rw [hm] at hshape; exact hshape.elim
    · rw [hsnd] at hsndeq
      exact absurd hsndeq.symm (addEdge_ne_self_S5 acc sf.label (modalNextWorld b))
  · exact hmint .neg φ hnk hshape
  · exact hmint .pos φ hnk hshape

/-- The box-positives group K's two minting arms (`diamondPos`/`boxNeg`, `Rules.lean`) emit at
a mint from trigger world `w`: for every recorded `(ψ', src) ∈ boxPositivesOf b` with
`src = w`, the propagated copy `T(ψ')@(modalNextWorld b)`, deduplicated against `b`. Named
(rather than left as `modalApplyOne`'s inline term) so `keyLowerBd`'s mint-case obligation can
state introduction lemmas against ONE shared expression -- both
`modalApplyOne_boxNeg_eq_S5`/`modalApplyOne_diamondPos_eq_S5` (the arm characterizations) and
`successorBirthContentS5_subset_relevantSetFinset_mint` (the consumer) refer to this def, so no
cross-lemma matcher-unification is ever needed. -/
private def mintBoxPropsS5 (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (w : WorldIndex) : List (SignedFormula (Proposition Atom) WorldIndex) :=
  (boxPositivesOf b).filterMap fun (ψ', src) =>
    if src == w then
      if b.any (· == (⟨.pos, ψ', modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) then none
      else some ⟨.pos, ψ', modalNextWorld b⟩
    else none

/-- The diamond-negatives group K's two minting arms emit at a mint from trigger world `w`:
for every `F(◇ψ')@w ∈ b`, the propagated copy `F(ψ')@(modalNextWorld b)`, deduplicated against
`b`. Companion of `mintBoxPropsS5`, same rationale. -/
private def mintDiaNegPropsS5 (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (w : WorldIndex) : List (SignedFormula (Proposition Atom) WorldIndex) :=
  b.filterMap fun sf' =>
    if sf'.sign == .neg && sf'.label == w then
      match sf'.formula with
      | .diamond ψ' =>
        if b.any (· == (⟨.neg, ψ', modalNextWorld b⟩ :
            SignedFormula (Proposition Atom) WorldIndex)) then none
        else some ⟨.neg, ψ', modalNextWorld b⟩
      | _ => none
    else none

omit [DecidableEq Atom] [Hashable Atom] in
/-- Introduction direction for `boxPositivesOf` (converse of `mem_boxPositivesOf_S5`): every
box-positive formula on the branch is recorded in the collector's output. -/
private lemma boxPositivesOf_intro_S5 {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {ψ : Proposition Atom} {src : WorldIndex}
    (h : (⟨.pos, .box ψ, src⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (ψ, src) ∈ boxPositivesOf b := by
  simp only [boxPositivesOf, List.mem_filterMap]
  exact ⟨⟨.pos, .box ψ, src⟩, h, rfl⟩

omit [Hashable Atom] in
/-- Introduction lemma for `mintBoxPropsS5` (the converse direction of
`boxProps_outputs_subset_S5`'s elimination reasoning): if `T(□χ)@w ∈ b`, then the propagated
copy `T(χ)@(modalNextWorld b)` is on the minted branch -- either freshly emitted into
`mintBoxPropsS5 b w` (when not already present on `b`), or already a member of `b` (the
dedup-guard case). This is exactly the dichotomy the `if b.any (· == sf')` guard inside
`boxProps`'s construction encodes. -/
private lemma mintBoxPropsS5_mem_intro (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (w : WorldIndex) (χ : Proposition Atom)
    (hmem : (⟨.pos, .box χ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (⟨.pos, χ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
        mintBoxPropsS5 b w ∨
      (⟨.pos, χ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  by_cases hany : b.any (· == (⟨.pos, χ, modalNextWorld b⟩ :
      SignedFormula (Proposition Atom) WorldIndex)) = true
  · right
    simp only [List.any_eq_true, beq_iff_eq] at hany
    obtain ⟨x, hxmem, rfl⟩ := hany
    exact hxmem
  · left
    unfold mintBoxPropsS5
    simp only [List.mem_filterMap]
    refine ⟨(χ, w), boxPositivesOf_intro_S5 hmem, ?_⟩
    simp [hany]

omit [Hashable Atom] in
/-- Introduction lemma for `mintDiaNegPropsS5`, symmetric to `mintBoxPropsS5_mem_intro`: if
`F(◇χ)@w ∈ b`, the propagated copy `F(χ)@(modalNextWorld b)` is either freshly emitted into
`mintDiaNegPropsS5 b w` or already on `b`. -/
private lemma mintDiaNegPropsS5_mem_intro
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w : WorldIndex)
    (χ : Proposition Atom)
    (hmem : (⟨.neg, .diamond χ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (⟨.neg, χ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
        mintDiaNegPropsS5 b w ∨
      (⟨.neg, χ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  by_cases hany : b.any (· == (⟨.neg, χ, modalNextWorld b⟩ :
      SignedFormula (Proposition Atom) WorldIndex)) = true
  · right
    simp only [List.any_eq_true, beq_iff_eq] at hany
    obtain ⟨x, hxmem, rfl⟩ := hany
    exact hxmem
  · left
    unfold mintDiaNegPropsS5
    simp only [List.mem_filterMap]
    refine ⟨⟨.neg, .diamond χ, w⟩, hmem, ?_⟩
    simp [hany]

omit [Hashable Atom] in
/-- Full characterization of K's `boxNeg` mint output (strengthens
`modalApplyOne_boxNeg_witness`, whose `rest` is existentially quantified): the emitted
`.linear` list is EXACTLY the witness `F(ψ)@(modalNextWorld b)` followed by
`mintBoxPropsS5 b sf.label ++ mintDiaNegPropsS5 b sf.label`. `keyLowerBd`'s mint case needs the
concrete tail to place every birth-content pair on the minted branch. -/
private lemma modalApplyOne_boxNeg_eq_S5
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (hsign : sf.sign = .neg) (hform : sf.formula = .box ψ) :
    (modalApplyOne sf b acc).fst
      = RuleResult.linear
          ((⟨.neg, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
            mintBoxPropsS5 b sf.label ++ mintDiaNegPropsS5 b sf.label) := by
  obtain ⟨s, f0, l⟩ := sf
  simp only at hsign hform
  subst hsign; subst hform
  have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.neg, .box ψ, l⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
      = false := by
    rw [tryAllPropRules_neg]
    simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
  simp only [modalApplyOne]
  rw [if_neg (by simp [htry])]
  rfl

omit [Hashable Atom] in
/-- Full characterization of K's `diamondPos` mint output, symmetric to
`modalApplyOne_boxNeg_eq_S5`: the emitted `.linear` list is EXACTLY the witness
`T(ψ)@(modalNextWorld b)` followed by
`mintBoxPropsS5 b sf.label ++ mintDiaNegPropsS5 b sf.label`. -/
private lemma modalApplyOne_diamondPos_eq_S5
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (hsign : sf.sign = .pos) (hform : sf.formula = .diamond ψ) :
    (modalApplyOne sf b acc).fst
      = RuleResult.linear
          ((⟨.pos, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
            mintBoxPropsS5 b sf.label ++ mintDiaNegPropsS5 b sf.label) := by
  obtain ⟨s, f0, l⟩ := sf
  simp only at hsign hform
  subst hsign; subst hform
  have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.pos, .diamond ψ, l⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
      = false := by
    rw [tryAllPropRules_pos]
    simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
  simp only [modalApplyOne]
  rw [if_neg (by simp [htry])]
  rfl

omit [Hashable Atom] in
/-- **The `keyLowerBd` mint-case correspondence**: every pair of the prospective birth content
`successorBirthContentS5 φ₀ b s φ w` is realized as an ACTUAL signed formula at label
`modalNextWorld b` on the freshly-minted branch
`(⟨s, φ, modalNextWorld b⟩ :: mintBoxPropsS5 b w ++ mintDiaNegPropsS5 b w) ++ b`: the witness
pair `(s, φ)` by the head witness formula itself, and each box-positive/diamond-negative
context pair by `mintBoxPropsS5_mem_intro`/`mintDiaNegPropsS5_mem_intro`'s
freshly-emitted-or-already-present dichotomy. Hence the fresh birth key is a LOWER BOUND on the
minted world's live relevant set at birth -- the fresh-key case of `keyLowerBd`'s
preservation. -/
private lemma successorBirthContentS5_subset_relevantSetFinset_mint (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (hwitU : ((s, φ) : Sign × Proposition Atom) ∈ signedSubfmls φ₀) :
    successorBirthContentS5 φ₀ b s φ w ⊆
      relevantSetFinset φ₀
        (((⟨s, φ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
            mintBoxPropsS5 b w ++ mintDiaNegPropsS5 b w) ++ b)
        (modalNextWorld b) := by
  intro p hp
  unfold successorBirthContentS5 successorBirthContent at hp
  rw [Finset.mem_insert] at hp
  unfold relevantSetFinset
  rw [Finset.mem_filter]
  rcases hp with rfl | hp
  · refine ⟨hwitU, ?_⟩
    simp only [List.any_eq_true, beq_iff_eq]
    exact ⟨⟨s, φ, modalNextWorld b⟩,
      List.mem_append_left _ List.mem_cons_self, rfl⟩
  · rw [Finset.mem_filter] at hp
    obtain ⟨hpU, hpc⟩ := hp
    refine ⟨hpU, ?_⟩
    obtain ⟨ps, pf⟩ := p
    simp only [List.any_eq_true, beq_iff_eq] at hpc ⊢
    rcases hpc with ⟨hps, x, hxmem, hxeq⟩ | ⟨hps, x, hxmem, hxeq⟩
    · subst hps; subst hxeq
      rcases mintBoxPropsS5_mem_intro b w pf hxmem with hin | hin
      · exact ⟨⟨Sign.pos, pf, modalNextWorld b⟩,
          List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_left _ hin)), rfl⟩
      · exact ⟨⟨Sign.pos, pf, modalNextWorld b⟩, List.mem_append_right _ hin, rfl⟩
    · subst hps; subst hxeq
      rcases mintDiaNegPropsS5_mem_intro b w pf hxmem with hin | hin
      · exact ⟨⟨Sign.neg, pf, modalNextWorld b⟩,
          List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_right _ hin)), rfl⟩
      · exact ⟨⟨Sign.neg, pf, modalNextWorld b⟩, List.mem_append_right _ hin, rfl⟩

omit [Hashable Atom] in
/-- **Phase 5 field 3/4**: `modalStepBranchS5gKeyed` preserves `keyLowerBd`
(`∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w`). Old keys survive because birth keys
never change and live relevant sets only grow under branch prepend (`relevantSetFinset_mono` --
the monotone-stability that defeats the v1 Gap-1 collapse by construction). The fresh key
equals the minted world's birth content, realized on the SAME minted branch by
`successorBirthContentS5_subset_relevantSetFinset_mint` via the concrete mint-arm
characterizations (`modalApplyOne_boxNeg_eq_S5`/`modalApplyOne_diamondPos_eq_S5`). -/
lemma modalStepBranchS5g_preserves_keyLowerBd (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (newKeys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS5gKeyed φ₀ b e acc keys = some (newBs, newExps, newAcc, newKeys))
    (hbClosure : ∀ x ∈ b, x ∈ modalUniverseS5 φ₀)
    (hLowerBd : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w) :
    ∀ b' ∈ newBs, ∀ w k, (w, k) ∈ newKeys → k ⊆ relevantSetFinset φ₀ b' w := by
  obtain ⟨sf, hsfmem, -, hcase⟩ :=
    modalStepBranchS5gKeyed_keys_full_shape φ₀ b e acc keys newBs newExps newAcc newKeys hstep
  have hmono : ∀ (xs : List (SignedFormula (Proposition Atom) WorldIndex))
      (w : WorldIndex) (k : Finset (Sign × Proposition Atom)),
      k ⊆ relevantSetFinset φ₀ b w → k ⊆ relevantSetFinset φ₀ (xs ++ b) w := fun xs w k hk =>
    hk.trans (relevantSetFinset_mono φ₀ b (xs ++ b) w
      (fun sf' h => List.mem_append_right _ h))
  rcases hcase with ⟨wBlock, -, hnewBs, hnk⟩ | ⟨hnk, -, hshape⟩ |
    ⟨φ, hsign, hform, -, hnk, hshape⟩ | ⟨φ, hsign, hform, -, hnk, hshape⟩
  · intro b' hb'
    rw [hnewBs] at hb'
    simp only [List.mem_singleton] at hb'
    subst hb'
    intro w k hk
    rw [hnk] at hk
    exact hLowerBd w k hk
  · intro b' hb'
    have hxs : ∃ xs, b' = xs ++ b := by
      rcases hm : (modalApplyOneS5 sf b acc).fst with nf | brs | nf | -
      · rw [hm] at hshape; rw [hshape] at hb'
        simp only [List.mem_singleton] at hb'; exact ⟨nf, hb'⟩
      · rw [hm] at hshape; rw [hshape] at hb'
        obtain ⟨br, -, rfl⟩ := List.mem_map.mp hb'; exact ⟨br, rfl⟩
      · rw [hm] at hshape; rw [hshape] at hb'
        simp only [List.mem_singleton] at hb'; exact ⟨nf, hb'⟩
      · rw [hm] at hshape; exact hshape.elim
    obtain ⟨xs, rfl⟩ := hxs
    intro w k hk
    rw [hnk] at hk
    exact hmono xs w k (hLowerBd w k hk)
  · have hS5eq : modalApplyOneS5 sf b acc = modalApplyOne sf b acc :=
      modalApplyOneS5_eq_of_not_boxPos_diaNeg sf b acc ⟨by simp [hsign], by simp [hform]⟩
    have heq := modalApplyOne_boxNeg_eq_S5 sf b acc φ hsign hform
    rw [hS5eq, heq] at hshape
    have hsrc : (Proposition.box φ) ∈ modalSubfmls φ₀ := by
      have := modalUniverseS5_mem_formula (hbClosure sf hsfmem)
      rwa [hform] at this
    have hφmem : φ ∈ modalSubfmls (Proposition.box φ) :=
      List.mem_cons_of_mem _ (modalSubfmls_self_mem_S5 φ)
    have hφsub : φ ∈ modalSubfmls φ₀ := modalSubfmls_trans_S5 hφmem hsrc
    have hwitU : ((Sign.neg, φ) : Sign × Proposition Atom) ∈ signedSubfmls φ₀ := by
      simp only [signedSubfmls, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton,
        List.mem_toFinset]
      exact ⟨by simp, hφsub⟩
    intro b' hb'
    rw [hshape] at hb'
    simp only [List.mem_singleton] at hb'
    subst hb'
    intro w k hk
    rw [hnk] at hk
    simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hk
    rcases hk with hk | ⟨rfl, rfl⟩
    · exact hmono _ w k (hLowerBd w k hk)
    · exact successorBirthContentS5_subset_relevantSetFinset_mint φ₀ b .neg φ sf.label hwitU
  · have hS5eq : modalApplyOneS5 sf b acc = modalApplyOne sf b acc :=
      modalApplyOneS5_eq_of_not_boxPos_diaNeg sf b acc ⟨by simp [hform], by simp [hsign]⟩
    have heq := modalApplyOne_diamondPos_eq_S5 sf b acc φ hsign hform
    rw [hS5eq, heq] at hshape
    have hsrc : (Proposition.diamond φ) ∈ modalSubfmls φ₀ := by
      have := modalUniverseS5_mem_formula (hbClosure sf hsfmem)
      rwa [hform] at this
    have hφmem : φ ∈ modalSubfmls (Proposition.diamond φ) :=
      List.mem_cons_of_mem _ (modalSubfmls_self_mem_S5 φ)
    have hφsub : φ ∈ modalSubfmls φ₀ := modalSubfmls_trans_S5 hφmem hsrc
    have hwitU : ((Sign.pos, φ) : Sign × Proposition Atom) ∈ signedSubfmls φ₀ := by
      simp only [signedSubfmls, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton,
        List.mem_toFinset]
      exact ⟨by simp, hφsub⟩
    intro b' hb'
    rw [hshape] at hb'
    simp only [List.mem_singleton] at hb'
    subst hb'
    intro w k hk
    rw [hnk] at hk
    simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hk
    rcases hk with hk | ⟨rfl, rfl⟩
    · exact hmono _ w k (hLowerBd w k hk)
    · exact successorBirthContentS5_subset_relevantSetFinset_mint φ₀ b .pos φ sf.label hwitU


-- ARCHIVED from Cslib/Logics/Modal/Tableau/S5Simplification.lean:3939-4001
-- Retired: 2026-07-16, task 515 phase 14 (plan v4)
-- Superseded by: `ModalLoopInvHintikka.bClosure`, discharged generically by `RuleApplicationSpecCore.outputsSubsetUniverse` (`modalApplyOneS5w_outputsSubsetUniverse`)
-- Why retired: the last `S5LoopInv` field-preservation lemma; sits after cluster 05 in the original file order because it consumes the pigeonhole bound. Retired with its invariant.
-- Status at retirement: CI-green, sorry-free, zero axioms beyond propext/Classical.choice/Quot.sound
-- Recover a compiling version at: git show af59318098f7ed0eceb7a33634d072babb45b603 -- Cslib/Logics/Modal/Tableau/S5Simplification.lean

/-- **Phase 4 field 1/6 (unblocked, cycle-3)**: `modalStepBranchS5gKeyed` preserves `bClosure`
(`∀ x ∈ b, x ∈ modalUniverseS5 φ₀`). The blocked case leaves `b` unchanged. The non-blocked case
combines `modalApplyOneS5_outputs_subset` (every newly-appended formula is in `U_{S5}(φ₀)`,
consuming the world-bound `modalMaxWorld b < modalWorldBoundS5 φ₀` derived from `worldsContiguous`
+ the pigeonhole bound `modalKnownWorlds_length_le_worldBoundS5`) with `bClosure` itself for the
unchanged suffix `b`. This is the fact that was missing per handoff
`02_phase4-bclosure-contiguity-gap.md` -- contiguity is exactly the bridge from Phase 6's known-
world COUNT bound to the fresh label's VALUE bound `modalApplyOneS5_outputs_subset` needs. -/
lemma modalStepBranchS5g_preserves_bClosure (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (newKeys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS5gKeyed φ₀ b e acc keys = some (newBs, newExps, newAcc, newKeys))
    (hkK : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hfresh : accFreshInv b acc)
    (hbClosure : ∀ x ∈ b, x ∈ modalUniverseS5 φ₀)
    (hcontig : modalMaxWorld b + 1 = (modalKnownWorlds b).length)
    (hTotal : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys)
    (hDistinct : ∀ w w' k k', (w, k) ∈ keys → (w', k') ∈ keys → w ≠ w' → k ≠ k')
    (hInUniv : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀) :
    ∀ b' ∈ newBs, ∀ x ∈ b', x ∈ modalUniverseS5 φ₀ := by
  have hW : modalMaxWorld b < modalWorldBoundS5 φ₀ :=
    modalMaxWorld_lt_worldBoundS5_of_keys φ₀ b keys hcontig hTotal hDistinct hInUniv
  obtain ⟨sf, hsfmem, -, hcase⟩ :=
    modalStepBranchS5gKeyed_acc_shape φ₀ b e acc keys newBs newExps newAcc newKeys hstep hkK
  rcases hcase with ⟨wBlock, -, -, hnewBs, -, -⟩ | ⟨-, hshape⟩
  · intro b' hb'
    rw [hnewBs] at hb'
    simp only [List.mem_singleton] at hb'
    rw [hb']
    exact hbClosure
  · have hsub := modalApplyOneS5_outputs_subset φ₀ sf b acc hbClosure hsfmem hfresh hW
    intro b' hb'
    rcases hm : (modalApplyOneS5 sf b acc).fst with nf | brs | nf | -
    · rw [hm] at hshape hsub
      rw [hshape.1] at hb'
      simp only [List.mem_singleton] at hb'
      rw [hb']
      intro x hx
      simp only [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hsub x hx
      · exact hbClosure x hx
    · rw [hm] at hshape hsub
      rw [hshape.1] at hb'
      obtain ⟨br, hbr, rfl⟩ := List.mem_map.mp hb'
      intro x hx
      simp only [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hsub x (List.mem_flatten.mpr ⟨br, hbr, hx⟩)
      · exact hbClosure x hx
    · rw [hm] at hshape hsub
      rw [hshape.1] at hb'
      simp only [List.mem_singleton] at hb'
      rw [hb']
      intro x hx
      simp only [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hsub x hx
      · exact hbClosure x hx
    · rw [hm] at hshape; exact absurd hshape (by simp)

