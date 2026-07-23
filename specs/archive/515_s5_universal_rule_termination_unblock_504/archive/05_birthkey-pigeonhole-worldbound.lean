/-
ARCHIVE -- NOT BUILT, NOT IMPORTED.

This file is archival: it is not in the `Cslib/` tree, carries no `import Cslib.Init`, is
not listed in `Cslib.lean`, and is never seen by `lake build` / `checkInitImports` /
`mk_all`. The blocks below will NOT compile as lifted out of context (they depend on the
surrounding file's variables, imports, and `omit` scopes); that is expected for an archive.
Each block's provenance header carries the `git` coordinates that recover a compiling version.
-/

-- Retired cluster 05: the birth-key pigeonhole world bound.

-- ARCHIVED from Cslib/Logics/Modal/Tableau/S5Simplification.lean:3840-3938
-- Retired: 2026-07-16, task 515 phase 14 (plan v4)
-- Superseded by: `modalMaxWorld_lt_worldBound_of_S5w` (`S5Simplification.lean`): `S5wWorldInv` + `usedTags ⊆ mintTags` + `mintTags_card_le_modalOps` + `modalOps_lt_worldBound`
-- Why retired: reaches the world bound by injecting known worlds into `(signedSubfmls φ₀).powerset` -- an exponential bound (`2 ^ (2 * |modalSubfmls φ₀|)`) requiring three `S5LoopInv` birth-key fields. The witness rule reaches a LINEAR bound (`modalOps φ₀`) at K's own `modalWorldBound` by tag-cardinality counting: no rank, no potential, no pigeonhole, no powerset, no birth keys.
-- Status at retirement: CI-green, sorry-free, zero axioms beyond propext/Classical.choice/Quot.sound
-- Recover a compiling version at: git show af59318098f7ed0eceb7a33634d072babb45b603 -- Cslib/Logics/Modal/Tableau/S5Simplification.lean

/-! ## Pigeonhole World Bound (task 515 Phase 6)

A **static** cardinality fact about any fixed `(b, keys)` pair satisfying `S5LoopInv`'s three
birth-key structural fields (`keysTotal`/`keysDistinct`/`keysInUniverse`) -- no step-preservation
reasoning is needed, only that every known world has a birth key, distinct known worlds have
distinct keys, and every key lies in the finite codomain `signedSubfmls φ₀`. Each known world
injects into `(signedSubfmls φ₀).powerset` via its (possibly non-unique-choice-of-witness, but
unique-by-value thanks to `keysDistinct`) birth key, so `Finset.card_le_card_of_injOn` composed
with `signedSubfmls_powerset_card_le` (`LoopChecking.lean`) bounds `modalKnownWorlds b`'s length
by `modalWorldBoundS5 φ₀`. Consumed both directly (Phase 5 exit criterion) and as the missing
piece Phase 4's `bClosure`/`eClosure` mint-case obligations need (see
`specs/515_.../handoffs/01_phase4-generic-field-preservation.md`). -/

omit [Hashable Atom] in
/-- **Phase 6**: the pigeonhole world bound. Any branch `b` whose known worlds all have birth
keys in `keys` (`hTotal`), with distinct known worlds forced to distinct keys (`hDistinct`) and
every key confined to `signedSubfmls φ₀` (`hInUniv`), has at most `modalWorldBoundS5 φ₀` known
worlds. -/
lemma modalKnownWorlds_length_le_worldBoundS5 (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hTotal : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys)
    (hDistinct : ∀ w w' k k', (w, k) ∈ keys → (w', k') ∈ keys → w ≠ w' → k ≠ k')
    (hInUniv : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀) :
    (modalKnownWorlds b).length ≤ modalWorldBoundS5 φ₀ := by
  classical
  -- Choose, for each known world, a witness birth key.
  set f : WorldIndex → Finset (Sign × Proposition Atom) :=
    fun w => if h : ∃ k, (w, k) ∈ keys then h.choose else ∅ with hf
  have hfspec : ∀ w ∈ modalKnownWorlds b, (w, f w) ∈ keys := by
    intro w hw
    have hex : ∃ k, (w, k) ∈ keys := hTotal w hw
    simp only [hf]
    rw [dif_pos hex]
    exact hex.choose_spec
  have hmapsto : Set.MapsTo f (modalKnownWorlds b).toFinset ↑(signedSubfmls φ₀).powerset := by
    intro w hw
    rw [Finset.mem_coe, List.mem_toFinset] at hw
    simp only [Finset.coe_powerset, Set.mem_preimage]
    exact hInUniv w (f w) (hfspec w hw)
  have hinj : Set.InjOn f (modalKnownWorlds b).toFinset := by
    intro w hw w' hw' heq
    rw [Finset.mem_coe, List.mem_toFinset] at hw hw'
    by_contra hne
    exact hDistinct w w' (f w) (f w') (hfspec w hw) (hfspec w' hw') hne heq
  have hcard := Finset.card_le_card_of_injOn f hmapsto hinj
  rw [List.toFinset_card_of_nodup (modalKnownWorlds_nodup_S5 b)] at hcard
  calc (modalKnownWorlds b).length ≤ (signedSubfmls φ₀).powerset.card := hcard
    _ ≤ modalWorldBoundS4 φ₀ := signedSubfmls_powerset_card_le φ₀
    _ = modalWorldBoundS5 φ₀ := rfl

omit [Hashable Atom] in
/-- **Phase 6 capstone**: the S5 termination chain's actual payload -- the a-priori world-index
bound `modalMaxWorld b < modalWorldBoundS5 φ₀`, in *value* form rather than the pigeonhole's
*count* form.

This is the exact bridge `worldsContiguous` (the 12th `S5LoopInv` field) was introduced for:
`modalKnownWorlds_length_le_worldBoundS5` bounds the known-world COUNT, while every downstream
consumer (`modalApplyOneS5_outputs_subset`, and any future Hintikka lift generalized over
`S5LoopInv` instead of `ModalLoopInvGen`) needs a bound on the fresh label's VALUE. Contiguity
(`modalMaxWorld b + 1 = (modalKnownWorlds b).length` -- worlds are minted only at exactly
`modalNextWorld b`, so the range `{0, ..., modalMaxWorld b}` has no gaps) converts one into the
other definitionally.

This is the S5 analogue of `modalMaxWorld_lt_worldBound_of_phiBound`
(`CompletenessLoop.lean`), which derives the same conclusion for K from the rank-based Φ-bound.
The whole point of the S5 chain is that it reaches this conclusion via the birth-key pigeonhole
instead, since the rank route is *mathematically false* for `modalApplyOneS5`
(`modalApplyOneS5_rankStep_not_dischargeable`, below). -/
lemma modalMaxWorld_lt_worldBoundS5_of_keys (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hcontig : modalMaxWorld b + 1 = (modalKnownWorlds b).length)
    (hTotal : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys)
    (hDistinct : ∀ w w' k k', (w, k) ∈ keys → (w', k') ∈ keys → w ≠ w' → k ≠ k')
    (hInUniv : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀) :
    modalMaxWorld b < modalWorldBoundS5 φ₀ := by
  have hbound := modalKnownWorlds_length_le_worldBoundS5 φ₀ b keys hTotal hDistinct hInUniv
  rw [← hcontig] at hbound
  exact hbound

omit [Hashable Atom] in
/-- **Phase 6 capstone, bundled form**: an `S5LoopInv` witness delivers the a-priori world bound
directly. This is the single fact the entire Phase 3-6 termination chain (keys-aware guard ->
twelve-field invariant -> preservation lemmas -> pigeonhole) exists to establish, and the form in
which any downstream consumer should consume it.

Note the scope boundary this lemma makes precise: `S5LoopInv` is an invariant of the *keyed*
stepper `modalStepBranchS5gKeyed`, whereas the shipped `modalTableauS5` surface runs the
*unguarded* `modalStepBranchGen modalApplyOneS5`. Connecting this bound to `modalTableauS5`
requires a driver over the keyed stepper (see this file's "Phase 8 Scope" note). -/
lemma S5LoopInv.worldBound {φ₀ : Proposition Atom}
    {b e : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    {keys : List (WorldIndex × Finset (Sign × Proposition Atom))}
    (inv : S5LoopInv φ₀ b e acc keys) :
    modalMaxWorld b < modalWorldBoundS5 φ₀ :=
  modalMaxWorld_lt_worldBoundS5_of_keys φ₀ b keys
    inv.worldsContiguous inv.keysTotal inv.keysDistinct inv.keysInUniverse

