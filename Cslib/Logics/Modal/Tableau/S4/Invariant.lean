/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.S4.Universe
public import Cslib.Logics.Modal.Tableau.S4.BirthKey
public import Cslib.Logics.Modal.Tableau.S4.Guard
public import Cslib.Logics.Modal.Tableau.S4.Driver
public import Cslib.Logics.Modal.Tableau.S4.InvariantKeys
public import Cslib.Logics.Modal.Tableau.S4.InvariantAcc

/-! # S4 Loop-Checking: The `S4LoopInv` Structure and Its Capstones

The `S4LoopInv` structure itself, the `eClosure`/`bClosure` preservation pairs (the two fields
not specific to either the keys-facing or accessibility-facing invariant split), and the two
assembling capstone theorems `modalStepBranchS4{,KeyedOrdered}_preserves_S4LoopInv` that combine
all ten fields from `InvariantKeys` and `InvariantAcc` into one preservation statement per
stepper.

## Why a separate module

This is where the four-way invariant split (`InvariantKeys`, `InvariantAcc`, `Invariant`,
`HintikkaInvariant` -- see `InvariantKeys.lean`'s docstring for the full rationale) reconverges:
`S4LoopInv`'s ten fields are declared here, but six of its preservation obligations
(`keyLowerBd`/`keysInUniverse`/`keysTotal`/`keysDistinct`/`keysWorldsKnown`/`keysOriginS4`) are
proved in `InvariantKeys` and three (`eNodup`/`accFresh`/`accKnown`) in `InvariantAcc`; only
`bClosure` and `eClosure` are proved here directly, alongside the two capstones that assemble
all ten into `S4LoopInv` preservation as a single obligation.

## Main Definitions
- `S4LoopInv`: the ten-field S4 loop invariant (research §3.5's "sibling of `ModalPotentialInv`,
  not an extension of it").

## Main Results
- `modalStepBranchS4{,KeyedOrdered}_preserves_eClosure`, `_bClosure`: the two closure fields
  proved directly in this module.
- `modalStepBranchS4_preserves_S4LoopInv`, `modalStepBranchS4KeyedOrdered_preserves_S4LoopInv`:
  the assembling capstones, combining all ten fields from `InvariantKeys` and `InvariantAcc`.
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Sanity Checks

`modalTableauS4` was confirmed to evaluate and close exactly on the T and 4 components via
an interactive `#eval` session (not embedded in this file as a permanent `#eval`/`#guard`/
`native_decide` declaration: this file's `module`/`public meta import` boundary makes all
three of those forms either fail to elaborate (`Proposition.atom` is not `meta`-accessible
without an additional `public meta import`) or fail at the native-code-lookup stage
(`modalFuel`'s compiled implementation is not resolvable in this configuration) -- no
existing file in `Cslib/Logics/Modal/Tableau/` uses any of these forms, confirming this is a
structural constraint of the module system here, not specific to this phase's code).
Confirmed interactively:
- `□p → p` (the T schema) evaluates to `.closed`: S4 is reflexive.
- `□p → □□p` (the 4 schema) evaluates to `.closed`: S4 is transitive -- this is the
  component that distinguishes S4 from T, and the entire reason this task's 4-rule exists.
- A bare atom `p` evaluates to `.openBranch _ _`: S4 does not prove arbitrary atoms. -/

/-! ## The S4 Loop Invariant `S4LoopInv` -/

/-- **Correction 1**: `S4LoopInv` is a **sibling** of `ModalPotentialInv` (`FmpMeasure.lean`),
not an extension of it. `ModalPotentialInv` holds two rank fields (`rankBound`/`rankEdge`)
encoding "modal depth strictly decreases along every edge", which the 4-rule (placing
`T(□ψ)`, unchanged modal depth, at a successor) and loop-back edges (creating `w → w''`
with `rank w'' + 2 = rank w`) both falsify. `S4LoopInv` reuses the five rule-independent
fields (`bClosure`/`eNodup`/`eClosure`/`accFresh`/`accKnown`, over
`modalUniverseS4` in place of `modalUniverse`), omits the two rank fields entirely, and adds
the four **stable birth-key** fields (replacing the structurally-unsound
`worldSetsDistinct`): `keysTotal`/`keyLowerBd`/`keysDistinct`/`keysInUniverse`, stated over
the threaded `keys` list (`modalStepBranchS4Keyed`) rather than the live branch. `keys` never
changes after a world is born and each key only ever lower-bounds a monotonically-growing live
relevant set, so this invariant survives every step (Gap 1), and `keysDistinct` is exactly
what the birth-content guard `blockingWorldS4` enforces at minting time (Gap 2).
`FmpMeasure.lean` is not modified here. -/
structure S4LoopInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) : Prop where
  /-- Every branch formula is a member of the fixed finite S4 universe `U_{S4}(φ₀)`. -/
  bClosure : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀
  /-- The expanded set has no duplicate entries. -/
  eNodup : e.Nodup
  /-- Every expanded-set formula is a member of `U_{S4}(φ₀)`. -/
  eClosure : ∀ x ∈ e, x ∈ modalUniverseS4 φ₀
  /-- All of `acc`'s recorded worlds are `< modalNextWorld b`. -/
  accFresh : accFreshInv b acc
  /-- Every `acc`-edge target is a label already appearing on the branch. -/
  accKnown : accTargetsKnown b acc
  /-- Every known world has a recorded birth key. -/
  keysTotal : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys
  /-- **Survives Gap 1**: a world's recorded birth key is a LOWER BOUND on its live relevant
  set. This is monotone-stable -- birth keys never change after a world is born, and live
  relevant sets only grow (`relevantSetFinset_mono`) -- unlike the old `worldSetsDistinct`,
  which compared live sets directly and so could be falsified by a later persistent step. -/
  keyLowerBd : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w
  /-- **Fixes Gap 2**: distinct worlds have DISTINCT birth keys. This is exactly what the
  redesigned guard (`blockingWorldS4`) enforces at minting time (`blockingWorldS4_none_fresh`),
  and no later step can violate it since keys themselves never change. This is the hypothesis
  the pigeonhole argument (`modalKnownWorlds_length_le_worldBoundS4`, below) consumes. -/
  keysDistinct : ∀ w w' k k', (w, k) ∈ keys → (w', k') ∈ keys → w ≠ w' → k ≠ k'
  /-- Birth keys are drawn from the powerset of the finite signed-subformula codomain
  `signedSubfmls φ₀`: the pigeonhole argument's injection target (below). -/
  keysInUniverse : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀

/-! ## `bClosure`/`eClosure` (both fully closed)

Both remaining `S4LoopInv` fields, closed:

- **`eClosure`** turned out to be immediate: `modalStepBranchS4Keyed`'s `newExps` component is
  `e ++ [sf]` (or `e` unchanged for `.persistent`) -- it only ever gains the *selected* formula
  `sf` (already `∈ b`, hence covered directly by `hb`), never the rule's output content (that
  goes to `newBs`, `bClosure`'s concern).
- **`bClosure`** needed exactly that formula-subset composite (`modalApplyOneS4Keyed_nonMint_
  universe_S4` and its supporting T-augmented/S4Rules-augmented pieces, "Non-Minting
  Universe-Membership Composite" section above) for its 12 non-minting shapes, plus the
  pigeonhole world-bound deliverable (`modalStepBranchS4_worldBound`, "Pigeonhole World
  Bound" section above) as a genuine PREREQUISITE for its 2 minting shapes: the newly-minted
  witness's label (`modalNextWorld b = modalMaxWorld b + 1`) needs the STRICT bound
  `modalMaxWorld b < modalWorldBoundS4 φ₀` to hold on the PRE-step branch `b`, which is exactly
  what `modalStepBranchS4_worldBound` supplies (consuming a new proof-internal auxiliary
  invariant `worldsContiguousS4`, threaded the same way as `keysWorldsKnown`). -/

/-- **`eClosure`'s driver-level preservation**: closes directly via the same case-split shape as
`modalStepBranchS4_preserves_eNodup` -- `newExps`'s only new content is the selected formula
`sf`, already in `b` and hence covered by `hb`. -/
lemma modalStepBranchS4_preserves_eClosure (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (heclosure : ∀ x ∈ e, x ∈ modalUniverseS4 φ₀)
    (_hknown : accTargetsKnown b acc)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ e' ∈ newExps, ∀ x ∈ e', x ∈ modalUniverseS4 φ₀ := by
  unfold modalStepBranchS4Keyed at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hsfbound : sf ∈ modalUniverseS4 φ₀ := hb sf hsfmem
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  rcases hres : result with nf | brs | nf | -
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    simp only [List.mem_singleton] at he'
    subst he'
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact heclosure x hx
    · exact hsfbound
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    obtain ⟨x0, -, rfl⟩ := List.mem_map.mp he'
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact heclosure x hx
    · exact hsfbound
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact heclosure
  · rw [hres] at hsf; simp at hsf

/-- **`eClosure`'s ordered-driver preservation.** Verbatim transcription of
`modalStepBranchS4_preserves_eClosure` against the ordered stepper, via
`modalStepBranchS4KeyedOrdered_selected_mem` in place of the direct `findSome?` extraction. -/
lemma modalStepBranchS4KeyedOrdered_preserves_eClosure (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (heclosure : ∀ x ∈ e, x ∈ modalUniverseS4 φ₀)
    (_hknown : accTargetsKnown b acc)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ e' ∈ newExps, ∀ x ∈ e', x ∈ modalUniverseS4 φ₀ := by
  obtain ⟨sf, hsfmem, hsf_ne, hsf⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsf_ne hx
  unfold modalStepBranchS4KeyedBody at hsf
  rw [if_neg (by simp [hany])] at hsf
  have hsfbound : sf ∈ modalUniverseS4 φ₀ := hb sf hsfmem
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  rcases hres : result with nf | brs | nf | -
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    simp only [List.mem_singleton] at he'
    subst he'
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact heclosure x hx
    · exact hsfbound
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    obtain ⟨x0, -, rfl⟩ := List.mem_map.mp he'
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact heclosure x hx
    · exact hsfbound
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact heclosure
  · rw [hres] at hsf; simp at hsf

/-- **`bClosure`'s driver-level preservation**: at the 12 non-minting shapes, the "Non-Minting
Universe-Membership Composite" section's `modalApplyOneS4Keyed_nonMint_universe_S4` bounds
emitted content directly; at the 2 minting shapes, the pigeonhole world-bound
(`modalStepBranchS4_worldBound`, consuming `worldsContiguousS4`) supplies the STRICT
`modalMaxWorld b < modalWorldBoundS4 φ₀` bound `modalApplyOne_boxNeg_outputs_subset_S4`/
`modalApplyOne_diamondPos_outputs_subset_S4` need to place the freshly-minted witness in
range. -/
lemma modalStepBranchS4_preserves_bClosure (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hWC : worldsContiguousS4 b)
    (hKT : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys)
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hKI : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀)
    (hknown : accTargetsKnown b acc)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ x ∈ b', x ∈ modalUniverseS4 φ₀ := by
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        have hW := modalStepBranchS4_worldBound φ₀ b keys hWC hKT hKD hKI
        have hsfmem' : (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hcontent := modalApplyOne_boxNeg_outputs_subset_S4 φ₀ b ψ sf.label hb hsfmem' hW
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        intro b' hb' x hx
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rcases List.mem_append.mp hx with hxnew | hxold
        · exact hcontent x hxnew
        · exact hb x hxold
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb' x hx
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        exact hb x hx
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        have hW := modalStepBranchS4_worldBound φ₀ b keys hWC hKT hKD hKI
        have hsfmem' : (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hcontent := modalApplyOne_diamondPos_outputs_subset_S4 φ₀ b ψ sf.label hb hsfmem'
          hW
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        intro b' hb' x hx
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rcases List.mem_append.mp hx with hxnew | hxold
        · exact hcontent x hxnew
        · exact hb x hxold
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb' x hx
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        exact hb x hx
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have hnm := modalApplyOneS4Keyed_nonMint_universe_S4 φ₀ keys sf b acc hb hsfmem hknown hnbd
    rw [hpair] at hnm
    dsimp only at hnm
    intro b' hb' x hx
    rcases hres : result with lf | brs | lf | -
    · rw [hres] at hsf hnm
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      rw [← hsf.1] at hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      rcases List.mem_append.mp hx with hxnew | hxold
      · exact hnm x hxnew
      · exact hb x hxold
    · rw [hres] at hsf hnm
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      rw [← hsf.1] at hb'
      obtain ⟨br, hbr, rfl⟩ := List.mem_map.mp hb'
      rcases List.mem_append.mp hx with hxnew | hxold
      · exact hnm x (List.mem_flatten.mpr ⟨br, hbr, hxnew⟩)
      · exact hb x hxold
    · rw [hres] at hsf hnm
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      rw [← hsf.1] at hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      rcases List.mem_append.mp hx with hxnew | hxold
      · exact hnm x hxnew
      · exact hb x hxold
    · rw [hres] at hsf; simp at hsf

/-- **`bClosure`'s ordered-driver preservation.** Verbatim transcription of
`modalStepBranchS4_preserves_bClosure` against the ordered stepper, via
`modalStepBranchS4KeyedOrdered_selected_mem` in place of the direct `findSome?` extraction. The
pigeonhole world-bound prerequisite `modalStepBranchS4_worldBound` is consumed UNCHANGED: it is
stated purely over the pre-step `b`/`keys`, independent of which traversal produced the step, so
no ordered analogue of it is needed. -/
lemma modalStepBranchS4KeyedOrdered_preserves_bClosure (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hWC : worldsContiguousS4 b)
    (hKT : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys)
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hKI : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀)
    (hknown : accTargetsKnown b acc)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ x ∈ b', x ∈ modalUniverseS4 φ₀ := by
  obtain ⟨sf, hsfmem, hsf_ne, hsf⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsf_ne hx
  unfold modalStepBranchS4KeyedBody at hsf
  rw [if_neg (by simp [hany])] at hsf
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        have hW := modalStepBranchS4_worldBound φ₀ b keys hWC hKT hKD hKI
        have hsfmem' : (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hcontent := modalApplyOne_boxNeg_outputs_subset_S4 φ₀ b ψ sf.label hb hsfmem' hW
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        intro b' hb' x hx
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rcases List.mem_append.mp hx with hxnew | hxold
        · exact hcontent x hxnew
        · exact hb x hxold
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb' x hx
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        exact hb x hx
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        have hW := modalStepBranchS4_worldBound φ₀ b keys hWC hKT hKD hKI
        have hsfmem' : (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hcontent := modalApplyOne_diamondPos_outputs_subset_S4 φ₀ b ψ sf.label hb hsfmem'
          hW
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        intro b' hb' x hx
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rcases List.mem_append.mp hx with hxnew | hxold
        · exact hcontent x hxnew
        · exact hb x hxold
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb' x hx
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        exact hb x hx
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have hnm := modalApplyOneS4Keyed_nonMint_universe_S4 φ₀ keys sf b acc hb hsfmem hknown hnbd
    rw [hpair] at hnm
    dsimp only at hnm
    intro b' hb' x hx
    rcases hres : result with lf | brs | lf | -
    · rw [hres] at hsf hnm
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      rw [← hsf.1] at hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      rcases List.mem_append.mp hx with hxnew | hxold
      · exact hnm x hxnew
      · exact hb x hxold
    · rw [hres] at hsf hnm
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      rw [← hsf.1] at hb'
      obtain ⟨br, hbr, rfl⟩ := List.mem_map.mp hb'
      rcases List.mem_append.mp hx with hxnew | hxold
      · exact hnm x (List.mem_flatten.mpr ⟨br, hbr, hxnew⟩)
      · exact hb x hxold
    · rw [hres] at hsf hnm
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      rw [← hsf.1] at hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      rcases List.mem_append.mp hx with hxnew | hxold
      · exact hnm x hxnew
      · exact hb x hxold
    · rw [hres] at hsf; simp at hsf

/-- **`modalStepBranchS4_preserves_S4LoopInv`**: every `modalStepBranchS4Keyed` step preserves
`S4LoopInv`, over every
branch/expanded-set pair it produces (any `b' ∈ newBs` paired with any `e' ∈ newExps` -- valid
because `modalStepBranchS4Keyed` never produces distinct `newExps` entries for distinct `newBs`
entries: the `.branching` arm maps EVERY branch to the identical `e ++ [sf]`, and the
`.linear`/`.persistent` arms produce singleton lists of each, so any member of one is
definitionally paired with any member of the other). Also threads and re-establishes TWO
proof-internal auxiliary invariants (neither an `S4LoopInv` field itself, to avoid reopening the
finalized struct design): `keysWorldsKnown` (needed by `accFresh`/`accKnown`) and
`worldsContiguousS4` (needed by `bClosure`'s own minting-case pigeonhole prerequisite,
`modalStepBranchS4_worldBound`), so repeated steps through this assembly can re-supply both at
each call.

**All nine fields are now fully closed, zero sorry** (`keysDistinct`/`keyLowerBd`/
`keysInUniverse`/`keysTotal`: the four "key" fields; `eNodup`/
`accFresh`/`accKnown`; and `eClosure`/`bClosure`,
`eClosure` directly and `bClosure` via the pigeonhole world-bound
(`modalStepBranchS4_worldBound`) as a genuine prerequisite for its minting-case obligation). -/
theorem modalStepBranchS4_preserves_S4LoopInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hinv : S4LoopInv φ₀ b e acc keys)
    (hKW : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hWC : worldsContiguousS4 b)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    (∀ b' ∈ newBs, ∀ e' ∈ newExps, S4LoopInv φ₀ b' e' newAcc keys') ∧
    (∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys' → w ∈ modalKnownWorlds b') ∧
    (∀ b' ∈ newBs, worldsContiguousS4 b') := by
  obtain ⟨hbC, heN, heC, haF, haK, hkT, hkL, hkD, hkI⟩ := hinv
  refine ⟨?_, modalStepBranchS4_preserves_keysWorldsKnown φ₀ b e acc keys newBs newExps newAcc
    keys' hKW hstep, modalStepBranchS4_preserves_worldsContiguousS4 φ₀ b e acc keys newBs newExps
    newAcc keys' hWC haK hstep⟩
  intro b' hb' e' he'
  exact
    { bClosure := modalStepBranchS4_preserves_bClosure φ₀ b e acc keys newBs newExps newAcc keys'
        hbC hWC hkT hkD hkI haK hstep b' hb'
      eNodup := modalStepBranchS4_preserves_eNodup φ₀ b e acc keys newBs newExps newAcc keys'
        hstep heN e' he'
      eClosure := modalStepBranchS4_preserves_eClosure φ₀ b e acc keys newBs newExps newAcc keys'
        hbC heC haK hstep e' he'
      accFresh := modalStepBranchS4_preserves_accFresh φ₀ b e acc keys newBs newExps newAcc keys'
        haK hKW haF hstep b' hb'
      accKnown := modalStepBranchS4_preserves_accKnown φ₀ b e acc keys newBs newExps newAcc keys'
        haK hKW hstep b' hb'
      keysTotal := modalStepBranchS4_preserves_keysTotal φ₀ b e acc keys newBs newExps newAcc
        keys' haK hkT hstep b' hb'
      keyLowerBd := modalStepBranchS4_preserves_keyLowerBd φ₀ b e acc keys newBs newExps newAcc
        keys' hbC hkL hstep b' hb'
      keysDistinct := modalStepBranchS4_preserves_keysDistinct φ₀ b e acc keys newBs newExps
        newAcc keys' hkD hstep
      keysInUniverse := modalStepBranchS4_preserves_keysInUniverse φ₀ b e acc keys newBs newExps
        newAcc keys' hbC hkI hstep }

/-- **`modalStepBranchS4KeyedOrdered_preserves_S4LoopInv`** (originally established for the
ordered driver, later extended with the origin-edge invariant's fourth conjunct): every
`modalStepBranchS4KeyedOrdered`
step preserves `S4LoopInv`, mirroring `modalStepBranchS4_preserves_S4LoopInv` exactly -- a
`refine`+`exact` assembly with no independent proof content of its own, just twelve calls to this
section's ordered per-field sub-lemmas (`modalStepBranchS4KeyedOrdered_preserves_{bClosure,
eNodup,eClosure,accFresh,accKnown,keysTotal,keyLowerBd,keysDistinct,keysInUniverse}`
plus the three proof-internal auxiliaries `modalStepBranchS4KeyedOrdered_preserves_{
keysWorldsKnown,worldsContiguousS4,keysOriginS4}`), each of which was itself verified against the
ordered stepper via `modalStepBranchS4KeyedOrdered_selected_mem` in place of the unordered
`findSome?` extraction. No landed statement (`keysUpdate_preserves_keysDistinct`,
`blockingWorldS4Keyed_none_fresh`, or any individual `S4LoopInv` field) required ANY weakening to
reach this point -- the plan's escalation trigger (`keysDistinct`, attempted first) did not fire,
confirming settled-context scheduling changes only *timing*, never producing a duplicate key or
otherwise degrading any invariant.

**Note**: `keysOriginS4` (like `keysWorldsKnown`/`worldsContiguousS4` before it) is
threaded as an extra hypothesis/conclusion, NOT an `S4LoopInv` field -- the struct itself is
untouched, and the unordered wrapper `modalStepBranchS4_preserves_S4LoopInv` is byte-for-byte
unchanged (this extension applies to the ordered driver only). -/
theorem modalStepBranchS4KeyedOrdered_preserves_S4LoopInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hinv : S4LoopInv φ₀ b e acc keys)
    (hKW : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hWC : worldsContiguousS4 b)
    (hKO : keysOriginS4 b acc keys)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    (∀ b' ∈ newBs, ∀ e' ∈ newExps, S4LoopInv φ₀ b' e' newAcc keys') ∧
    (∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys' → w ∈ modalKnownWorlds b') ∧
    (∀ b' ∈ newBs, worldsContiguousS4 b') ∧
    (∀ b' ∈ newBs, keysOriginS4 b' newAcc keys') := by
  obtain ⟨hbC, heN, heC, haF, haK, hkT, hkL, hkD, hkI⟩ := hinv
  refine ⟨?_, modalStepBranchS4KeyedOrdered_preserves_keysWorldsKnown φ₀ b e acc keys newBs
    newExps newAcc keys' hKW hstep,
    modalStepBranchS4KeyedOrdered_preserves_worldsContiguousS4 φ₀ b e acc keys newBs newExps
    newAcc keys' hWC haK hstep,
    modalStepBranchS4KeyedOrdered_preserves_keysOriginS4 φ₀ b e acc keys newBs newExps newAcc
    keys' haK hKO hstep⟩
  intro b' hb' e' he'
  exact
    { bClosure := modalStepBranchS4KeyedOrdered_preserves_bClosure φ₀ b e acc keys newBs newExps
        newAcc keys' hbC hWC hkT hkD hkI haK hstep b' hb'
      eNodup := modalStepBranchS4KeyedOrdered_preserves_eNodup φ₀ b e acc keys newBs newExps
        newAcc keys' hstep heN e' he'
      eClosure := modalStepBranchS4KeyedOrdered_preserves_eClosure φ₀ b e acc keys newBs newExps
        newAcc keys' hbC heC haK hstep e' he'
      accFresh := modalStepBranchS4KeyedOrdered_preserves_accFresh φ₀ b e acc keys newBs newExps
        newAcc keys' haK hKW haF hstep b' hb'
      accKnown := modalStepBranchS4KeyedOrdered_preserves_accKnown φ₀ b e acc keys newBs newExps
        newAcc keys' haK hKW hstep b' hb'
      keysTotal := modalStepBranchS4KeyedOrdered_preserves_keysTotal φ₀ b e acc keys newBs
        newExps newAcc keys' haK hkT hstep b' hb'
      keyLowerBd := modalStepBranchS4KeyedOrdered_preserves_keyLowerBd φ₀ b e acc keys newBs
        newExps newAcc keys' hbC hkL hstep b' hb'
      keysDistinct := modalStepBranchS4KeyedOrdered_preserves_keysDistinct φ₀ b e acc keys newBs
        newExps newAcc keys' hkD hstep
      keysInUniverse := modalStepBranchS4KeyedOrdered_preserves_keysInUniverse φ₀ b e acc keys
        newBs newExps newAcc keys' hbC hkI hstep }

end Cslib.Logic.Modal.Tableau

end
