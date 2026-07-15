# Handoff: Cycle 5 -- `keysTotal` Attempt Made and Reverted, No Net Change to Lean Sources

**Date**: 2026-07-15
**Session**: sess_1784130637_a36e2a (cycle 5, FINAL cycle of this orchestration invocation)
**Status**: Phases 1, 2, 3, 4, 6 remain `[COMPLETED]`. Phase 5 remains 2/4 (`keysDistinct`,
`keysInUniverse` landed at cycle 4; `keyLowerBd`/`keysTotal` still `[NOT STARTED]`). **No new
Lean declarations landed this cycle** -- `Cslib/Logics/Modal/Tableau/S5Simplification.lean` is
byte-identical to commit `fcbe121c` (verified via `git diff`, empty). This handoff exists to save
the next dispatch from re-discovering the same bugs, since a genuine, substantial attempt was
made and several concrete infrastructure pieces + bug diagnoses came out of it even though
nothing was committed.

## Why nothing landed

The orchestrator sent a mid-cycle instruction to stop pushing on new proof obligations and reach
a green checkpoint. At that point the in-progress `keysTotal` proof attempt was NOT yet closing
(see "What went wrong" below), so per the zero-debt contract (never commit a `sorry`, never leave
broken state), the entire uncommitted diff to `S5Simplification.lean` was reverted with
`git checkout -- Cslib/Logics/Modal/Tableau/S5Simplification.lean`. Full CI was re-run against the
reverted file and confirmed green (`lake build` 3239/3239, `checkInitImports` clean, `lint-style`
clean, `lake lint` -- only the 1 pre-existing unrelated `PrimeExclusion.lean` error, `lake test`
exit 0, `lake shake` -- 0 new suggestions). Zero sorry (only a "sorry-free" prose mention), zero
new axioms.

## What was attempted: `modalStepBranchS5g_preserves_keysTotal`

**Statement to prove**: `∀ b' ∈ newBs, ∀ w ∈ modalKnownWorlds b', ∃ k, (w, k) ∈ newKeys`.

**Core difficulty identified**: the existing shape-characterization lemmas
`modalStepBranchS5gKeyed_acc_shape` (gives the `newBs`/`newAcc` shape) and
`modalStepBranchS5gKeyed_keys_shape` (gives the `newKeys` shape) each independently
`obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep` from the SAME `hstep`
hypothesis. Since `Exists` elimination produces a fresh opaque local constant each time it is
invoked, a caller that calls BOTH lemmas gets two a priori UNRELATED witnesses (`sf₁` from
`_acc_shape`, `sf₂` from `_keys_shape`) with no available proof `sf₁ = sf₂`, even though
mathematically they must denote the same value (the unique triggering formula `List.findSome?`
picked). `keysTotal` genuinely needs BOTH facts tied to the SAME `sf` (to know that "the world
that got minted" and "the key that got appended" are the same event), so composing the two
existing lemmas as black boxes does not work.

**Approach taken**: author a new combined private helper
`modalStepBranchS5gKeyed_keys_full_shape` giving both facts from ONE case split (mirroring
`_keys_shape`'s proven skeleton but also threading through the `newBs`/`(modalApplyOneS5 sf b
acc).snd = acc` facts `_acc_shape` gives). This is architecturally the right fix and should be
attempted again, but the SPECIFIC construction attempted this cycle had three bugs, all now
diagnosed (see below). Two small supporting lemmas built along the way DID compile standalone and
should be reused verbatim.

## Reusable infrastructure that DID compile (verified via `lake build`, zero errors)

Both belong right after the already-landed `modalApplyOneS5_snd_eq` (`S5Simplification.lean`,
around line 347). Insert them there again in the next dispatch -- they are self-contained and did
not depend on anything from the broken combined helper.

```lean
omit [Hashable Atom] in
/-- K's own `modalApplyOne` leaves `acc` unchanged at every shape OTHER than its two minting
shapes (`.neg,box` boxNeg, `.pos,diamond` diamondPos): direct from `Rules.lean`'s definition,
where `.pos,.box`/`.neg,.diamond` (propagation, non-mint) and every prop/atomic shape return
`(_, acc)` verbatim, and only `.neg,.box`/`.pos,.diamond` return `(_, acc.addEdge ..)`. This is
the converse-shape fact `keysTotal`/`keyLowerBd`'s preservation proofs need to rule out minting
at the keyed stepper's non-minting-shape (`| _, _ =>`) dispatch. -/
private lemma modalApplyOne_snd_eq_acc_of_not_mint_shape_S5
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hns : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
           ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)) :
    (modalApplyOne sf b acc).snd = acc := by
  obtain ⟨h1, h2⟩ := hns
  unfold modalApplyOne
  by_cases hpa :
      (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf).isApplicable
  · simp [hpa]
  · rw [if_neg hpa]
    obtain ⟨s, ff, l⟩ := sf
    simp only at h1 h2
    rcases s with _ | _
    · rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · dsimp only; split <;> rfl
      · exact absurd ⟨rfl, φ, rfl⟩ h2
    · rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd ⟨rfl, φ, rfl⟩ h1
      · dsimp only; split <;> rfl

omit [Hashable Atom] in
/-- S5 lift of `modalApplyOne_snd_eq_acc_of_not_mint_shape_S5` via `modalApplyOneS5_snd_eq`:
`modalApplyOneS5` also leaves `acc` unchanged outside the two K-minting shapes. -/
private lemma modalApplyOneS5_snd_eq_acc_of_not_mint_shape
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hns : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
           ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)) :
    (modalApplyOneS5 sf b acc).snd = acc := by
  rw [modalApplyOneS5_snd_eq]
  exact modalApplyOne_snd_eq_acc_of_not_mint_shape_S5 sf b acc hns
```

Both were confirmed to build with zero errors and zero new warnings via
`lake build Cslib.Logics.Modal.Tableau.S5Simplification` in isolation before the combined helper's
own construction went wrong. Re-add these first in the next dispatch; they are correct.

## The three bugs in the combined helper (all now diagnosed -- avoid repeating them)

The target combined helper's shape (still the right shape to aim for):

```lean
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
  ...
```

**Bug 1 (hygiene mismatch)**: do NOT pre-establish which shape you are in via
`by_cases hshape : (...) ∨ (...)` followed by `rcases hshape with ⟨hsign, ψ, hform⟩ | ...` and
then `rw [hsign, hform] at hsf`. `modalStepBranchS5gKeyed`'s own definition uses `φ` as the
pattern-bound name in its `| .neg, .box φ => ...` match arm. Rewriting a SEPARATELY-obtained
witness (`ψ`, or even `φ` reused) into the match discriminant via `rw` causes Lean's hygiene
mechanism to rename the match's OWN internal binder to a fresh inaccessible name (shows up as
`φ✝` in error messages) to avoid variable capture -- so a later proof trying to supply YOUR
witness for the existential in the goal's conclusion fails to unify with `hsf`'s post-split
`φ✝`-typed component (`Application type mismatch ... has type ... φ✝ ... but is expected ... φ`).
**Fix**: never pre-establish the shape via a separate `by_cases`/`rcases` and rewrite it in;
instead fully destructure `sf` itself via `obtain ⟨s, ff, l⟩ := sf` BEFORE any case analysis, then
`rcases s with _ | _ <;> rcases ff with _ | _ | ⟨a,c⟩ | ⟨x,y⟩ | ⟨x,y⟩ | φ | φ` (mirroring
`modalApplyOne_outputs_subset_S5`'s and `modalApplyOne_snd_eq_acc_of_not_mint_shape_S5`'s own
proofs) so that `φ` in the box/diamond arms is a genuine, directly rcases-introduced local with no
separately-sourced witness to unify against.

**Bug 2 (wrong `Sign` constructor order)**: `Sign`'s constructors are declared `pos` THEN `neg`
(`Cslib/Foundations/Logic/Tableau/Sign.lean:46-50`: `inductive Sign where | pos : Sign | neg :
Sign`). This means `rcases s with _ | _`'s FIRST bullet is `Sign.pos`, NOT `Sign.neg`. It is easy
to assume "neg-box first" reading order and write the first bullet's content as if it were
handling `.neg, .box` -- this silently produces a proof for the WRONG shape in each bullet
(confirmed by error traces showing `sf.sign = Sign.pos` inside a bullet whose code assumed
`Sign.neg`). **Fix**: the FIRST `rcases s with _|_` bullet must handle the **pos-diamond**
special case (`.pos, .diamond φ`, diamondPos) plus the wildcard shapes EXCLUDING diamond
(atom/bot/imp/and/or/box); the SECOND bullet handles **neg-box** (`.neg, .box φ`, boxNeg) plus the
wildcard shapes excluding box (atom/bot/imp/and/or/diamond).

**Bug 3 (missing split before injection in the wildcard sub-case)**: even once `sf` is fully
concrete (via `obtain ⟨s,ff,l⟩ := sf; rcases s; rcases ff`), `hsf`'s type for a WILDCARD
(non-minting) shape is still `(let (result, newAcc) := modalApplyOneS5 sf b acc; match result
with | .linear nf => some (...) | ... ) = some (newBs, newExps, newAcc, newKeys)` -- a match on
`result`, which is NOT concrete (its value depends on `b`/`acc`, which remain fully generic). This
match must ALSO be split (`split at hsf <;> repeat' split at hsf`, exactly as the minting-shape
branches already do) BEFORE `injection hsf` will accept the hypothesis. Skipping this step and
calling `injection hsf` directly on the still-unreduced match produces "equality of constructor
applications expected" / "too many identifiers provided" errors uniformly across every wildcard
case (atom, bot, imp, and, or, and the "wrong-sign" box/diamond). **Fix**: apply
`(split at hsf <;> repeat' split at hsf)` to ALL 7 formula-shape cases within each sign-branch
uniformly (both the 1 special shape and the 6 wildcard shapes) via a single `all_goals` before
attempting ANY of `Or.inl` / mint / wildcard closing, then dispatch the resulting sub-goals with a
single `first | ... | ... | ...` combinator (3 alternatives per sign-branch: blocked, this-branch's
mint shape, wildcard-with-`hsnd`). Do NOT try to special-case "split only for the minting shape,
skip split for wildcard" -- that asymmetry is what produced bug 3.

## Recommended next dispatch order

1. Re-add the two standalone lemmas verbatim (`modalApplyOne_snd_eq_acc_of_not_mint_shape_S5`,
   `modalApplyOneS5_snd_eq_acc_of_not_mint_shape`) right after `modalApplyOneS5_snd_eq` (~line
   347). Confirm `lake build Cslib.Logics.Modal.Tableau.S5Simplification` is still green.
2. Author `modalStepBranchS5gKeyed_keys_full_shape` using the UNIFIED-split structure described
   above (fix all three bugs together): `obtain ⟨s,ff,l⟩ := sf` up front, correct `Sign` order
   (pos-diamond in the first bullet, neg-box in the second), single `(split at hsf <;> repeat'
   split at hsf)` applied uniformly across all 7 formula-shapes per sign-branch via `all_goals`,
   then ONE `first | Or.inl | mint | wildcard` combinator per branch (using `_`/`by assumption`
   for existential witnesses in the mint alternative, matching `_keys_shape`'s own proven style,
   NOT manually-supplied names).
3. Once the combined helper compiles, `keysTotal`'s proof follows the outline already sketched in
   handoff `03_phase5-keysdistinct-landed-keylowerbd-scope.md`: case on the helper's 4-way
   disjunction; blocked/wildcard cases reduce `b'`'s known-worlds to `b`'s (via
   `mem_modalKnownWorlds_S5`/`modalKnownWorlds_mono_append_S5`), using the ambient `hTotal`
   hypothesis directly; the two mint cases additionally need the case where `w = modalNextWorld
   b`, discharged by the SAME disjunct's own `newKeys = keys ++ [(modalNextWorld b, ...)]` fact
   (the witness is literally the freshly-appended entry).
4. `keyLowerBd` remains the harder field (needs new "introduction" lemmas for `boxProps`/
   `diaNegProps` membership, converse to the existing elimination-direction lemmas) -- see handoff
   `03_...` for that plan; it is independent of the combined-helper work above except for reusing
   `relevantSetFinset_mono` (`LoopChecking.lean:344`, already public).
5. Phase 7 (soundness bridge, `FrameSoundness.lean`) remains fully independent and untouched --
   still available to attempt in parallel with, or instead of, further Phase 5 work.
