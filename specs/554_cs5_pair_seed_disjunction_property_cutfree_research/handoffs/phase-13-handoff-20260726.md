# Phase 13 Handoff: Theorem 4.1, Modal and Structural Cases

**Status**: implemented (skeleton) -- all 9 of Phase 13's own target constructors fully proven;
`nested_sound` fully assembled over all 19 `NestedProof` constructors, carrying forward the one
strategic sorry (`impL`, not in Phase 13's own task list) untouched from Phase 11's deviation
note. Stage D (Theorem 4.1, soundness) is now complete for every constructor except `impL`.

## Immediate Next Action

Phase 14 ("Nested derivations of the `CS5` axioms") opens Stage E. It does not depend on `impL`
being closed. Separately (not blocking Phase 14, but flagged forward): a dedicated, not-yet-
numbered phase is needed to close `nested_sound_impL`'s strategic sorry, building the source's
own induction-on-`n` argument over the `Λ{ }` chain (page 10's `L_X, L_Y, L_Z` construction). `cut`
is a related but distinct gap: it is not yet a landed `NestedProof` constructor at all (Phase 14's
territory per the plan), so `impL`'s closure and `cut`'s introduction are two separate follow-ups,
not one.

## Current State

`Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean` now has, in addition to
everything Phases 11/12/the id-repair landed:
- `cs5DerivAndCongrLeft`, `cs5DerivFourBoxDiaDistrib`, `cs5DerivBStructDistrib` (new combinators)
- `nested_sound_boxL`, `nested_sound_fourL`, `nested_sound_bStruct` (via Lemma 4.5 + the above)
- `nested_sound_boxR`, `nested_sound_diaL` (thin wrappers over Phase 11's `lemma4_6_boxR`/
  `lemma4_6_diaL`)
- `nested_sound_tR`, `nested_sound_tL` (via `OutputCtx.fillRhs_fm_mono`/Lemma 4.5 + `tDia`/`tBox`)
- `cs5DerivKdiaUncurrySwapSchema`, `buildRhsChain_imp_buildFullChain_dia`,
  `fillRhs_imp_fillFull_dia`, `nested_sound_diaR` (new `kdia`-flavoured bridge, analogous to
  Phase 12's `tBox`-flavoured `impR` bridge)
- `buildRhsChain_imp_buildFullChain_four`, `fillRhs_imp_fillFull_four`, `nested_sound_fourR`
  (same bridge shape, plus one `fourDia` composition to descend `◇◇A` to `◇A`)
- `nested_sound_impL` (single `sorry`, documented, strategic)
- `nested_sound` (the assembled top-level function, all 19 constructors)
- `nested_sound_provable` (corollary: `NestedProof (∅,A°) → Derivable CS5ModalAxiom A`)

Also added: `public import Cslib.Logics.Modal.Metalogic.Constructive.Nested.Rules` to
`Soundness.lean`'s import list (needed for `NestedProof` itself; Phases 11/12 only needed the
context/translation lemmas, not the inductive type).

`lean_verify` on `nested_sound` reports exactly `{propext, sorryAx, Classical.choice, Quot.sound}`
-- the `sorryAx` is the one documented `impL` hole, no other new axiom. Scoped `lake build` is
green. Whole-project `lake build` (3259/3259), `lake test` (9253/9253, exit 0), `lake lint` (one
pre-existing error in `Temporal/Tableau/Saturation.lean`, outside territory), `lake exe
checkInitImports` (exit 0), `lake exe lint-style` (clean), `lake exe mk_all --module` (no update
necessary), scoped `lake shake` (only the known `Cslib.Init` false-positive pattern already
documented by every prior phase in this file) are all clean.

## Key Decisions Made

1. **`boxL`'s anticipated "case-split" does not exist.** Phase 11's docstring speculated `boxL`
   might need a case-split like `id`/`orL`'s obstruction. Direct computation shows `boxL` is
   exactly the same shape as `contract`/`andL`/`diaL`/`tL` (both premise and conclusion fill the
   *same* `InputCtx` via `.fillLhs`), so it closes via Lemma 4.5 (`InputCtx.fillLhs_fm_antitone`)
   composed with Lemma 4.7(iv)'s `(□A ∧ ◇B) ⊃ ◇(A ∧ B)` (`cs5DerivBoxDiaDistrib`, already landed
   for Lemma 4.8), instantiated at `B := Δ.fm`. No case-split, no new axiom, no diamond ever
   appears in the final term.
2. **`fourL`/`bStruct` need one extra lift step** (`fourBox`/`bBox` respectively) before the same
   `cs5DerivBoxDiaDistrib` pattern applies, since their leaf is already boxed/needs symmetrizing.
   Landed as two small combinators (`cs5DerivFourBoxDiaDistrib`, `cs5DerivBStructDistrib`) that
   each compose a `cs5DerivAndCongrLeft` lift with `cs5DerivBoxDiaDistrib` directly -- both are
   genuinely new, small, mechanical lemmas, not restatements.
3. **`diaR`/`fourR` needed a genuinely new bridge**, the `kdia`-flavoured analogue of Phase 12's
   `tBox`-flavoured `impR` bridge. The key subtlety (worth flagging for future bridge-style
   proofs): the inner recursive helper **must** be indexed by an explicit head/tail pair
   (`Γ₂ : NestedLhs`, `rest : List (NestedLhs)`, both representing a provably-nonempty list `Γ₂ ::
   rest`), never by a bare `l : List (NestedLhs)`. A first attempt indexed by bare `l` forced an
   `l = []` case that is genuinely **false** (`⊢ □(Δ.fm⊃A) ⊃ □(◇Δ.fm⊃A)` does not hold in `CK`,
   confirmed by direct semantic counterexample reasoning) -- Lean's exhaustiveness checker would
   have required (and rejected) a proof of it. The head/tail-indexed version sidesteps this
   entirely, since it is never invoked (nor internally defined) at an empty list.
4. **`fourR`'s only difference from `diaR`** is one extra `cs5DerivImpCongrRight _ (fourDia A)`
   composition at each level, to descend `◇◇A` (what the `kdia`-based schema alone produces,
   since its leaf `A` is instantiated to the already-diamond-wrapped `◇A`) to plain `◇A`.
5. **`impL` stays exactly as Phase 11 deferred it** -- not attempted this phase (it was never in
   Phase 13's own task list). Landed as a single top-level case lemma (`nested_sound_impL`, not a
   bare inline `sorry` inside `nested_sound`'s match), so the hole is isolated and independently
   trackable, matching this file's established per-constructor-lemma convention.

## What NOT to Try

- Do not re-attempt a bare-`l`-indexed helper for the `fillRhs`-vs-`fillFull` bridge family
  (`diaR`/`fourR`, and by extension any future rule needing this shape) -- the `l = []` case is
  mathematically false for this bridge direction (unlike Phase 12's `tBox`-flavoured `impR`
  bridge, where the analogous base case genuinely holds via `tBox`). Always index by an explicit
  head/tail pair instead.
- Do not attempt to close `nested_sound_impL` via Lemma 4.4/4.5/4.8's already-landed congruence
  lemmas alone -- Phase 11 already established (and this phase's own investigation did not find
  reason to revisit) that `impL` needs the source's dedicated induction-on-`n` argument over the
  `Λ{ }` chain, a genuinely separate piece of machinery.
- Do not add `kdisj` or any axiom beyond the fixed 26 to close anything in this phase -- none of
  the nine target constructors needed it (only `orL`, already resolved in the prior id-repair
  dispatch, was ever a candidate, and it closed without `kdisj` too).

## Remaining Goals (verbatim from plan)

None for Phase 13 itself -- all four of its own checklist items are checked off. The plan's
Deviation note (see the plan file) documents the `impL` strategic sorry explicitly; it is not a
remaining Phase 13 goal, since `impL` was never on Phase 13's task list.

## References

- Plan: `specs/554_cs5_pair_seed_disjunction_property_cutfree_research/plans/02_cutfree-pair-conservativity.md`
  (Phase 13 section, updated with the Deviation note)
- Progress: `specs/554_cs5_pair_seed_disjunction_property_cutfree_research/progress/phase-13-progress.json`
- Code: `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean`
- Source: `~/Projects/Literature/.sources-recovered/arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics.pdf`,
  pages 6 (Figure 2), 7 (Figure 3), 8 (Figure 4), 9-10 (Theorem 4.1, Lemmas 4.2-4.9)
