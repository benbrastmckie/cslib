# Phase 12 Handoff: Theorem 4.1, Propositional and `k` Cases

**Status**: implemented (skeleton) -- 7 of 10 target constructors fully proven, 2 landed as
documented strategic sorries, 1 (`impL`) deferred per Phase 11's own note (unchanged from before
this phase).

## Immediate Next Action

Phase 13 ("Theorem 4.1, modal and structural cases") should discharge `boxL`, `boxR`, `diaL`,
`diaR`, `tL`, `tR`, `fourL`, `fourR`, `bStruct`, then assemble the top-level `nested_sound`
function from all landed per-case lemmas (this phase's `nested_sound_botL`/`andL`/`andR`/
`orRLeft`/`orRRight`/`contract`/`impR` plus Phase 13's own new lemmas plus the two strategic
sorries `nested_sound_id`/`nested_sound_orL`). The assembled `nested_sound` will itself carry
the two inherited sorries -- this is expected and tracked (see `sorry_inventory` below).

## Current State

`Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean` now has (in addition to Phase
11's Lemma 4.2-4.9 family):
- `cs5DerivOrElim`, `cs5DerivDiaBotElim`, `buildRhsChain_of_derivable`, `cs5DerivFillRhsOfDerivable`
  (small toolkit additions)
- `lemma_botL_lambda_core`, `nested_sound_botL` (⊥• soundness, fully proven)
- `nested_sound_andL`, `nested_sound_andR`, `nested_sound_orRLeft`, `nested_sound_orRRight`,
  `nested_sound_contract` (fully proven, thin `modus_ponens` wrappers over Phase 11's lemmas)
- `cs5DerivCurrySwapSchema`, `buildFullChain_imp_buildRhsChain`, `fillFull_imp_fillRhs`,
  `nested_sound_impR` (fully proven; resolves Phase 11's deferred `impR` bridging induction)
- `nested_sound_id`, `nested_sound_orL` (both `sorry`, documented strategic holes)

Scoped `lake build` for this module is green (2 documented sorries only). Whole-project `lake
lint`/`checkInitImports`/`lint-style`/`mk_all --module` are all clean for this file (the one
`lake lint` error remains the pre-existing, out-of-territory `Temporal/Tableau/Saturation.lean`
issue noted by Phases 10-11).

## Key Decisions Made

1. **`botL`'s general-`Λ` soundness is resolvable** (unlike `id`/`orL`) via a new combinator
   `cs5DerivDiaBotElim : ⊢ ◇⊥ ⊃ ⊥`, derived from `efq` (`⊥ ⊃ □⊥`), `◇`-monotonicity (`kdia`), and
   `bDia` (`◇□X ⊃ X`). This works *only* because the target is `⊥` (absorbing under `efq`) --
   it is not a template that generalizes to `id`'s bare-atom target or `orL`'s disjunction target.
2. **`impR` is fully resolvable**, not merely "hard": `OutputCtx.fillFull` and `OutputCtx.fillRhs`
   both bottom out through `.box` in their recursions (never `.dia`), so `tBox` (`□X ⊃ X`)
   reconciles the one-extra-box mismatch at the base case, and curry/uncurry
   (`cs5DerivCurrySwapSchema`) handles the singleton case. No new axiom was needed.
3. **`id` and `orL` are genuinely blocked for `Λ`-depth ≥ 2** -- this is the phase's main finding,
   not a "ran out of time" deferral:
   - `id`: needs `⊢ ◇X ⊃ X` for arbitrary `X` (a "diamond can be shed" step). No dual of `tBox`
     exists for `◇` in `CS5ModalAxiom`. **Concrete counterexample**: instantiating `Γ' := []`,
     `Λ := [.empty, .empty]` in `id`'s constructor reduces the needed soundness fact to
     `⊢ ◇a ⊃ a` for an arbitrary atom `a` -- false in any non-degenerate frame (would force every
     accessible world to agree with the root on every atom). This is evidence against `id`'s
     current fully-general `(Γ' Λ : OutputCtx)` signature in `Rules.lean`, not against this
     phase's proof effort.
   - `orL`: needs `⊢ ◇(X ∨ Y) ⊃ (◇X ∨ ◇Y)` at `Λ`-depth ≥ 2 -- exactly `kdisj`
     (`Intuitionistic/IS5.lean`'s axiom), deliberately absent from `CS5ModalAxiom`. Depth ≤ 1 is
     fully provable by pure propositional reasoning (`orE`) with no diamond involved.
   - Both obstructions share the same root cause: `OutputCtx.fillLhs`'s recursion inserts a
     `.dia` (not a `.box`) past depth 1, and `CS5` (unlike its box side, via `tBox`) has no way to
     "shed" that diamond for an arbitrary wrapped formula.

## What NOT to Try

- Do not attempt to prove `nested_sound_id`/`nested_sound_orL` via a stronger induction
  hypothesis (e.g., carrying `□a` or `◇a` instead of `a` through the recursion) -- multiple
  strengthenings were tried (see the module docstring and this session's analysis) and all reduce
  to the same unavailable "diamond-shedding" step, or to a false base case (`a ⊃ □a`).
  `fourDia` (`◇◇X ⊃ ◇X`) *does* let you collapse nested diamonds down to one, but you are always
  left with exactly one `◇` that cannot be removed without `◇X ⊃ X` or `kdisj`.
  `bBox`/`bDia`/`fourBox` were also tried and do not bridge the gap (they govern box/diamond
  duality and iteration, not a connective's distribution or a bare-formula collapse).
- Do not try to reuse Phase 11's `lemma4_2_id` (for `OutputCtx.fillFull`) as a template for `id`'s
  `InputCtx.fillLhs` case -- they are structurally different (`fillFull`'s recursion is
  `.box`-based with no diamond at all; `fillLhs`'s is `.dia`-based), confirmed by direct
  computation on a length-2 example.

## Remaining Goals (verbatim from plan)

Phase 12's own remaining item: none -- all Phase 12 tasks are checked off (see the plan file's
Deviation note for the exact scope of what "discharged" means: 7/10 constructors, 2 strategic
sorries, `impL` untouched per Phase 11's precedent).

The two strategic sorries are **not** Phase 12's or Phase 13's job to close via more Lean
cleverness -- they require either (a) a `Rules.lean` change to `id`'s (and possibly `orL`'s)
signature, restricting or re-deriving the `Λ` parameter, or (b) accepting a weaker soundness
theorem that only covers `Λ`-depth ≤ 1 for these two constructors. This is a decision for the
task owner / a follow-up research phase, not something to force through implementation.

## References

- Plan: `specs/554_cs5_pair_seed_disjunction_property_cutfree_research/plans/02_cutfree-pair-conservativity.md`
  (Phase 12 section, updated with the Deviation note)
- Progress: `specs/554_cs5_pair_seed_disjunction_property_cutfree_research/progress/phase-12-progress.json`
- Code: `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean`
- Source: `~/Projects/Literature/.sources-recovered/arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics.pdf`,
  pages 6 (Figure 2), 8-10 (Theorem 4.1, Lemmas 4.2-4.9)
