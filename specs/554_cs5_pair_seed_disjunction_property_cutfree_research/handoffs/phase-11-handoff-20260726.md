# Task 554 Continuation Handoff — After Phase 11

**Date**: 2026-07-26
**Session**: sess_1785046950_33beb4_554
**Plan**: `specs/554_cs5_pair_seed_disjunction_property_cutfree_research/plans/02_cutfree-pair-conservativity.md`

## State

Phase 11 (`Soundness auxiliary lemmas`, opening Stage D) is now COMPLETE. 11/32 phases done.
Scoped `lake build` for the new file is green. Whole-project `lake build` currently fails only in
`Cslib/Logics/Modal/Tableau/{CompletenessLoop,FiveSimplification}.lean` -- outside this phase's
territory, caused by a **concurrent session's uncommitted, in-progress** `LoopChecking.lean`
(confirmed via `git status`), not a regression from this phase. `Cslib/` sorry census unchanged
at 39, axiom count unchanged at 26, zero new axioms, zero new sorries.

## What Landed (Phase 11: `Nested/Soundness.lean`, new file)

A local Hilbert-combinator toolkit (mirroring `Translation.lean`'s established per-file
reproduction pattern: `private`, so no name clash) plus:

| Lemma | What it states | Proof route |
|---|---|---|
| 4.2 (`id`, `⊥•`) | `fm(Γ{a•,a°})`/`fm(Γ{⊥•,Π°})` provable for any `OutputCtx` `Γ` | induction on `Γ.fillFull`, `buildFullChain_fm` bridge |
| 4.3(i)-(v) | congruence: consequent, antecedent (contravariant), `∧`, `□`, `◇` | thin restatements of the local toolkit |
| 4.4 | `OutputCtx.fillFull` congruence (general, both LHS+RHS vary) | induction, new `cs5DerivAndImpCongr` for the singleton case |
| 4.5 | `InputCtx.fillLhs` contravariant congruence | restated `InputCtx.fillLhs_fm_antitone` (Phase 8, unchanged) |
| 4.6 (`w,c,∨°,□°,∧•,◇•`) | soundness of 7 one-premise rules | Lemma 4.4/4.5 + axiom instances |
| 4.7(i)-(iv) | branching congruence (2-hypothesis) | new `cs5DerivAndImpCongr2`, box/dia-and distributivity |
| 4.8 | `OutputCtx.fillFull` branching lift | induction using 4.7(i)/(iii) |
| 4.9 (`∧°`/`andR`) | `OutputCtx.fillRhs` branching lift + concrete `andR` corollary | mirrors `Translation.lean`'s `fillRhs_fm_mono` shape (simpler than 4.8, no singleton case) |

## Key Design Decisions Binding Successors

1. **Lemma 4.7(i)/(ii) share one Lean fact** (`lemma4_7_i_ii`): the source's page 10 displays both
   parts with the *same* visible conclusion formula, verified by direct page render (not just
   `pdftotext`, which independently corrupts this exact region). Both citations in Lemma 4.9's
   proof are discharged by the one lemma.
2. **`fillRhs` vs `fillFull` is a real fault line**, not an artifact of this phase's laziness: any
   rule whose premise and conclusion straddle the two filling operations (`diaR`, `impR`, `boxL`'s
   case-split, `orL`, `impL`, `cut`) needs a dedicated bridging argument this phase did **not**
   build (see "What NOT to Try" below) -- do not assume Lemma 4.4/4.8's `fillFull` machinery
   trivially covers a `fillRhs`-premise rule, or vice versa, without checking which shape each side
   actually has.
3. **`lemma4_9_fillRhs` mirrors `OutputCtx.fillRhs_fm_mono`'s two-case shape**, not Lemma 4.8's
   three-case one: `fillRhs`'s only special case is `ctx = []` (congruence against a fixed `⊤`);
   `ctx = Γ :: rest` is handled uniformly via `buildRhsChain_fm_and`, with no singleton-vs-general
   split needed (unlike `fillFull`, whose singleton case genuinely needs the and-uncurry
   combinator `cs5DerivAndImpCongr`/`cs5DerivAndImpCongr2`).

## What NOT to Try

- Do not assume `Lemma 4.6`/`Lemma 4.9`'s deferred rules (`diaR`, `impR`, `boxL`, `orL`, `impL`,
  `cut`) are trivial corollaries of what's landed -- each genuinely needs new machinery (see the
  plan's Phase 11 "Deviation" note for the precise reason per rule).
- Do not attempt `cut`'s Lemma 4.9 case before Phase 14 lands the `cut` constructor itself.
- Do not touch `Cslib/Logics/Modal/Tableau/` -- still owned by the concurrent task-553 session
  (uncommitted `LoopChecking.lean` changes present at handoff time); its build failure is not
  yours to fix.

## Literature Access This Session

Rendered PDF pages 6 (Figure 2, re-confirming `id`/`⊥•`'s input-context shape), 9, and 10 (Lemmas
4.2-4.9, Theorem 4.1) directly via `Read` with `pages`; cross-checked page 10 against
`pdftotext -f 10 -l 10 -layout`, which corrupts Lemma 4.7(ii)-(iv) at the box/diamond-adjacent
positions exactly as Phase 9/10 already documented for this PDF's font encoding.

## Next Action

Resume at **Phase 12: Theorem 4.1, propositional and `k` cases** (`nested_sound`'s case analysis,
same file `Nested/Soundness.lean`). Depends on Phase 11 (this phase, done). The plan's own task
list asks to "leave the modal/structural cases as explicit named holes closed in Phase 13 -- no
`sorry`"; Phase 12 will need to decide, per case, which of Lemma 4.2/4.4/4.5/4.6/4.8/4.9 applies
directly and which of the *deferred* rules (`diaR`, `impR`, `boxL`, `orL`, `impL`) need a fresh,
targeted derivation against the concrete `NestedProof` constructor (rather than waiting on a fully
general Lemma 4.6/4.9 corollary that this phase intentionally did not build).

## Scale Reminder

32 phases total. Stage D (Phases 11-13, soundness) is now 1/3 through. Each phase should still be
committed independently per the Commit-Per-Green-Substep Mandate (this phase landed 5 incremental
commits: toolkit+4.2+4.3, 4.4+4.5, 4.6, 4.7+4.8, 4.9).
