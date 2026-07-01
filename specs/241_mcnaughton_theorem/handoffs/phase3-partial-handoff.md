# Phase 3 Handoff — omegaPow_da_muller (task 241, McNaughton's theorem)

## Status: PARTIAL

Phase 3 is marked `[PARTIAL]` in `specs/241_mcnaughton_theorem/plans/02_mcnaughton-choueka-route.md`.
2 of 3 planned milestones landed green and committed. The third (hardest) milestone and the
final assembly were not attempted this dispatch — see the plan's Phase 3 section for the full
worked-out proof route with exact CSLib lemma names.

## What is done (committed, scoped-build green, sorry-free, standard axioms only)

- Commit `11807051`: `Cslib/Computability/Automata/DA/Choueka.lean` created with
  `DA.chouekaLang` (definition) and `DA.chouekaLang_regular` (regularity proof).
- Commit `602293de`: same file, added `DA.greater_subseq` (private helper) and
  `DA.chouekaLang_omega_limit_subset_omega_power` (the easier inclusion direction).
- Commit `6a1476d1`: plan file updated to `[PARTIAL]` with the full continuation.

Verified via `lake build Cslib.Computability.Automata.DA.Choueka
Cslib.Computability.Automata.DA.Concat Cslib.Computability.Automata.DA.MullerClosure
Cslib.Computability.Languages.OmegaRegularLanguage` (all green together) and
`lean_verify` on both new theorems (axioms: `propext`, `Classical.choice`, `Quot.sound` only).

## What remains

1. **`DA.chouekaLang_omega_power_subset_omega_limit`** (the Ramsey-based reverse inclusion) —
   NOT STARTED. Full proof route with exact lemma names is in the plan file's Phase 3 section
   (steps 1-5). This is the deepest remaining piece; step 5 requires porting a `Nat.find`-based
   breakpoint-search argument from `ctchou/AutomataTheory`'s `ChouekaLemma.lean:187-212`
   (cached locally at
   `/tmp/claude-1000/-home-benjamin-Projects-cslib-refactor-prop-logic/f23f339a-287d-446f-96b9-dad43b56c569/scratchpad/Languages_ChouekaLemma.lean`).
2. **`DA.chouekaLang_omega_power_eq_omega_limit`** — trivial `Subset.antisymm` assembly once (1)
   lands, using CSLib's already-existing `kstar_omegaPow_eq_omegaPow` /
   `kstar_hmul_omegaPow_eq_omegaPow` (`OmegaLanguage.lean:443,449`).
3. **`IsRegular.omegaPow_da_muller`** in `OmegaRegularLanguage.lean` — the final assembly
   combining (2) with `Language.IsRegular.kstar`, `Language.IsRegular.iff_dfa`,
   `chouekaLang_regular`, `IsRegular.omegaLim_da_muller` (already green), and
   `DA.concat_language_eq` (Phase 2, already green). Exact recipe is step 7 in the plan.
4. After (3): Phase 5 (`IsRegular.to_da_muller`) and Phase 6 (final `iff_da_muller` assembly +
   dead-cluster removal) remain as originally planned; they are unblocked once Phase 3 is
   fully green.

## Key files

- `/home/benjamin/Projects/cslib/Cslib/Computability/Automata/DA/Choueka.lean` (new file, 333
  lines, this dispatch's work)
- `/home/benjamin/Projects/cslib/Cslib/Computability/Automata/DA/Concat.lean` (Phase 2, already
  green — `concat_language_eq`)
- `/home/benjamin/Projects/cslib/Cslib/Computability/Automata/DA/MullerClosure.lean` (Phase 4,
  already green — `Muller.union`, `Muller.exists_iSup_univ`)
- `/home/benjamin/Projects/cslib/Cslib/Computability/Languages/OmegaRegularLanguage.lean` (not
  yet touched this dispatch; `IsRegular.omegaLim_da_muller` at line 81 already green; the
  `buchiCongr_DMA_accept_mem` Ramsey idiom at lines ~447-527 is the pattern to copy for step 4
  of the remaining proof)
- `/home/benjamin/Projects/cslib/specs/241_mcnaughton_theorem/plans/02_mcnaughton-choueka-route.md`
  (Phase 3 section has the full remaining proof route)

## Environment note

An unrelated concurrent-task file (`Cslib/Logics/Modal/Tableau/SoundnessStep.lean` and/or other
Logics/Temporal/Propositional files) may be in a broken/mid-edit state in the shared working
tree, blocking `lake exe checkInitImports`, whole-project `lake build`/`lake test`, and
`lake shake`/`lake lint`. This blocked full-pipeline verification this dispatch (matches the
same issue flagged by the Phase 2 and Phase 4 completion notes). Scoped builds of all
Phase-3-relevant modules are green independent of that unrelated breakage.

## Sorry inventory

Empty. No `sorry`/`admit` were introduced. No new axioms.
