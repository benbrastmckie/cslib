# Implementation Summary: Propositional Coverage Gaps and the Ordering Overclaim

- **Task**: 618 - Close remaining coverage gaps in the propositional metatheory; correct the
  docstring that overclaims a result the tree does not prove
- **Status**: [COMPLETED WITH EXCLUSIONS]
- **Started**: 2026-08-10T00:00:00Z
- **Completed**: 2026-08-10T00:00:00Z
- **Effort**: 11 hours (estimated)
- **Dependencies**: None blocking. Task 614 (`computable_ctxtoimp_context_decidability`) was not
  landed at implementation time; Phase 4 proceeded against `ctxToImp` as-is, per the plan.
- **Artifacts**: plans/01_propositional-coverage-gaps.md, reports/01_propositional-coverage-gaps.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

All ten phases of the plan landed. Six docstrings that asserted unproved or non-existent results
(A1-A6) were corrected, one deliberate architectural absence (G9) was documented, and the
measured coverage gaps were closed: LJ cut-free completeness (B1), public general split
interpolation (B2), LM decidability (B3), `OrImpAxiom` completeness relative to IPL semantics
(D1-relative), and full LM parity with LJ via generalising LJ's cut elimination, subformula
property, and Craig interpolation from `IPL` to an arbitrary `Theory T` and instantiating each at
`MPL` (C1a, C1b, C2, C3). Every new/changed module builds, zero `sorry` was introduced, and every
verified headline theorem carries only the standard `{propext, Classical.choice, Quot.sound}`
axiom set.

## What Changed

- **Phase 1 (A1-A6, G9)**: corrected six overclaiming docstrings across
  `ConservativeChain.lean`, `Tableau/Classical/DecisionProcedure.lean`,
  `Tableau/Intuitionistic/DecisionProcedure.lean`, `CslibTests/TableauConformance.lean`,
  `Tableau/Minimal/DecisionProcedure.lean`, and `LJ/Basic.lean`; added a module-docstring note to
  `NaturalDeduction/Equivalence.lean` (G9).
- **Phase 2 (B1)**: added `SequentCalculus/LJ/CutFreeCompleteness.lean` with
  `ljCutFreeCompleteness` and `ljCutFreeIffIValid`.
- **Phase 3 (B2)**: added public `LKProof.splitInterpolation` / `LJProof.splitInterpolation`
  wrappers around the existing private Maehara cores.
- **Phase 4 (B3)**: generalised four LJ deduction-theorem helpers to `SeqProof T`; added
  `SequentCalculus/LM/Decidability.lean` (`instDecidableLMDerivable`,
  `instDecidableDerivableInMPL`).
- **Phase 5 (D1-relative)**: added an `OrImpAxiom` completeness theorem relative to IPL
  semantics on the and-bot-free sublanguage, docstring-qualified as such.
- **Phase 6 (C1a)**: generalised `LJ/CutElimination.lean`'s internal admissibility machinery
  (`LJCutIH`, the five `ljCutAdm*` lemmas) from `IPL` to `{T : Theory Atom}`; inverted the
  `CutFreeLJProof`/`CutFreeSeqProof` re-export direction; `LJProof.cutElim`'s signature is
  unchanged.
- **Phase 7 (C1b)**: added `SequentCalculus/LM/CutElimination.lean`
  (`SeqProofMinimal.cutElim`), instantiating the generalised admissibility machinery at `MPL`.
  Fixed a missing `open Theory` that caused the bare `MPL` identifier to silently auto-bind as a
  fresh local implicit instead of resolving to `Theory.MPL` (Lean's autoImplicit) -- this would
  have both broken elaboration and produced an unintentionally over-generalised statement had it
  type-checked.
- **Phase 8 (C2)**: generalised the subformula property
  (`ljCutFreeSubformulaProp`/`CutFreeLJProof.subformula_property`/`LJProof.subformula_property`)
  to `{T}`, re-exporting each original name at `IPL`; added
  `SequentCalculus/LM/SubformulaProperty.lean`.
- **Phase 9 (C3)**: generalised Craig interpolation (`ljMaeharaCore`/`ljCraigInterpolation`) to
  `{T}`, re-exporting `LJProof.splitInterpolation`/`LJProof.interpolation` at `IPL`; added
  `SequentCalculus/LM/Interpolation.lean`. Two `botL`-based derivations of `Γ ⊢ ⊤` in the
  IPL-specific original proved to be spurious under generalisation (`Γ ⊢ ⊥ → ⊥` needs only `ax`,
  not ex falso) and were replaced; the two genuine `botL` reconstructions (of the original
  proof's own `botL` node) extract their locally-bound `IsIntuitionistic T` instance via `letI`.
- **Phase 10**: this summary; full-scope verification (see Impacts and Follow-ups below).

`SequentCalculus/LM.lean` now imports all seven modules (`Basic`, `Soundness`, `Completeness`,
`CutElimination`, `SubformulaProperty`, `Interpolation`, `Decidability`), up from three at plan
time.

## Decisions

- **B2 public API shape**: bundled `CutFreeLKProof`/`CutFreeLJProof` wrappers; `maeharaCore`/
  `ljMaeharaCore` (renamed `seqProofMaeharaCore` under generalisation) stay `private`.
- **A2**: plain deletion of both the `:23` list entry and the dangling `:33-34` description;
  G6 (a `Fintype`-free decidability route) recorded as considered-and-not-taken, not attempted.
- **B3 vs. task 614**: did not block. Task 614 had not landed at implementation time, so Phase 4
  built against `ctxToImp` as-is and carries the `noncomputable` taint with an explicit docstring
  note.
- **Generic cut-elimination duplication**: rather than centralising a single public generic
  `SeqProof.cutElim` in `LJ/CutElimination.lean` (out of every consuming phase's declared file
  scope), each of Phases 7, 8, and 9 carries its own small file-local generic cut-elimination
  helper (`SeqProof.cutElim` / `seqProofCutElim` / `seqProofCutElim`), consistent with
  plan-compliance discipline of not widening a phase's declared file list mid-implementation.
  This is a known, accepted duplication (three near-identical ~35-line inductions); consolidating
  them into one shared generic declaration in `LJ/CutElimination.lean` is a reasonable future
  cleanup, not required for correctness.

## Impacts

- **Zero debt**: `grep -rn '\bsorry\b'` under `Cslib/Logics/Propositional/` returns only
  docstring prose (all "sorry-free" statements); zero vacuous definitions; the only `^axiom `
  grep hits are comment-prose false positives, not declarations -- no new axiom was introduced.
  Every new/changed headline theorem verified via `lean_verify` reports exactly
  `{propext, Classical.choice, Quot.sound}`.
- **Scoped builds all green**: every touched module builds individually
  (`LJ.CutFreeCompleteness`, `LK.Interpolation`, `LJ.Interpolation`, `LM.Decidability`,
  `OrImpConservative`, `LJ.CutElimination`, `LM.CutElimination`, `LJ.SubformulaProperty`,
  `LM.SubformulaProperty`, `LM.Interpolation`, `LM`), and the entire
  `Cslib.Logics.Propositional.SequentCalculus` subtree builds. A full top-to-bottom
  `lake build` reached 3330/3331 targets -- every module in the entire project, including every
  file this task touched -- before the one remaining target (see Follow-ups) failed.
- **A4 re-tensing verified split, not blanket**: `CslibTests/TableauConformance.lean`'s
  intuitionistic clause is past tense; the temporal clause remains present tense, citing the
  still-blocked `Temporal/Tableau/Completeness.lean:122` obligation.
- **A1 re-verified against Phases 6/8/9's new results**: neither generalisation phase proves
  strictness of the Imp → Int → Prop chain, so A1's "strictly"/"five" corrections were not
  reinstated on their strength.

## Follow-ups

1. **Full whole-repo CI gate blocked by an unrelated, pre-existing conflict (excluded from this
   task's scope; see "Reasoned Exclusions" in the plan's Phase 10).** `lake build` (and
   everything downstream of it -- `lake exe checkInitImports`, `lake lint`, `lake shake`,
   `lake test`) fails at the very last target, the top-level `Cslib.lean` barrel:
   `import Cslib.Foundations.Logic.Operators failed, environment already contains
   'Cslib.Logic.HasDiamond.casesOn' from Cslib.Foundations.Logic.Connectives`. This is task 619's
   in-flight `HasDia`/`HasDiamond` migration (both `Operators.lean` and `Connectives.lean` define
   `HasDiamond`), already committed on `main` (`b81f7e48`, `8d13fdba`) before this task's Phase 7
   began, and explicitly out of this task's territory. `lake exe lint-style` (text-only) and
   `lake exe mk_all --module` both ran successfully and are unaffected; `mk_all` added this
   task's six new modules to `Cslib.lean`'s import list (no other lines touched). Re-run the full
   CI pipeline once task 619 lands.
2. **D1-absolute** -- fragment-matched algebraic completeness for the `⟨∨,→,⊤⟩` signature. Needs
   an algebra class chosen and defined first, because the meet-free signature gives `→` nothing
   to residuate against. Warrants its own research pass. Not attempted here (declared Non-Goal).
3. **D2** -- the two separation theorems establishing `MPL ⊊ IPL ⊊ CPL`. Measured by the research
   as roughly one phase, NOT an open research problem: `⊥ → p` separates MPL from IPL (~15-25
   lines, via the one-point model `World := Unit`, `v _ _ := False`, `bf _ := True`), and
   `p ∨ ¬p` separates IPL from CPL (~30-50 lines, via a two-point Kripke chain), following the
   `CslibTests/ModalFrameSeparation.lean` hand-built-countermodel precedent to route around the
   `decide`/`WellFounded.fix` kernel-stall. Not attempted here (declared Non-Goal).
4. **G6** -- a `Fintype`-free `Decidable (Derivable PropositionalAxiom φ)` via the tableau route,
   coupled to A2's deletion. Considered and not taken; a separate judgment call outside this
   task's scope.

## References

- `specs/618_propositional_coverage_gaps_and_ordering_overclaim/plans/01_propositional-coverage-gaps.md`
- `specs/618_propositional_coverage_gaps_and_ordering_overclaim/reports/01_propositional-coverage-gaps.md`
- `specs/reviews/review-2026-08-10.md` (findings H3, M4 -- the originating review)
