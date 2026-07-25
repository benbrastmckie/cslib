# Implementation Summary: Minimal Sequent Calculus (LM) and Three-Way MPL TFAE

- **Task**: 547 - minimal_sequent_calculus_lm_close_tfae_matrix
- **Status**: [COMPLETED]
- **Plan**: `specs/547_minimal_sequent_calculus_lm_close_tfae_matrix/plans/01_lm-sequent-calculus-tfae.md`
- **Report**: `specs/547_minimal_sequent_calculus_lm_close_tfae_matrix/reports/01_minimal-sequent-calculus-lm.md`

## Overview

Closed the `(SequentCalculus, Minimal)` hole in the proof-system × logic equivalence matrix. The
minimal sequent-calculus rules already existed in CSLib as `SeqProofMinimal := SeqProof MPL`
(reuse-first finding from the research report); the new work was three thin files mirroring the
LJ tree, a barrel, and the TFAE extension from a two-way to a three-way equivalence.

## Phases Completed (4/4)

1. **Phase 1 — `LM/Basic.lean`**: `LMProof` discoverability alias over `SeqProofMinimal`, and
   `not_isIntuitionistic_mpl` (proves `MPL` admits no `IsIntuitionistic` instance, so `botL` is
   structurally unconstructible).
2. **Phase 2 — `LM/Soundness.lean`**: `SeqProofMinimal.sound` — generalizes `LJProof.sound` from
   fixed `bot_forces = fun _ => False` to an arbitrary upward-closed `bf`; the `botL` case is
   discharged via `absurd (by assumption) not_isIntuitionistic_mpl`. Corollary
   `lm_msemantic_entails` feeds completeness.
3. **Phase 3 — `LM/Completeness.lean`**: 8 `lmAxiom…` proof trees (mirroring `ljAxiom…`, dropping
   `ljAxiomEfq`), `lmOfMinAxiom` dispatch, `ndToLM` translation (`efq` arm discharged via a new
   `not_isIntuitionistic_axiomTheory_minPropAxiom` helper, mirroring `not_isIntuitionistic_mpl`),
   and the `nd_iff_lm` / `hilbert_iff_lm` / `lm_iff_mvalid` bridges.
4. **Phase 4 — Barrel + TFAE + docstrings**: `LM.lean` barrel; `SequentCalculus.lean` import;
   `mplProofSystemsTfae` / `mplProofSystemsTfaeClosed` in `ProofSystemEquivalence.lean` (retaining
   `mplHilbertIffNd`); stale docstrings (module doc, lines 19–20; `mplHilbertIffNd` doc, line 116)
   corrected to no longer claim "no minimal sequent calculus exists in CSLib"; `Cslib.lean`
   registration via 4 targeted `Edit`-tool line insertions.

All four phases are marked `[COMPLETED]` in the plan file with checklist items checked off.

## Files Created / Modified

- `Cslib/Logics/Propositional/SequentCalculus/LM/Basic.lean` (new, ~65 lines)
- `Cslib/Logics/Propositional/SequentCalculus/LM/Soundness.lean` (new, ~150 lines)
- `Cslib/Logics/Propositional/SequentCalculus/LM/Completeness.lean` (new, ~290 lines)
- `Cslib/Logics/Propositional/SequentCalculus/LM.lean` (new barrel)
- `Cslib/Logics/Propositional/SequentCalculus.lean` (added `LM` import)
- `Cslib/Logics/Propositional/ProofSystemEquivalence.lean` (added `mplProofSystemsTfae`,
  `mplProofSystemsTfaeClosed`; corrected stale docstrings; retained `mplHilbertIffNd`)
- `Cslib.lean` (4 targeted line insertions registering the new `LM` modules, alphabetically
  placed after the `LK.SubformulaProperty` entry — **not** produced by `mk_all`)

## Verification

- **Zero sorry**: confirmed via `grep -n sorry` across all new/modified files — no matches.
- **Zero new axioms**: `grep -n "^axiom "` across new/modified files — no matches. Whole-repo
  `axiom` count (25) is the pre-existing baseline, unaffected by this task.
- **`lean_verify`** on `mplProofSystemsTfae` and `mplProofSystemsTfaeClosed`: both report only
  `["propext", "Classical.choice", "Quot.sound"]` — no unexpected axioms.
- **Scoped builds**: `LM.Basic`, `LM.Soundness`, `LM.Completeness`, `ProofSystemEquivalence` each
  built individually with zero errors; the only warnings were one pre-existing-pattern `Try this`
  linter hint (present identically in the accepted `LJ/Completeness.lean:308` and
  `LK/Completeness.lean:382`, not a regression) and two now-fixed issues (a long doc line, and a
  missing `omit [DecidableEq Atom] in` on the new axiom-theory helper).
- **Full project build** (`lake build`): succeeds, 3253/3253 jobs. Remaining warnings are all
  pre-existing `sorry`s in unrelated `Tableau/Intuitionistic/*` and `Tableau/Minimal/Completeness`
  files, untouched by this task.
- **`lake exe checkInitImports`**: exit 0, no output.
- **`lake lint`**: "Linting passed for Cslib." — zero warnings anywhere, including the new files.
- **`lake exe lint-style`**: zero output — clean.
- **`lake shake --add-public --keep-implied --keep-prefix`**: the only note attached to the new
  files is "remove `import Cslib.Init`" — an existing false-positive-style suggestion also present
  on the accepted `LJ/Basic.lean`, `LJ/Soundness.lean`, `LJ/Completeness.lean` (kept per CSLib's
  mandatory `Cslib.Init` import rule; not a regression). `LM/Basic.lean` had zero shake notes.
- **`lake test`**: exit 0, full `CslibTests/` suite passes.

## Plan Deviations

- **Phase 1**: Skipped the plan's optional `LMCutFree`/`CutFreeLMProof` re-exports — the plan
  itself flagged these as optional ("skip if they add lint surface without TFAE value") and they
  are not required by any TFAE theorem or the Non-Goals section.
- **Phase 2**: `lm_msemantic_entails` was proved directly via `d.sound` (mirroring the inline
  `h_entail` pattern already used in `nd_iff_lj`, `LJ/Completeness.lean:261`) rather than routing
  through `MSemanticEntails_of_MValid`, since the input is a proof tree, not an `MValid` fact.
  Semantically equivalent to the plan's suggested route.
- **Phase 3**: Added one helper not explicitly named in the plan,
  `not_isIntuitionistic_axiomTheory_minPropAxiom` (in `LM/Completeness.lean`), needed to discharge
  the `efq` arm of `ndToLM` — this mirrors `not_isIntuitionistic_mpl` from Phase 1 but at the
  distinct theory `AxiomTheory MinPropAxiom` rather than `MPL` itself, as flagged as a possibility
  in the plan's own strategy note ("discharged via `absurd` on the uninhabited
  `[IsIntuitionistic (AxiomTheory MinPropAxiom)]`").
- **Phase 4**: Barrel registration in `Cslib.lean` was done via 4 targeted `Edit`-tool line
  insertions rather than `lake exe mk_all --module`, per the concurrent-work notice (tasks 541 and
  543 were editing disjoint files in the same checkout, including their own barrel entries). A
  `lake exe mk_all --module` was accidentally run once for real during CI verification (intended
  as a dry comparison); it added one unrelated line for a concurrent task's file
  (`Cslib.Logics.LTL.EmbeddingSemantics`). This was caught immediately via `diff` against a
  pre-saved snapshot and reverted by restoring the snapshot, leaving `Cslib.lean` with exactly the
  4 intended LM lines (confirmed via `git diff Cslib.lean`). No other files were affected.

## Concurrent-Work Compliance

No files belonging to task 541 (`Cslib/Logics/LTL/EmbeddingSemantics.lean`) or task 543
(`Cslib/Foundations/Logic/PropositionalTableau.lean` deletion, `Tableau/PropositionalRules.lean`,
`Tableau/Sign.lean`, `Semantics/Algebra*`, `Semantics/Bool.lean`) were staged or committed by this
agent. Each phase commit was scoped via targeted `git add` of only the files this task touched;
`git status --short` was checked after every commit to confirm no foreign files were swept in.

## Commits

- `task 547 phase 1: LM/Basic.lean`
- `task 547 phase 2: LM/Soundness.lean`
- `task 547 phase 3: LM/Completeness.lean`
- `task 547 phase 4: barrel + TFAE + docstring fixes` (this phase, committed alongside this summary)

## Outcome

`mplProofSystemsTfae` and `mplProofSystemsTfaeClosed` are established, giving MPL a three-way
Hilbert ↔ ND ↔ LM equivalence structurally symmetric with the existing CPL (`LK`) and IPL (`LJ`)
rows. `mplHilbertIffNd` is retained unchanged for backward compatibility. The tableau system
remains out of all three TFAEs (scope guard for task 375 respected). Zero sorry, zero new axioms,
full CI order green.
