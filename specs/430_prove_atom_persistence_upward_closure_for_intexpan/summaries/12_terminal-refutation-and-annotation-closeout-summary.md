# Implementation Summary: Task #430 — Terminal Refutation and Annotation Close-Out

- **Task**: 430 - prove_atom_persistence_upward_closure_for_intexpan
- **Plan**: `plans/12_terminal-refutation-and-annotation-closeout.md`
- **Status**: [COMPLETED] (plan-level). This dispatch executed Phase 15 — the plan's only live
  phase — to completion. ODP-1 remains OPEN as a decision point, not a scheduled phase.

## What this dispatch did

Phase 15 ("Annotation and docstring close-out") is an annotation-only dispatch: it records, *in
the source*, the terminal refutation established by `reports/11_gap1-fixpoint-completeness.md`
and the machine-verified counterexample `scratch/BetaSplitRefutation.lean` (`phiRef1`). No
statement, proof, or `sorry` was added, removed, or relocated in content — only comments and
docstrings changed.

### Edits (four files, comments/docstrings only)

1. **`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`**
   - DP-5's sorry site (`truthLemma`'s T-imp case) re-annotated as **PERMANENTLY DEFERRED —
     unprovable as stated**, citing `scratch/BetaSplitRefutation.lean`/`phiRef1` and naming the
     mechanism (independent beta-splits at two augmented-preorder-equivalent worlds joined by a
     never-re-validated loop-back edge).
   - The Gap-1 STOP-gate note's stale "this measure has not been built" claim corrected via an
     appended **CORRECTION** paragraph (the original stale text is retained in place, per the
     plan's instruction not to delete the STOP-gate): cites
     `applyPersistenceFixpoint_genuine_of_count_le_fuel` (`:5386`) and
     `applyAllTImpRules_eq_self_of_length_eq` (`:5335`), and clarifies this does not discharge
     DP-3/DP-4/DP-5 (separately refuted).
   - The Phase-6 conjunct (`openBranch_countermodel`'s upward-closure existential) annotated at
     both its docstring and its inline pre-`sorry` comment as **DISPOSITION UNDECIDED**, gated on
     **ODP-1** — explicitly *not* annotated as REFUTED. The `[UNVERIFIED]` marker on the
     `fimpWitnesses`-to-existential-falsity inference is preserved verbatim, along with the
     raw-frame counter-consideration.
2. **`Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`**
   - `intFImpReuseWitnessAnc?`'s docstring gained a **"Recorded limitation: a FRAME-CONSTRUCTION
     defect, not a proof-route gap"** paragraph (reuse-time-only containment; the loop-back edge
     is never re-validated; the `phiRef1` mechanism; termination explicitly unaffected;
     `intExpandBranches_closed_unsat`/`Soundness.lean` remain sorry-free; two repair directions
     recorded as out of scope) and a **"Secondary finding"** paragraph on the reuse self-loop
     (`[(1,2),(2,2)]`, non-strict `x.ble w` guard, reflexive `isAccessible`).
   - One additional fix beyond the plan's enumerated tasks: the docstring's own opening line
     carried a pre-existing "task 574" citation (untouched by the two paragraphs above). Since
     this sat inside the exact docstring block already being edited, and the plan's own final
     verification bullet (`grep -nE 'task [0-9]+|tasks [0-9]+' ...` returns nothing) would
     otherwise fail, it was rephrased to "the ancestor-blocking calculus repair's Phase 3",
     matching this same file's established phrasing elsewhere (`Phase 3`/`Phase 4` used bare at
     lines 255 and 286 already).
3. **`Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean`**
   - DP-3's "Notes on sorry" section and `intuitionisticTableau_complete`'s docstring/inline
     comment re-annotated as **PERMANENTLY DEFERRED**, citing the same counterexample.
4. **`Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean`**
   - DP-4's "Notes on sorry" section and `minimalTableau_complete`'s docstring/inline comment
     re-annotated as **PERMANENTLY DEFERRED**, with its **independent** refutation under
     `isMinimallyClosed` recorded explicitly (not merely inherited from DP-3).

`Soundness.lean` and `Rules.lean` were not touched, per the plan's Files-to-modify list.

## Plan Deviations

- **Task 6 (optional §1.4 `case6` composition): dropped, not attempted.** The plan authorizes
  dropping this task if it does not compile within a small budget; rather than spend budget
  attempting an `[UNVERIFIED]`, never-compiled proof-term insertion into the `key` induction's
  `case6` arm — inside an `atomic-batch` phase whose Scope Hypothesis is annotation-only — this
  dispatch skipped it outright. It buys nothing toward the deferred sorries by the plan's own
  framing, and skipping it removed the only source of risk to the phase's annotation-only scope.
- **One fix beyond the enumerated task list**: the pre-existing "task 574" citation in
  `Expansion.lean`'s `intFImpReuseWitnessAnc?` docstring (see above). This was necessary to
  satisfy the plan's own final verification bullet and was a same-file, same-docstring-block,
  prose-only change.

## Verification (all commands actually run; output summarized)

- `lake exe cache get`: skipped — cache already warm for this branch (no full-rebuild fallback
  observed; scoped and full builds both completed in normal time).
- `lake build` (scoped, four touched modules): green.
- `lake build` (full project): **green, 3311 jobs.** Exactly 5 `declaration uses 'sorry'`
  warnings: `Scheme.lean:689` (DP-5), `Scheme.lean:7862` (Phase-6 conjunct),
  `Completeness.lean:150` (Intuitionistic, DP-3), `Completeness.lean:144` (Minimal, DP-4), and
  `FrameSoundness.lean:1252` (unrelated, pre-existing). Line numbers shifted from the original
  baseline (731/7884/146/141/1276) purely because of added comments — content confirmed
  unchanged by direct read of each site before and after.
- `lake exe checkInitImports`: exit 0.
- `lake lint`: repo-wide run produced ~360 pre-existing warning lines (unrelated modules,
  e.g. `Bimodal`, `LTL`, `Modal`); **zero** of them are in any of the four touched files
  (confirmed via targeted `grep`).
- `lake exe lint-style`: exit 0.
- `lake shake --add-public --keep-implied --keep-prefix`: findings in 8 pre-existing files
  (`TimeM.lean`, `Deterministic.lean`, `StackTape.lean`, `Defs.lean`, `NonDeterministic.lean`,
  `Confluence.lean`, `Free.lean`, `Basic.lean`, `CombinatoryLogic/Defs.lean`); **zero** in any of
  the four touched files.
- `lake test`: exit 0, 3788 jobs; `lake build CslibTests.TableauConformance` explicitly green,
  943 jobs.
- `lake exe mk_all --module`: "No update necessary."
- Sorry census: `grep -rnE '^[[:space:]]*sorry([[:space:]]*--.*)?$' --include='*.lean' Cslib/`
  returns exactly the same 5 declarations as the pre-dispatch baseline captured at Stage 0.
- Vacuous-definition grep: 1 hit, `Cslib/Computability/URM/Basic.lean:92`
  (`theorem J_IsJump ... := trivial`) — a real theorem with a non-trivial statement type, a false
  positive of the naive pattern, pre-existing and untouched.
- Axiom count: 26 `^axiom ` declarations repo-wide, none in the four touched files (confirmed by
  targeted grep); no axiom added or removed by this dispatch.
- `lean_verify`:
  - `intuitionisticTableau_complete`: `{propext, sorryAx, Classical.choice, Quot.sound}`
  - `minimalTableau_complete`: `{propext, sorryAx, Classical.choice, Quot.sound}`
  - `truthLemma`: `{sorryAx}`
  - `tableau_complete`: `{propext, sorryAx, Classical.choice, Quot.sound}`
  - `openBranch_countermodel`: `{propext, sorryAx, Classical.choice, Quot.sound}`
  - `intExpandBranches_closed_unsat`: `{propext, Classical.choice, Quot.sound}` — **no
    `sorryAx`**, confirming it remains sorry-free.
  - No new axioms anywhere; the `sorryAx` present is exactly the expected transitive one from
    the four permanently-deferred sorries.
- `git diff --stat -- Cslib/`: exactly the four files the Scope Hypothesis names, no fifth file.
  `git diff` line-by-line review: every changed line is a comment or docstring addition/edit; no
  statement, type signature, or tactic block changed.
- `git status --short Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean
  Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean`: empty (untouched).
- DP-2 (`intFreshMint_preserves_nw`, `Scheme.lean:4271` pre-dispatch): confirmed outside this
  dispatch's diff by content.
- `grep -nE 'task [0-9]+|tasks [0-9]+' Cslib/Logics/Propositional/Tableau/ -r`: returns nothing
  (after the one additional fix described above).
- Scratch evidence artifacts (`BetaSplitRefutation.lean`, `Gap1FixpointProbe.lean`,
  `HvalidShapeRefutation.lean`) confirmed present on disk, untouched, none deleted.

## Outcome

Phase 15 is `[COMPLETED]`. This plan's only live phase is finished; Phases 1-9 remain
`[COMPLETED]`, Phase 10 and Phases 11-14 remain `[COMPLETED WITH EXCLUSIONS]`. The plan-level
`Status` field is updated to `[COMPLETED]`. **ODP-1 (the Phase-6 conjunct's disposition) remains
OPEN** — it is a decision point requiring machine-checked confirmation or explicit human
sign-off, not a scheduled phase, and its openness does not block this plan's completion. No
successor persistence route, no quotient/blocking-frame reconstruction, and no calculus-level
repair of the loop-check were proposed or scheduled; all three remain explicitly out of scope
per the plan's Reasoned Exclusions and Non-Goals.
