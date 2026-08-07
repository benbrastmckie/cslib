# Implementation Summary: Task #430 — Terminal Refutation and Annotation Close-Out

- **Task**: 430 - prove_atom_persistence_upward_closure_for_intexpan
- **Plan**: `plans/12_terminal-refutation-and-annotation-closeout.md`
- **Status**: [COMPLETED] (plan-level). This dispatch executed Phase 15 — the plan's only live
  phase — to completion. ODP-1 remains OPEN as a decision point, not a scheduled phase.
- **Started**: 2026-07-30
- **Completed**: 2026-07-30
- **Artifacts**: `plans/12_terminal-refutation-and-annotation-closeout.md`,
  `reports/11_gap1-fixpoint-completeness.md`, `scratch/BetaSplitRefutation.lean`,
  `scratch/Gap1FixpointProbe.lean`, this summary
- **Standards**: Lean 4 / CSLib contribution conventions; annotation-only change set (no
  statement, signature, or proof-term modifications)

## Overview

The task set out to prove positive-formula persistence along the augmented accessibility
relation and thereby discharge three sorries at once. That goal is **not achievable**: the
statement is false. A machine-verified counterexample built by a closure-asymmetry recipe
exhibits two augmented-preorder-equivalent worlds that disagree on an atom, joined by a
loop-back edge the reuse witness never re-validates once recorded.

Permanent deferral of all three obligations was pre-authorized by the prior plan's own risk
analysis, which named this exact mechanism and specified terminal deferral (not escalation) if it
proved realizable. This close-out therefore records the refutation in the source rather than
continuing to build machinery against a false statement. No successor persistence route was
proposed, and the quotient / blocking-frame route remains prohibited.

One consequence is deliberately left unresolved rather than acted on: whether an already-landed
upward-closure conjunct is itself false rests on an inference that is argued but not
machine-checked, so it is recorded as an open decision point (ODP-1) and no landed code was
changed on its basis.

## What Changed

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

## Decisions

1. **Permanent deferral is authorized by mechanism, not by discovering phase.** Plan 06's
   line-218 risk row names the beta-split refutation shape and states that if realizable, the
   statement is FALSE and all three sorries are permanently deferred ("Refutation ⇒ terminal
   deferral, NOT escalation"). That authorization was read as scoped to the *mechanism*, so it
   fires even though the gating probe itself recorded a PASS and the refutation arrived later
   from a different candidate family (the closure-asymmetry recipe).

2. **The upward-closure conjunct is annotated DISPOSITION UNDECIDED, never REFUTED.** The
   inference from `fimpWitnesses = [1]` to "the whole `∃ edges` conjunct is false" is argued,
   not machine-checked, and carries an `[UNVERIFIED]` marker. Report 11 §6 recommends
   re-annotating the conjunct as REFUTED; that recommendation was deliberately declined, since
   §3.3 of the same report concedes the inference is unverified. Landed code was therefore left
   untouched on that point.

3. **The stale STOP-gate note was corrected by appending, not by deleting.** The original text
   claiming the fuel measure "has not been built" is retained in place with a correction
   paragraph appended, preserving the historical record rather than silently rewriting it.

4. **The optional `case6` composition was dropped without attempting compilation**, per its own
   authorized drop clause, rather than forced into place.

## Impacts

- **Public theorems**: no signature, statement, or proof term changed anywhere. Comment-stripped
  Lean source is byte-identical across all four touched files, so the annotation-only claim is
  mechanically established rather than asserted.
- **Sorry set**: unchanged in membership. `Soundness.lean` remains sorry-free.
- **Superseded criterion**: the original bar (`grep -n sorry` returning no bare sorry in both
  `Completeness.lean` files) is now unachievable, not merely unmet — the obligations are
  unprovable as stated. It is formally retired.
- **Preserved assets**: nothing sorry-free that landed earlier is false. The raw-edge
  persistence export still holds, confirmed against the refuting witness itself.
- **Downstream**: the defect is characterized as a frame construction issue — containment
  validated at reuse time, the loop-back edge never re-validated once recorded. This is
  calculus-level, not proof-route. Termination is unaffected.

## Follow-ups

Neither item below is scheduled work, and neither blocks this close-out. Both need a human
decision before anything is acted on.

1. **ODP-1 — disposition of the upward-closure conjunct.** Resolve whether it is genuinely
   false by machine-checking the `fimpWitnesses` inference, or record explicit sign-off. If it
   is false, a `sorry` currently stands for a false statement, which is worth removing. Until
   then, revert / weaken / delete / restate of that conjunct are all explicitly unauthorized.

2. **Frame-construction repair of the reuse witness.** Re-validating the loop-back edge after
   it is recorded is a calculus-level change, outside this task's scope and not proposed here.
   It would be a separate task. The quotient / blocking-frame reconstruction route remains
   PROHIBITED and must not be revived as a substitute.

## References

- `reports/11_gap1-fixpoint-completeness.md` — two-part verdict: the fixpoint question is
  provable and already landed; the residual beta arm is refuted.
- `scratch/BetaSplitRefutation.lean` — the machine-verified counterexample. Independently
  re-verified during orchestration: compiles exit 0 with zero errors and zero sorries,
  `branchesAgree` and `minBranchesAgree` both `true` (the recreated loop returns exactly the
  branch the real decision procedures return), violation `some (2, 1, 2)` at the real fuel,
  `decisiveFacts = (true, false)`, 3 of 4 candidates refuting.
- `scratch/Gap1FixpointProbe.lean` — empirical probe behind the provability half of the verdict.
- `handoffs/10_origin-tracing-scoping-and-new-blocker.md` — the scoping pass that narrowed the
  invariant and surfaced the blocker.
- `handoffs/07_post-reuse-closure-verdict.md` — the earlier COLLAPSED verdict and the exact
  shape of the residual sub-case.
- `plans/12_terminal-refutation-and-annotation-closeout.md` — governing plan for this close-out.
