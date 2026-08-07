# Continuation Handoff: Plan 08, Phase 7.6 COMPLETE, Phase 7.7 open question

- **Plan**: `plans/08_reformulated-s4-redirect-sound-inv.md` (v7)
- **Date**: 2026-08-05
- **Dispatch scope**: finish Phase 7.6, then Phase 7.7 (assigned scope)
- **Outcome**: Phase 7.6 COMPLETE and verified. Phase 7.7 investigated (tasks 1-3 of 4
  confirmed) but task 4 (conjunct (d)'s discharge) surfaced a genuine open technical question,
  not forced through. No `sorry`, no vacuous placeholder, phase left `[IN PROGRESS]` with the
  finding recorded.

## What landed this dispatch (4 commits, all sorry-free where Lean was written)

1. **Phase 7.6 — COMPLETE.** `S4RedirectSoundInv_boxNeg_mint` and `S4RedirectSoundInv_diaPos_mint`
   (`FrameCompleteness.lean`), completing the six-item design from the prior dispatch's Progress
   Record. Supporting lemmas: `mem_boxPositivesOf_of_mem` (forward direction),
   `outDeg_addEdge_freshTarget_eq_zero`, `mem_mintPayload_{boxPos,diaNeg}_compensation`,
   `modalApplyOneS4Rules_{boxPos,diaNeg}_fst_notApplicable_of_mint`. One correction to the plan's
   own item-4 framing: `hmint` alone (via `modalNonMintCandidates_eq_nil_iff`) discharges the
   propositional/other-world case exactly as the blocked arm does, but the same-world
   box-positive/diamond-negative case needed the genuinely new P3-assembly lemmas above -- the
   blocked arm's `notApplicable_of_saturated` lemmas hold only at the OLD, unextended `acc` and
   do not survive the new mint edge without P3's compensation argument. Full verification:
   scoped build, `checkInitImports`, `lint-style`, full-project `lake lint` (confirmed zero
   findings in `FrameCompleteness.lean`), `#print axioms` (both arms: exactly `{propext,
   Classical.choice, Quot.sound}`), sorry census exactly 1, `git diff --stat` purely additive.

2. **Phase 7.7 — investigated, NOT landed.** Confirmed:
   - The `hacc` call site in `modalApplyOneS4Rules_{boxPos,diaNeg}_soundIn` is exactly one hop of
     `IsTrans`, matching the plan's Scope Hypothesis.
   - The ghost-successor case is genuinely vacuous via the dedup route: conjunct (c) forces the
     ghost target's box-positive/diamond-negative content already `∈ b`, which is exactly the
     `modalFourBoxProp`/`modalFourDiaNegProp` filterMap's own "already in b" dedup guard, so a
     ghost successor never even produces a candidate to reason about `hacc` for.
   - **Task 4 (discharge (a)/(c)/(d)) hit a real plan-vs-Lean mismatch.** The plan's note "(d)
     covered by the same `outDeg` argument as Phase 7.5" does not transfer: Phase 7.5's new
     formulas land at the FIRING CANDIDATE'S OWN world (whose `outDeg = 0` is forced by old
     conjunct (d)'s contrapositive), but the 4-rule shapes' new formulas land at a RECORDED
     SUCCESSOR world `w'` -- an ordinary, already-existing world whose `outDeg` is unconstrained
     by anything established in Phases 7.1-7.6. If a non-ghost successor `w'` has `outDeg acc w'
     ≠ 0`, conjunct (d) demands the freshly-produced `⟨.pos, .box φ, w'⟩` be `∈ e` (false, it was
     just created) or `.notApplicable` (no argument establishes this in general;
     `modalS4Saturated` is not available at a primary-scan call site, and no growth lemma applies
     since there is no PRIOR state with this formula on the branch to transport a fact from).

## Why this dispatch stopped here

Per this task's standing discipline (never commit a `sorry`, never force an unsound closure,
stop at a clean boundary), and given the genuine open technical content of the task-4 finding
(the plan's own Scope Hypothesis explicitly asked to "confirm which one actually applies rather
than assuming" -- this dispatch did exactly that and found the assumed route does not close),
writing the `_soundIn` restatements or arm theorems around an unresolved (d) discharge would
either require an unjustified assumption or a `sorry`, both prohibited. The full Progress Record
entry (plan file, Phase 7.7 section) records three candidate resolution routes for the next
dispatch to pursue.

## Next continuation step

1. Read the plan file's `#### Phase 7.7 Progress Record` subsection in full -- it is the
   authoritative continuation brief, not a repeat of it here.
2. Pursue one of the three candidate resolution routes recorded there:
   - Search `S4LoopInv`/`S4KeyedHintikkaInv`/`accTargetsKnown`-adjacent invariants
     (`LoopChecking.lean`) for anything bounding `outDeg` at a recorded successor world under the
     driver's actual processing order.
   - Investigate whether `S4RedirectSoundInv`'s conjunct (d) is too strong as stated for the
     4-rule arms specifically, and whether a definition-level weakening is warranted (this would
     require re-verifying every already-landed arm against the new definition, a much larger
     scope than a Phase-7.7-local fix).
   - If neither closes, escalate to the user: Phase 7's reformulation may need a further design
     iteration for the 4-rule case.
3. Only after (d)'s discharge is actually designed should the `_soundIn` restatements and the two
   arm theorems be written.
4. Phase 7.8 (the dispatcher) remains blocked until ALL of 7.3, 7.5, 7.6, 7.7 close -- 7.6 is now
   done, 7.7 is not.

## Verification performed this dispatch

- Scoped `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` green after every Lean-bearing
  commit (2 of the 4 commits touched Lean; the other 2 were plan-file-only).
- `#print axioms` via `lake env lean` (not `lean_verify`) on both new arm theorems.
- `lake exe lint-style` and `lake exe checkInitImports` clean throughout.
- Full-project `lake lint` run once (in background, ~15 min); confirmed zero findings anywhere in
  `FrameCompleteness.lean` (all findings reported are pre-existing, unrelated to files this task
  touches -- Bimodal/LTL/Propositional/Temporal modules).
- Sorry census (repo's canonical two-grep code-position form) exactly 1 at every checkpoint.
- `git diff --stat` / `git diff | grep '^-[^-]'` confirmed purely additive changes to
  `FrameCompleteness.lean` at both Lean-bearing commits.
