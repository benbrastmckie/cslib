# Phase 8 Summary: Tableau Subtree (PARTIAL)

- **Task**: 180 - Add allFuture (G) and allPast (H) as primitive constructors to Temporal.Formula
- **Phase**: 8 of 9 (Tableau subtree scoped-green)
- **Status**: [PARTIAL]
- **Plan**: `specs/180_temporal_primitive_always_historically/plans/03_primitive-gh-metalogic-plan.md`

## What Was Done

### `Cslib/Logics/Temporal/Tableau/Defs.lean` -- GREEN

- `temporalFormulaHash`: added `allFuture`/`allPast` hash arms (constructor tags 5/6).
- `asAllFuture?`/`asAllPast?`: the WIP had authored these against the *old* Lukasiewicz
  encoding (`𝐆ψ = (⊤ U ¬ψ) → ⊥`), which stopped being definitionally equal to the *primitive*
  `𝐆`/`𝐇` constructor once Phase 1 promoted it. Rewrote both adapters to match the primitive
  constructor directly (`| .allFuture ψ => some ψ`). The universal-expansion *semantics*
  downstream in `Rules.lean` (`allFuturePosAt`/`allPastPosAt`) were already correctly shaped for
  a primitive constructor -- only the decomposition adapter needed the fix.
- `lake build Cslib.Logics.Temporal.Tableau.Defs` GREEN, no `sorry`.

### `Cslib/Logics/Temporal/Tableau/Rules.lean` -- GREEN

The actual defect here was **not** a missing G/H case -- `temporalApplyPos`/`temporalApplyNeg`
already dispatched through `asAllFuture?`/`asAllPast?` correctly. The defect was in the WIP's
*proof* layer (`temporalApplyPos_preserves`, `temporalApplyNeg_preserves`,
`temporalApplyOne_preserves`), which used `rcases <expr> with _ | y` on bare expressions
(`asAllFuture? sf.formula`, `asUntl? sf.formula`, `sf.sign`) rather than on hypotheses. `rcases`/
`cases` on a non-hypothesis expression only generalizes the goal *target*; it does not propagate
into other hypotheses (like the already-computed `h : temporalApplyPos sf b ord = (result,
newOrd)`). Every subsequent `simp only at h` therefore silently made no progress (confirmed with
`lean_goal`: `goals_before` identical to `goals_after`). This bug pre-dates task 180 -- the file
was WIP-edited but never independently compiled (Preserved-Assets table: "Verified: No").

Fix: replaced every such `rcases` with `split at h` (which correctly reduces `h` itself), chained
via `<;> try split at h` to fully unfold the case tree (matching the original bullet structure --
9 leaves for `temporalApplyPos_preserves`, 7 for `temporalApplyNeg_preserves`), then `rename_i` to
recover readable names for extracted formulas. Two more unrelated latent bugs surfaced once
elaboration reached far enough:
- `List.mem_cons_self` is argument-free in the current Lean/Std version; the WIP called it as
  `List.mem_cons_self _ _`.
- `simp only [List.mem_cons, List.mem_singleton] at hnf` left an unreduced `nf ∈ []` residual for
  2-branch `RuleResult.branching` results; needed `List.not_mem_nil, or_false` added.

`lake build Cslib.Logics.Temporal.Tableau.Rules` GREEN, zero `sorry`, zero lint-style warnings.

### `Cslib/Logics/Temporal/Tableau/{Closure,Branch,Saturation,Soundness,TimeOrdering}.lean` -- GREEN, verify-only

None of these files pattern-match `Formula` constructors directly; all temporal decomposition
routes through the `Defs.lean` adapters, so no edits were needed. All five build green.

### `Cslib/Logics/Temporal/Tableau/Completeness.lean` -- BLOCKED, untouched

`grep allFuture\|allPast` on this file returns **zero** matches -- the 90 build errors are not a
G/H problem. They are entirely confined to `private lemma temporalTruthLemma_propositional_aux`
(lines 403-767, ~360 lines), a large pre-existing WIP proof about purely propositional case
analysis (`.imp`/`.atom`/`.bot`), never independently compiled. Root cause: `simp only
[temporalApplyOne, tryAllPropRules, ...] at hout` delta-unfolds definitions into `hout` *before*
the subsequent `cases hφ'`/`cases hψ'` substitute concrete subformula shapes; the substitution
propagates correctly (since `hφ'`/`hψ'` are genuine hypotheses) but does not force the now-concrete
nested `match`/`if` inside `hout` to iota-reduce, leaving `hout` frozen at ~20 leaf branches. Left
untouched per PM5 (no edits attempted, no reverts) -- scoped as its own dedicated re-dispatch.

## Plan Deviations

- Phase 8 could not close in one dispatch; marked `[PARTIAL]` in the plan (not `[COMPLETED]`) per
  PM3/PM7 -- never fake green.
- The plan's task list anticipated adding G/H *cases* to Rules.lean; the actual required fix was
  repairing a pre-existing broken proof-tactic idiom (`rcases` on non-hypothesis expressions) that
  the constructor promotion happened to expose (by shifting the match structure enough that the
  file's elaboration reached these previously-never-compiled proof bodies). This is documented in
  detail in the Phase 8 section of the plan.
- Completeness.lean's breakage was discovered to be unrelated to G/H entirely; this was not
  anticipated by the plan and is flagged for a dedicated re-dispatch rather than folded into this
  phase's budget (PM1: one phase per run).

## Verification

- `lake build Cslib.Logics.Temporal.Tableau.Defs` -- GREEN
- `lake build Cslib.Logics.Temporal.Tableau.Rules` -- GREEN
- `lake build Cslib.Logics.Temporal.Tableau.{Closure,Branch,Saturation,TimeOrdering}` -- GREEN
- `lake build Cslib.Logics.Temporal.Tableau.Soundness` -- GREEN
- `lake build Cslib.Logics.Temporal.Tableau.Completeness` -- **RED** (90 errors, see blockers)
- `sorry` count in touched files: 0
- New axioms: 0
- Vacuous definitions: 0

## Next Steps

Re-dispatch Phase 8 targeting only `Completeness.lean`'s
`temporalTruthLemma_propositional_aux`. See `.orchestrator-handoff.json` `continuation_context`
for the detailed fix strategy.
