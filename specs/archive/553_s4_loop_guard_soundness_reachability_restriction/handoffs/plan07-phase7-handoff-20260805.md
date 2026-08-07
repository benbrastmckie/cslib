# Handoff: Plan v6 (`plans/07_canonical-witness-truth-lemma.md`), Phase 7 continuation

- **Date**: 2026-08-05
- **Session**: sess_1785947077_74defa (continuation dispatch)
- **Plan**: `plans/07_canonical-witness-truth-lemma.md` (v6, latest; plans 01-05 superseded)
- **Status at handoff**: Phases 1-6 `[COMPLETED]`, Phase 7 `[NOT STARTED]`

## What landed this dispatch (all sorry-free, verified)

Re-scoped Phases 3-6 (per the `#### Phase 1 Verdict`) are now fully complete, folded into one
continuous piece of work. See the plan's `#### Phase 3-6 Completion Record` for the full
itemized list of landed declarations. In short:

1. **`modalS4Saturated_addEdge_of_blocked`** (`Cslib/Logics/Modal/Tableau/LoopChecking.lean`) --
   the hard content re-scoped Phase 3 left as an explicit hypothesis: `modalS4Saturated`
   preservation under the keyed redirect's `addEdge`, now UNCONDITIONALLY proved.
2. **`modalHintikkaSetS4_addEdge_of_blocked`** (`Cslib/Logics/Modal/Tableau/
   FrameCompleteness.lean`) -- assembles (1) with the three already-landed mechanical conjuncts.
3. **`branchSatisfiableIn_s4FC_addEdge_of_blocked`** (`Cslib/Logics/Modal/Tableau/
   FrameCompleteness.lean`) -- **the actual redirect-preservation capstone**: applies
   `modalTruthLemmaS4` at the redirect-extended accessibility with `extractModelS4` as witness.
4. `canonicalWitnessRestrictionProbe_agreementConditional` and its section header removed from
   `FrameSoundness.lean` (zero code dependents; one docstring cross-reference in
   `LoopChecking.lean` updated to point at the landed replacement).

Verification: scoped builds of all three touched files clean; `lake exe checkInitImports` and
`lake exe lint-style` clean; full `lake build` (3313 jobs) and `lake test` (including
`CslibTests.S4LoopGuardRegression`) both pass; bare-tactic sorry census over
`Cslib/Logics/Modal/Tableau/` returns exactly one line (`FrameSoundness.lean:1251`, the
standing, explicitly-retained sorry -- untouched). `lean_verify` AND a direct `lake env lean`
`#print axioms` check (to rule out the MCP tool's occasional `sorryAx` false positive on
multi-declaration files) both confirm every new declaration's axioms are exactly `{propext,
Classical.choice, Quot.sound}`.

## What remains: Phase 7

**Goal** (unchanged from the plan): wire `branchSatisfiableIn_s4FC_addEdge_of_blocked` into the
keyed ordered driver's per-step soundness argument, extend the regression corpus, and close out
with the full gate set (`lake build`, `lake lint`, `lake exe lint-style`, `lake test`, and,
since the file scope hasn't grown, likely also `lake shake` — not yet run this dispatch).

**Entry point**: `modalStepBranchS4KeyedOrdered` (`LoopChecking.lean:1439`) is the keyed ordered
driver's actual step function. Its structural case split,
`modalStepBranchS4KeyedOrdered_cases` (`LoopChecking.lean:1456`), is "the single case split
every other structural lemma below factors through" (its own docstring) -- start there. The
per-step soundness argument needs to show: whenever `modalStepBranchS4KeyedOrdered` returns
`some (newBs, newExps, newAcc, keys')`, and the incoming branch is `branchSatisfiableIn s4FC b
acc`, SOME `b' ∈ newBs` is `branchSatisfiableIn s4FC b' newAcc`.

**Why this is NOT an instance of the generic `modalStepBranchGen_preserves_satIn`**
(`FrameSoundness.lean:197`, verified at v5 planning time, not re-argued): that generic lemma's
`hAgree` hypothesis requires `apply` to agree with `modalApplyOne` off the two T/4-rule-relevant
shapes -- but the keyed guard's BLOCKED arm (at the two MINTING shapes, `F(□φ)`/`T(◇φ)`) departs
from `modalApplyOne` precisely there, adding a redirect edge instead of minting. A bespoke step
lemma is needed that case-splits on `modalStepBranchS4KeyedOrdered_cases`'s two branches (primary
non-mint-candidate scan vs. literal fallback traversal), and within the fallback traversal
further splits on whether the specific step blocks (redirects, consuming
`branchSatisfiableIn_s4FC_addEdge_of_blocked` at exactly the shape/hypotheses the guard's own
`blockingWorldS4Keyed` decision supplies) or proceeds as an ordinary K/T/4 step (reusing existing
machinery, likely close to what the generic lemma already does for the non-blocked shapes).

**Concrete sub-tasks, in likely order**:
1. Re-locate `modalStepBranchS4Keyed`, `modalStepBranchS4KeyedBody`, `modalNonMintCandidates`,
   `S4LoopInv` (all `LoopChecking.lean`) and `S4LoopInv.bClosure`/`S4LoopInv.keyLowerBd` by grep
   -- confirm these are exactly the `hUniv`/`hkL` hypotheses
   `branchSatisfiableIn_s4FC_addEdge_of_blocked` needs, and how a caller holding an `S4LoopInv`
   projects them out.
2. Determine which step(s) `modalStepBranchS4KeyedBody`/`modalStepBranchS4Keyed` can produce that
   actually invoke `blockingWorldS4Keyed` returning `some wBlock` (the redirect case) -- this is
   the ONLY case needing `branchSatisfiableIn_s4FC_addEdge_of_blocked`; every other step shape
   should reduce to existing K/T/4 soundness lemmas (`modalApplyOne_boxPos_sound` etc.,
   `SoundnessStep.lean`, read-only) the same way the T/S4 systems' own bespoke assemblies already
   do (see `FrameSoundness.lean`'s "Bespoke S5 Fuel-Induction Assembly" /
   "Bespoke Five/KB5 Fuel-Induction Assembly" sections for the established idiom to mirror --
   S4-keyed needs its own analogous section, not a reuse of those).
3. State and prove the bespoke step-preservation lemma, then the fuel-induction assembly over it
   (mirroring the existing per-system assemblies' shape).
4. Record the **layering note** the import graph forces (already flagged in the plan's Overview
   and Phase 7's own task list): soundness content for the keyed ordered driver now necessarily
   lives in `FrameCompleteness.lean`, since that's the only file seeing both `LoopChecking` and
   `FrameSoundness`.
5. Extend `CslibTests/S4LoopGuardRegression.lean` with a permanent witness row for the
   redirect-preservation result (keep every existing row unchanged, including the ordered-driver
   `"OPEN"` row on the counterexample formula).
6. Run the full gate set: `lake build` (whole library), `lake exe lint-style`, `lake lint`,
   `lake test`, and `lake shake --add-public --keep-implied --keep-prefix` (not yet run any
   dispatch this task -- confirm it is clean or fix reported unused imports).

**Constraints that still apply, unchanged**:
- File scope: `FrameCompleteness.lean`, `FrameSoundness.lean`, `LoopChecking.lean`,
  `CslibTests/S4LoopGuardRegression.lean`. `Rules.lean`, `Saturation.lean`, `Branch.lean`,
  `SoundnessStep.lean`, `Support/Accessibility.lean`, and everything under `Metalogic/**` stay
  read-only (this dispatch also did not touch `Support/Accessibility.lean`, keeping the new
  `successorsOf`/`addEdge` helper lemmas local to `LoopChecking.lean` instead, for the same
  reason).
- The standing sorry at `FrameSoundness.lean:1251` is retained by explicit user decision -- do
  not touch it. Sorry census must stay exactly 1 at every phase boundary.
- Never commit a `sorry`. If Phase 7's bespoke step lemma cannot be closed within one dispatch,
  mark it `[BLOCKED]` with the exact `lean_goal` state and return to the blocker record rather
  than sorrying it -- the pattern `modalS4Saturated_addEdge_of_blocked`/
  `branchSatisfiableIn_s4FC_addEdge_of_blocked` establish (a genuine, fully-proved lemma with an
  explicit hypothesis list, landed as forward progress) is the sanctioned way to split work
  across dispatches without sorrying.
- Re-locate every declaration by `grep -n '^def\|^lemma\|^theorem\|^structure\|^abbrev'`; no
  line number from any prior plan version or handoff (including this one) should be trusted
  without re-verifying via grep, since edits shift line numbers.
- **Tooling note discovered this dispatch**: the `lean_verify` MCP tool's `axioms` field can
  report a spurious `sorryAx` for a declaration that does NOT actually depend on `sorry` (a
  false positive, likely from its source-scan heuristic rather than a true `#print axioms`
  trace). If `lean_verify` ever reports `sorryAx` on a newly-landed declaration, cross-check with
  a direct `lake env lean` script (`import <module>; #print axioms <fully.qualified.name>`)
  before treating it as a real blocker -- do not assume the sorry is real without this check.

## Continuation entry point

Read the plan's `#### Phase 3-6 Completion Record` first (records exactly what landed and why),
then resume at Phase 7 per the sub-tasks above, starting from `modalStepBranchS4KeyedOrdered`
and `modalStepBranchS4KeyedOrdered_cases` (`LoopChecking.lean`).
