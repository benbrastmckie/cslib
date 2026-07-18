# Blocker Analysis: Task #525

**Parent Task**: #525 - KB5 tableau completeness + kb5Valid decidability
**Generated**: 2026-07-18
**Blocker**: `modalTruthLemmaKb5` is mathematically false for task 524's frozen
`modalApplyOneKb5'` rule (proven in-repo as `extractModelKb5_nonRoot_boxPos_gap`,
`FrameCompleteness.lean`, with concrete witness φ₀ = ¬◇◇□p). The rule's box-positive/diamond-
negative 0-target arm is gated on trigger-identity (`w == 0`) in addition to cluster-nonemptiness,
but the extraction's closure relation lets non-root triggers reach the root once symmetry pulls
the root into the cluster — so the rule under-emits relative to what the extracted model actually
satisfies.

## Root Cause

Diagnosed precisely by the architecture investigation report
(`specs/525_kb5_completeness_and_decidability/reports/02_s5-architecture-investigation.md`):
a single misplaced boolean gate, not a structural dead end.

- `modalKb5BoxAllFull`'s world-0-target arm (`Cslib/Logics/Modal/Tableau/FiveSimplification.lean:1544`,
  dually the diamond-negative arm at `:1561`) is gated on `w == 0 && clusterNonempty`. The
  membership dichotomy `modalKb5BoxAllFull_mem` (`:1573`) confirms a `0`-labeled output requires
  the trigger to be literally `0`.
- The correct gate is `clusterNonempty` alone: drop the trigger-identity conjunct so a non-root
  trigger also dumps its box-positive content onto world 0 when the cluster is connected to the
  root. The mint arms (`T(◇φ)`/`F(□φ)`) stay untouched — task 524 already established
  (`FiveSimplification.lean:1517-1522`, and the R7 refutation at `S5Simplification.lean:1944-2035`)
  that existential shapes must keep witness-reuse mints or termination diverges; only the
  universal-shape gate changes.
- `extractModelKb5` (`Relation.EuclGen (Relation.SymmGen acc.hasEdge)`,
  `FrameCompleteness.lean:3230`) is **already** the total/universal cluster on the connected
  branch-edge world set (the least PER over a connected symmetric graph is total on its field).
  No re-extraction and no new "cluster-membership bookkeeping device" is needed: cluster
  membership for KB5 is exactly known-world-ness, already certified by the landed
  `accReachableInv` invariant (`FrameSoundness.lean`) and consumed by task 524's soundness proof.
- Handoff fix (ii) — keep the trigger-gated rule, change the extraction instead — is a proven
  dead end: the scout-lemma remark at `FrameCompleteness.lean:3507-3511` shows any kb5FC-satisfying
  relation preserving raw edges forces `r w 0` for chain-connected non-root `w`, so no admissible
  extraction can rescue a root-trigger-gated rule.
- Soundness of the corrected rule is nearly free. Task 524's semantic lemma family is already
  trigger-agnostic and covers three of the four `(trigger, target)` cases; only the new
  `w ≠ 0, v = 0` case needs a one-line symmetrization:

  | Obligation (trigger `w`, target `v`) | Landed discharge |
  |---|---|
  | `w = 0`, `v ≠ 0` | `reachable_imp_related_kb5` (`FrameSoundness.lean:1582`) |
  | `w ≠ 0`, `v ≠ 0` | `accReachableInv_related_kb5` (`FrameSoundness.lean:1610`) |
  | `w = 0`, `v = 0` | `accReachableInv_kb5_root_refl` (`FrameSoundness.lean:1633`) |
  | `w ≠ 0`, `v = 0` (**new**) | `Std.Symm.symm` of `reachable_imp_related_kb5` (one-liner) |

- Truth-lemma coverage: task 525's already-landed Phase 1 (`symmEuclGen_mem_modalKnownWorlds_iff`,
  `extractModelKb5_root_reach_mem_modalKnownWorlds`) and Phase 2 (`modalKb5BoxAllFull_mem_of`,
  `modalKb5DiaNegAllFull_mem_of`, `hintikkaKb5'_box_pos`, `hintikkaKb5'_diamond_neg`) survive as
  reusable assets, but the Phase 2 Hintikka lemmas are pinned to the frozen rule's
  trigger-sensitive membership dichotomy and need mechanical re-derivation against the corrected
  rule's simpler, trigger-free dichotomy (known-non-root target, or target `0` with cluster
  nonempty).
- Out of scope, orthogonal, and explicitly NOT folded into the fix: the pre-existing `lake test`
  `decide` kernel stall in `modalExpandBranchesGen`'s fuel recursion
  (`S5Simplification.lean:1959-1963`) — unrelated to the rule gate, tracked separately per the
  architecture report's Section 5 recommendation.

## Proposed New Tasks

### New Task 1: Corrected-gate KB5 tableau rule, soundness, and completeness
- **Effort**: ~10-14 hours (task-524-sized)
- **Task Type**: cslib
- **Rationale**: This is the single coherent fix that unblocks task 525's Phase 3
  (`modalTruthLemmaKb5`) and everything downstream of it (Phases 4-7: open-branch supply lemmas,
  completeness assembly, decidability instance, docstring reconciliation, CI). The four sub-parts
  (new rule, its soundness, the truth lemma/completeness chain, and CI/docstring reconciliation)
  share the same files, the same frozen-524-reuse dependencies, and each step's proof obligations
  are only meaningful once the prior step's declarations exist — splitting them into separate
  tasks would create tasks that cannot be independently planned or verified (a soundness proof
  needs the new rule's exact statement in hand; the truth lemma needs the soundness proof's case
  table to know which reachability facts are actually available). Per the scope guidance, this
  is preferred as ONE task over a multi-task split.
- **Depends on**: None (internally)

## Dependency Reasoning

Only one new task is proposed, so there is no internal dependency graph to reason about within
`new_tasks[]`. However, task 525 itself must be made to depend on this new task: task 525's
plan (`specs/525_kb5_completeness_and_decidability/plans/01_kb5-completeness-decidability.md`)
Phases 3-7 are `[BLOCKED]` precisely because `modalTruthLemmaKb5` cannot be proved against the
frozen `modalApplyOneKb5'` rule. Once the new task lands the corrected-gate rule
(`modalKb5BoxAllUniv`/`modalKb5DiaNegAllUniv` or equivalent naming), its soundness theorem, its
truth lemma, and its completeness/decidability assembly, task 525's remaining phases become
either (a) redundant (fully absorbed by the new task, in which case task 525 should be marked
superseded/completed by reference to the new task's declarations) or (b) reduced to the thin
reconciliation/CI verification the new task's own Phase-analogue (item 4 in the scope guidance)
already performs. Either way, task 525 cannot proceed independently of this new task's rule
definition, so the dependency is: **task 525 depends on New Task 1**, because the specific
identifiers, gate condition, and lemma names New Task 1 chooses (e.g. whatever it names the
corrected rule and its truth lemma) are exactly what task 525's remaining phase content must be
rewritten around or retired in favor of.

## After Completion

Once the new task is complete, resume task 525 with `/implement 525` (or mark it superseded if
the new task fully absorbs its remaining phases — determined at task 525's resume time by
diffing the new task's landed declarations against task 525's Phase 3-7 goals).

The blocker will be resolved because: the new task lands a KB5 tableau rule whose 0-target
box-positive/diamond-negative arm fires on cluster-nonemptiness alone (not trigger-identity),
which is sound against `kb5FC` (reusing task 524's trigger-agnostic semantic lemma family plus
one new one-line symmetrization case) and against which `modalTruthLemmaKb5`'s root case can
actually be proved true (per the architecture report's Section 2.3 discharge sketch) — dissolving
the exact gap that `extractModelKb5_nonRoot_boxPos_gap` demonstrated for the frozen rule.
