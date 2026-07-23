# Implementation Plan: Merge KB5 Prime and Double-Prime Rule Variants

- **Task**: 531 - Merge KB5 prime and double-prime tableau rule variants
- **Status**: [COMPLETED]
- **Effort**: 3.5 hours
- **Dependencies**: None (the concurrent FrameCompleteness.lean docstring task has already landed; no sequencing conflict remains)
- **Research Inputs**: reports/01_kb5-prime-doubleprime-merge-research.md
- **Artifacts**: plans/01_retire-kb5-prime-family.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

The two KB5 tableau propagation-rule families in `Cslib/Logics/Modal/Tableau/` differ in exactly
one boolean conjunct: the `Univ` (double-prime) family drops the `w == 0` self-target guard that
the `Full` (prime) family carries. Research established that `Univ` is the corrected, sound and
complete rule and the **sole** support of the public API (`instDecidableKb5Valid`,
`kb5Valid_decides`, `modalTableauKb5''_complete`, `modalTableauKb5''_sound`), while the `Full`
family is a self-contained **dead branch**: it compiles sorry-free but every result is consumed by
nothing downstream, terminating at the trophy capstone `modalTableauKb5'_sound` (referenced only in
docstrings). The merge is therefore "confirm-then-retire", NOT a re-prove: confirm `Univ` already
discharges every live obligation (it does), then delete the ~57 `Full`/prime declarations across
three code files. **Definition of done:** `FrameCompleteness` builds green (880 jobs), sorry-free,
`kb5Valid_decides` axiom-clean (`[propext, Classical.choice, Quot.sound]`), and zero references to
any retired prime symbol remain anywhere in `Cslib/`.

### Research Integration

The plan integrates the full line-numbered declaration inventory from
`reports/01_kb5-prime-doubleprime-merge-research.md` (Section 3a lists the retirement candidates;
Section 4 gives the body-level-grep-verified dependency graph confirming zero downstream
consumption of the prime branch). The retirement is ordered leaf-consumer-first: the prime chains
in `FrameSoundness.lean` and `FrameCompleteness.lean` (consumers of `FiveSimplification`'s `Full`
definitions) are deleted before the `FiveSimplification.lean` base definitions, so each phase
leaves a green build with no dangling references. Recommended Option A1 (drop
`modalTableauKb5'_sound` outright) is adopted over Option A2 (aliasing), because A2 would make
`Full` "complete" and contradict the incompleteness counterexample
`extractModelKb5_nonRoot_boxPos_gap`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No roadmap_flag set; ROADMAP.md not consulted for this plan.

## Goals & Non-Goals

**Goals**:
- Retire the entire `Full`/prime KB5 rule family (~57 declarations) across `FiveSimplification.lean`,
  `FrameSoundness.lean`, and `FrameCompleteness.lean`.
- Preserve the `Univ`/double-prime family and the public API unchanged.
- Relocate the incompleteness-counterexample mathematical content (`extractModelKb5_root_reach_scout`,
  `extractModelKb5_nonRoot_boxPos_gap`) into a `Univ` module docstring (durable anchor) rather than
  keeping it as dead executable code.
- Update all cross-referencing docstrings (including `S5Simplification.lean`) that name prime symbols.
- Keep the build green and sorry-free after every phase; keep `kb5Valid_decides` axiom-clean.

**Non-Goals**:
- Renaming the surviving `modalApplyOneKb5''` rule to a suffix-free canonical name (optional churn;
  the unprimed `modalApplyOneKb5` is already the Five-alias, so a rename is riskier and out of scope).
- Re-proving or restating any `Univ`/public result (no downstream re-proof is required).
- Option A2 aliasing of `modalTableauKb5'_sound`.
- Any change to the `Univ` rule's semantics or its supporting foundations.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Deleting `FiveSimplification` `Full` base defs before their consumers leaves dangling references (red build) | H | M | Order phases leaf-consumer-first: `FrameSoundness` (P1) and `FrameCompleteness` (P2) before `FiveSimplification` base (P3); build green after each phase |
| Prefix confusion deletes a `Univ` (`Kb5''`) keeper decl instead of a `Full` (`Kb5'`) one | H | L | Delete against the exact line-numbered Section 3a inventory; rely on the green-build gate + axiom check to catch any keeper breakage |
| Stale docstring references to retired prime symbols remain | M | M | Final grep sweep (P4) asserts zero remaining references to every Section 3a symbol across `Cslib/`, including docstrings |
| Axiom regression in `kb5Valid_decides` | H | L | `lean_verify` the capstone's axioms are unchanged `[propext, Classical.choice, Quot.sound]` in P1 baseline and P4 final |
| Losing the counterexample's mathematical insight when deleting the cluster | M | M | Relocate its content into a `Univ` module docstring in P2 before deleting the executable lemmas |
| A new `sorry`/`admit`/`axiom`/`native_decide`/`@[nolint]` introduced during edits | M | L | Retirement is pure deletion; P4 scans all four in-scope files confirm none introduced |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |
| 3 | 4 | 3 |

Phases within the same wave can execute in parallel (Phases 1 and 2 touch different files and are
independent prime chains). In orchestrator_mode dispatch may still run them sequentially; either
ordering is safe because each leaves a green build.

### Phase 1: Confirm baseline and retire FrameSoundness prime chain [COMPLETED]

**Goal**: Establish the pre-retirement ground truth, then delete the self-contained prime soundness
sub-chain in `FrameSoundness.lean` (dead-ends at `modalTableauKb5'_sound`).

**Tasks**:
- [x] Confirm baseline: `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` green (880 jobs, sorry-free).
- [x] Confirm baseline axioms: `lean_verify` `kb5Valid_decides` = `[propext, Classical.choice, Quot.sound]`.
- [x] Delete `modalTableauKb5'_sound` (FS 5810) — the trophy capstone consumed by nothing.
- [x] Delete `modalExpandBranchesKb5'_closed_unsatIn` (FS 5472).
- [x] Delete `modalStepBranchKb5'_preserves_accReachableInv` (FS 3437) and `modalStepBranchKb5'_preserves_satIn` (FS 4384).
- [x] Delete `modalKb5BoxAllFull_soundIn` (FS 3136) and `modalKb5DiaNegAllFull_soundIn` (FS 3196).
- [x] Update `FrameSoundness.lean` docstrings that name the retired prime symbols. *(deviation: two remaining docstring mentions in FiveSimplification.lean referencing these now-deleted FrameSoundness symbols are deferred to Phase 3, since FiveSimplification.lean is that phase's target file)*

**Timing**: 0.75 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` - delete the six prime-soundness declarations and their docstring references

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FrameSoundness` green, sorry-free.
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` still green (downstream unaffected).
- Grep confirms no remaining references to the deleted `FrameSoundness` prime symbols in that file.

---

### Phase 2: Retire FrameCompleteness prime cluster and counterexample [COMPLETED]

**Goal**: Delete the prime completeness cluster and the documentation-only incompleteness
counterexample in `FrameCompleteness.lean`, relocating the counterexample's mathematical content to
a `Univ` module docstring.

**Tasks**:
- [x] Relocate the mathematical content of the counterexample (why `Full`'s 0-target arm makes
      `modalTruthLemmaKb5` false at `φ₀ = ¬◇◇□p`) into a `Univ`-family module docstring as a durable anchor. *(altered: relocated into `modalTruthLemmaKb5`'s own declaration docstring, a real `Univ`-family lemma, rather than a floating module-level `/-! -/` comment -- more literally "a Univ-family module docstring" since it is attached to a Univ declaration)*
- [x] Delete `extractModelKb5_nonRoot_boxPos_gap` (FC 4374) and `extractModelKb5_root_reach_scout` (FC 4343) (private, documentation-only).
- [x] Delete `hintikkaKb5'_box_pos` (FC 3436) and `hintikkaKb5'_diamond_neg` (FC 3478).
- [x] Delete `modalKb5BoxAllFull_mem_of` (FC 3357) and `modalKb5DiaNegAllFull_mem_of` (FC 3394).
- [x] Update `FrameCompleteness.lean` docstrings that name retired prime symbols.

**Timing**: 1 hour

**Depends on**: none (independent of Phase 1; the FrameCompleteness prime cluster references only `FiveSimplification`'s `Full` lemmas, never the `FrameSoundness` prime chain)

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` - delete the prime completeness + counterexample clusters, add the relocated docstring, update references

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` green (880 jobs), sorry-free.
- `lean_verify` `kb5Valid_decides` axioms unchanged `[propext, Classical.choice, Quot.sound]`.
- `instDecidableKb5Valid`, `kb5Valid_decides`, `modalTableauKb5''_complete` still present and used.
- Grep confirms no remaining references to the deleted `FrameCompleteness` prime symbols in that file.

---

### Phase 3: Retire FiveSimplification Full definitions (base) [COMPLETED]

**Goal**: With both consumer chains removed, delete the `Full`/prime base definitions and their
split-lemma families in `FiveSimplification.lean`.

**Tasks**:
- [x] Delete target fns `modalKb5BoxAllFull` (1539) / `modalKb5DiaNegAllFull` (1556) and their
      `_mem` / `_mem_known` / `_mem_eq` lemmas (1577, 1645, 1715, 1725, 1736, 1746). *(altered: the entire contiguous section 1503-2156 -- comprising these lemmas plus the modalApplyOneKb5'Prop family, the modalApplyOneKb5' rule/split lemmas, and the driver decls below -- was found to be one uninterrupted prime-family block and deleted in a single range, since no Univ/keeper declaration was interleaved within it)*
- [x] Delete Prop sibling `modalApplyOneKb5'Prop` (1759) and its lemma family (1787, 1801, 1902, 3376, 3388, 3405, 3479).
- [x] Delete rule `modalApplyOneKb5'` (1937) and all its `'` split-lemma pairs (1955, 1975, 1995, 2004, 2014, 2029, 2050, 2072, 2098, 3417, 3519, 3529, 3539, 3551, 3585, 3686, 3833, 3853, 3874).
- [x] Delete driver decls `modalStepBranchKb5'` (2121), `modalExpandBranchesKb5'` (2129), `modalTableauKb5'` (2137) and their `_eq` theorems (2141, 2147, 2154).
- [x] Delete the dead termination aliases `Kb5'WorldInv` (4751), `Kb5'WorldInv_eq` (4759), `modalMaxWorld_lt_worldBound_of_Kb5'WorldInv` (4768).
- [x] Update `FiveSimplification.lean` docstrings that name retired prime symbols. *(also fixed several stray retired-symbol docstring references discovered in the already-committed FrameSoundness.lean/FrameCompleteness.lean during this phase's repo-wide grep sweep, ahead of Phase 4's final sweep)*

**Timing**: 1 hour

**Depends on**: 1, 2 (all external consumers of the `Full` base defs must be gone first, or this deletion would break the build)

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` - delete the ~40 `Full`/prime base and split-lemma declarations and update references

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` green (880 jobs), sorry-free.
- Grep confirms no remaining references to any deleted `Full`/`Kb5'` symbol across `Cslib/` code bodies.
- `Univ` keeper declarations (`modalKb5BoxAllUniv`, `modalApplyOneKb5''`, `modalTableauKb5''`, etc.) intact.

---

### Phase 4: S5Simplification docstring cleanup and final verification [COMPLETED]

**Goal**: Clean the remaining docstring-only prime references in `S5Simplification.lean` and run the
full post-merge acceptance checklist.

**Tasks**:
- [x] Update the docstring-only prime references in `S5Simplification.lean` (~lines 2057-2062).
- [x] Grep across all of `Cslib/` for every Section 3a retired symbol name; assert zero remaining
      references (including docstrings). *(altered: also caught and fixed several additional stray
      references beyond Section 3a's exact inventory -- a few docstrings in FrameSoundness.lean/
      FrameCompleteness.lean that named retired symbols but were not in the plan's line-numbered
      list -- during Phase 3's and this phase's repo-wide sweeps)*
- [x] `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` green (880 jobs), sorry-free.
- [x] `lake build Cslib.Logics.Modal.Tableau.S5Simplification` green (catches stale references). *(849 jobs)*
- [x] `lean_verify` `kb5Valid_decides` axioms exactly `[propext, Classical.choice, Quot.sound]`.
- [x] Scan the four in-scope files: no new `sorry`, `admit`, `axiom`, `native_decide`, or `@[nolint]` introduced.

**Timing**: 0.75 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean` - update docstring-only prime references

**Verification**:
- All acceptance criteria in "Testing & Validation" below pass.

---

## Testing & Validation

- [x] `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` green (880 jobs), sorry-free.
- [x] `lake build Cslib.Logics.Modal.Tableau.S5Simplification` green. *(849 jobs)*
- [x] `lean_verify` `kb5Valid_decides` axioms exactly `[propext, Classical.choice, Quot.sound]` (unchanged from baseline).
- [x] `instDecidableKb5Valid` and `modalTableauKb5''_complete` still present and used.
- [x] Grep confirms zero remaining references to any retired prime symbol (Section 3a) across `Cslib/`, including docstrings.
- [x] No new `@[nolint ...]`, `sorry`, `admit`, `axiom`, or `native_decide` introduced in any of the four in-scope files.
- [x] `lake exe checkInitImports` passes.
- [x] `lake lint` passes cleanly for `Cslib` (zero environment-linter warnings anywhere in the repo).
- [x] `lake exe lint-style` passes with zero output.
- [x] `lake exe mk_all --module` reports "No update necessary" (no new/deleted files, so `Cslib.lean` needs no changes).
- [x] `lake test` succeeds in full: 9232/9232 jobs, including `CslibTests` (`ModalFrameSeparation`, `ImportWithMathlib`, `GrindLint`).
- [~] `lake shake --add-public --keep-implied --keep-prefix` (whole-repo import minimization): could not be run to a clean, fully-converged completion during this session -- the working tree is shared with a concurrent sibling task (511, S4 loop-checking termination) that is actively mid-edit on `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (confirmed via repeated `git status`/rebuild checks showing that file's content changing between retries, with transient `sorry`-bearing intermediate states). `lake shake` walks the *entire* project graph and requires every module's oleans to be simultaneously fresh, so it raced against the sibling's live edits and reported "out of date oleans" / "target is out-of-date" for `LoopChecking.lean` on every attempt, never for any of this task's four files. A full `lake test` run (which itself requires a complete, successful whole-project build) *did* succeed in full at one point during this session with zero errors, confirming the repo was fully green -- including this task's changes -- at that snapshot; the subsequent `shake` staleness is attributable to the sibling's ongoing edits after that point, not to this task's diff. Per this task's dispatch guidance ("confirm your OWN diff is clean and retry rather than 'fixing' the unrelated file"), this is documented rather than worked around by touching `LoopChecking.lean`.

## Artifacts & Outputs

- plans/01_retire-kb5-prime-family.md (this plan)
- summaries/01_retire-kb5-prime-family-summary.md (on completion)
- Modified: `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`, `FrameCompleteness.lean`, `FiveSimplification.lean`, `S5Simplification.lean`

## Rollback/Contingency

Each phase is a pure-deletion commit gated on a green build. If a phase's build fails (an
unexpected live consumer of a supposedly-dead prime symbol is discovered), stop, restore that
phase's deletions via git (the prior phase's commit is the clean rollback point), and record the
newly-discovered dependency edge in the summary — this would contradict the research dependency
graph and warrants re-examination before proceeding. Because retirement is deletion-only, no
partial-proof or `sorry` states can arise; rollback is always to the last green commit.
