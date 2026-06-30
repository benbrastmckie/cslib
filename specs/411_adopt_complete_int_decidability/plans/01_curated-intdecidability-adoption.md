# Implementation Plan: Task #411

- **Task**: 411 — adopt_complete_int_decidability (parent 370)
- **Status**: [NOT STARTED]
- **Effort**: 1.5 hours
- **Dependencies**: none blocking (deliverable already exists on `refactor/prop_logic`). NOT a branch merge.
- **Research Inputs**: reports/01_int-decidability-integration-findings.md; reports/02_task411-collision-and-corrected-adoption.md
- **Artifacts**: plans/01_curated-intdecidability-adoption.md (this file)
- **Standards**: plan-format.md; CONTRIBUTING.md; ORGANISATION.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Adopt the complete, sorry-free `IntDecidability.lean` from branch `refactor/prop_logic` (tasks
415/416) onto `main` via a **curated single-file swap**, delivering the
`instDecidableDerivableIntPropAxiom'` FMP decision instance that main's task-385 witness stub lacks.
This completes the Int side of parent task 370.

The task stalled because of a **task-number fork collision** (report 02): the branch's "task 411" is
an unrelated DMA automata-concat task, so merging "task 411" from the branch lands the wrong work.
The IntDecidability deliverable lives at `refactor/prop_logic:…/IntDecidability.lean` (436 lines,
sorry-free) and must be adopted as a **file swap on main**, never via `git merge`.

## Goals & Non-Goals

**Goals**:
- Replace `main:Cslib/Logics/Propositional/Metalogic/IntDecidability.lean` with the branch's complete
  version (`git show refactor/prop_logic:… > path`).
- Repo-wide `lake build` green; full CI clean; `#print axioms instDecidableDerivableIntPropAxiom'`
  shows ONLY `propext`/`Classical.choice`/`Quot.sound` (no `sorryAx`).
- Record the task-number collision in the task notes so 411 is never re-attempted as a branch merge.

**Non-Goals**:
- `git merge refactor/prop_logic` (drags in 22 automata-concat commits + add/add + rename/delete
  conflicts + colliding 408–416 metadata).
- Touching `Scheme.lean`, `CslibTests/GrindLint.lean`, `IntStrongCompleteness.lean`, or any specs/
  metadata (keep main's versions; the GrindLint skip and Cslib.lean import are already present).
- Copying the branch's spec directories.
- Closing the tableau-route sorries (that is task 317).
- Min-side FMP (task 421) or route reconciliation (task 422).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `IntLindenbaum` divergence (87+/29−) breaks the swapped file's build | H | L | Static analysis (report 02 §3): `IntDecidability` consumes only `IntStrongCompleteness`'s public API, which on main ⊇ branch; main's Lindenbaum→StrongCompleteness chain already builds. Phase 2 gates empirically; contingency in Phase 3. |
| Proof-term defeq drift vs main's chain | M | L | Phase 2 `lake build` is the gate; if a proof breaks, Phase 3 backports only the specific lemma(s) needed — NO sorry/axiom, NO full branch merge. |
| Accidental `git merge` / extra files swept in | H | L | Explicit file-scoped `git show > path`; commit only the one file. No `git merge`, no `git add -A`. |
| Re-introduces the colliding 408–416 metadata | M | L | Do not touch specs/state.json beyond 411's own status; do not copy branch spec dirs. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | — |
| 2 | 2 | 1 |
| 3 | 3 | 2 (only if build fails) |

### Phase 1: Curated single-file swap [NOT STARTED]

**Goal**: Put the branch's complete `IntDecidability.lean` onto main, changing nothing else.

**Tasks**:
- [ ] `git show refactor/prop_logic:Cslib/Logics/Propositional/Metalogic/IntDecidability.lean > Cslib/Logics/Propositional/Metalogic/IntDecidability.lean`.
- [ ] Confirm `Cslib.lean` still imports `…Metalogic.IntDecidability` (already true; no change).
- [ ] Confirm the `GrindLint` skip `Cslib.Logic.PL.IntFinWorld.mk.sizeOf_spec` is present (already true; no change).
- [ ] `grep -nE '\bsorry\b' …/IntDecidability.lean` → only the "sorry-free" prose lines (16/29/429).
- [ ] `git status` shows EXACTLY one changed file. No merge, no other files.

**Files to modify**: `Cslib/Logics/Propositional/Metalogic/IntDecidability.lean` (whole-file replace).

**Verification**: file present, 436 lines, contains `instDecidableDerivableIntPropAxiom'`.

### Phase 2: Build-verify gate [NOT STARTED]

**Goal**: Empirically confirm the swap is green and sorry-free across the full CI pipeline.

**Tasks**:
- [ ] `lake build` (repo-wide) → GREEN.
- [ ] `lake test`; `lake exe checkInitImports`; `lake exe lint-style`;
      `lake shake --add-public --keep-implied --keep-prefix` → all clean.
- [ ] Axiom check: `#print axioms instDecidableDerivableIntPropAxiom'` (or `lean_verify`) → ONLY
      `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`.
- [ ] `grep` confirms main's pre-existing Scheme.lean / Completeness.lean sorries are UNTOUCHED.
- [ ] If GREEN: commit `task 411: adopt complete sorry-free IntDecidability (curated file swap)` and
      add a one-line note recording the task-number collision (branch 411 = dma_concat; this
      adoption is a file swap, not a branch merge). Mark task completed. **DONE — skip Phase 3.**

**Verification**: full CI pipeline green; axioms clean.

### Phase 3: IntLindenbaum-drift contingency [NOT STARTED]

**Goal**: ONLY if Phase 2 build fails due to a missing/renamed lemma from the branch's `IntLindenbaum`
(or `IntStrongCompleteness`) — backport the minimal delta, never a full merge.

**Tasks**:
- [ ] Identify the exact failing reference(s) from the build error.
- [ ] Backport ONLY the specific lemma(s)/signature(s) `IntDecidability` (transitively) needs, into
      main's `IntLindenbaum.lean`/`IntStrongCompleteness.lean`. Prefer the smallest additive change.
- [ ] Re-run Phase 2 verification. NO sorry/axiom; NO branch merge; NO unrelated branch files.
- [ ] Commit with the backported file(s) scoped explicitly.

**Verification**: Phase 2 pipeline green after the minimal backport.

## Testing & Validation

- [ ] Repo-wide `lake build` GREEN.
- [ ] `lake test`, `checkInitImports`, `lint-style`, `shake` clean.
- [ ] `instDecidableDerivableIntPropAxiom'` present; axioms = {propext, Classical.choice, Quot.sound}.
- [ ] Exactly the intended files changed (Phase 1: one file; Phase 3 only if triggered).
- [ ] No specs metadata corruption; branch spec dirs not copied.

## Artifacts & Outputs

- `plans/01_curated-intdecidability-adoption.md` (this plan).
- `summaries/01_*.md` on completion.
- main `IntDecidability.lean` upgraded to the sorry-free FMP version with the decidability instance.

## Rollback/Contingency

- Single-file swap is trivially reversible: `git checkout HEAD -- …/IntDecidability.lean`.
- If Phase 2 fails and Phase 3's minimal backport balloons (more than a couple of small lemmas),
  STOP and escalate — do not attempt a branch merge; reassess whether a small follow-on task should
  port the required `IntLindenbaum` delta first.
- Commit only at a GREEN pipeline; never commit a build-red or sorry-bearing state.
