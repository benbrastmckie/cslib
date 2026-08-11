# Implementation Plan: Reconcile `→` Notation Precedence and Associativity with Upstream

- **Task**: 497 - reconcile_imp_naming (retargeted to notation-only)
- **Status**: [COMPLETED]
- **Effort**: 1.25 hours
- **Dependencies**: None (sole dependency 400 is completed)
- **Research Inputs**: specs/497_reconcile_imp_naming/reports/01_arrow-notation-precedence-reconciliation.md
- **Artifacts**: plans/01_arrow-precedence-infixr-reconciliation.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Move the `→` connective notation from the fork's non-associative `infix:30` to upstream's
right-associative `infixr:25` in the four non-Propositional formula files, and move the
co-declared `↔` from `infix:30` to `infixr:20` in the three of those files that declare it. The
change is 7 declaration lines plus 2 header docstring precedence tables. Research has already
applied both the arrow-only and the arrow+iff variants and built the full 372-module dependency
cone green under each, so there is no call-site remediation work in this plan — only the edits,
the prose sync, and a confirming rebuild. Definition of done: the 7 declarations read `infixr:25`
/ `infixr:20`, the 2 docstring tables agree with them, and the 372-module targeted build returns
exit 0 with 0 errors and the warning count unchanged at 32.

### Research Integration

The research report is decisive and its conclusions are inputs, not open questions:

- **Transitive parse impact is empirically zero.** The arrow-only change was applied to all four
  files and the entire dependency cone was built: 372 modules, exit 0, 2013 jobs, 0 errors,
  warnings unchanged at 32, with 364/434 `.olean` files genuinely recompiled (mtimes postdating
  the edit). The working tree was reverted clean afterward. No phase in this plan fixes call
  sites, because there are none to fix.
- **The edit set is 7 lines, not 4.** The task description's premise that moving `→` alone
  inverts no relationship holds only for the out-of-scope `Propositional/Defs.lean`. In
  `Modal/Basic.lean:237`, `LTL/Syntax/Formula.lean:210`, and `Temporal/Syntax/Formula.lean:170`,
  `↔` sits at `infix:30` — the *same* level as `→`. Moving `→` alone to 25 leaves `↔` binding
  tighter, confirmed by `rfl`: `(a ⟹ b ⟺ c) = (a → (b ↔ c))`, backwards from convention and from
  upstream. Bimodal declares no `↔` and needs no iff edit. The combined arrow+iff variant also
  built green under identical conditions.
- **`∧`/`∨` do not move.** Their order relative to `→` is preserved at either arrow precedence,
  and both already require parenthesized arrow arguments. `∨` at 35 vs upstream's 30, and the
  `infix`→`infixr` conversion for `∧`/`∨`, are real divergences owned by the notation-wide
  reconciliation.
- **Dead ends already cleared — do not re-open.** The `infix:29` equivalence operator at
  `Cslib/Foundations/Logic/LogicalEquivalence.lean:33` is the only precedence hazard class and is
  real in a minimal model, but every `≡`/`→` co-occurrence inside the four subtrees is a comment.
  Turnstile notations use unannotated `notation:50` arguments and are precedence-immune. Validity
  notations with annotated `:50` arguments already require parentheses today.
- **Upstream confirmed.** `b8ad3923` is an ancestor of `upstream/main` but not of fork HEAD;
  `upstream/main` tip `3951377e`, merge-base `f36649cf`. The fork has no
  `Foundations/Logic/Operators.lean`.
- **Zero-debt posture.** No `sorry`, no axiom, no blocker. Pure notation-declaration edits.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context; no ROADMAP.md consultation performed.

## Goals & Non-Goals

**Goals**:
- Bring `→` to upstream's `infixr:25` in all four in-scope files, making `a → b → c` parse
  right-associatively instead of surfacing as a type mismatch against Lean's `Prop` arrow.
- Bring `↔` to upstream's `infixr:20` in the three in-scope files that declare it, so the
  arrow/biconditional relationship is not left inverted between this task and the notation-wide
  reconciliation.
- Keep the two header docstring precedence tables truthful about the declarations they describe.
- Confirm the 372-module dependency cone stays green with an unchanged warning count.

**Non-Goals**:
- `Cslib/Logics/Propositional/Defs.lean` — owned by a sibling task carrying a standing-approval
  dependency chain. Not touched, not built against, not coordinated with.
- Part (c), rebinding `→` to the existing `HasImp` typeclass at
  `Cslib/Foundations/Logic/Connectives.lean:85` — a different sibling task's scope.
- Moving `∧` (36) or `∨` (35), or converting them from `infix` to `infixr`.
- Repairing call sites: research proved the set is empty.
- Fixing the pre-existing full-build stall on
  `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — tracked separately and
  outside this task's dependency cone.
- Renaming the 4 residual `impl` tactic-hypothesis tokens in `Connectives.lean` (cosmetic).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Bare `lake build` is run and stalls indefinitely on `Scheme.lean` (92 min pegged CPU observed, no cached `.olean`, never built in this checkout) | H | M | Phase 3 uses the targeted-module recipe exclusively. Never run a bare full `lake build`; never `lake env lean <file>` without `--setup`. This is stated on every phase that touches a build. |
| Only the 4 arrow lines are edited, leaving `↔` inverted at 30 | M | M | The `↔` edits are in the same phase as the arrow edits under `Commit Mode: atomic-batch`, so an arrow-only tree is never a commit boundary. Phase 3 checks all 7 lines. |
| Docstring tables drift from the declarations they document | L | M | Phase 2 is a dedicated prose phase gated on Phase 1; Phase 3 greps both tables. |
| A `↔`-at-20 collision with LTL's `⇝` (`infix:20`, `LTL/Syntax/Formula.lean:215`) breaks a live site | L | L | Research's build proves no live site writes `a ⇝ b ↔ c`. Post-change that shape needs parentheses; no existing code has it. Moving `⇝` is out of scope and upstream has no `⇝` to match. |
| Warning count rises above 32, signalling `unusedSectionVars`/`simpNF` fallout | M | L | Phase 3 treats the warning count as a hard gate, not an observation; a rise blocks phase closure. |
| Line numbers drift before implementation | L | L | Phases match on declaration text, not line number; the line numbers are given as locators and every phase carries a Scope Hypothesis requiring re-confirmation. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel. This plan is fully sequential: Phases 1 and 2
edit overlapping files (LTL and Temporal `Formula.lean`), so they are serialized to avoid
concurrent edits to the same file rather than because of a logical dependency.

---

### Phase 1: Move `→` to `infixr:25` and `↔` to `infixr:20` [COMPLETED]

**Goal**: All 7 notation declarations in the four in-scope files match upstream's precedence and
associativity.

**Tasks**:
- [x] Confirm the 7 target lines still read `@[inherit_doc] scoped infix:30` before editing
      (`grep -n 'infix.*" → "\|infix.*" ↔ "'` over the four files).
- [x] `Cslib/Logics/Bimodal/Syntax/Formula.lean:101` — `scoped infix:30 " → "` -> `scoped infixr:25 " → "`
- [x] `Cslib/Logics/LTL/Syntax/Formula.lean:209` — `scoped infix:30 " → "` -> `scoped infixr:25 " → "`
- [x] `Cslib/Logics/LTL/Syntax/Formula.lean:210` — `scoped infix:30 " ↔ "` -> `scoped infixr:20 " ↔ "`
- [x] `Cslib/Logics/Modal/Basic.lean:234` — `scoped infix:30 " → "` -> `scoped infixr:25 " → "`
- [x] `Cslib/Logics/Modal/Basic.lean:237` — `scoped infix:30 " ↔ "` -> `scoped infixr:20 " ↔ "`
- [x] `Cslib/Logics/Temporal/Syntax/Formula.lean:169` — `scoped infix:30 " → "` -> `scoped infixr:25 " → "`
- [x] `Cslib/Logics/Temporal/Syntax/Formula.lean:170` — `scoped infix:30 " ↔ "` -> `scoped infixr:20 " ↔ "`
- [x] Preserve each line's `@[inherit_doc]` attribute, `scoped` modifier, the spaces inside the
      token string, and the right-hand side verbatim. Only the `infix:NN` token changes.
- [x] Confirm no eighth `infix:30` connective declaration was missed in these four files.

**Timing**: 20 minutes

**Depends on**: none

**Verification Tier**: interface

**Commit Mode**: atomic-batch

**Scope Hypothesis**: The edit set is exactly 7 declaration lines across 4 files, at the line
numbers above, and Bimodal declares no `↔`. Confirm at implementation time by running
`grep -n 'infix.*" → "\|infix.*" ↔ "'` over the four in-scope files before editing and again
after: before, it must return exactly 7 `infix:30` lines; after, exactly 4 `infixr:25 " → "` and
3 `infixr:20 " ↔ "` lines and zero `infix:30` matches. Also confirm
`grep -c '↔' Cslib/Logics/Bimodal/Syntax/Formula.lean` finds no declaration. If the actual counts
differ from 7/4/3, stop and report rather than widening the edit set.

**Files to modify**:
- `Cslib/Logics/Bimodal/Syntax/Formula.lean` - arrow declaration only (no `↔` declared here)
- `Cslib/Logics/LTL/Syntax/Formula.lean` - arrow + iff declarations
- `Cslib/Logics/Modal/Basic.lean` - arrow + iff declarations
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - arrow + iff declarations

**Verification**:
- The post-edit grep above returns 4 `infixr:25 " → "`, 3 `infixr:20 " ↔ "`, 0 `infix:30`.
- `git diff` shows exactly 7 changed lines and no collateral edits.
- No file outside the four in-scope files appears in `git status --short` for `Cslib/`; in
  particular `Cslib/Logics/Propositional/Defs.lean` must be untouched.
- `atomic-batch` rationale: the arrow-only intermediate state is precisely the known-inverted-`↔`
  hazard, so it must never be a commit boundary. Intermediate per-file states are expected red
  and are not committed; one commit covers the declared 7-line batch after the batch-level
  verification above passes.

---

### Phase 2: Sync the two header docstring precedence tables [COMPLETED]

**Goal**: The human-readable precedence tables in the LTL and Temporal file headers state the
precedences the file actually declares.

**Tasks**:
- [x] `Cslib/Logics/LTL/Syntax/Formula.lean:37` — `` - `→` (infix, 30) : implication (`Formula.imp`) `` -> `(infixr, 25)`
- [x] `Cslib/Logics/LTL/Syntax/Formula.lean:38` — `` - `↔` (infix, 30) : biconditional (`Formula.iff`) `` -> `(infixr, 20)`
- [x] `Cslib/Logics/Temporal/Syntax/Formula.lean:37` — same arrow change
- [x] `Cslib/Logics/Temporal/Syntax/Formula.lean:38` — same iff change
- [x] Leave the `¬` (prefix, 40), `∧` (infix, 36), and `∨` (infix, 35) rows untouched — those
      declarations are not changing and their table rows remain accurate.
- [x] Confirm the two remaining in-scope files need no prose update: `Modal/Basic.lean` has no
      header precedence table, and `Bimodal/Syntax/Formula.lean` has no `→`/`↔` precedence prose.
- [x] Confirm `NOTATION.md` still needs no edit (it carries no precedence table; its only
      nearby entry concerns `S` as *Since*).

**Timing**: 15 minutes

**Depends on**: 1

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: Exactly 2 docstring tables need updating (LTL and Temporal), 2 rows each,
4 prose lines total; Modal and Bimodal need none, and `NOTATION.md` needs none. Confirm at
implementation time with `grep -rn '(infix, 30)' Cslib/Logics/` restricted to the four in-scope
files — it must return exactly 4 lines before the edit and 0 after — and with
`grep -n 'infix\|prec' NOTATION.md` returning no precedence table. If a third in-scope file turns
out to carry a precedence table, extend this phase to it and record the discovery; if the count is
lower than 4, record a Reasoned Exclusions entry rather than silently closing.

**Files to modify**:
- `Cslib/Logics/LTL/Syntax/Formula.lean` - header docstring rows for `→` and `↔`
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - header docstring rows for `→` and `↔`

**Verification**:
- Diff read-through confirms every changed hunk lies inside the module header docstring block,
  above any declaration — no hunk crosses out of the comment region.
- The four changed rows now read `(infixr, 25)` / `(infixr, 20)` and match the Phase 1
  declarations exactly.
- `grep -rn '(infix, 30)'` over the four in-scope files returns nothing.
- Blind spot acknowledged and covered downstream: these are Lean module docstrings, so a
  malformed edit could in principle break elaboration of the docstring itself. Phase 3's build
  is what catches that; this phase does not attempt to.

---

### Phase 3: Verify the dependency cone and the new parse [COMPLETED WITH EXCLUSIONS]

**Goal**: The full 372-module dependency cone of the four in-scope files builds clean with an
unchanged warning count, and the new associativity and precedence are confirmed by `rfl`.

**Tasks**:
- [x] Regenerate the target list mechanically:
      `grep -oE "Cslib\.Logics\.(Bimodal|LTL|Modal|Temporal)[A-Za-z0-9_.]*" Cslib.lean | sort -u > /tmp/targets.txt`
      -> 372 modules, matching the research baseline exactly; `Scheme.lean` confirmed absent
      (`grep -c 'Scheme' /tmp/targets.txt` = 0).
- [x] Run `lake build $(cat /tmp/targets.txt)` and record exit code, job count, error count, and
      warning count. -> "Build completed successfully (2013 jobs)", 0 `^error:` lines,
      32 `^warning:` lines.
- [x] Gate on: exit 0, 0 errors, warning count exactly 32 (research baseline, held across both
      experimental variants). A rise blocks phase closure and must be investigated as
      `unusedSectionVars`/`simpNF` fallout, not waved through. -> Gate passed: 32/32, exact match.
- [x] Run the capability regression checks in a scratch file inside each relevant namespace:
      - `example (a b c : Formula Nat) : Formula Nat := a → b → c` (Bimodal, LTL, Temporal)
      - `example (a b c : Proposition Nat) : Proposition Nat := a → b → c` (Modal)
      - `example (a b c : Formula Nat) : (a → b → c) = (a → (b → c)) := rfl`
      - `example (a b c : Formula Nat) : (a → b ↔ c) = ((a → b) ↔ c) := rfl`
      -> All 8 examples (arrow-chain + both `rfl` per applicable namespace) built via
      `lake build Cslib.Scratch497Check`: "Build completed successfully (734 jobs)", 0 errors.
- [x] Confirm `git status --short -- Cslib/` lists only the four in-scope files.
      *(deviation: altered -- after Phases 1/2 committed, the four in-scope files no longer
      appear as dirty; the only remaining entry is a pre-existing, unrelated modification to
      `Cslib/Logics/Propositional/Tableau/Intuitionistic.lean` that predates this task's work and
      was never touched by it. `Cslib/Logics/Propositional/Defs.lean` itself is confirmed
      untouched.)*
- [x] Delete the scratch file; it is a check, not a deliverable. -> `Cslib/Scratch497Check.lean`
      removed after the build confirmed all examples elaborate.

**Timing**: 40 minutes (dominated by the cone rebuild)

**Depends on**: 2

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: The dependency cone is 372 modules (Bimodal 139, LTL 12, Modal 163,
Temporal 58), the build produces 2013 jobs, and the warning baseline is 32. Confirm at
implementation time by `wc -l /tmp/targets.txt` and by reading the `lake build` job and warning
counts directly. Treat all three numbers as research-time hypotheses: a module count that has
drifted since the report is expected and fine (the list is regenerated mechanically, not
hardcoded), but a *warning* count above 32 is a gate failure, not drift.

**Files to modify**:
- None. This phase is verification only; it produces no committed file changes beyond the
  temporary scratch file it deletes.

**Verification**:
- `lake build $(cat /tmp/targets.txt)` exits 0 with 0 errors and 32 warnings.
- All four capability regression examples elaborate, including both `rfl` checks.
- `grep` confirms the 7 declarations and 4 docstring rows are in their final state.

#### Reasoned Exclusions

Pre-declared at plan time. If the phase closes having relied on these, mark the heading
`[COMPLETED WITH EXCLUSIONS]` and confirm each Evidence cell with implementation-time output;
otherwise mark `[COMPLETED]` and delete this table.

| Item | Reason | Evidence |
|------|--------|----------|
| Whole-repository `lake build` | Pre-existing, separately-tracked stall: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (9,884 lines) never completes — 92 minutes of pegged CPU at 1.3 GB RSS with no cached `.olean`, i.e. it has never built in this checkout. Not caused by this change and not in this task's dependency cone. | Confirmed: `grep -c 'Scheme' /tmp/targets.txt` returned 0 (module absent from the 372-module target list); the targeted build substituted as the gate and returned `Build completed successfully (2013 jobs)`, 0 `^error:` lines, 32 `^warning:` lines -- exact match to the research baseline. |
| `Cslib/Logics/Propositional/Defs.lean` and its dependents | Explicitly out of scope; owned by a sibling task with a standing-approval dependency chain. Research separately established that PL can move independently of these four files — the `scoped` notations resolve by type, so the two precedences never collide. | Confirmed: `git status --short -- Cslib/Logics/Propositional/Defs.lean` returned empty (untouched). The four in-scope files are already committed as of Phases 1-2, so `git status --short -- Cslib/` at Phase 3 close shows only a pre-existing, unrelated modification to `Cslib/Logics/Propositional/Tableau/Intuitionistic.lean` that predates and is untouched by this task. |

---

## Testing & Validation

- [ ] `grep` over the four in-scope files returns 4 `infixr:25 " → "`, 3 `infixr:20 " ↔ "`, and
      0 `infix:30` connective declarations.
- [ ] Both header docstring tables read `(infixr, 25)` for `→` and `(infixr, 20)` for `↔`.
- [ ] `lake build $(cat /tmp/targets.txt)` — exit 0, 0 errors, 32 warnings.
- [ ] `a → b → c` elaborates in all four namespaces (it does not today).
- [ ] `(a → b → c) = (a → (b → c)) := rfl` holds.
- [ ] `(a → b ↔ c) = ((a → b) ↔ c) := rfl` holds.
- [ ] `Cslib/Logics/Propositional/Defs.lean` is unmodified.
- [ ] No `sorry` and no new axiom introduced (none is expected: these are notation declarations).

## Artifacts & Outputs

- `specs/497_reconcile_imp_naming/plans/01_arrow-precedence-infixr-reconciliation.md` (this file)
- `specs/497_reconcile_imp_naming/summaries/01_arrow-precedence-infixr-summary.md` (on completion)
- Modified: `Cslib/Logics/Bimodal/Syntax/Formula.lean`, `Cslib/Logics/LTL/Syntax/Formula.lean`,
  `Cslib/Logics/Modal/Basic.lean`, `Cslib/Logics/Temporal/Syntax/Formula.lean`

## Rollback/Contingency

The change is 11 lines across 4 files with no generated or derived artifacts, so reverting is a
targeted `git revert` of the phase commits (or, before any commit,
`bash .claude/scripts/git-snapshot.sh 497` followed by a scoped checkout of the four files — never
a bare destructive git command on a dirty tree). Research already performed and reverted this
exact experiment cleanly, so the revert path is proven.

If the Phase 3 build unexpectedly fails or the warning count rises: fix forward first — the
failure would be new information contradicting a full green build over the same 372 modules, so
capture the exact failing module and message rather than reverting reflexively. If the failure is
attributable to the `↔` move specifically, the arrow-only variant is independently green and is a
valid fallback state, but it leaves `↔` binding tighter than `→`; adopting it requires recording
that known-inverted precedence as an explicit, tracked exclusion rather than shipping it silently.
