# Repo Lint & Hygiene Cleanup — CI Gate Restoration (v2)

- **Task**: 575
- **Status**: PARTIAL
- **Effort**: ~14.5h spent. Phase 5 is the sole remaining workstream; the count-1 actionable tier
  is now fully closed. Only the deliberately-deferred count-6 file remains (needs a cycle with a
  large context budget reserved for it specifically).
- **Dependencies**: none blocking.
- **Research Inputs**: four parallel subsystem reviews (Propositional, Modal, Temporal/Bimodal,
  shared infrastructure), 2026-07-27; findings inlined here rather than filed as separate reports.
- **Artifacts**: `plans/02_lint-hygiene-ci-gate.md` (this file, supersedes `01_`);
  `handoffs/NN_cycle-*.md` (per-cycle detail)
- **Standards**: `.claude/rules/no-task-references-in-deliverables.md`,
  `.claude/rules/git-workflow.md` (commit-per-green-substep), `CONTRIBUTING.md`
- **Type**: cslib
- **Created**: 2026-07-27
- **Last updated**: 2026-07-27 (cycle-26 close)

> **Why v2 exists.** `01_lint-hygiene-ci-gate.md` reached 2,938 lines, 45% of it a cycle-by-cycle
> changelog of Phase 5 (18 `Done (cycle N)` entries and 6 verbatim copies of the same `Method`
> paragraph). Every durable instruction, constraint, finding, and hazard is carried forward here;
> only the per-cycle narrative is dropped. That narrative is preserved in git history and in
> `handoffs/`. **Nothing that prevents a repeated mistake has been discarded** — findings were
> consolidated by category (see Phase 5's "Accumulated findings"), not summarized away.

---

## RESUME HERE

**Only Phase 5 (suppression audit) is open. Phases 1-4 and 6-8 are all CLOSED.** No item requires
a user decision to make further Phase 5 progress.

**State at cycle-26 close**: 444 sites audited across 112 files. **The count-1 actionable tier is
now fully closed** — all 9 files that were open at cycle-25 close are cleared to 0 blanket
suppressions. **25 blanket suppressions remain repo-wide**: 14 are upstream-shared and carved out
of scope; 5 are permanent exceptions (1 each); 6 belong to the deliberately-deferred count-6 file
(`CounterexampleElimination/Interface.lean`). **Zero actionable local-only files remain outside
the deferred count-6 file.**

### Step 1 — confirm the baseline (~5 min)

```bash
lake build --wfail --iofail   # expect exit 1, exactly 5 baseline sorry warnings (listed below)
lake test                     # expect exit 0
lake shake --add-public --keep-implied --keep-prefix Cslib   # expect exactly 12 upstream-shared files, zero local-only
bash scripts/check-lint-suppressions.sh   # expect exit 0, "25 (baseline ceiling 25)"
```

If any differ, something else landed — reconcile before proceeding.

### Step 2 — pick the next target

**Count-1 tier is CLOSED (cycle 26).** All 9 files from the cycle-25 worklist cleared to 0
blanket suppressions (see "Done (cycle 26)" below for the per-file table).

**NEXT AND ONLY TARGET: `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination/Interface.lean`
(3048 lines, 6 blanket suppressions) — the deliberately-deferred count-6 tier file.**

This is now the *only* remaining actionable item in Phase 5's audit. Re-verify line and
suppression counts live before starting — counts only ever go down:

```bash
wc -l Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination/Interface.lean
grep -n "set_option linter\." Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination/Interface.lean
```

**Cold-start instructions for this file specifically**:
- Reserve a full cycle's context budget for this file alone — do not start it opportunistically
  alongside other work, and do not expect to finish it in a single dispatch if context runs low.
  If a handoff is needed mid-file, document exactly which of the 6 suppressions are resolved,
  which remain, and the live warning list for any suppression already removed but not yet
  reconciled.
- Per the Method (below), remove ALL blanket suppressions in the file at once (or one at a time —
  either is valid), rebuild, and categorize what surfaces before fixing. Given the file's size
  (3048 lines), expect a much larger warning surface than any count-1 file this task has
  processed — E1 (line count does not predict warning count) applies with extra force here.
- Its sibling file `CounterexampleElimination/Elimination.lean` (244 lines) is a **permanent
  exception** in the same directory (`linter.privateModule`, C7) — do NOT assume Interface.lean
  hits the same category; verify live, it may differ (Interface.lean is presumably not
  all-`private` given it is the public-facing counterpart).
- No live worst-offender list is needed anymore — this is the only file left. If it clears to 0,
  Phase 5 (and the whole task) is done pending final Definition-of-Done sign-off; if it bottoms
  out at a genuine irreducible count, document it the same way as the 5 existing permanent
  exceptions and close Phase 5 with that as the final state.

**Permanent exceptions — 5 files, do not attempt further reduction:**
```
1  117 Cslib/Computability/Automata/DA/Conversions.lean                     # pre-existing
1  120 Cslib/Logics/Bimodal/Metalogic/BXCanonical/Filtration/DefectChain.lean # pre-existing
1  244 Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination/Elimination.lean # cycle 25
1  435 Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/QLemma.lean       # persistent open Classical
1  871 Cslib/Logics/Bimodal/Metalogic/Separation/Eliminations.lean          # persistent open Classical
```

### Step 3 — before editing, read Phase 5's "Accumulated findings"

Particularly the **parse hazard** (P1) and the **dangling-`by` hazard** (P5) — both recur across
cycles and are not solved problems. Cycle 26 hit zero new hazard categories, but a 3048-line file
is far larger than anything processed to date; treat E1 and the existing category-fix catalog
(C1-C7) as the starting hypothesis set, not an exhaustive one.

### Do not

- Re-derive the sorry census with a naive grep. Use "Measurement notes".
- Re-open Phase 3's citation census, Phase 7's `NOTATION.md`/`NOTE:`-block items, or any other
  closed phase. They are settled; their sections record the outcome.
- Touch the five permanent exceptions listed above (Phase 5, "Permanent exceptions").

---

## Overview

Restore `lake build --wfail --iofail` — the exact CI invocation in
`.github/workflows/lean_action_ci.yml` — to green, and clear the hygiene debt surfaced alongside
it. `--wfail` promotes every warning to a build failure, so at task start CI was red despite
`lake build` and `lake test` both being green.

## Goals & Non-Goals

**Goals**: zero linter warnings; zero task-tracker references in deliverables; import gate
re-enabled; suppression debt audited and reduced; scripts that can actually fail.

**Non-Goals**:
- Discharging any `sorry`. Five sorry sites legitimately remain and WILL still be CI-red at task
  end. That is the correct end state; clearing them is mathematical work owned elsewhere.
- Any structural consolidation requiring mathematics — see "Routed elsewhere".
- Hygiene edits to files shared with `upstream` — carved out below; route to an upstream PR.

## Constraints

- **No sorry may be discharged, added, moved, or suppressed.**
- **No proof term, definition, or theorem statement may be altered.** Only tactic surface syntax
  (`simp [X] at h` → `simp only [...] at h`).
- **No new `set_option linter.* false`.** Suppressing instead of fixing is the pattern Phase 5
  exists to reverse. If a warning cannot be fixed without changing mathematics, report it.
- **Before editing any file, confirm it is local-only**: `git cat-file -e upstream/main:<path>`
  must FAIL (non-zero). If it succeeds, the file is shared upstream — skip and record it.
- Verification: **risk-tiered batch verification** — see "Testing & Validation". Nothing is ever
  committed unverified; the tiering changes verification *granularity*, not its strictness.

### Upstream-exposure scope

This repository is a fork of `leanprover/cslib` (remote `upstream`), 3,899 commits ahead and 541
behind, with an active sync branch. Hygiene edits split into two populations:

| Population | Files | Sync cost |
|---|---|---|
| **Local-only** (added here; absent upstream) | 521 added | None — upstream never touches these paths |
| **Shared with upstream** (modified here) | 70 modified, 21 deleted | Every edit is another conflict hunk |

Measured against `upstream/main` (tip `f36649cf`): `Logics/Bimodal` is 0-of-139 upstream,
`Logics/Temporal` 0-of-53, `Logics/Modal` 0-of-142, `Logics/Propositional` 1-of-110. **Every file
Phase 5 has processed is local-only**, as is every remaining target.

**IN SCOPE**: blanket suppressions in local-only files, plus local-only `@[nolint]` attributes.

**OUT OF SCOPE**: the 14 blanket suppressions in upstream-shared files (chiefly
`Computability/Automata/**`, `Foundations/**`, `Languages/LambdaCalculus/LocallyNameless/**`) and
their `@[nolint]` attributes. Fixing lint in a file upstream also maintains is better done as an
upstream PR then synced down: same end state, no conflict debt. Record, do not edit.

Lint cleanliness is a **precondition** for upstream acceptance (upstream CI runs `--wfail`), so
this work is aligned with eventual upstreaming, not opposed to it.

### Explicit non-targets — do NOT "clean" these

Each was investigated and found correct. Re-investigating wastes a cycle.

- `Temporal/Metalogic/PropositionalHelpers.lean` and `Bimodal/Theorems/Perpetuity/Helpers.lean`
  are **not** redundant wrappers. Their aliases carry 187 and 416 call sites (`impTrans` alone:
  47 and 96). They absorb `@`-positional boilerplate once instead of at every call site.
- `TemporalConservativity.lean:245`'s "sorry-free" claim is **true**. It scopes to two
  declarations that both verify axiom-clean; line 243 names the sorry'd one as the gap.
- The three `Chronicle` modules' `Chronicle.` prefix is **not** a doubled namespace (Phase 2).
- The `S`→`Sys` rename stays excluded: 1229 raw matches with semantic false positives inside the
  target files (`ProofSystem.lean`'s docstrings use "K, S, MP" as *combinatory-logic* naming).

---

## Risks & Mitigations

Every risk below was *realized* during execution, not hypothesized. Each mitigation is the one
that actually caught it.

| Risk | Realized as | Mitigation |
|---|---|---|
| A "mechanical" cleanup list contains items whose edit breaks the build | The three `Chronicle` modules: `Chronicle.` is a structure-projection namespace, not a doubled one; stripping it fails on 81 dot-notation call sites | Per-item verification before editing |
| A mechanical edit compiles green but silently corrupts meaning | The `S`→`Sys` rename: docstrings use "K, S, MP" in an unrelated sense | Semantic (not just syntactic) census before a rename |
| A dead-code list flags live code | `HilbertSearch.lean` (a real tactic implementation, invisible to a declaration-keyword scan) and a documented `proof_wanted` stub | Full reference-count grep per candidate |
| Planning-time counts are wrong by orders of magnitude | "~484 reference sites" was truly 6 (~80x); "5 files" for the rename was 24 files + 231 call sites | Treat every asserted count as a hypothesis; re-derive before relying on it |
| A census regex silently undercounts | The reference census missed hyphenated `task-N` and letter-suffixed `Phase 3a`; a naive `\bsorry\b` scan counted `warn.sorry` option lines as proof holes | Documented census method in "Measurement notes" |
| Uniform per-file verification makes atomic refactors inexpressible | A rename that must land across 24 files at once cannot decompose into independently-green commits | Risk-tiered verification; Tier 4 permits one atomic batch |
| Editing files owned by a concurrent task corrupts its provenance | Overlapping `file_scope` with concurrent work on `FrameSoundness.lean` | Check liveness before editing; retain forward references with recorded rationale |
| A suppression-removal idiom safe in one case breaks another | `omit [...] in` is safe for `unusedSectionVars` but broke compilation for `unusedDecidableInType` | Rebuild before committing every batch; restore-and-narrow rather than leave blanket |

## Baseline and current state

| Gate | At task start | Now |
|------|--------------|-----|
| `lake build` | green 3259/3259 | green |
| `lake test` | green, 0 errors | green, 0 errors |
| `lake build --wfail --iofail` | **exit 1**, 27 modules, 460 warnings | **exit 1**, **exactly 5 genuine sorry warnings** |
| `lake exe mk_all --check` | pass | pass |
| `lake exe checkInitImports` | pass | pass |
| `lake shake` | 94 files flagged (CI step disabled) | CI step enabled; exactly the 12 upstream-shared files remain (out of scope), zero local-only |
| Linter sites | 240 | **0** |
| Blanket `set_option linter.*` | 511 | **25** repo-wide (11 local-only in scope + 14 carved out) |
| `@[nolint]` | 118 | 88 |
| Task-tracker refs in `Cslib/**` | 376 (undercounted) | 20, all individually accounted for |
| Doubled public names | 6 cross-module leaks | **0** |
| Bare sorries (correct method) | 28 | 28 (unchanged by design) |

The 5 sorry warnings — the correct end state for the sorry census:
```
Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1252                      declaration uses `sorry`
Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:570        declaration uses `sorry`
Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:2583       declaration uses `sorry`
Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean:124  declaration uses `sorry`
Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:118         declaration uses `sorry`
```

### Measurement notes — two independent causes of this repo's recurring sorry-count error

Any future census must account for both, or it will be wrong again.

1. `set_option warn.sorry false` contains `sorry` at a word boundary, so a naive `\bsorry\b` scan
   counts 12 option lines as proof holes. This inflated Bimodal 23 → 35.
2. Nine tracked scratch files at the repo root (8 `Test_*.lean` + `OF`) carried 15 sorries while
   belonging to no build target — invisible to `lake build`, counted by every grep. Removed in
   `2f608bdf`.

The project's own "41 → 40" figures were wrong in both ways. **Correct method**: strip `/- -/` and
`--` comments, exclude lines containing `warn.sorry`, scan only build-reachable files. Implemented
in `scripts/pre-pr-check.sh`.

---

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4 | 1 |
| 3 | 5, 6, 7, 8 | 4 |

Phases 1-3 are independent edit passes over disjoint concerns. Phase 4 follows Phase 1 because
re-enabling the import gate is only meaningful once the build is warning-clean. Phases 5-8 were
sequenced last because Phase 5's size was not knowable in advance, so the bounded phases were
ordered ahead of it to guarantee they land regardless of how far Phase 5 gets.

### Phase 1: Linter sites [COMPLETED]

All 240 distinct linter sites across 27 files cleared. A transient cycle-12 regression (7
additional non-sorry warnings across 3 local-only files, arriving via an unrelated upstream-sync
merge) was found and fixed in cycle 13. Closure criterion re-verified empirically since.

### Phase 2: Doubled-namespace public API [COMPLETED]

Closed at 7 of 10 rows. The three `Chronicle` modules were **excluded by finding**: `Chronicle.`
is a structure-projection namespace, not a doubled one — stripping it fails on 81 dot-notation
call sites. This finding is what later justified *narrowing* rather than removing `dupNamespace`
suppressions in Phase 5 (see finding C4).

### Phase 3: Task-number references in deliverables [COMPLETED]

226 task-citations replaced with durable anchors. Final state: 20 remaining strings in `Cslib/**`,
each individually accounted for — 2 genuinely irreducible sites plus 8 confirmed false positives
(legitimate internal section headings), with the balance documented in the closure notes.

The census regex was fixed mid-phase after it was found to miss hyphenated `task-N` and
letter-suffixed `Phase 3a` forms; the true starting baseline was 399, not 376.

> **Process note, retained deliberately.** This phase's acceptance criterion was once rewritten by
> the same dispatch that failed to meet it, then marked met under the new wording. Acceptance
> criteria may be revised when genuinely wrong, but **a phase closing at less than 100% must
> surface the restatement for explicit sign-off rather than absorb it into its own closure
> notes.** This rule now governs every phase in this plan.

### Phase 4: Import gate (`lake shake`) [COMPLETED]

Imports fixed and the `lake shake` CI step uncommented in `.github/workflows/lean_action_ci.yml`.
Clean on the local-only tree — exactly the 12 upstream-shared files remain flagged and are out of
scope. A post-close regression across 11 local-only files, landed via an unrelated merge, was
found and fixed in cycle 16.

### Phase 5: Suppression audit [PARTIAL — 444 sites done across 112 files; count-1 actionable tier CLOSED; only the deferred count-6 file (6 blanket suppressions) remains]

The sole open workstream. **Scope**: local-only files only; gate every candidate with
`git cat-file -e upstream/main:<path>` (must FAIL to be in scope).

#### Method

**Remove the blanket suppression, rebuild, fix whatever surfaces.** Only removal-plus-rebuild
proves whether a suppression is load-bearing. Then: categorize what surfaced, fix the mechanical
categories outright, and narrow anything genuinely needed to declaration or usage-site scope
(`set_option ... in`). Never leave a blanket suppression as the resolution.

#### Ratchet — lock in every reduction

`scripts/check-lint-suppressions.sh` enforces that blanket counts may only decrease. It runs in
CI's `Lint Hygiene` workflow and as step 6 of `pre-pr-check.sh`; policy in
`docs/lint-suppression-policy.md`. After each reduction, re-baseline **in the same commit as the
file**:

```bash
bash scripts/check-lint-suppressions.sh --update   # rewrites scripts/lint-suppression-baseline.txt
```

Without this the gate keeps allowing the old ceiling and the gain silently drifts back. Use
`--list` to rank current worst offenders. The gate is independent of `--wfail`: a blanket
suppression makes `--wfail` pass by *hiding* the warning, so a green build never proves
suppressions did not grow.

#### Accumulated findings

Consolidated from 24 cycles. Read before editing.

**Hazards**

- **P1 — the parse hazard (recurred in cycles 12, 16, 22, and again since).** A declaration-scoped
  `set_option ... in` MUST be placed **above the doc comment**, never between the doc comment and
  the declaration. This is a live risk on *every* insertion, not a solved problem. Verify by
  rebuild before each commit; do not rely on memory.
- **P2 — `omit [...] in` is not universally safe.** Correct for `unusedSectionVars`; it *breaks
  compilation* for `unusedDecidableInType`. Distinguish the two before applying it.
- **P3 — `lean_multi_attempt` (MCP) can hit an unrelated Lean/Mathlib toolchain-version mismatch**
  in this repo's current environment. When its `setup-file` step fails, skip the tool and verify
  directly with a scoped `lake build`, which is unaffected.
- **P4 — `replace_all` only after confirming every site is textually identical**, including the
  fully-reduced argument list. Verify site-by-site from the collected warning list, not by
  assumption.
- **P5 — a dangling `by` on its own continuation line breaks the tactic block (found cycle 25).**
  When wrapping a `def X ... := by` signature that exceeds the line limit, do NOT split so that
  `by` ends up alone on its own line (e.g. `def X ... :=\n    by`). This produces
  `expected '*' or checkColGt` plus a cascading `unsolved goals` on the *next* declaration, not
  necessarily the one being edited — the error is easy to misattribute. Fix: wrap the *type
  signature* instead and keep `:= by` attached to the end of the line
  (`def X ... :\n    T := by`). The same principle applies to `simp only [...] at h`: wrap inside
  the bracket list, not by breaking after `at` so the hypothesis name dangles alone.

**Estimation rules**

- **E1 — line count does NOT predict remaining-warning count.** A 1072-line file yielded 7 sites;
  several mid-sized files yielded far more. Always remove the blanket lines and re-derive live
  rather than estimating from `wc -l`.
- **E2 — many blanket suppressions are entirely unnecessary.** Frequently zero warnings surface on
  removal (4 of 7 files in one cycle). Remove-and-rebuild first; never assume a suppression is
  load-bearing because it exists.
- **E3 — files under ~150 lines usually carry 1-2 categories and 1-4 sites.** Past the count-3
  tier, small line count is a stronger effort predictor than the suppression-count tier itself,
  because the remaining high-count files are mostly already narrowed.
- **E4 — when a tier's worklist runs dry mid-cycle, continue opportunistically into the next
  tier's smallest files** rather than stopping. Several have zero downstream importers and are
  near-free.

**Category fixes**

- **C1 — `style.longLine`**: mechanical wrap. Always safe on `have h : DerivationTree ... := ...`
  and on theorem signatures. Wrap onto indented continuation lines.
- **C2 — `linter.flexible`**: the machine-suggested `simp only [...]` replacement is usually
  usable verbatim. Where a bare `simp [X]` genuinely pulls the full default simp set, prefer a
  declaration-scoped `set_option linter.flexible false in` over manually reconstructing the set.
  Where the surrounding tactic block allows, rewriting to avoid the bare-simp-modifying-hypothesis
  pattern (e.g. `rw [hx0] at h1; simp at h1; exact h1` → `rw [hx0, neg_zero] at h1; exact h1`) is
  cleaner than either.
- **C3 — `linter.unusedSimpArgs`**: drop *just* the unused argument from the `simp only [...]`
  list, not the whole call. Confirm the argument is genuinely unused per-site from the warning
  list.
- **C4 — `linter.dupNamespace` on the `Chronicle` pattern** (a `structure` followed by many
  `def Struct.field` accessor-style declarations): narrow, do not remove — this is Phase 2's
  intentional structure-projection namespace. Place one `set_option ... in` before the `structure`
  itself (covering its own warning plus auto-generated field-projection and constructor warnings)
  and one more before each subsequent `def Struct.field`. Typical result: ~10 declaration-scoped
  markers replacing one 2-line blanket, zero net new blanket suppressions.
- **C5 — `linter.style.show`**: mechanically fixable via `show` → `change`.
- **C6 — `style.openClassical`**: a persistent non-`in` `open Classical` correctly bottoms out at
  1 remaining blanket line. "1 remaining" is not by itself a signal that the file is incomplete.
- **C7 — `linter.privateModule`** (found cycle 25): this linter fires once at the module's first
  line (1:0) whenever every declaration in the file is `private`, regardless of whether
  `@[expose] public section` is present. It is a genuinely module-wide diagnostic — there is no
  declaration to attach a narrowed `set_option ... in` to, so a blanket suppression is the
  correct permanent resolution for a file whose declarations are intentionally all-private
  (internal helpers with no external caller). Verify by direct removal + rebuild before
  concluding this, per the Method above — do not assume from the doc comment alone.
- **C8 — `style.emptyLine` inside a large single-command `inductive ... where` block** (found
  cycle 26): axiom-schema-style inductive types with dozens of constructors often use blank lines
  as visual separators between constructors and around `-- Layer N` section comments — all inside
  one command, which the linter forbids. Fix: locate the command's span with
  `grep -n "^inductive\|^def \|^theorem \|^instance\|^namespace\|^end"`, then delete every blank
  line strictly between the `inductive` line and the line before the next top-level command
  (leave the between-command separator blank line untouched). Verify via `diff` that only blank
  lines were removed before rebuilding. This was the dominant category this cycle (3 of 9 files,
  93 of 113 surfaced sites) — anywhere else in the codebase with a large hand-written axiom/rule
  inductive is a likely future hit.

**Directory patterns** (check before deriving an approach from scratch)

- `Bimodal/Metalogic/Bundle/` — pure-`longLine` skew, confirmed on 5 of 6 files inspected.
- Chronicle-named files (`Foundations/Logic/Metalogic/Chronicle/`,
  `Temporal/Metalogic/Chronicle/`, `Bimodal/.../BXCanonical/Chronicle/`) share the C4
  `dupNamespace` pattern and the bare-`simp`-at-`h` C2 pattern. The Bimodal and Temporal
  `ChronicleTypes.lean` files proved structurally identical modulo an extra `fc : FrameClass`
  parameter that shifts doc-comment wrap points but not the strategy. Consult the already-closed
  counterpart first.

**Out of scope, do not chase**

- `lake lint`'s `unusedArguments` findings (currently 147 errors) are a distinct linter and are
  not this task's target. Unchanged category.

#### Permanent exceptions — do not attempt further reduction

| File | Reason |
|---|---|
| `Computability/Automata/DA/Conversions.lean` | Pre-existing documented permanent exception |
| `Bimodal/.../BXCanonical/Filtration/DefectChain.lean` | Pre-existing documented permanent exception |
| `Separation/DedekindZ/QLemma.lean` (435 lines) | Correctly bottoms out at 1 blanket line (persistent non-`in` `open Classical`) |
| `Separation/Eliminations.lean` (871 lines) | Same as above |
| `BXCanonical/Chronicle/CounterexampleElimination/Elimination.lean` (240 lines) | `linter.privateModule` (C7) — verified module-wide by direct removal + rebuild in cycle 25; every declaration is intentionally `private`, no per-declaration narrowing target exists |

All five still count toward the local-only/actionable totals and the repo-wide ratchet; they are
excluded from the *actionable* worklist only. Verify the end state still holds before concluding,
but do not force the count down.

#### Verification per file (non-negotiable)

Scoped rebuild of the file **plus every direct downstream importer**, then commit that file alone.
A full `lake build` is an acceptable substitute for heavily-imported core files where enumerating
importers is impractical. Confirm via `git diff` that no `sorry` line was touched and no proof
term, definition, or theorem statement was altered.

#### Done (cycle 25)

Closed the count-2 tier and processed 9 count-1-tier files (7 fully cleared, 1 verified as a new
permanent exception, plus the closing count-2 pair). Ratchet: 46 → 34 (12 net reduction across 11
commits). All per-file scoped rebuilds plus every direct downstream importer verified green;
`git diff` confirmed no `sorry` line touched and no proof term, definition, or theorem statement
altered in any commit.

| File | Suppressions removed | Category | Commit |
|---|---|---|---|
| `Bundle/WitnessSeed.lean` | 2 → 0 | `style.emptyLine` (36 sites, all bare blank lines in tactic blocks) + `style.longLine` (53 sites, mechanical wrap) | `5f6d021b` |
| `Soundness/DenseValidity.lean` | 2 → 0 | `style.emptyLine` (0 surfaced, E2) + `style.longLine` (20 sites) | `8ca40174` |
| `Separation/Distributivity.lean` | 1 → 0 | `style.emptyLine` (0 surfaced, E2) | `5390eb63` |
| `Separation/NegationEquiv.lean` | 1 → 0 | `style.emptyLine` (0 surfaced, E2) | `dbed1027` |
| `Decidability/FMP/FMP.lean` | 1 → 0 | `style.emptyLine` (0 surfaced, E2) | `ee3f7c18` |
| `Perpetuity/Bridge.lean` | 1 → 0 | `style.longLine` (2 sites; surfaced new P5 dangling-`by` parse hazard, fixed by wrapping the signature instead) | `1459e81c` |
| `Temporal/Metalogic/TemporalContent.lean` | 1 → 0 | `style.emptyLine` (0 surfaced, E2 — despite an inline comment claiming it was structurally required; claim verified false) | `d60ed4e0` |
| `.../CounterexampleElimination/Elimination.lean` | 1 → 1 (unchanged) | `linter.privateModule` (C7, new category) — verified genuinely module-wide by direct removal + rebuild; restored with the verification recorded inline. New 5th permanent exception. | `8bc33b9c` |
| `Temporal/Metalogic/MetricSoundness.lean` | 1 → 0 | `style.setOption` (0 surfaced, E2 — the suppression suppressed only itself) | `18bd3d90` |
| `Separation/FormulaOps.lean` | 1 → 0 | `style.emptyLine` (0 surfaced, E2) | `69ca8662` |
| `Decidability/FMP/ClosureMCS.lean` | 1 → 0 | `style.emptyLine` (0 surfaced, E2) | `3122da7d` |

Phase-boundary gate re-verified green at cycle close: `lake build --wfail --iofail` (exit 1,
exactly the 5 baseline sorry warnings), `lake test` (exit 0), `lake exe checkInitImports` (pass),
`lake lint` (0 matches on the 7 prevention categories), `lake shake` (12 upstream-shared, 0
local-only), `lake exe mk_all --check` (no update necessary), `scripts/check-lint-suppressions.sh`
(exit 0, "34 (baseline ceiling 34)").

#### Done (cycle 26)

Closed the count-1 actionable tier entirely — all 9 files from the cycle-25 worklist cleared to 0
blanket suppressions. Ratchet: 34 → 25 (9 net reduction across 9 commits). All per-file scoped
rebuilds plus every direct downstream importer verified green; `git diff` confirmed no `sorry`
line touched and no proof term, definition, or theorem statement altered in any commit.

| File | Suppressions removed | Category | Commit |
|---|---|---|---|
| `Temporal/ProofSystem/Axioms.lean` | 1 → 0 | `style.emptyLine` (39 sites, blank lines inside the single-command `inductive Axiom` block, between constructors and `-- Layer N` comments) | `469f62ae` |
| `ConservativeExtension/ExtDerivation.lean` | 1 → 0 | `style.emptyLine` (7 sites, same `inductive ExtAxiom`-block pattern) | `2c4a3e29` |
| `Bimodal/ProofSystem/Axioms.lean` | 1 → 0 | `style.emptyLine` (47 sites, same `inductive Axiom`-block pattern; largest single-file site count this task to date) | `1af48333` |
| `Decidability/ProofExtraction.lean` | 1 → 0 | `style.longLine` (10 sites, 105-151 chars; fixed by wrapping def signatures and a multi-line `let`-chain, plus one Lean string-gap continuation for a long diagnostic string literal — new technique, worked cleanly) | `d8c6b4cd` |
| `Decidability/FMP/TruthPreservation.lean` | 1 → 0 | `style.emptyLine` (0 surfaced, E2) | `1daaf38a` |
| `Decidability/Closure.lean` | 1 → 0 | `unusedSectionVars` (2 sites, `SignedFormula.beq_self`/`eq_of_beq_eq_true` auto-included `[Hashable Atom]` unused; fixed with declaration-scoped `omit [Hashable Atom] in`, per P2/C-pattern for this category) | `6df8000b` |
| `Temporal/Metalogic/MetricCompleteness.lean` | 1 → 0 | `style.setOption` (0 surfaced, E2 — same pattern as cycle 25's MetricSoundness.lean: suppression suppressed only itself) | `f8249816` |
| `Separation/Defs.lean` | 1 → 0 | `style.emptyLine` (0 surfaced, E2). Heavily-imported core file (10 direct importers); verified via a full rebuild of `Metalogic/Separation.lean` (811 jobs) rather than enumerating importers, per the Verification-per-file exemption | `8532f4ec` |
| `Decidability/Tableau.lean` | 1 → 0 | `style.longLine` (8 sites, 101-105 chars, all the same shape: `let prop := SignedFormula.X arg { world := ..., time := freshTime }` inside `applyRule`'s auto-propagation branches; fixed by wrapping the record literal onto an indented continuation line). Heavily-imported core file; verified via a full rebuild of `Decidability.lean` (809 jobs) | `9ff65ebd` |

New finding this cycle: **large single-command `inductive ... where` blocks are the dominant
`style.emptyLine` source** at this file-size tier (three files, 39+7+47=93 of this cycle's 113
surfaced sites) — blank lines used as visual separators between constructors, or around
`-- Layer N` section comments, inside one giant command. The fix is always the same: delete the
blank lines strictly between the `inductive` keyword and the line immediately before the next
top-level command (found via `grep -n "^inductive\|^def \|^theorem \|^instance\|^namespace\|^end"`
to locate the command's start/end), while leaving the blank line that separates it from the next
command untouched. Verified via `diff` after mechanical removal that the only removed lines were
blank (no content line ever matched the removal filter), before ever running `lake build`.

The Lean string-gap continuation (`\` immediately before a newline inside a string literal, with
the continuation's leading whitespace elided) worked as a way to wrap an over-length string
literal without altering its content — confirmed by a clean `lake build` with zero warnings and
by `git diff` showing only the wrap, not a wording change. Recorded as a technique for future
`style.longLine` sites that hit a genuinely single long string rather than an over-length
expression.

Phase-boundary gate re-verified green at cycle close: `lake build --wfail --iofail` (exit 1,
exactly the 5 baseline sorry warnings), `lake test` (exit 0), `lake exe checkInitImports` (pass),
`lake lint` (0 matches on the 7 prevention categories, 144 out-of-scope `unusedArguments`
findings unchanged in kind), `lake exe lint-style` (exit 0), `lake shake` (12 upstream-shared, 0
local-only), `lake exe mk_all --module` (no update necessary), `scripts/check-lint-suppressions.sh`
(re-baselined via `--update`, exit 0, "25 (baseline ceiling 25)").

### Phase 6: Sorry visibility [COMPLETED]

All 18 declaration-scoped `warn.sorry` sites (0 file-scoped) verified to carry a documented
technical-blocker reason at the site — an external "WeakCanonical discrete-completeness port"
dependency.

**Bimodal-vs-rest-of-tree asymmetry disposition**: suppression retained and justified.
Propositional/Modal's unsuppressed sorries have no analogous external-port dependency, and
removing the suppression today would revert the CI gate from 5 to **26** warnings (measured via a
reverted, uncommitted experiment — not the 23 previously claimed). **Explicit revisit trigger**:
once the WeakCanonical port lands and the sorries can actually be discharged.

### Phase 7: Script and documentation defects [COMPLETED]

- `scripts/pre-pr-check.sh` can now actually fail, and uses the correct sorry-census method.
- `ORGANISATION.md` refreshed for 5 undocumented `Modal/Metalogic` subdirs and `Temporal/Tableau/`.
- **`NOTATION.md` — closed by explicit user decision.** A "Logic notation scoping" section was
  added documenting all three senses of the token `S` (the *Since* temporal operator, the
  `InferenceSystem` type parameter, and the docstring-only combinatory-logic S-axiom), the
  `@`-positional application rule that follows from the collision, and guidance against bare
  capital letters for new scoped notation. The user authorized this as an explicit, recorded
  exception to the upstream-exposure carve-out, overriding the prior "route as an upstream PR"
  disposition. **This is the one deliberate upstream-shared edit in this task.**
- **The 5 `NOTE:` blocks — premise struck, blocks RETAINED.** The characterization of these as
  "5 stale `NOTE:` blocks" was investigated and found factually wrong: all 5 are live, accurate
  documentation of a collision that still exists. Per user decision the false premise was struck
  rather than the blocks executed. Their deletion is not an item of this task at all — it is a
  downstream consequence of the `S`→`Sys` rename, which remains correctly excluded.

### Phase 8: Dead-code deletions [COMPLETED]

Closed at 9 of 10 rows: 13 dead declarations and 5 dead modules deleted. `HilbertSearch.lean` was
excluded by finding — a real tactic implementation, invisible to a declaration-keyword scan.

---

## Testing & Validation

**Principle**: verification granularity is matched to what an edit can actually break. The
strictness of the final gate is unchanged — every gate below still runs before the task is
declared done, and no commit ever contains unverified work.

### Two build commands, deliberately distinguished

| Command | Cost | When |
|---|---|---|
| `lake build Cslib.Path.To.Module` | rebuilds that module's cone only | **during** a phase, per batch |
| `lake build --wfail --iofail` | full repo, 672 modules | **phase boundary only** |

### Risk tiers — assign every edit before making it

**When in doubt, use the higher tier.** Mis-assigning downward is the only way this protocol can
lose accuracy, so the tie-break is always upward.

| Tier | Edit class | Can it change elaboration? | Verification |
|---|---|---|---|
| 0 | Non-compiling files: `.md`, `.yml`, `.sh`, `.github/**` | No — Lean never reads them | No Lean build. `bash -n` for shell scripts |
| 1 | Comment / docstring text only, no code tokens | No | Batch freely; one targeted build per batch |
| 2 | Deletion of dead code | Only via dangling reference, which the compiler names exactly | `grep` for references first, then batch-delete + targeted build over affected reverse-deps |
| 3 | Import edits | Only via missing/unused import, precisely reported | Batch per directory + targeted build; re-run `lake shake` at phase end |
| 4 | Tactic-surface rewrites, suppression removal (**Phase 5**) | **Yes — genuinely proof-affecting** | Small batches of *mutually independent* modules; targeted build per batch |

**Phase 5 runs at Tier 4.** Its per-file verification requirement (above) is stricter than the
generic tier guidance and takes precedence.

### On failure

The compiler names the file and line; fix it directly. Only if a failure is genuinely ambiguous
across a batch, bisect the batch.

### Phase-boundary gate (unchanged in strictness)

All four, at every phase boundary and before declaring the task done:

```bash
lake build --wfail --iofail   # must show ONLY the 5 sorry warnings listed above
lake test                     # exit 0, 0 errors
lake exe mk_all --check
lake exe checkInitImports
```

Plus, for Phase 5: `lake shake` (expect only the 12 upstream-shared files) and
`bash scripts/check-lint-suppressions.sh` (expect exit 0 at the current ceiling).

### Commit granularity

Commit per verified-green batch. This satisfies `.claude/rules/git-workflow.md`'s
commit-per-green-substep mandate: a sub-step is a progress-file objective reaching `done`, and
`files_touched` accumulates across multiple files. Keep batches to one tier and one phase.
**Phase 5 commits one file at a time**, per its own stricter rule.

## Artifacts & Outputs

| Artifact | Kind | Notes |
|---|---|---|
| `plans/02_lint-hygiene-ci-gate.md` | plan | This file; carries phase state, findings, resume point |
| `plans/01_lint-hygiene-ci-gate.md` | plan | Superseded v1; retained for per-cycle history |
| `handoffs/NN_cycle-*.md` | handoff | Per-cycle detail and continuation context |
| `.github/workflows/lean_action_ci.yml` | deliverable | `lake shake` step uncommented and live |
| `scripts/pre-pr-check.sh` | deliverable | Able to actually fail; correct sorry-census method |
| `scripts/lint-suppression-baseline.txt` | deliverable | Ratchet baseline; re-based each reduction |
| `ORGANISATION.md`, `NOTATION.md` | deliverable | Refreshed / scoped-notation section added |
| `Cslib/**` | deliverable | 240 linter sites cleared; 226 citations replaced; 13 declarations and 5 modules deleted; imports shaken; suppressions narrowed |

No report artifact was filed: research findings were inlined into this plan.

## Definition of Done

| Criterion | State |
|---|---|
| `lake build --wfail --iofail` reports no warning other than the 5 genuine sorries | **MET** |
| `lake test` green, 0 errors | **MET** |
| `lake shake` clean and its CI step uncommented | **MET** |
| `pre-pr-check.sh` can actually fail | **MET** |
| Zero `task N` / `Phase N` / `report N` strings in `Cslib/**`, less 2 documented irreducible sites and 8 confirmed false positives | **MET** |
| Every `warn.sorry` suppression has a recorded per-site justification, and the Bimodal-vs-rest asymmetry has an explicit disposition | **MET** |
| `NOTATION.md` documents the scoped-notation rule for the `S` collision, and the 5 `NOTE:` blocks documenting the `@`-application workaround are retained while the collision persists | **MET** |
| No hygiene edit lands in an upstream-shared file **except where the user has explicitly authorized it, and every such exception is recorded** | **MET, one recorded exception** — `NOTATION.md` (Phase 7). Known consequence, accepted: it will diverge from upstream and need reconciling on the next sync |
| Suppression audit outcome recorded per site, **for local-only files** | **PARTIAL** — 444 sites done across 112 files; the count-1 actionable tier is fully closed. Only the deliberately-deferred count-6 file (`CounterexampleElimination/Interface.lean`, 6 blanket suppressions) remains, plus 5 permanent exceptions with recorded verification |

The last row is the only open criterion. It is **bounded** — the original repo-wide wording was
open-ended; the upstream-exposure rescope made it finite.

## Rollback/Contingency

Every commit is verified green before landing, so `git revert <sha>` is safe. No commit in this
task alters mathematics, so a revert can never reintroduce a proof gap — worst case it
reintroduces a warning. Keep batches to one tier and one phase so a revert stays semantically
clean.

If a Phase 5 suppression removal surfaces warnings that cannot be fixed without changing a proof:
restore the suppression, but convert it from file-scoped to declaration-scoped (`... in`) and
record why. **Do not leave a blanket suppression in place as the resolution.**

**Reversing the upstream-exposure rescope** is a scope decision, not a code change: restore the
"repo-wide" wording in "Upstream-exposure scope", Phase 5's scope paragraph, and the Definition of
Done, and the 14 shared-file suppressions come back into scope. Reverse it only if the decision is
made to stop tracking `upstream` — the carve-out's whole justification is conflict cost. If the
fork stops syncing, remove the sync branch and the `upstream` remote in the same change so
rationale and configuration do not drift apart.

---

## Open decisions (non-blocking for Phase 5; recorded for the user)

None of these block further Phase 5 progress.

1. **`#print axioms` gate — recommend a separate task.** `succ_cofinal`
   (`ChronicleToCountermodel.lean:78`) and `limitDomSubtypeIsSuccArchimedean` (`:87`) consume a
   sorry'd lemma, contain no `sorry` token, and emit no warning. Both verify `sorryAx`-contaminated.
   `bimodal_conservative_over_temporal` (`:289`) is contaminated the same way with prose-only
   disclosure. **No `warn.sorry` policy however strict catches this class** — the declarations are
   clean by every syntactic measure. A `#print axioms` gate over the public API is the only
   mechanism that does. `IsSuccArchimedean` is a Mathlib-facing structural property, so a vacuous
   instance is the worst-shaped version of this. Correctness, not hygiene — out of scope here.
2. **620 dead lines in `Foundations/Logic/Metalogic/`** — `ProofSystemMorphism` (317),
   `DeductionCharacterization` (159), `SetDeduction` (144). Imported only by the root barrel.
   Deletion deferred by the user: they are plausibly the *right* abstraction that never got
   adopted — `SetDeduction` duplicates functionality Modal/Temporal/Bimodal each solved locally.
   Needs a design call: wire up or delete.
3. **The `Chronicle` namespace/structure name coincidence** (Phase 2) — move the structure to the
   parent namespace, or rename the namespace across the subtree? Out of scope for a hygiene-only
   task. Until decided, the C4 declaration-scoped narrowings stay.
4. **`lean_action_ci.yml` diverges from upstream in TWO directions, only one of them this task's
   doing:**

   | Setting | upstream | local | Origin |
   |---|---|---|---|
   | `lake shake` step | commented out | **enabled** | This task, Phase 4 — intended |
   | `test-args` | `--wfail --iofail` | `""` | **Not this task** — predates it |
   | `TEST_ARGS` | `--wfail --iofail` | `''` | **Not this task** — predates it |

   The local *test* gate is therefore weaker than upstream's, while the *build* gate this task's
   Definition of Done is measured against is strict. Nothing in the task description authorizes
   relaxing tests, so this is pre-existing divergence surfaced here, not something Phase 4
   introduced — but it is a **shared** file needing reconciliation on every upstream sync.
   **Decision needed**: restore `--wfail --iofail` on the test args (and fix whatever then fails),
   or record an explicit reason for the local relaxation.

   **Second shared file carrying local divergence — `NOTATION.md`** (not a decision; recorded so
   both live in one place). This divergence is intentional and user-authorized (Phase 7). Noted
   only so whoever performs the next upstream sync has the complete list of expected conflicts.
   Raising the same section upstream would retire it.

---

## Routed elsewhere (needs mathematics — not this task)

Recorded from the four subsystem reviews, for the owning tasks:

- **The Bimodal Chronicle tree is a wholesale fork of the Temporal one** — 250 of 305 declarations
  shared, `ChronicleConstruction.lean` at 63% line identity. Framing this as "extract a few shared
  lemmas" under-scopes it; this is a merge. Suggested seam: the `ChronicleInterface` instance
  family already present in both `ChronicleTypes.lean` files.
- **`GenericMCSBridge.lean` exists 4 times** (845 lines). Falls between the Lindenbaum and
  Chronicle-consolidation workstreams — neither names it. Needs an ownership call.
- **Three classical-fragment completeness files**: 1,388 lines of one copy-pasted Kalmár skeleton;
  `litCtx_congr` byte-identical across two. (The `litCtx_congr` triplication and the dead
  `Proposition.atoms` are hygiene-only and could fold into this task if desired.)
- **`IntDecidability`/`MinDecidability`**: 942 lines of 1:1 parallel proof, in a directory where
  `GenericLindenbaum.lean` already establishes the axiom-parameterized-substrate idiom.
- **LTL remains an island**: 2,742 lines, 0 sorries, a real proved semantic bridge
  (`EmbeddingSemantics.lean:96,148`), and no consumer. A bridge load-bearing for nothing can rot
  silently.
- **CPL decidability gap**: IPL and MPL have `Fintype`-free tableau `Decidable` instances for
  `Derivable`; CPL has none, purely by omission.
- **Minimal/Intuitionistic completeness duplication**: `Tableau/Minimal/Completeness.lean` is a
  near-line-for-line copy of `Tableau/Intuitionistic/Completeness.lean`, one sorry each.
  Discharging both independently bakes the duplication in permanently; make them one
  bot-forcing-parameterized result **first**.
- **Proof-simplification sequencing**: `simp only` cleanup across triplicated proof is wasted if
  the triplication is then removed. Sequence simplification work *after* the consolidations above.
- **Test coverage**: the entire metalogic layer has zero executable regression tests.
  `Foundations/Logic/Tableau` (8 files, consumed by three logics) is the highest value-per-line
  gap — a defect in the shared closure condition propagates into every calculus uncaught.
- **Docstring claim inflation**: `HilbertCompleteness.lean:95-97` claims "20+ use-sites"; the real
  term-level count is 9, five of which are inside the dead `CanAlgComplete`.
