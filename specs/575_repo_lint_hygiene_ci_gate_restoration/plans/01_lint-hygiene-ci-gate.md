# Repo Lint & Hygiene Cleanup — CI Gate Restoration

- **Task**: 575
- **Status**: PARTIAL
- **Effort**: ~4h spent; ~6-10h remaining (Phase 3 dominates)
- **Dependencies**: none blocking. Coordinate with 557/558 (Modal/Tableau refactor) before large
  edits to `Modal/Tableau/`; coordinate with 317 before edits to `Propositional/Tableau/`.
- **Research Inputs**: four parallel subsystem reviews (Propositional, Modal, Temporal/Bimodal,
  shared infrastructure) conducted 2026-07-27; findings inlined below rather than filed as
  separate reports.
- **Artifacts**: `plans/01_lint-hygiene-ci-gate.md` (this file);
  `remaining-warnings.txt` (historical W1 worklist, now exhausted)
- **Standards**: `.claude/rules/no-task-references-in-deliverables.md`,
  `.claude/rules/git-workflow.md` (commit-per-green-substep), `CONTRIBUTING.md`
- **Type**: cslib
- **Created**: 2026-07-27
- **Last updated**: 2026-07-27

---

## RESUME HERE

Everything below Phase 3 is untouched work. To pick this up cold:

1. Confirm the baseline still holds (2 commands, ~5 min):
   ```bash
   lake build --wfail --iofail   # expect exit 1 with EXACTLY 5 warnings, all "declaration uses sorry"
   lake test                     # expect exit 0, 0 errors
   ```
   If either differs, something landed from another session — reconcile before proceeding.
2. Start at **Phase 3** (task-number references, 312 sites). It is the largest remaining item and
   needs no design decisions.
3. Phases 4-7 are independent of each other and of Phase 3; any order works.
4. Two items need a **user decision before work starts** — see "Open decisions" at the bottom.

**Do not** re-derive the sorry census with a naive grep. Use the method in "Measurement notes".

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
- Discharging any `sorry`. Four files legitimately retain sorries and WILL still be CI-red at task
  end. That is the correct end state; clearing them is mathematical work owned by tasks 317 and
  553/557.
- Any structural consolidation requiring mathematics — see "Routed elsewhere".

## Constraints

- **No sorry may be discharged, added, moved, or suppressed.**
- **No proof term, definition, or theorem statement may be altered.** Only tactic surface syntax
  (`simp [X] at h` -> `simp only [...] at h`).
- **No new `set_option linter.* false`.** Suppressing instead of fixing is the pattern Phase 5
  exists to reverse. If a warning cannot be fixed without changing mathematics, report it.
- Verification protocol (user decision): rebuild after **each file**, commit only when green.

### Explicit non-targets — do NOT "clean" these

Each was investigated and found correct. Re-investigating wastes a cycle.

- `Temporal/Metalogic/PropositionalHelpers.lean` and `Bimodal/Theorems/Perpetuity/Helpers.lean`
  are **not** redundant wrappers. Their aliases carry 187 and 416 call sites (`impTrans` alone:
  47 and 96). They absorb `@`-positional boilerplate once instead of at every call site.
- `TemporalConservativity.lean:245`'s "sorry-free" claim is **true**. It scopes to two
  declarations that both verify axiom-clean; line 243 names the sorry'd one as the gap.
- The three `Chronicle` modules' `Chronicle.` prefix is **not** a doubled namespace — see Phase 2.

---

## Baseline and current state

| Gate | At task start | Now |
|------|--------------|-----|
| `lake build` | green 3259/3259 | green |
| `lake test` | green, 0 errors | green, 0 errors |
| `lake build --wfail --iofail` | **exit 1**, 27 modules, 460 warnings | **exit 1**, 4 modules, **5 warnings — all genuine sorries** |
| `lake exe mk_all --check` | pass | pass |
| `lake exe checkInitImports` | pass | pass |
| `lake shake` | 94 files flagged (CI step disabled) | unchanged |
| Linter sites | 240 | **0** |
| `set_option linter.*` | 511 | 482 |
| `@[nolint]` | 118 | 88 |
| Task-tracker refs in `Cslib/**` | 376 | 312 |
| Doubled public names | 6 cross-module leaks | **0** |
| Bare sorries (correct method) | 28 | 28 (unchanged by design) |

The 5 remaining warnings, which are the correct end state:
```
Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1253            declaration uses `sorry`
Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:568    declaration uses `sorry`
Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:2580   declaration uses `sorry`
Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean:124  declaration uses `sorry`
Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:118     declaration uses `sorry`
```

### Measurement notes — two independent causes of this repo's recurring sorry-count error

Any future census must account for both, or it will be wrong again.

1. `set_option warn.sorry false` contains `sorry` at a word boundary, so a naive `\bsorry\b` scan
   counts 12 option lines as proof holes. This inflated Bimodal 23 -> 35.
2. Nine tracked scratch files at the repo root (8 `Test_*.lean` + `OF`) carried 15 sorries while
   belonging to no build target — invisible to `lake build`, counted by every grep. Removed in
   `2f608bdf`.

The project's own "41 -> 40" figures were wrong in both ways. Correct method: strip `/- -/` and
`--` comments, exclude lines containing `warn.sorry`, scan only build-reachable files.

---

## Implementation Phases

### Phase 1: Linter sites [COMPLETED]

240 distinct source sites across 27 files (460 raw warnings; one recurring flexible-simp pattern
accounted for 241 warnings at only 42 sites). Cleared in 23 individually-verified commits
(`1475b0a4` … `a4cdbe64`).

Fix recipes used, for reference if warnings reappear:
- "simp argument is unused" -> delete the argument from the `simp only [...]` list
- "flexible tactic modifying h" -> `simp [args] at h` becomes `simp only [<explicit>] at h`;
  get the explicit list from `simp?` via `lean_multi_attempt`, never by guessing
- "does not use the following hypothesis in its type" -> rename binder to `_name`; do not delete
- "section variable(s) unused" -> `omit ... in` before the theorem, matching file convention
- "`show` should only indicate intermediate goal states" -> replace `show` with `change`
- unnecessary `simpa` -> prefer `exact <lemma>` over bare `simp`, to keep the citation

Fixing warnings cascades: four extra files (FiveSimplification, TDriver, BDriver,
FrameCompleteness) surfaced new warnings only after earlier fixes landed. Expect this and re-run
the gate after each batch.

### Phase 2: Doubled-namespace public API [PARTIAL — 7 of 10 files]

**Done** (30 declarations, commits `f60f9a74` … `6196b01e`): MetricSoundness (1), Bimodal
Core/DerivationTree (2), Temporal Metalogic/DerivationTree (2), MCS (2), DenseMCS (4), Temporal
ProofSystem/Derivable (9), Bimodal ProofSystem/Derivable (10), plus 2 vestigial suppressions in
the two `ProofSystem/Axioms.lean`. 42 of 78 `dupNamespace` suppressions deleted. All 6
cross-module leaks (`Cslib.Logic.Temporal.Temporal.ThDerivable` and friends) eliminated.

**Aborted, and the original diagnosis was WRONG** — do not retry as a mechanical rename. The
three `Chronicle` modules' `Chronicle.` prefix is not a repeated namespace component; it is the
*structure* name. `namespace ...Metalogic.Chronicle` contains `structure Chronicle`, so
`def Chronicle.c0` correctly declares the projection-namespace member that 81 dot-notation call
sites (`chi.c0`, `chi.c3`, …) depend on. Stripping it fails with
`Invalid field 'c0': the environment does not contain ...Chronicle.Chronicle.c0`.

The genuine defect is the `namespace Chronicle` / `structure Chronicle` name coincidence. Fixing
it means moving the structure to the parent namespace, or renaming the namespace across the whole
`Chronicle/` subtree — a design decision. The remaining 36 suppressions (33 `@[nolint]`,
3 `set_option`) are **load-bearing** until that call is made. Files:
`Temporal/Metalogic/Chronicle/ChronicleTypes.lean`,
`Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean`,
`Foundations/Logic/Metalogic/Chronicle/Types.lean` (9 declarations each).

**Estimation lesson**: the original "~484 reference sites" was wrong by ~80x. The true count was
**6**. Short-form references (`Temporal.SetMaximalConsistent`, 289 occurrences) need no edit —
they resolve to the un-doubled name via the enclosing-namespace walk once the declaration loses
its doubled component. Only fully-qualified spellings break.

### Phase 3: Task-number references in deliverables [NOT STARTED]

**312 sites.** Violates `.claude/rules/no-task-references-in-deliverables.md`. An earlier cleanup
stripped ~918; these are a regression.

The narrow `task N` regex finds only 121 and **misses `Minimal/Completeness.lean` entirely**. Use:
```bash
grep -rnoiE '\b(task|tasks|phase|report) [0-9]+(\.[0-9]+)?\b' Cslib --include='*.lean'
```
Sampling confirmed the `Phase N` / `report N` hits are task-tracker history ("Phase 6", "plan v3",
"report 08"), not mathematical algorithm phases. Spot-check before bulk-editing any file, since a
legitimate "Phase 3" could exist in an algorithm description.

Worst files (recount before starting): Intuitionistic/Scheme, LoopChecking, Nested/Soundness,
ChronicleToCountermodel, Intuitionistic/Completeness, Intuitionistic/Expansion.

Replace each with a durable anchor — sibling filename, section heading, or verified fact. **Never
delete the surrounding explanation**; the prose is usually load-bearing, only the identifier rots.

### Phase 4: Import gate (`lake shake`) [NOT STARTED]

Commented out at `.github/workflows/lean_action_ci.yml:29-32`.

**Do not naively re-enable.** ~77% of flagged removals are a redundant `import Cslib.Init`; only
**~24 are genuine** unused module imports, clustered in Tableau code. For every flagged file
another `Cslib.*` import carries `Cslib.Init` transitively, so `checkInitImports` would not break
— but the churn diff would be large and valueless.

Correct sequence: configure shake to always keep `Cslib.Init`, fix the ~24 genuine imports, then
uncomment the CI step.

Reconcile counts first — two runs disagreed: 94 files / 91 removes / 19 adds versus
92 / 106 / 36. Likely flag or version drift; resolve before acting.

### Phase 5: Suppression audit [PARTIAL — 18 of ~570 done]

**Done**: 18 provably-vestigial deletions (`37046110`) — 14 `longLine` in files with no line over
100 chars, 4 `setOption` whose only effect was silencing themselves. Rebuild produced zero new
warnings, confirming they suppressed nothing.

**Structural finding**: 464 of the original 511 were *file-scoped blanket* suppressions; only 47
declaration-scoped. A blanket suppression atop a 2,000-line file silences every *future* violation
too — coverage accumulates rather than decaying. Suppression density also tracks incompleteness:
`Separation/` and `CounterexampleElimination/` dominate the worst-offender list and are the same
areas carrying the sorries.

| Category | Count | Verdict |
|---|---|---|
| Pure style (emptyLine 103, longLine 89, setOption 68, show 18, openClassical 7, maxHeartbeats 3) | 288 | Not justified; no mathematics needed. **Best next target.** |
| Correctness-adjacent (flexible 68, unusedSimpArgs 43, unusedDecidableInType 30, unusedSectionVars 21, dupNamespace 15, unusedVariables 7, unusedTactic 2, privateModule 2) | 188 | Mixed; assess per site |
| `tacticAnalysis.verifyGrindOnly` | 35 | **Justified and correctly scoped — leave alone** |

Of the 118 `@[nolint]`: `dupNamespace` 60 (Phase 2 territory), `unusedArguments` 40 (plausible —
uniform signatures across a lemma family often carry arguments a given case ignores; no evidence
against them found), `docBlame` 15, singletons 3.

Worst offenders: `Separation/DedekindZ/Cases.lean` (12),
`CounterexampleElimination/Elimination.lean` (8), then several at 6-7.

**Method**: remove, rebuild, fix whatever surfaces. Only removal-plus-rebuild proves whether a
suppression is load-bearing.

### Phase 6: Sorry visibility [NOT STARTED]

- `ChronicleToCountermodel.lean:46` is the **only file-scoped `warn.sorry` in the repo** (the
  other 11 use `... in` and bind one declaration). It was appended to a block of style
  suppressions and matched their form — correct for linters, wrong for a soundness signal. Blast
  radius: all 12 sorries in the file, plus any added later. Line 43 of that same block suppresses
  the linter that would flag the block itself. **Fix: split into 12 scoped `... in` forms.**
  Mechanical.
- All 12 `warn.sorry` suppressions repo-wide are in Bimodal; Propositional's 4 and Modal's 1 are
  unsuppressed and do surface. Measured asymmetry: `Minimal.Completeness` exits 1 under `--wfail`
  while `Bundle.UntilSinceCoherence` (2 suppressed sorries) exits 0.

### Phase 7: Script and documentation defects [NOT STARTED]

- **`scripts/pre-pr-check.sh:5-26` cannot fail.** Steps 1-3 wrap their greps in `if` conditions,
  so `set -e` never applies and no step sets an exit code; only step 4's `lake build` can fail it.
  Its sorry check uses the naive grep that caused the count inflation, and its debug-command scan
  returns 4 false positives (docstring mentions at `S5Simplification.lean:1963,1966,1970` and
  `LoopChecking.lean:7178`). Fix: accumulate a failure flag and `exit 1`; strip comments and
  exclude `warn.sorry`; anchor the debug grep to line starts; add `lake build --wfail --iofail`.
- **`LoopChecking.lean:160-161`** asserts "Repo-wide: 11 TODO:, 8 NOTE:". Both wrong (13 and 9),
  and self-referentially incoherent: claims no `NOTE:` tags in its own file while containing two,
  and the two asserting lines are themselves among the counted tags. Delete them; a repo-wide
  census belongs in a script where it cannot go stale.
- **`ORGANISATION.md` stale by ~100 files.** Every claimed path exists (no phantoms); the failure
  is omission. Modal lists `Metalogic/` as 5 files; reality is 94 undocumented across `Systems/`
  (45), `Constructive/` (24), `InterSystem/` (10), `Intuitionistic/` (9), `Minimal/` (6).
  Temporal's `Tableau/` (8 files) absent entirely. The `Foundations/Logic/Tableau/` entries ARE
  current and correct. Consider a CI check diffing sketch against filesystem — at this drift rate
  a hand-maintained census will go stale again.
- **`NOTATION.md` has no logic section**, for a tree that is ~450 of 676 files. Concrete cost:
  `Foundations` names its proof-system type parameter `S`, colliding with Temporal/Bimodal scoped
  notation `S` for *Since*, forcing `@`-positional application in 5 files. Documented five times
  in `NOTE:` blocks, fixed zero times. Fix: rename `S` -> `Sys` in `Foundations/Logic/`, delete
  the 5 NOTE blocks, add a scoped-notation rule to NOTATION.md.

### Phase 8: Dead-code deletions [PARTIAL — 1 of 10 done]

User-approved in full. Only the root scratch files have landed.

| Target | Lines | Status | Evidence |
|---|---|---|---|
| 9 root scratch files | — | **DONE** `2f608bdf` | In no build target; 15 phantom sorries |
| `KripkeBridge.lean` | 296 | NOT STARTED | All 6 exports: 0 external refs |
| `Bridge.lean` | 133 | NOT STARTED | Self-documents "no in-tree consumer"; 1 hit is a docstring |
| `CanAlgComplete` + `FragmentGeneric` | 333 | NOT STARTED | 0 term-level consumers |
| 9 zero-declaration aggregator modules | 238 | NOT STARTED | 0 decls, 0 importers |
| 7 dead MCS-transfer wrappers | ~50 | NOT STARTED | 0 external refs (8th has 6 — **keep it**) |
| `Theory.Derivation.normalize` + `normalizeAux` | ~25 | NOT STARTED | 0 consumers, no correctness theorem |
| 2 dead `GenericMCSBridge` lemmas | ~15 | NOT STARTED | 0 consumers |
| `NativePropositionalEmbedding` | ~5 | NOT STARTED | Uninstantiated stub |
| `hilbertConjImpConservativeOverImp_direct` | ~4 | NOT STARTED | Pure alias; `_direct` name is backwards |

Deleting modules requires updating `Cslib.lean` and re-running `lake exe mk_all --module`.

---

## Testing & Validation

Run after every file, and all four before declaring done:

```bash
lake build --wfail --iofail   # must show ONLY the 5 sorry warnings listed above
lake test                     # exit 0, 0 errors
lake exe mk_all --check
lake exe checkInitImports
```

## Definition of Done

- `lake build --wfail --iofail` reports no warning other than the 5 genuine sorries. **[MET]**
- `lake test` green, 0 errors. **[MET]**
- Zero `task N` / `Phase N` / `report N` strings in `Cslib/**`.
- `lake shake` clean and its CI step uncommented.
- Suppression audit outcome recorded per site.
- `pre-pr-check.sh` can actually fail.

## Rollback / Contingency

Every change is an isolated commit verified green before landing, so `git revert <sha>` is safe
per-file. No commit in this task alters mathematics, so a revert can never reintroduce a proof
gap — worst case it reintroduces a warning.

If a Phase 5 suppression removal surfaces warnings that cannot be fixed without changing a proof:
restore the suppression, but convert it from file-scoped to declaration-scoped (`... in`) and
record why. Do not leave a blanket suppression in place as the resolution.

---

## Open decisions (blocking, need the user)

1. **`#print axioms` gate — recommend a separate task.** `succ_cofinal`
   (`ChronicleToCountermodel.lean:78`) and `limitDomSubtypeIsSuccArchimedean` (`:87`) consume a
   sorry'd lemma, contain no `sorry` token, emit no warning, and carry docstrings giving no
   warning. Both verify `sorryAx`-contaminated. `bimodal_conservative_over_temporal` (`:289`) is
   contaminated the same way with prose-only disclosure. **No `warn.sorry` policy however strict
   catches this class** — the declarations are clean by every syntactic measure. A `#print axioms`
   gate over the public API is the only mechanism that does. `IsSuccArchimedean` is a
   Mathlib-facing structural property, so a vacuous instance is the worst-shaped version of this.
   This is correctness, not hygiene, and is out of scope for 575.
2. **620 dead lines in `Foundations/Logic/Metalogic/`** — `ProofSystemMorphism` (317),
   `DeductionCharacterization` (159), `SetDeduction` (144). Imported only by the root barrel.
   User deferred deletion: they are plausibly the *right* abstraction that never got adopted —
   `SetDeduction` in particular duplicates functionality Modal/Temporal/Bimodal each solved
   locally. Needs a design call: wire up or delete.
3. **The `Chronicle` namespace/structure name coincidence** (Phase 2) — move the structure to the
   parent namespace, or rename the namespace across the subtree? Until decided, 36 suppressions
   stay.

---

## Routed elsewhere (needs mathematics — not this task)

Recorded from the four subsystem reviews for the owning tasks:

- **Bimodal Chronicle tree is a wholesale fork of the Temporal one** — 250 of 305 declarations
  shared, `ChronicleConstruction.lean` at 63% line identity. **Task 41 looks under-scoped** if
  framed as extracting a few shared lemmas; this is a merge. Suggested seam: the `ChronicleInterface`
  instance family already in both `ChronicleTypes.lean` files.
- **`GenericMCSBridge.lean` exists 4 times** (845 lines). Falls between task 393 (Lindenbaum) and
  task 41 — neither names it. Needs an ownership call.
- **Three classical-fragment completeness files**: 1,388 lines of one copy-pasted Kalmár skeleton;
  `litCtx_congr` byte-identical across two. (The `litCtx_congr` triplication and the dead
  `Proposition.atoms` are hygiene-only and could fold into 575 if desired.)
- **`IntDecidability`/`MinDecidability`**: 942 lines of 1:1 parallel proof, in a directory where
  `GenericLindenbaum.lean` already establishes the axiom-parameterized-substrate idiom.
- **LTL remains an island**: 2742 lines, 0 sorries, a real proved semantic bridge
  (`EmbeddingSemantics.lean:96,148`), and no consumer. A bridge load-bearing for nothing can rot
  silently.
- **CPL decidability gap**: IPL and MPL have `Fintype`-free tableau `Decidable` instances for
  `Derivable`; CPL has none, purely by omission.
- **Task 317 scope note**: `Tableau/Minimal/Completeness.lean` is a near-line-for-line copy of
  `Tableau/Intuitionistic/Completeness.lean`, one sorry each. Discharging both independently bakes
  the duplication in permanently; make them one bot-forcing-parameterized result **first**.
- **Task 413 sequencing**: it targets proof simplification, but `simp only` cleanup across
  triplicated proof is wasted if the triplication is then removed. Sequence 413 after the
  consolidations above.
- **Test coverage**: the entire metalogic layer has zero executable regression tests.
  `Foundations/Logic/Tableau` (8 files, consumed by three logics) is the highest value-per-line
  gap — a defect in the shared closure condition propagates into every calculus uncaught.
- **Docstring claim inflation**: `HilbertCompleteness.lean:95-97` claims "20+ use-sites"; real
  term-level count is 9, five of which are inside the dead `CanAlgComplete`.
