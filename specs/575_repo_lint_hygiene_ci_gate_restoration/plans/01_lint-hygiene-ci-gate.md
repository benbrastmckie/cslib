# Repo Lint & Hygiene Cleanup — CI Gate Restoration

- **Status**: IMPLEMENTING
- **Task**: 575
- **Created**: 2026-07-27

## Objective

Restore `lake build --wfail --iofail` (the exact CI invocation in
`.github/workflows/lean_action_ci.yml`) to green, and clear the accumulated hygiene debt
that the reviews surfaced alongside it.

## Baseline (measured, not estimated)

| Gate | State at task start |
|------|--------------------|
| `lake build` | green, 3259/3259 |
| `lake test` | green, 9253/9253 |
| `lake build --wfail --iofail` | **exit 1**, 27 modules |
| `lake exe mk_all --check` | pass |
| `lake exe checkInitImports` | pass |
| `lake shake` | 94 files flagged (disabled in CI) |

True in-library bare-sorry census: **28** (Bimodal 23, Propositional 4, Modal 1, Temporal 0,
Foundations 0).

### Two independent causes of the repo's recurring sorry-count error

Both found during this task; any future census must account for both.

1. `set_option warn.sorry false` contains the substring `sorry` at a word boundary, so a naive
   `\bsorry\b` scan counts 12 option lines as proof holes. This inflated Bimodal 23 -> 35.
2. Nine tracked scratch files at the repo root (8 `Test_*.lean` + `OF`) carried 15 sorries while
   belonging to no build target — invisible to `lake build`, counted by every grep.

Correct method: strip `/- -/` and `--` comments, exclude lines containing `warn.sorry`, and scan
only files reachable from a build target.

## Constraints

- **No sorry may be discharged, added, moved, or suppressed.** Four files legitimately retain
  sorries and will still be CI-red at task end. That is expected and correct; clearing them is
  mathematical work owned by tasks 317 and 553/557.
- **No proof term, definition, or theorem statement may be altered.** Only the surface syntax of
  tactics may change (`simp [X] at h` -> `simp only [...] at h`).
- **No new `set_option linter.* false`.** Suppressing instead of fixing is the pattern
  workstream 4 exists to reverse.
- Verification protocol (user decision): rebuild after **each file**, commit only when that file
  is green, per `.claude/rules/git-workflow.md` commit-per-green-substep.

### Explicit non-targets — do NOT "clean" these

- `Temporal/Metalogic/PropositionalHelpers.lean` and `Bimodal/Theorems/Perpetuity/Helpers.lean`
  are **not** redundant wrappers. Their aliases carry 187 and 416 call sites respectively
  (`impTrans` alone: 47 and 96). They absorb `@`-positional boilerplate once instead of at every
  call site. The consolidation they document genuinely landed.
- `TemporalConservativity.lean:245`'s "sorry-free" claim is **true**. It scopes to two
  declarations that both verify axiom-clean; line 243 names the sorry'd one as the gap. An
  earlier suspicion that this was a false claim was wrong.

## Workstreams

### W1 — Linter sites (in progress)

240 distinct source sites across 27 files (460 raw warnings; one recurring flexible-simp pattern
accounts for 241 warnings at only 42 sites).

Distribution: FmpMeasure 64, FrameSoundness 49, LoopChecking 34, Completeness 21,
SoundnessStep 17, Intuitionistic/Scheme 10, S5Simplification 9, Modal/Basic 6, then 18 files at
1-4 each.

Linter kinds: flexible 283, unusedSimpArgs 75, unusedDecidableInType 35, unusedSectionVars 32,
style.longLine 12, style.show 4, unusedVariables 3, plus singletons.

Authoritative site list: `specs/575_.../remaining-warnings.txt`.

### W2 — Task-number references in deliverables

Violates `.claude/rules/no-task-references-in-deliverables.md`. An earlier cleanup stripped ~918;
these are a regression.

**Scope corrected during review**: the initial `task N` regex found 121. The real leakage also
includes bare `Phase 6`, `plan v3`, `report 08`. Sampling confirmed these are task-tracker
history, not mathematical algorithm phases. Correct pattern:

```
\b(task|tasks|phase|report) [0-9]+(\.[0-9]+)?\b
```

Widened count: **376**. Worst: Intuitionistic/Scheme 92, LoopChecking 50, Nested/Soundness 28,
ChronicleToCountermodel 22, Intuitionistic/Completeness 15, Intuitionistic/Expansion 13.
`Minimal/Completeness.lean` (8) was missed entirely by the narrow pattern.

Replace each with a durable anchor (sibling filename, section heading, verified fact). Never
delete the surrounding explanation.

### W3 — Import gate (`lake shake`)

Commented out at `lean_action_ci.yml:29-32`. Flags 94 files.

**Cost correction from review**: ~77% of removals are redundant `import Cslib.Init`; only ~24 are
genuine unused module imports. For every flagged file another `Cslib.*` import carries
`Cslib.Init` transitively, so `checkInitImports` would not break. Re-enabling as-written produces
a large no-benefit churn diff — configure shake to always keep `Cslib.Init`, then re-enable.
Genuine removals cluster in Tableau code.

Reconcile counts before acting: my run reported 94 files / 91 removes / 19 adds; the review's
reported 92 / 106 / 36.

### W4 — Suppression audit

629 total: 511 `set_option linter.* false` + 118 `@[nolint]`.

**Structural finding**: 464 of 511 are *file-scoped blanket* suppressions; only 47 are
declaration-scoped. A blanket suppression atop a 2,000-line file silences every future violation
too — coverage accumulates rather than decaying.

| Category | Count | Verdict |
|---|---|---|
| Pure style (emptyLine 103, longLine 89, setOption 68, show 18, openClassical 7, maxHeartbeats 3) | 288 | Not justified; no mathematics to fix |
| Correctness-adjacent (flexible 68, unusedSimpArgs 43, unusedDecidableInType 30, unusedSectionVars 21, dupNamespace 15, unusedVariables 7, unusedTactic 2, privateModule 2) | 188 | Mixed |
| `tacticAnalysis.verifyGrindOnly` | 35 | Justified, correctly scoped — leave alone |

Suppression density tracks incompleteness: `Separation/` and `CounterexampleElimination/` dominate
the worst-offender list and are the same areas carrying the sorries.

### W5 — Dead code (user-approved)

| Target | Lines | Evidence |
|---|---|---|
| 9 root scratch files | — | DONE, commit `2f608bdf` |
| `KripkeBridge.lean` | 296 | All 6 exports: 0 external refs |
| `Bridge.lean` | 133 | Self-documents "no in-tree consumer"; 1 hit is a docstring |
| `CanAlgComplete` + `FragmentGeneric` | 333 | 0 term-level consumers |
| `Theory.Derivation.normalize` + `normalizeAux` | ~25 | 0 consumers, no correctness theorem |
| `NativePropositionalEmbedding` | ~5 | Uninstantiated stub |
| 2 dead `GenericMCSBridge` lemmas | ~15 | 0 consumers |
| `hilbertConjImpConservativeOverImp_direct` | ~4 | Pure alias; `_direct` name is backwards |
| 9 zero-declaration aggregator modules | 238 | 0 decls, 0 importers |
| 7 dead MCS-transfer wrappers | ~50 | 0 external refs (8th has 6, keep) |

**Deferred by user decision**: 620 lines in `Foundations/Logic/Metalogic/`
(`ProofSystemMorphism` 317, `DeductionCharacterization` 159, `SetDeduction` 144). Imported only
by the root barrel, but plausibly the *right* abstraction that never got adopted — `SetDeduction`
in particular duplicates functionality the three subsystems each solved locally. Needs a design
call, not a deletion.

### W6 — Doubled-namespace public API (user-approved)

The `dupNamespace` linter was overridden 78 times (63 `@[nolint]` + 15 `set_option`) and was
correct every time. 57 declarations across 10 files carry a namespace prefix they are already
inside, producing doubled public names. Verified leaking across module boundaries:

- `Cslib.Logic.Bimodal.Bimodal.ThDerivable` — 5 uses
- `Cslib.Logic.Temporal.Temporal.ThDerivable` — 1 use

Files: Bimodal/ProofSystem/Derivable (10), Temporal/ProofSystem/Derivable (9), the three parallel
`ChronicleTypes`/`Types` modules (9 each), Temporal/Metalogic/DenseMCS (4), MCS (2),
DerivationTree (2), Bimodal/Metalogic/Core/DerivationTree (2), MetricSoundness (1).

Strip the prefix; delete all 78 suppressions. Compiler-verified — a wrong rename fails the build.
Sequenced before any upstream PR, since renaming public API post-release is far more expensive.

**Outcome: PARTIAL — 7 of 10 files done (30 declarations), 3 files aborted (27 declarations).**

Done: MetricSoundness (1), Bimodal Core/DerivationTree (2), Temporal Metalogic/DerivationTree
(2), MCS (2), DenseMCS (4), Temporal ProofSystem/Derivable (9), Bimodal ProofSystem/Derivable
(10). Plus 2 vestigial suppressions in the two `ProofSystem/Axioms.lean`. 42 of 78 suppressions
deleted.

Only **6** reference sites needed editing, not the ~484 estimated. The estimate counted every
occurrence of the short form (`Temporal.SetMaximalConsistent`, 289 of them). Those need no edit:
consumers sit inside `namespace Cslib.Logic.Temporal` or `open Cslib.Logic`, so after the
declaration loses its doubled component the same source text resolves to the un-doubled name via
the enclosing-namespace walk. Only fully-qualified spellings actually break — and there were
exactly 6, the cross-module leaks this workstream was written to eliminate.

**Aborted: the three Chronicle modules are misdiagnosed above.** Their `Chronicle.` prefix is not
a repeated namespace component — it is the *structure* name. `namespace ...Metalogic.Chronicle`
contains `structure Chronicle`, so `def Chronicle.c0` correctly declares
`...Metalogic.Chronicle.Chronicle.c0`, the projection-namespace member that 172 dot-notation call
sites (`chi.c0`, `chi.c3`, …) across 12 files depend on. Stripping the prefix was tried and
reverted; it fails with `Invalid field 'c0': the environment does not contain
...Chronicle.Chronicle.c0` for all nine predicates. The real `dupNamespace` violation is the
`namespace Chronicle` / `structure Chronicle` name coincidence, and clearing it means moving the
structure to the parent namespace or renaming the namespace across the whole `Chronicle/`
subtree — a design decision, not a mechanical rename. 36 suppressions (33 `@[nolint]`,
3 `set_option`) remain there and are load-bearing until that call is made.

### W7 — Script and documentation defects

- `scripts/pre-pr-check.sh:5-26` — steps 1-3 wrap their greps in `if` conditions, so `set -e`
  never applies and no step sets an exit code. **The script exits 0 regardless of findings**;
  only step 4's `lake build` can fail it. Its sorry check also uses the naive grep that produced
  the count inflation, and its debug-command scan returns 4 false positives (docstring mentions).
  Fix: accumulate a failure flag and `exit 1`; strip comments and exclude `warn.sorry`; anchor
  the debug grep to line starts; add `lake build --wfail --iofail`.
- `LoopChecking.lean:160-161` — asserts "Repo-wide: 11 TODO:, 8 NOTE:". Both wrong (13 and 9),
  and self-referentially incoherent: claims no `NOTE:` tags in its own file while containing two,
  and the two asserting lines are themselves among the counted tags. Delete them; a repo-wide
  census belongs in a script where it cannot go stale.
- `ORGANISATION.md` — stale by ~100 files. Every claimed path exists (no phantoms); the failure
  is omission. Modal lists `Metalogic/` as 5 files; reality is 94 undocumented files across
  `Systems/` (45), `Constructive/` (24), `InterSystem/` (10), `Intuitionistic/` (9),
  `Minimal/` (6). Temporal's `Tableau/` (8 files) absent entirely. The
  `Foundations/Logic/Tableau/` entries ARE current and correct.
- `NOTATION.md` — no logic section at all, for a tree that is ~450 of 676 files. This has a
  concrete cost: `Foundations` names its proof-system type parameter `S`, which collides with
  Temporal/Bimodal scoped notation `S` for *Since*, forcing `@`-positional application in 5 files.
  The defect is documented five times in `NOTE:` blocks and fixed zero times. Fix: rename
  `S` -> `Sys` in `Foundations/Logic/`, delete the 5 NOTE blocks.

### W8 — Sorry visibility (from the suppression audit)

- `ChronicleToCountermodel.lean:46` is the **only file-scoped `warn.sorry` in the repo** (the
  other 11 use `... in` and bind one declaration). It was appended to a block of style
  suppressions and matched their form — correct for linters, wrong for a soundness signal. Its
  blast radius is all 12 sorries in the file plus any added later. Line 43 of that same block
  suppresses the linter that would flag the block itself. Fix: split into 12 scoped forms.
- All 12 `warn.sorry` suppressions repo-wide are in Bimodal; Propositional's 4 and Modal's 1 are
  unsuppressed and do surface. Measured: `Minimal.Completeness` exits 1 under `--wfail` while
  `Bundle.UntilSinceCoherence` (2 suppressed sorries) exits 0.
- **Contamination is invisible to any `warn.sorry` policy**: `succ_cofinal`
  (`ChronicleToCountermodel.lean:78`) and `limitDomSubtypeIsSuccArchimedean` (`:87`) consume a
  sorry'd lemma, contain no `sorry` token, emit no warning, and carry docstrings giving no
  warning. Both verify `sorryAx`-contaminated. `bimodal_conservative_over_temporal` (`:289`) is
  contaminated the same way with prose-only disclosure. A `#print axioms` gate over the public
  API is the only mechanism that catches this class.

## Definition of done

- `lake build --wfail --iofail` reports no failures other than the 4 genuine-sorry modules.
- `lake shake` clean; its CI step uncommented.
- Zero `task N` / `Phase N` / `report N` strings in `Cslib/**`.
- `lake test` still 9253/9253.
- Suppression audit outcome recorded per site.
- `pre-pr-check.sh` can actually fail.

## Out of scope (routed elsewhere)

Structural duplication needing mathematics, recorded for the owning tasks:

- Bimodal Chronicle tree is a wholesale fork of the Temporal Chronicle tree — 250 of 305
  declarations shared, `ChronicleConstruction.lean` at 63% line identity. **Task 41 looks
  under-scoped** if framed as extracting a few shared lemmas; this is a merge.
- `GenericMCSBridge.lean` exists 4 times (845 lines). Falls between task 393 (Lindenbaum) and
  task 41 (temporal/bimodal sharing) — neither names it. Needs an ownership call.
- Three classical-fragment completeness files: 1,388 lines of one copy-pasted Kalmár skeleton,
  with `litCtx_congr` byte-identical across two.
- `IntDecidability`/`MinDecidability`: 942 lines of 1:1 parallel proof.
- LTL remains an island: 2742 lines, 0 sorries, a real proved semantic bridge, and no consumer.
- **Task 317 scope note**: `Tableau/Minimal/Completeness.lean` is a near-line-for-line copy of
  `Tableau/Intuitionistic/Completeness.lean`, one sorry each. Discharging both independently
  bakes the duplication in permanently; they should become one bot-forcing-parameterized result
  first.
- **Task 413 sequencing**: it targets proof simplification, but running `simp only` cleanup across
  triplicated proof is wasted if the triplication is then removed. Sequence 413 after the
  consolidations above.
