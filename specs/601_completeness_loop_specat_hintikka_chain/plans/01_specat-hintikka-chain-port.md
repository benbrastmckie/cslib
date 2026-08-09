# Implementation Plan: CompletenessLoop `...At` Hintikka Chain Port

- **Task**: 601 - Port the CompletenessLoop.lean top-loop Hintikka chain to the additive
  `RuleApplicationSpecAt` interface so D (and DB/D4/D5/D45) can reach
  `modalExpandBranchesD_hintikka`
- **Status**: [IMPLEMENTING]
- **Effort**: 3 hours
- **Dependencies**: None (research complete; verified patch artifact on disk)
- **Research Inputs**: `specs/601_completeness_loop_specat_hintikka_chain/reports/01_specat-hintikka-chain-route.md`
- **Artifacts**: plans/01_specat-hintikka-chain-port.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md,
  `.claude/rules/cslib.md`, `.claude/rules/lean4.md`, `.claude/rules/plan-compliance.md`
- **Type**: cslib
- **Lean Intent**: false

## Overview

The research pass selected and machine-verified **Route 3 — in-place bundled narrowing**: retype
nine `CompletenessLoop.lean` declarations from `RuleApplicationSpecCore`/`RuleApplicationSpec` to
their `...At φ0` siblings, reusing the `φ0` parameter each declaration already carries, then fix
nine call sites (three internal, six external) with `.toAt φ0` insertions. Because every proof
body consumed `outputsSubsetUniverse` only at its own already-explicit `φ0`, narrowing *weakens*
the hypothesis and every proof body survives character-for-character. That unblocks the twenty-line
D bridge `modalExpandBranchesD_hintikka` in `DDriver.lean`. Definition of done: full `lake build`
green, `#print axioms modalExpandBranchesD_hintikka` = `[propext, Classical.choice, Quot.sound]`,
zero sorry, zero new axioms, all five CSLib CI lint gates clean, and every docstring that still
describes the pre-narrowing interface rewritten.

### Research Integration

The report's findings are load-bearing and change the shape of this plan versus the original task
description:

- **Neither route named in the task description was selected.** The ~755-line estimate was
  computed from declaration *body* sizes under an assumption of full duplication; the correct
  measurement is ~32 changed lines + 20 new lines, a 14x reduction.
- **A ninth declaration** — `modalExpandBranchesGen_hintikka` (`CompletenessLoop.lean:1874`) —
  is included beyond the original seven. Narrowing it is what makes the D bridge a genuine
  one-liner rather than a bespoke engine entry point.
- **Zero new definitions, structures, typeclasses, or notation.** `RuleApplicationSpecCoreAt`,
  `RuleApplicationSpecAt`, `RuleApplicationSpecCore.toAt`, and `RuleApplicationSpec.toAt` all
  already exist in `GenericDriver.lean` (lines 375, 443, 496, 514). The CSLib reuse-first check
  was performed across `Cslib/Foundations/Logic/` and `Cslib/Logics/`; Mathlib has no analogue.
- **A verified patch artifact exists** at
  `specs/601_completeness_loop_specat_hintikka_chain/artifacts/verified-route3.patch`. It was
  re-checked against the current working tree during planning: `git apply --check` exits 0 and
  `git apply --stat` reports the expected 6 files / 54 insertions / 30 deletions. This makes the
  patch the primary application path, with the report's §4.1-4.3 change tables as the manual
  fallback.
- **Four of the five `_core` twins never mention `φ0` at all** and need only an added implicit
  `{φ0 : Proposition Atom}`; their call sites do not change, since the argument is positional and
  `φ0` is inferred. That alone eliminated 269 of the 755 estimated lines.

The report's suggested Phase A/B split (narrow `CompletenessLoop` first, then fan out) is **not**
adopted. Phase A's checkpoint would leave `FrameCompleteness.lean` red project-wide while only
one module builds, which is a partial-work commit rather than a green one. This plan instead
declares the whole narrowing as a single pre-declared `atomic-batch` phase, matching how the
change was actually verified (one edit, one full build).

### Prior Plan Reference

No prior plan exists for this task. The governing predecessor is
`specs/598_serial_rule_spec_decision_tableau/plans/01_serial-d-driver-route-e2.md` phase 9
(BLOCKER + Reasoned Exclusions), whose per-declaration line-count table this task's research
supersedes with a measured, machine-checked alternative. Calibration lesson carried forward: that
BLOCKER's estimate was 24x the measured cost because it assumed a coercion direction
(`...CoreAt φ0` to `...Core`) that is genuinely impossible but was never actually needed. Effort
estimates below are anchored to the *measured* diff, not to declaration body sizes.

### Roadmap Alignment

No `roadmap_path` was supplied in the delegation context; no roadmap consultation was performed
and no roadmap phases are included.

## Goals & Non-Goals

**Goals**:
- Narrow nine `CompletenessLoop.lean` declarations to the `RuleApplicationSpecCoreAt φ0` /
  `RuleApplicationSpecAt φ0` interface, keeping every proof body unchanged.
- Repair all nine downstream call sites (three internal to `CompletenessLoop.lean`, six external
  across `TDriver`/`BDriver`/`TBDriver`/`FrameCompleteness`) using the existing `.toAt` bridges.
- Land `modalExpandBranchesD_hintikka` in `DDriver.lean` with a full CSLib-style docstring,
  unblocking D/DB/D4/D5/D45.
- Reconcile every docstring that still describes the pre-narrowing interface, including the
  section header at `CompletenessLoop.lean:961-968` that defers this very generalization pass.
- Pass the full CSLib CI verification order with zero sorry and zero new axioms.

**Non-Goals**:
- `modalTableauD_complete`. It hits a distinct downstream gap (a `modalLoopInvGen_initial_at`
  sibling in `DDriver.lean`, ~60-80 lines) because `modalLoopInvGen_initial` proves the initial
  invariant where branch formula and seed are the same `φ0`, while D needs branch formula `φ` at
  seed `modalDualAugment φ`. **Flag only — do not absorb.**
- The Decidable-instance arm (`FrameSoundness.lean` / `FrameCompleteness.lean`).
- Any new definition, structure, typeclass, notation, or `Cslib.lean` barrel change. No new file
  is added, so `lake exe mk_all --module` is not required.
- Introducing `...At` twins or unbundling any hypothesis into raw Pi-typed arguments (Routes 1
  and 2, both rejected with evidence in report §5).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Concurrent sessions edit the six target files, invalidating the patch | H | M | Phase 1 re-runs `git apply --check` as its first task. On non-zero exit, fall back to the manual change tables in report §4.1-4.3 rather than forcing the patch. Several implementation agents are active in this session on adjacent modal-tableau work. |
| Manual transcription of the narrowing introduces a signature/argument-order error | M | M | The patch is the primary path precisely to avoid transcription. If the fallback is used, apply the report's §4.1 table declaration-by-declaration and build the module before touching external call sites. |
| Argument-order regression at a call site typechecks but at the wrong `φ0` | H | L | The narrowed types are `φ0`-indexed, so a wrong `φ0` cannot unify. Full `lake build` is the gate; do not accept a module-scoped build as sufficient for Phase 1. |
| `lint-style` 100-char violations from the lengthened `.toAt φ₀` lines and the D bridge | L | M | The verified patch already wraps these lines. Preserve the patch's wrapping verbatim; do not reflow. Phase 4 runs `lake exe lint-style` and may use `--fix`. |
| `lake lint` (environment linters, never exercised during research) surfaces a new warning | M | M | Phase 4 is scoped to absorb lint fixes. If a linter demands a proof-content change rather than a cosmetic one, stop and record it rather than weakening a statement. |
| Docstring reconciliation is skipped as "cosmetic" | M | M | Phase 3 is a mandatory dependent phase with an enumerated site list. `CompletenessLoop.lean:961-968` actively asserts this pass has *not* happened; leaving it is a factual contradiction in the source, not a style nit. |
| Mathlib olean cache missing, causing a 30-45 minute rebuild | L | L | Run `lake exe cache get` before the first build if the cache is cold (step 0 of the CSLib CI order). |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel. This plan is fully sequential: each phase's
gate is a precondition for the next.

---

### Phase 1: Narrow the Nine Declarations and Repair All Call Sites [COMPLETED]

- **Goal**: Retype the nine `CompletenessLoop.lean` declarations to the `...At φ0` interface and
  repair every call site, arriving at a green full `lake build` with no behavior change.

- **Tasks**:
  - [x] Run `git apply --check specs/601_completeness_loop_specat_hintikka_chain/artifacts/verified-route3.patch`.
        If exit 0, apply it with `git apply`. If non-zero, abandon the patch path and use the
        manual fallback below. *(Re-checked at implementation time: exit 0, `git apply --stat`
        matched the plan's expected 6-file/54+/30- shape exactly. Patch path used; manual fallback
        not needed.)*
  - [x] **Manual fallback only**: apply report §4.1 declaration-by-declaration — *(deviation:
        skipped — patch path succeeded, manual fallback not needed)*.
  - [x] **Manual fallback only**: fix the three internal call sites per report §4.2 — *(deviation:
        skipped — patch path succeeded)*.
  - [x] **Manual fallback only**: fix the six external call sites per report §4.3 — *(deviation:
        skipped — patch path succeeded)*.
  - [x] Confirm no proof body was otherwise altered: `git diff --stat` must report changes only in
        `CompletenessLoop.lean`, `TDriver.lean`, `BDriver.lean`, `TBDriver.lean`,
        `FrameCompleteness.lean` (`DDriver.lean` belongs to Phase 2). *(Applied the patch with
        `git apply --include=...` restricted to these 5 files so DDriver.lean's hunk stayed
        unapplied until Phase 2 — confirmed via `git status --short`.)*
  - [x] Run full `lake build` and confirm green. *(3325/3325 jobs, matches research baseline.)*
  - [x] Confirm zero new `sorry`: any `sorry` grep hit must resolve to pre-existing docstring
        prose, not to a tactic block. *(All 4 hits across the 5 files are prose in
        FrameCompleteness.lean documenting a pre-existing, unrelated standing sorry in
        FrameSoundness.lean.)*

- **Timing**: 45 minutes

- **Depends on**: none

- **Verification Tier**: full

- **Commit Mode**: atomic-batch

- **Scope Hypothesis**: This phase asserts 9 narrowed declarations, 3 internal call sites, and 6
  external call sites across 5 files. Confirm at implementation time by (a) `git apply --stat` on
  the patch reporting exactly `CompletenessLoop.lean` 52 +/-, `FrameCompleteness.lean` 6 +/-,
  `TDriver.lean` 2 +/-, `BDriver.lean` 2 +/-, `TBDriver.lean` 2 +/- (DDriver's 20 + belongs to
  Phase 2), and (b) after applying, `grep -c 'RuleApplicationSpecCoreAt\|RuleApplicationSpecAt'
  Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` returning at least 9. If either count differs,
  the tree has drifted from the verified baseline — reconcile against report §4.1-4.3 before
  building, and record the divergence.

- **Files to modify**:
  - `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` — nine declaration signatures narrowed;
    three internal call sites repaired; `outputsSubsetUniverse` applications lose their explicit
    `φ0` argument at two sites.
  - `Cslib/Logics/Modal/Tableau/TDriver.lean` — one token at the
    `modalExpandBranchesT_hintikka` body.
  - `Cslib/Logics/Modal/Tableau/BDriver.lean` — one token at the
    `modalExpandBranchesB_hintikka` body.
  - `Cslib/Logics/Modal/Tableau/TBDriver.lean` — one token at the
    `modalExpandBranchesTB_hintikka` body.
  - `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — three `.toAt φ₀` insertions in
    `modalTableauS5_complete`, `modalTableauFive_complete`, `modalTableauKb5''_complete`.

- **Verification**:
  - Full `lake build` green (research baseline: 3325 jobs).
  - `#print axioms modalTableau_complete` = `[propext, Classical.choice, Quot.sound]` — the K
    regression check confirming the narrowing broke nothing upstream.
  - `#print axioms modalExpandBranchesHintikka` and `#print axioms
    modalExpandBranchesGen_hintikka` both = the three standard axioms.
  - Zero new `sorry`, zero new axioms.

- **Rationale for atomic-batch**: the nine signature changes and nine call-site repairs are a
  single interface migration. Any intermediate per-file state is red by construction — narrowing
  `modalExpandBranchesHintikka` breaks `FrameCompleteness.lean` until its three call sites are
  fixed. This batch is declared here, in advance, exactly as
  `rules/git-workflow.md`'s anti-abuse guard requires; it must not be widened at implementation
  time to absorb Phase 2 or Phase 3.

---

### Phase 2: Land `modalExpandBranchesD_hintikka` [COMPLETED]

- **Goal**: Add the D-system instantiation of the generic top-loop Hintikka lemma to
  `DDriver.lean`, unblocking D/DB/D4/D5/D45.

- **Tasks**:
  - [x] Append the `/-! ## D Instantiation of the Generic Top-Loop Hintikka Lemma -/` section and
        `theorem modalExpandBranchesD_hintikka` immediately before
        `end Cslib.Logic.Modal.Tableau` in `DDriver.lean`, per report §4.4.
  - [x] Write a full CSLib-style docstring (the report's version is abbreviated). It must name:
        the lemma as the D-system instantiation of `modalExpandBranchesGen_hintikka`; the seed
        `φ0 := modalDualAugment φ` and why D's dual-closed seed differs from T/B/TB's plain `φ0`;
        and `modalApplyOneD_specAt φ` (`DDriver.lean:1243`) as the twelve-field witness supplied
        in place of a universally-quantified spec. *(Replaced the patch's abbreviated one-line
        docstring with a full multi-paragraph docstring naming all three required elements.)*
  - [x] Confirm the proof term stays a one-liner:
        `modalExpandBranchesGen_hintikka modalApplyOneD (modalDualAugment φ)
        (modalApplyOneD_specAt φ) fuel`. If it does not elaborate as written, stop and report —
        do not introduce a bespoke D-specific derivation. *(Elaborated as written; `lake build
        Cslib.Logics.Modal.Tableau.DDriver` green, 882 jobs.)*
  - [x] Confirm no `Cslib.lean` barrel change is needed (no new file added). *(Confirmed —
        DDriver.lean already existed and is already registered.)*

- **Timing**: 30 minutes

- **Depends on**: 1

- **Verification Tier**: local

- **Files to modify**:
  - `Cslib/Logics/Modal/Tableau/DDriver.lean` — approximately 20 new lines appended before the
    namespace end; no existing declaration touched.

- **Verification**:
  - `lake build Cslib.Logics.Modal.Tableau.DDriver` green (in-phase, `local` tier).
  - Full `lake build` green before the phase closes.
  - `#print axioms modalExpandBranchesD_hintikka` = `[propext, Classical.choice, Quot.sound]`.
  - `#print axioms modalExpandBranchesGen_hintikka` unchanged at the three standard axioms.
  - Zero `sorry` in the new declaration.

- **Blind spot note**: `local` covers the in-phase granularity only — the addition is purely
  additive within one module and changes no externally visible signature, so a single-module build
  is the right in-phase check. The full gate set still runs before this phase closes, unchanged.

---

### Phase 3: Docstring Reconciliation [NOT STARTED]

- **Goal**: Bring every docstring that describes the pre-narrowing interface into agreement with
  the landed signatures, including the section header that explicitly defers this pass.

- **Tasks**:
  - [ ] `CompletenessLoop.lean` `## Step Preservation for ModalLoopInvHintikka` section header
        (around line 961-968, shifted by Phase 1): rewrite. It currently states that weakening the
        five declarations in place "is left for a future generalization pass" and that the `_core`
        twins leave "every existing declaration above untouched." Both clauses are now false.
        Record that the generalization pass happened and that the twins are typed at
        `RuleApplicationSpecCoreAt φ0`.
  - [ ] `modalStepHintikka_preserves_inv` docstring: "Only needs `RuleApplicationSpecCore`" ->
        `RuleApplicationSpecCoreAt φ0`.
  - [ ] `modalExpandBranchesHintikka` docstring: "Takes only `RuleApplicationSpecCore`" ->
        `RuleApplicationSpecCoreAt φ0`.
  - [ ] `ModalLoopAuxK_stepPreserved` docstring: "generic over any `apply` with a full
        `RuleApplicationSpec`" -> `RuleApplicationSpecAt φ0`; the `spec.toCore`-parametrized
        phrasing also needs updating.
  - [ ] `modalExpandBranchesGen_hintikka` docstring: the "`spec.toCore` weakens
        `RuleApplicationSpec` to the `RuleApplicationSpecCore` the lift asks for" sentence
        describes the old bridging and must describe the `...At` chain instead.
  - [ ] `CompletenessLoop.lean` module docstring (around line 39): the
        `modalExpandBranchesGen_hintikka` bullet says "over an abstract `(apply, spec)`" — update
        to reflect the `φ0`-indexed spec.
  - [ ] `GenericDriver.lean` around line 365-369: "This narrowing is purely additive:
        `RuleApplicationSpec`/`RuleApplicationSpecCore` themselves, and all seven of
        `RuleApplicationSpec`'s existing discharge sites, are untouched." Keep the true part (the
        structures and all seven witnesses genuinely are unchanged) and add that
        `CompletenessLoop.lean`'s consumers are now typed at the `...At` interface.
  - [ ] `GenericDriver.lean` module docstring (around line 141): the
        `modalExpandBranchesGen_hintikka` / "turns any `RuleApplicationSpec apply` witness ... into
        a Hintikka-set-producing top-loop lemma for free" passage now needs the `.toAt φ0` step.
  - [ ] `TDriver.lean` (around 779-786): "direct application of `modalExpandBranchesGen_hintikka`
        at `(modalApplyOneT, modalApplyOneT_spec)`" -> `modalApplyOneT_spec.toAt φ0`.
  - [ ] `BDriver.lean` (around 809-811): same treatment for `modalApplyOneB_spec`.
  - [ ] `TBDriver.lean` (around 876-879): same treatment for `modalApplyOneTB_spec`.
  - [ ] Read the resulting diff end to end and confirm every changed hunk lies inside a `/-- -/`
        or `/-! -/` comment block — no hunk may cross out of a comment boundary.

- **Timing**: 45 minutes

- **Depends on**: 2

- **Verification Tier**: prose

- **Scope Hypothesis**: This phase asserts eleven docstring sites across five files. Confirm at
  implementation time by grepping the four modal-tableau files for bare
  `RuleApplicationSpecCore`/`RuleApplicationSpec` mentions in comment regions after the edits and
  checking that each surviving mention is genuinely about the unchanged *structure* or an
  unchanged *discharge site*, not about a narrowed declaration's own hypothesis. If additional
  drifted sites are found beyond the eleven, fix them and record the overrun; if a listed site
  turns out already correct, record it as a reasoned exclusion with the grep output as evidence.

- **Files to modify**:
  - `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` — six docstring/section-header sites.
  - `Cslib/Logics/Modal/Tableau/GenericDriver.lean` — two sites.
  - `Cslib/Logics/Modal/Tableau/TDriver.lean` — one site.
  - `Cslib/Logics/Modal/Tableau/BDriver.lean` — one site.
  - `Cslib/Logics/Modal/Tableau/TBDriver.lean` — one site.

- **Verification**:
  - Diff read-through confirming every hunk is inside a comment region (`prose` tier).
  - `lake build` still green before the phase closes — Lean doc-comments are attached syntax, so
    a malformed `/-- -/` is a compile error, not a cosmetic slip.
  - No signature, term, or tactic text changed by this phase.

- **Blind spot note**: `prose` does not cover a hunk that crosses out of a comment boundary or a
  doc-comment that is load-bearing. Both are handled explicitly by the last task and by the
  build check above.

---

### Phase 4: CI Lint Gates and Residual Recording [NOT STARTED]

- **Goal**: Run the full CSLib CI verification order clean, and record the out-of-scope residuals
  for the successor task without absorbing them.

- **Tasks**:
  - [ ] `lake exe cache get` if the Mathlib olean cache is cold (step 0; skip if warm).
  - [ ] `lake build` — full project, syntax linters run during build.
  - [ ] `lake exe checkInitImports` — every file imports `Cslib.Init`.
  - [ ] `lake lint` — environment linters. Not exercised during research; expect this to be the
        gate most likely to surface something new.
  - [ ] `lake exe lint-style` — text linters. Watch the 100-char limit on the new `DDriver.lean`
        theorem and the `FrameCompleteness.lean` `.toAt φ₀` insertions; the verified patch already
        wraps them, so preserve that wrapping rather than reflowing.
  - [ ] `lake test` — run `CslibTests/`.
  - [ ] `lake shake --add-public --keep-implied --keep-prefix` — import minimization.
  - [ ] Skip `lake exe mk_all --module`: no new file was added, so the `Cslib.lean` barrel is
        unchanged.
  - [ ] Final axiom audit: `#print axioms modalExpandBranchesD_hintikka`,
        `modalExpandBranchesGen_hintikka`, `modalExpandBranchesHintikka`, and
        `modalTableau_complete` — all four must be exactly
        `[propext, Classical.choice, Quot.sound]`.
  - [ ] Final `sorry` audit across the six touched files: every hit must be docstring prose.
  - [ ] Record in the implementation summary, as **out of scope, flagged not absorbed**: (a)
        `modalTableauD_complete` needs a `modalLoopInvGen_initial_at` sibling in `DDriver.lean`
        (~60-80 lines) because `modalLoopInvGen_initial` proves the initial invariant where branch
        formula and seed coincide, while D needs branch formula `φ` at seed `modalDualAugment φ`;
        the report notes `modalSubfmls_self_mem` transported by
        `mem_modalSubfmls_foldrAnd_of_base` (`DDriver.lean:106`) and a `phiBound` re-derivation as
        the likely route, with the fuel bridge `modalExpMeasure_entry_le_fuel_at`
        (`DDriver.lean:359`) already landed; and (b) the Decidable-instance arm
        (`FrameSoundness.lean` / `FrameCompleteness.lean`).
  - [ ] Do not create the successor task from within this phase; record the residuals in the
        summary and let the orchestrator decide.

- **Timing**: 60 minutes (dominated by build and lint wall time)

- **Depends on**: 3

- **Verification Tier**: full

- **Files to modify**:
  - Any of the six touched files, only if a linter demands a cosmetic fix (line wrapping, import
    minimization). If a linter demands a change to a *statement* or a proof term, stop and record
    it rather than weakening the statement to satisfy the linter.

- **Verification**:
  - All seven CI steps exit clean.
  - Four `#print axioms` checks return exactly the three standard axioms.
  - Zero sorry, zero new axioms.

---

## Testing & Validation

- [ ] Full `lake build` green (research baseline: 3325 jobs).
- [ ] `lake exe checkInitImports` clean.
- [ ] `lake lint` clean.
- [ ] `lake exe lint-style` clean.
- [ ] `lake test` clean.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` clean.
- [ ] `#print axioms modalExpandBranchesD_hintikka` = `[propext, Classical.choice, Quot.sound]`.
- [ ] `#print axioms modalTableau_complete` unchanged (K regression, confirms the narrowing is a
      strict weakening and broke nothing upstream).
- [ ] `#print axioms modalExpandBranchesGen_hintikka` and `modalExpandBranchesHintikka` = the
      three standard axioms.
- [ ] Zero new `sorry` across all six touched files.
- [ ] Zero new axioms.
- [ ] No new definition, structure, typeclass, or notation introduced.
- [ ] `CompletenessLoop.lean:961-968` no longer claims the generalization pass is pending.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` — nine narrowed declarations, three repaired
  internal call sites, six reconciled docstring sites.
- `Cslib/Logics/Modal/Tableau/DDriver.lean` — new `modalExpandBranchesD_hintikka` (~20 lines).
- `Cslib/Logics/Modal/Tableau/TDriver.lean`, `BDriver.lean`, `TBDriver.lean` — one call-site token
  and one docstring site each.
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — three `.toAt φ₀` call-site insertions.
- `Cslib/Logics/Modal/Tableau/GenericDriver.lean` — two docstring sites (Phase 3 only; no
  signature change).
- `specs/601_completeness_loop_specat_hintikka_chain/summaries/01_specat-hintikka-chain-port-summary.md`
  — implementation summary including the two flagged out-of-scope residuals.

## Rollback/Contingency

- **Phase 1 fails to build**: the change is a pure interface migration with no proof-content
  change, so a build failure means a signature or argument-order slip. Diff the working tree
  against `artifacts/verified-route3.patch` to locate the divergence rather than re-deriving the
  proof. Do not run destructive git on the dirty tree; take
  `bash .claude/scripts/git-snapshot.sh 601` first if a rollback is genuinely needed.
- **Patch no longer applies**: fall back to the manual change tables in report §4.1-4.3. The
  patch is a convenience, not the specification; the tables are the specification.
- **Phase 2 one-liner fails to elaborate**: this would contradict the research verification. Stop
  and report rather than writing a bespoke D derivation — a failure here means Phase 1's
  narrowing of `modalExpandBranchesGen_hintikka` (declaration #9) is incomplete or mis-ordered.
- **A linter demands a statement change in Phase 4**: do not weaken the statement. Record the
  conflict and stop; the acceptance criteria (zero sorry, zero new axioms, three standard axioms)
  outrank linter convenience.
- **Full revert**: `git revert` the phase commits in reverse order. Phase 1's atomic-batch commit
  is self-contained (interface migration plus all call sites), so reverting it alone restores a
  buildable tree; Phase 2 must be reverted before Phase 1, since the D bridge depends on
  declaration #9's narrowed signature.
