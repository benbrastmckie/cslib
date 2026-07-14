# Implementation Plan: Task #300 — Frame-Specific Modal Tableau Extensions (T/S4/S5/B/5)

- **Task**: 300 - Extend modal K tableau with frame-specific rules for T, S4, S5, B, 5 (full modal cube)
- **Status**: [PARTIAL]
- **Effort**: 18 hours (risk-weighted; phases 5–6 may exceed and are candidates for task-splitting)
- **Dependencies**: 299 (Modal K tableau, COMPLETED, sorry-free)
- **Research Inputs**: specs/300_modal_extensions_t_s4_s5/reports/01_frame-specific-tableau-extensions.md
- **Artifacts**: plans/01_frame-extensions-implementation.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; CONTRIBUTING.md; NOTATION.md; ORGANISATION.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Extend the completed, sorry-free modal **K** tableau (`Cslib/Logics/Modal/Tableau/`) with
frame-specific saturation rules and per-system soundness + completeness proofs for **T**
(reflexive), **S5** (equivalence), **B** (symmetric), **S4** (reflexive-transitive), and **5**
(Euclidean), covering the full modal cube. The definition of done for each system is a
self-contained, green (`lake build` passing), **zero-sorry / zero-axiom** frame-restricted
completeness + decidability result whose extracted countermodel provably satisfies the frame
condition. Phases are ordered strictly by the research risk gradient (low-risk T/S5/B first,
high-risk S4 loop-checking and pure-5 last) so that no early phase is ever forced toward a
`sorry`, and each risky phase carries an explicit **[BLOCKED]** fallback rather than any debt.

### Research Integration

The plan adopts the report's primary findings verbatim:
- **Strategy B (closure-at-extraction)**: extract the countermodel with a *closed*
  accessibility relation `r := Cl(acc.hasEdge)` (Mathlib `Relation.ReflGen` / `ReflTransGen` /
  `SymmGen` / `EqvGen`). The frame-condition instance (`Std.Refl`, `IsTrans`, `Std.Symm`,
  `IsEquiv`) then comes **free** off the Mathlib closure operator; all new work is confined to
  the truth lemma. No new frame predicates are defined — reuse `Cube.lean` frame classes and the
  `Satisfies.t/b/four/five` semantic validity theorems.
- **Difficulty gradient**: T and B add no new worlds (low/moderate). S5 needs no loop-checking
  (universal-cluster simplification). **S4 termination is the crux** — K's depth-based
  `modalWorldBound` provably breaks under transitive box propagation, so genuine loop-checking /
  subset-blocking (`#worlds ≤ 2^|Sf|`) must be built from scratch, rivaling the 2,959-line K FMP
  measure. **Pure-5 (Euclidean) has no Mathlib closure operator** and is highest-risk.
- **Under-budget caveat**: the task as scoped (all five systems including S4 loop-checking and
  pure-5 in one 1,200–1,800 line task) is under-budgeted. This plan therefore realizes the
  report's recommended decomposition and flags phases 5–6 (S4) and 7 (5) as candidates for
  promotion to standalone tasks if they do not converge within one agent run.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided in the delegation context; no ROADMAP.md consulted. Task 300 is a
child of task 296 and depends on the completed task 299, continuing the Modal Logic tableau line.

## Goals & Non-Goals

**Goals**:
- Frame-restricted soundness + completeness + `Decidable` validity for **T**, **S5**, **B**.
- A from-scratch S4 loop-checking / subset-blocking termination argument and S4
  soundness + completeness (or a documented [BLOCKED] handoff if it cannot close in one run).
- **5 / Euclidean** coverage via the KB5/S5 equivalence route (Euclideanness bundled in
  `EqvGen`), with a documented [BLOCKED] handoff for genuine *pure*-K5 completeness.
- Every delivered phase ends green: `lake build` passing, zero `sorry`, zero new `axiom`,
  and CSLib CI clean (checkInitImports, lint, lint-style, test, mk_all, shake).
- Countermodel frame conditions phrased against existing `Cube.lean` classes /
  `Satisfies.t/b/four/five`, extracted via Strategy B closure operators.

**Non-Goals**:
- A custom `EuclGen` inductive Euclidean-closure operator (no Mathlib support) — deferred to a
  dedicated pure-K5 task if genuine pure-5 completeness is later required.
- Introducing any `sorry`, `axiom`, or vacuous `def X := True` to "close" a phase.
- Re-proving or refactoring the existing K soundness/completeness/FMP machinery beyond the
  minimal generalization needed to thread a frame predicate.
- Subset-blocking (smaller models) for S4 — start with the simpler, still-terminating
  *equality*-of-formula-set blocking per research recommendation §8.2.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| S4 termination bound (`#worlds ≤ 2^\|Sf\|`) cannot be closed in one agent run | H | H | Split into structure (Phase 5) vs invariant (Phase 6); Phase 6 has [BLOCKED] fallback + recommend dedicated S4-termination task. Never `sorry`. |
| Pure-5 has no Mathlib closure operator | H | H | Deliver 5 only via KB5/S5 (`EqvGen`) route in Phase 7; [BLOCKED] handoff for pure-K5 with recommendation to split a dedicated Euclidean-closure task. |
| Generalizing `kValid`/`branchSatisfiable` to `frameValid FC` breaks the K arms | M | M | Phase 1 re-instantiates K through `frameValid` with the trivial predicate and must stay green before any system phase starts. |
| Shared-file edit conflicts (FrameRules/FrameSoundness/FrameCompleteness touched by many phases) | M | M | Execute logically-parallel phases sequentially, or use H7 territory contracts; wave table notes this. |
| Truth-lemma box bridge for `ReflTransGen` path induction is intricate | M | M | Reuse `ReflTransGen.head_induction_on`; carry `T(□φ)` via the 4-rule and discharge the reflexive endpoint via the T-rule. |
| Task under-budgeted vs 1,200–1,800 line estimate | M | H | Phases 5–7 explicitly flagged as task-split candidates; per-phase green milestones bound blast radius. |
| Lint failures (docBlame, defLemma, simpNF) on new decls | L | M | Docstring every decl; Prop-valued results as `lemma`/`theorem`; run full CI at each phase end. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 4 | 1 |
| 3 | 5, 7 | 2 (Phase 5); 3 (Phase 7) |
| 4 | 6 | 5 |

Phases within the same wave are *logically* independent and can execute in parallel **only under
H7 territory contracts**, because Phases 2/4/5 all edit `FrameRules.lean`, `FrameSoundness.lean`,
and `FrameCompleteness.lean`. Absent territory contracts, execute them sequentially in the order
2 → 3 → 4 → 5 → 7 → 6. Each phase must be a single agent run ending at a green, zero-sorry
milestone with a task-scoped commit.

---

### Phase 1: Shared frame-validity scaffolding [COMPLETED]

- **Goal:** Introduce the frame-relativized soundness vocabulary shared by all five systems and
  re-instantiate the existing K result through it, so downstream phases only add per-system arms.
- **Tasks:**
  - [x] In `FrameSoundness.lean`, define `frameValid (FC : ∀ {W}, (W → W → Prop) → Prop) (φ)`
    and `branchSatisfiableIn FC b acc` per report §4 (generalizing `Soundness.lean:322`
    `kValid` and `SoundnessStep.lean:63` `branchSatisfiable`; preserve the one-directional
    "`m.r` superset of `acc` edges" contract).
  - [x] Provide the trivial predicate `FC := fun _ => True` instantiation and re-derive
    `modalTableau_sound` (K) through `frameValid`, confirming the K arms port unchanged.
  - [x] Add a `FrameCompleteness.lean` skeleton with a shared closure-at-extraction helper
    signature (parameterized extractor over a closure operator) and docstrings.
  - [x] `import Cslib.Init`; add both new files to the module tree; run full CSLib CI.

**Implementation notes:**
- `FrameCondition` and `frameValid`/`branchSatisfiableIn` quantify `World` at the fixed
  universe `Type` (not `Type*`), matching the pre-existing `kValid`/`branchSatisfiable`
  convention in `Soundness.lean`/`SoundnessStep.lean` (which already fixes `World : Type` for
  `kValid`'s universal quantifier). This is a strict-enough generalization: the K
  re-derivation (`modalTableau_sound_frame`) reuses `modalExpandBranches_closed_unsat`
  verbatim via the bridge lemma `branchSatisfiableIn_trivial_imp`, with no changes to
  `Soundness.lean`/`SoundnessStep.lean`.
- `extractModelWith` in `FrameCompleteness.lean` intentionally does not import
  `FrameSoundness.lean` (unused per `lake shake`; will be added back by whichever downstream
  phase first needs `frameValid`/`trivialFC` in `FrameCompleteness.lean`).
- **Concurrency note**: `Cslib/Logics/Modal/Tableau/Defs.lean` and files under
  `Cslib/Logics/Modal/Metalogic/Constructive/` were being actively edited by a concurrent
  session (tasks 396/501) during this phase (no git worktree isolation between concurrent
  orchestrator sessions in this environment). This task's commits touch only
  `FrameSoundness.lean`, `FrameCompleteness.lean`, `Cslib.lean` (mk_all-regenerated), and this
  plan file — no files owned by the concurrent session were modified.
- **Timing:** 2 hours
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (new) — `frameValid`, `branchSatisfiableIn`.
  - `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (new) — shared extractor skeleton.
  - `Cslib.lean` / module aggregator — register new files (`lake exe mk_all --module`).
- **Verification:**
  - `lake build` green; zero sorry/axiom; K soundness re-derived via `frameValid (fun _ => True)`.
  - `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`, `lake shake` clean.

---

### Phase 2: T system (reflexive) — LOW risk [BLOCKED]

- **Goal:** Deliver self-contained `Decidable (tValid φ)` with reflexive-frame countermodel.
- **Tasks:**
  - [x] In `FrameRules.lean`, add the T rules `T(□φ)@w ⊢ T(φ)@w` and `F(◇φ)@w ⊢ F(φ)@w` as
    `.persistent` arms (outputs at existing worlds; no new worlds) — `modalTBoxSelf`,
    `modalTDiaNegSelf`, `modalApplyOneT` (and its agreement lemma with `modalApplyOne`
    outside the two T-relevant shapes).
  - [x] In `FrameCompleteness.lean`, define `extractModelT` via `Relation.ReflGen`; obtain
    `Std.Refl` free (`extractModelT_refl`, via `Relation.ReflGen`'s built-in `Std.Refl`
    instance — `Relation.reflexive_reflGen` is deprecated in favour of `inferInstance`, used
    instead) plus `extractModelT_hasEdge_imp_r` (raw `acc.hasEdge` edges survive into the
    closure via `Relation.ReflGen.single`).
  - [x] In `FrameSoundness.lean`, add rule-level T soundness (`reflFC`, `tValid`,
    `branchSatisfiableIn_reflFC_boxPos_mem`/`_diaNeg_mem`, `modalTBoxSelf_sound`/
    `modalTDiaNegSelf_sound`), discharged directly by reflexivity (no `Satisfies.t` needed at
    this rule-soundness layer since branch-level `branchSatisfiableIn reflFC` already carries
    the `Std.Refl` witness).
  - [ ] *(deviation: blocked)* Re-prove the box-pos truth-lemma bridge for the reflexive
    self-edge and state `tValid`'s completeness + `Decidable (tValid φ)`.
  - [ ] *(deviation: blocked, same root cause)* `modalHintikkaSet` reflexive conjunct,
    enlarged `modalUniverse`, `modalWork_drop_persistent` measure reuse — all deferred, they
    are only needed to build the T-specific fuel-driven tableau driver below.
- **Timing:** 2 hours (planned) — actual scope discovered to be an order of magnitude larger
  (see blocker below); ~1 hour spent, stopped at last clean milestone rather than force it.
- **Depends on:** 1
- **Files to modify:** `FrameRules.lean` (new/T arms) — done; `FrameCompleteness.lean`
  (extractModelT, T truth bridge, tValid + Decidable) — extractModelT done, truth
  bridge/decidability blocked; `FrameSoundness.lean` (T soundness arm) — rule-level soundness
  done, branch-level fuel-induction soundness (the `modalTableau_sound`-style top theorem)
  not attempted (blocked on the same driver dependency).
- **Verification:** `lake build` green, zero sorry for everything delivered; `Decidable
  (tValid φ)` NOT delivered (see blocker).

**BLOCKER (Phase 2):**
- **What failed**: `Decidable (tValid φ)` requires an actual terminating decision procedure
  that *produces* a branch satisfying the T-Hintikka property, not just a conditional truth
  lemma. Investigation of the existing K infrastructure (`Saturation.lean` 258 lines,
  `Completeness.lean` 935 lines, `FmpMeasure.lean` 2,959 lines, `CompletenessLoop.lean` 1,353
  lines — 8,066 lines total for K alone) shows `modalStepBranch`/`modalExpandBranches`/
  `modalTableau` hard-code `modalApplyOne` (91 call sites across the three termination/driver
  files, not parametrized). A T-specific driver needs an analogous
  `modalStepBranchT`/`modalExpandBranchesT`/`modalTableauT` built on `modalApplyOneT`
  (already in `FrameRules.lean`), **plus** a from-scratch re-derivation of the
  `FmpMeasure.lean`-style termination/fuel-sufficiency argument for it.
- **Why it's stuck**: The T self-propagation rule (`modalTBoxSelf`/`modalTDiaNegSelf`) can
  introduce a formula `T(ψ)@w` that was never previously processed at world `w`. If `ψ` is
  itself diamond-shaped, the *ordinary* K diamond-positive rule (reached via
  `modalApplyOneT`'s fall-through to `modalApplyOne` outside the two T-relevant shapes) can
  mint a **new** witness world in response — so the claim "the T rule never mints new worlds"
  is true only of the one atomic self-propagation step, not of its transitive closure under
  full saturation. Soundly bounding this (proving termination and the `Decidable` instance)
  requires re-deriving K-scale termination machinery for `modalApplyOneT`, not a lightweight
  wrapper around the existing K algorithm's output.
- **What was tried**: (1) A "post-process the K algorithm's finished branch with a bounded
  T-closure" shortcut was considered and rejected — it cannot soundly ignore the potential
  cascading diamond-rule world-minting above. (2) Reuse of
  `modalApplyOneT_eq_of_not_boxPos_diaNeg` (already proved) to reduce most truth-lemma cases
  to the existing K bridge lemmas was confirmed promising for the *conditional* truth lemma
  (assuming a Hintikka-T branch exists), but this does not by itself supply the *existence*
  (termination) argument needed for `Decidable`.
- **What is needed**: A dedicated task-scale effort (comparable to the original K tableau
  build) to construct `modalStepBranchT`/`modalExpandBranchesT`/`modalTableauT` and their
  termination proof, mirroring `Saturation.lean`/`FmpMeasure.lean`/`CompletenessLoop.lean`.
  Recommend splitting this into its own dedicated task (e.g.
  `t-frame-tableau-decidability`) rather than attempting it inline as "Phase 2" of a
  five-system task — the same driver-rebuild cost recurs, likely worse, for every later phase
  (S5, B, S4, 5).
- **Prohibited workarounds**: No `sorry`, no `def tValid_decidable := True`/`trivial`, no
  vacuous placeholder was introduced. Everything committed for Phase 2 is a genuine,
  independently useful, sorry-free result (T rules + their rule-level semantic soundness +
  the free-`Std.Refl` model extractor); only the driver/decidability piece is deferred.

---

### Phase 3: S5 simplification (equivalence) — MODERATE risk [NOT STARTED]

- **Goal:** Deliver S5 soundness + completeness + decidability via universal-cluster
  simplification with **no loop-checking**. Independent of the S4 line.
- **Tasks:**
  - [ ] In `S5Simplification.lean`, implement the Bimodal-style "propagate box to ALL branch
    worlds" universal rule (report §4 S5) plus its saturation conjunct.
  - [ ] Extract the countermodel with the universal relation `r w w' := True` (trivially
    reflexive/symmetric/transitive/Euclidean); optionally note the tighter `Relation.EqvGen`
    route (`Relation.EqvGen.instIsEquiv`) as an alternative.
  - [ ] Prove the truth lemma for the universal relation (box/diamond bridges over "all worlds").
  - [ ] S5 soundness arm; state `s5Valid` (against `Cube.S5`), `..._complete`, `Decidable`.
  - [ ] Confirm world count stays K-bounded (each diamond mints ≤ once per formula) so the K
    fuel machinery suffices — no new termination bound needed.
- **Timing:** 2.5 hours
- **Depends on:** 1
- **Files to modify:** `S5Simplification.lean` (new), `FrameSoundness.lean` (S5 arm),
  `FrameCompleteness.lean` (s5Valid + Decidable) — or keep S5 self-contained in
  `S5Simplification.lean` to avoid shared-file contention.
- **Verification:** `lake build` green, zero sorry; `Decidable (s5Valid φ)` type-checks; CI clean.

---

### Phase 4: B system (symmetric) — MODERATE risk [NOT STARTED]

- **Goal:** Deliver B soundness + completeness + decidability with symmetric-frame countermodel.
- **Tasks:**
  - [ ] In `FrameRules.lean`, add the symmetric box rule: box-positives propagate **backward**
    along recorded edges (`T(□φ)@w` + edge `v→w` ⊢ `T(φ)@v`), dually for `F(◇)`; add the
    backward-propagation saturation conjunct (the delicate part).
  - [ ] `extractModelB` via `Relation.SymmGen`; `Std.Symm` free from `Relation.SymmGen.instSymm`.
  - [ ] B truth-lemma bridge (box case over symmetric closure); confirm backward propagation
    adds formulas only at existing worlds so the K world bound survives (reuse persistent measure).
  - [ ] B soundness arm via `Satisfies.b` (`Basic.lean:323`); state `bValid`, `..._complete`,
    `Decidable`.
- **Timing:** 2.5 hours
- **Depends on:** 1
- **Files to modify:** `FrameRules.lean` (B arms), `FrameCompleteness.lean` (extractModelB,
  B bridge, bValid + Decidable), `FrameSoundness.lean` (B arm).
- **Verification:** `lake build` green, zero sorry; `Decidable (bValid φ)` type-checks; CI clean.

---

### Phase 5: S4 rules + loop-checking machinery (structure) — HIGH risk [NOT STARTED]

- **Goal:** Build the S4 rules and loop-checking data structures and land the S4
  soundness + truth lemma green, with fuel-parameterized recursion but **before** the a-priori
  termination bound (decidability deferred to Phase 6). Everything delivered is zero-sorry.
- **Tasks:**
  - [ ] In `FrameRules.lean`, add the 4-rule: `T(□φ)@w`, edge `w→w'` ⊢ `T(□φ)@w'` **and**
    `T(φ)@w'` (propagate the box itself transitively), dually `F(◇φ)@w ⊢ F(◇φ)@w'`; reuse the
    Phase-2 T-rule for the reflexive component.
  - [ ] In `LoopChecking.lean`, build the blocking machinery (report §5): `formulasAtWorld b w`,
    an **equality**-of-relevant-formula-set test over `modalSubfmls φ0`, and the diamond-rule
    **minting guard** that adds a loop-back edge instead of minting when an equal-set world
    exists. Reuse `modalKnownWorlds`, `Accessibility`/`hasEdge`/`successorsOf`, `outDeg`,
    `boxPositivesOf`.
  - [ ] `extractModelS4` via `Relation.ReflTransGen`; `Std.Refl` + `IsTrans` free.
  - [ ] Re-prove the box-pos truth-lemma bridge by induction on the `ReflTransGen` path
    (`ReflTransGen.head_induction_on`), carrying `T(□φ)` via the 4-rule and discharging the
    reflexive endpoint via the T-rule; confirm loop-back cycles are absorbed by `ReflTransGen`.
  - [ ] S4 soundness arm via `Satisfies.four` (`Basic.lean:348`).
- **Timing:** 3 hours (exceeds the 1–2h guideline by design; single-agent-run bounded per
  research caveat — split into a dedicated task if it does not converge).
- **Depends on:** 1, 2
- **Files to modify:** `FrameRules.lean` (4-rule), `LoopChecking.lean` (new: formulasAtWorld,
  equality test, minting guard), `FrameCompleteness.lean` (extractModelS4, S4 bridge),
  `FrameSoundness.lean` (S4 arm).
- **Verification:** `lake build` green, zero sorry for all delivered decls; S4 soundness +
  truth lemma type-check; CI clean. (Decidability intentionally not yet claimed.)
- **[BLOCKED] fallback:** If the S4 truth lemma or the loop-back-edge extraction cannot be
  closed sorry-free within the run, mark this phase **[BLOCKED]** with the documented open goal
  state and recommend promoting S4 to a standalone task. Do **not** introduce `sorry`/`axiom`.

---

### Phase 6: S4 termination bound + decidability (the crux) — HIGH risk [NOT STARTED]

- **Goal:** Prove the loop-checking termination bound `#worlds ≤ 2^|modalSubfmls φ0|` and its
  loop invariant, then discharge `Decidable (s4Valid φ)`.
- **Tasks:**
  - [ ] Add the new world-count bound `#worlds ≤ 2^|modalSubfmls φ0|` as a field on
    `ModalPotentialInv` (`FmpMeasure.lean:2116`); prove it a loop invariant under the
    equality-blocking minting guard (distinct saturated formula-sets are finite).
  - [ ] Bound world creation via the loop-check so the persistent-rule measure machinery
    (`modalWork_drop_persistent`, `modalApplyOne_persistent_props`) ports.
  - [ ] Establish fuel sufficiency for the S4 recursion and state `s4Valid` (against `Cube.S4`),
    `..._complete`, `Decidable`.
- **Timing:** 4 hours (crux; rivals the 2,959-line K FMP measure — strong candidate for a
  dedicated task).
- **Depends on:** 5
- **Files to modify:** `LoopChecking.lean` (termination bound + invariant),
  `FmpMeasure.lean` (extend `ModalPotentialInv`), `FrameCompleteness.lean` (s4Valid + Decidable).
- **Verification:** `lake build` green, zero sorry/axiom; `Decidable (s4Valid φ)` type-checks;
  full CI clean.
- **[BLOCKED] fallback:** If the `2^|Sf|` invariant cannot be closed sorry-free within the run,
  mark this phase **[BLOCKED]** with the documented goal state (which invariant field is open)
  and recommend a dedicated `s4-loop-checking-termination` task. Phase 5's S4
  soundness/truth-lemma results remain green and preserved. Never `sorry`/`axiom`.

---

### Phase 7: 5 / Euclidean coverage via KB5/S5 route — HIGHEST risk [NOT STARTED]

- **Goal:** Provide 5-axiom / Euclidean frame coverage via the KB5/S5 equivalence route
  (Euclideanness bundled inside `EqvGen`/equivalence), and a documented handoff for pure-K5.
- **Tasks:**
  - [ ] Using the Phase-3 S5 machinery, expose the Euclidean frame condition
    (`Relation.RightEuclidean`) for the equivalence-extracted model — every equivalence relation
    is Euclidean (report §2) — and state the `5`/KB5 validity + completeness via this route.
  - [ ] Reuse `Satisfies.five` (`Basic.lean:376`) and CSLib's Euclidean API
    (`Cslib/Foundations/Relation/Euclidean.lean`: `RightEuclidean.symm`, `refl_serial`) for the
    soundness arm.
  - [ ] Document, in-file, that **pure-K5** (Euclidean-without-full-equivalence) has no Mathlib
    closure operator and is out of scope for this task.
- **Timing:** 2 hours
- **Depends on:** 3
- **Files to modify:** `FrameCompleteness.lean` / `S5Simplification.lean` (5/KB5 validity +
  completeness via EqvGen), `FrameSoundness.lean` (5 arm via `Satisfies.five`).
- **Verification:** `lake build` green, zero sorry; KB5/S5-route 5-validity result type-checks;
  CI clean.
- **[BLOCKED] fallback:** If genuine **pure-K5** completeness is required, mark the pure-5 portion
  **[BLOCKED]** with a note that a custom `EuclGen` inductive closure must be built, and recommend
  a dedicated `pure-k5-euclidean-closure` task. Never introduce an `axiom`/`sorry`.

---

## Testing & Validation

Run the full CSLib CI pipeline at the end of **every** phase (order per report §7):
- [ ] `lake build` — green, and **zero `sorry` / zero new `axiom`** in all delivered decls.
- [ ] `lake exe checkInitImports` — every new file imports `Cslib.Init`.
- [ ] `lake lint` — docstrings on every new decl (docBlame); Prop-valued results as
  `lemma`/`theorem` (defLemma); lowerCamelCase names (`extractModelS4`, `frameApplyOne`,
  `loopBlocked`); `@[simp]` only with verified LHS (simpNF); `omit` unused section vars.
- [ ] `lake exe lint-style` — style clean.
- [ ] `lake test` — CslibTests suite passes.
- [ ] `lake exe mk_all --module` — new files registered.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — dependency analysis clean.
- [ ] Per-system acceptance: `Decidable (tValid φ)`, `Decidable (s5Valid φ)`,
  `Decidable (bValid φ)` type-check (Phases 2–4); `Decidable (s4Valid φ)` (Phase 6);
  KB5/S5-route 5-validity (Phase 7).

## Artifacts & Outputs

- `Cslib/Logics/Modal/Tableau/FrameRules.lean` — T/B/4 propagation rules + per-system Hintikka conjuncts.
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — S4 equality-blocking machinery + `2^|Sf|` bound.
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean` — universal-cluster S5 rule + EqvGen extraction.
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` — `frameValid`, `branchSatisfiableIn`, per-system arms.
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — per-system `extractModel*`, truth bridges, `*Valid` + `Decidable`.
- `specs/300_modal_extensions_t_s4_s5/summaries/01_frame-extensions-summary.md` (on completion).

## Rollback/Contingency

- Each phase is a self-contained, task-scoped commit at a green milestone; revert an
  individual phase's commit to roll back without disturbing prior systems.
- The frame line is additive: it introduces new files and generalizes (does not rewrite) the K
  result, so reverting the frame files restores the sorry-free K tableau intact.
- Preferred contingency for the two crux items (Phase 6 S4 termination, Phase 7 pure-5) is a
  documented **[BLOCKED]** handoff with the open goal state and a recommended task split — never
  a `sorry` or `axiom`. T/S5/B (Phases 1–4) stand alone and ship independently of the S4/5 line.
```
