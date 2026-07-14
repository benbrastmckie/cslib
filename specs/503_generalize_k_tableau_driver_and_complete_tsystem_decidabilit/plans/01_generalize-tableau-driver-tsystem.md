# Implementation Plan: Task #503 — Generalize K Tableau Driver + Complete T-System Decidability

- **Task**: 503 - Generalize the K tableau driver and complete T-system decidability
- **Status**: [NOT STARTED]
- **Effort**: 13 hours
- **Dependencies**: None (builds on the already-committed, green rule-level work in
  `FrameRules.lean`/`FrameSoundness.lean`/`FrameCompleteness.lean`; parent task 300 [PARTIAL])
- **Research Inputs**: specs/300_modal_extensions_t_s4_s5/reports/02_spawn-analysis.md;
  specs/300_modal_extensions_t_s4_s5/handoffs/phase2-blocked-handoff.md
- **Artifacts**: plans/01_generalize-tableau-driver-tsystem.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md;
  CONTRIBUTING.md; NOTATION.md; ORGANISATION.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Parametrize the K signed-tableau decision procedure over an abstract rule-application function
`apply : SignedFormula → branch → Accessibility → RuleResult × Accessibility` (matching
`modalApplyOne`'s signature) plus a small, explicit bundle of structural hypotheses (no new-world
creation outside the unmodified K `diamondPos`/`boxNeg` arms; every added formula is a member of
the finite `modalUniverse φ0` catalog). The generic driver replaces the hard-coded `modalApplyOne`
across `Saturation.lean` (driver defs), `FmpMeasure.lean` (termination/FMP measure), and
`CompletenessLoop.lean` (fuel loop + top completeness/decidability theorems) — 91 call sites
total. K is re-derived as the trivial instantiation (`apply := modalApplyOne`) and **must stay
green with zero regression, zero sorry, zero axiom**. The generic driver is then instantiated with
the already-proved `modalApplyOneT` to build `modalStepBranchT`/`modalExpandBranchesT`/
`modalTableauT`, discharge the T structural hypotheses, close the T truth-lemma box-positive case
(reflexive self-edge; other cases reduced to existing K bridge lemmas via
`modalApplyOneT_eq_of_not_boxPos_diaNeg`), and state `tValid`'s completeness plus
`Decidable (tValid φ)`. Definition of done: every delivered result is genuinely sorry-free /
axiom-free and the full CSLib CI is clean; if the T truth-lemma or the termination re-derivation
cannot close, the affected phase is marked **[BLOCKED]** with a documented open goal state rather
than introducing any debt.

### Research Integration

Adopted directly from `reports/02_spawn-analysis.md` and the Phase-2 blocker handoff:
- **Root cause**: `Saturation.lean` (258 lines), `FmpMeasure.lean` (2,959 lines), and
  `CompletenessLoop.lean` (1,353 lines) call `modalApplyOne` directly at 6 / 84 / 75 sites
  respectively (verified: 165 textual occurrences, ~91 semantically distinct call sites), with no
  abstraction layer. A T-specific driver on `modalApplyOneT` needs its own termination argument.
- **Key insight (generality)**: worlds are minted **only** by the unmodified `diamondPos`/`boxNeg`
  arms of `modalApplyOne` itself, reached identically whether the triggering box/diamond-negative
  formula arrived via a plain K rule or via a T/S5/B self-/universal-/backward-propagation arm. T,
  S5, and B are "persistent-only" extensions: they add formulas only at *existing* worlds, all
  drawn from the same finite `modalUniverse φ0` catalog the K measure already bounds. So the K
  termination measure's *shape* (a finite `(SignedFormula, WorldIndex)` catalog with a
  monotone-decreasing fuel measure) generalizes to any `apply` satisfying "no new-world creation
  outside the K `diamondPos`/`boxNeg` dispatch, and every added formula ∈ `modalUniverse φ0`".
- **S4 is deliberately out of scope** (task 506): it provably breaks this bound (depth-based
  `modalWorldBound` fails under transitive box propagation, needing `#worlds ≤ 2^|Sf|`
  loop-checking). The interface designed here must serve T, S5 (504), and B (505) — **not** S4.
- **Interface-against-a-real-client**: the structural-hypothesis interface can only be correctly
  designed against a genuine client, so the generalization is bundled with T's instantiation
  (rather than designed speculatively in isolation). T is the first non-trivial instance.
- **Reuse `modalApplyOneT_eq_of_not_boxPos_diaNeg`** (already proved) to reduce most truth-lemma
  cases to the existing K bridge lemmas; only the box-positive reflexive-self-edge case is new.

### Prior Plan Reference

Prior plan `specs/300_modal_extensions_t_s4_s5/plans/01_frame-extensions-implementation.md`
(task 300, [PARTIAL]) is reference-only. Learned from it: (1) Phase 1 frame scaffolding
(`frameValid`/`branchSatisfiableIn`/`trivialFC`) and the Phase-2 rule-level T work
(`modalTBoxSelf`, `modalTDiaNegSelf`, `modalApplyOneT`, `modalApplyOneT_eq_of_not_boxPos_diaNeg`,
`extractModelT` via `Relation.ReflGen` with free `Std.Refl`, rule-level T soundness) are committed
and green — **do not re-derive them**. (2) Its 2-hour Phase-2 estimate was an order of magnitude
too small precisely because it treated the driver rebuild as inline work; this plan treats the
driver generalization as the primary deliverable and budgets it accordingly. (3) Its risk table
already validates the "never `sorry`; mark [BLOCKED] with documented goal state" discipline used
here. No phases are copied from it.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context; no ROADMAP.md was consulted or modified.
Task 503 is the structural prerequisite unblocking tasks 504 (S5/Euclidean), 505 (B/symmetric), and
506 (S4/loop-checking) per the spawn analysis; the abstraction interface delivered here is the
shared foundation those three tasks instantiate (504/505) or diverge from (506).

## Goals & Non-Goals

**Goals**:
- A generic tableau driver `modalStepBranchGen`/`modalExpandBranchesGen`/`modalTableauGen`
  parametrized over an abstract `apply` function with `modalApplyOne`'s signature.
- An explicit, documented structural-hypothesis bundle (the "frame-rule interface") capturing
  exactly what a rule extension must prove to reuse the K-style termination measure: (i) new-world
  creation confined to the unmodified K `diamondPos`/`boxNeg` arms, (ii) added formulas ∈
  `modalUniverse φ0`, plus the persistence/measure hooks the FMP measure consumes.
- K re-derived as the trivial instantiation (`apply := modalApplyOne`) with **zero regression,
  zero sorry, zero axiom** — `modalTableau_decides`/`instDecidableKValid` still green.
- `modalStepBranchT`/`modalExpandBranchesT`/`modalTableauT` built by instantiating the generic
  driver with `modalApplyOneT`, with the T structural hypotheses discharged.
- The T truth lemma (box-positive reflexive self-edge case closed; remaining cases reduced to K
  bridge lemmas), `tValid` completeness, and `Decidable (tValid φ)` — all genuinely sorry-free.
- Full CSLib CI clean at every phase end (checkInitImports, lint, lint-style, test, mk_all, shake).
- The interface documented in-file so tasks 504 (S5) and 505 (B) can discharge the same hypotheses.

**Non-Goals**:
- S4 support or loop-checking / `2^|Sf|` termination machinery (task 506; structurally different).
- S5, B, or 5/Euclidean instantiation (tasks 504/505; this task only fixes the interface + T).
- Re-proving or refactoring the rule-level T work already committed in `FrameRules.lean` /
  `FrameSoundness.lean` / `FrameCompleteness.lean`.
- Any `sorry`, `axiom`, or vacuous `def X := True`/`trivial` placeholder to "close" a phase.
- Changing K's observable behavior or its public theorem statements (only the *definitions* are
  generalized; `kValid`, `modalTableau_decides`, `instDecidableKValid` keep their exact types).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Generic termination measure re-derivation (`FmpMeasure.lean`, 2,959 lines) cannot close sorry-free in one run | H | M | Isolated as Phase 3 (its own phase); if the generic measure will not close, mark **[BLOCKED]** with the exact open lemma/goal state and recommend a dedicated `generic-tableau-termination` task. Never `sorry`. Phases 1–2 remain green and preserved. |
| Definitional generalization (`...Gen apply`) breaks one of the 91 K call sites | H | M | Phase 1 re-derives K as `...Gen modalApplyOne` via `@[reducible]`/`abbrev` or definitional unfolding so existing K proofs see defeq; build must stay green before any later phase starts. Keep original K lemma statements untouched. |
| Structural-hypothesis interface is designed too narrowly for T and fails to serve S5/B | M | M | Extract hypotheses as *semantic* properties (world-creation confinement, catalog membership) not T-specific syntactic ones; validate the field set against the S5-universal-rule and B-backward-rule shapes documented in the spawn analysis before finalizing Phase 2. |
| T truth-lemma box-positive (reflexive self-edge) case cannot be closed | H | M | Phase 5 has an explicit **[BLOCKED]** fallback with documented goal state; reuse `modalApplyOneT_eq_of_not_boxPos_diaNeg` to isolate the single genuinely-new case. Never `sorry`. |
| `modalApplyOneT`'s fall-through can still mint a new world when T self-propagation yields a diamond, so "T never mints worlds" is false for the transitive closure | H | H | This is *the* reason the interface hypothesis is "no world creation **outside the K diamondPos/boxNeg arms**" (which permits K-arm minting) rather than "no world creation at all"; the generic measure must bound K-arm minting exactly as it does for K. Discharge in Phase 4 via the agreement lemma. |
| Shared-file churn: `FrameCompleteness.lean`/`FrameSoundness.lean` touched by later tasks 504/505 | M | L | This task owns the generic-driver files and the T-specific files; tasks 504/505 are downstream and sequenced after. No concurrent territory conflict expected within 503. |
| Lint failures (docBlame, defLemma, simpNF, unusedSectionVars) on new generic decls | L | M | Docstring every new decl; Prop-valued results as `lemma`/`theorem`; run full CI at each phase end. |
| Context exhaustion mid-phase on the large FmpMeasure generalization | M | M | Phase 3 writes a handoff at 80% context per the metadata schema; each phase ends at a green, committed milestone so resume is clean. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |
| 7 | 7 | 6 |

The chain is intrinsically sequential: the generic driver definitions (Phase 1) must exist before
the generic measure can be stated over them (Phase 2 defines the interface bundle, Phase 3 proves
termination against it), the completeness loop (Phase 3-integration lives with the measure) before
T instantiation (Phase 4), and the T truth lemma (Phase 5) before decidability (Phase 6). Each
phase must be a single agent run ending at a green, zero-sorry milestone with a task-scoped commit.

---

### Phase 1: Generic driver definitions in Saturation.lean [COMPLETED]

- **Goal:** Parametrize the driver definitions over an abstract `apply` and re-derive K's
  `modalStepBranch`/`modalExpandBranches`/`modalTableau` as the trivial instantiation, keeping the
  entire K build green with no changes to K's downstream proofs.
- **Tasks:**
  - [x] In `Saturation.lean`, introduce `modalStepBranchGen (apply : SignedFormula … → branch →
    Accessibility → RuleResult … × Accessibility) (b expanded acc)` as a verbatim copy of
    `modalStepBranch` with the sole change `modalApplyOne sf b acc` → `apply sf b acc` (line 114).
  - [x] Introduce `modalExpandBranchesGen apply branches expandedSets accs fuel` and
    `modalTableauGen apply φ` mirroring lines 140–197, threading `apply` through `processNext` and
    the recursive call.
  - [x] Re-derive K: define `modalStepBranch := modalStepBranchGen modalApplyOne` (and likewise for
    `modalExpandBranches`/`modalTableau`) as `@[reducible]`/`abbrev` or with `@[simp]` unfolding
    lemmas `modalStepBranch_eq`/`modalExpandBranches_eq`/`modalTableau_eq`, so all existing K
    references in `FmpMeasure.lean`/`CompletenessLoop.lean` remain defeq / rewritable.
    *(deviation: altered -- the `abbrev`/wrapper-defeq approach was tried first and broke 14+
    downstream `simp only [modalStepBranch]`/`unfold modalStepBranch` call sites and all
    `modalExpandBranches.processNext`-referencing proofs in `Soundness.lean`/`CompletenessLoop.lean`,
    because wrapping changes the auto-generated equation-lemma/internal-helper shape. Fix: kept
    `modalStepBranch`/`modalExpandBranches`/`modalTableau` as byte-identical original recursive
    definitions (zero touch), added `*Gen` as fully separate parallel definitions, and proved the
    three `_eq` bridge lemmas as genuine theorems (not `@[simp]`, to avoid altering existing bare
    `simp` call behavior) -- `modalStepBranch_eq` by `rfl`, `modalExpandBranches_eq` by induction on
    `fuel` with an inner induction on the worklist mirroring `processNext`'s own recursion, and
    `modalTableau_eq` via `modalExpandBranches_eq`. This is strictly safer than the plan's suggested
    mechanism for the zero-regression requirement.)*
  - [x] Confirm the fuel-structural termination of `modalExpandBranchesGen` is accepted by Lean's
    equation compiler for an abstract `apply` (fuel decreases structurally; no measure needed here).
  - [x] `import Cslib.Init`; run `lake build` for the Tableau module tree; confirm zero new
    sorry/axiom and no K regression.
- **Timing:** 2 hours
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/Saturation.lean` — add `*Gen` defs; re-derive K instances.
- **Verification:**
  - `lake build` green; K's `modalTableau` unfolds to `modalTableauGen modalApplyOne`.
  - `lean_verify` on `modalTableauGen` and the K re-derivations: zero sorry/axiom.

---

### Phase 2: Structural-hypothesis interface bundle [NOT STARTED]

- **Goal:** Define, in a new file, the explicit structural-hypothesis bundle a rule extension must
  satisfy to reuse the K-style termination measure, and prove `modalApplyOne` satisfies it (the
  trivial witness). This fixes the interface tasks 504/505 will discharge.
- **Tasks:**
  - [ ] Create `Cslib/Logics/Modal/Tableau/GenericDriver.lean` (name per ORGANISATION.md); define a
    `structure RuleApplicationSpec (apply)` (or a bundle of named `Prop` fields) capturing:
    (a) **world-creation confinement** — `apply sf b acc` extends `acc` with a new edge/world only
    when the K `diamondPos`/`boxNeg` dispatch on `sf` would (state via agreement with
    `modalApplyOne` on the world-minting arms); (b) **catalog membership** — every formula in
    `apply`'s output at world `w` is a member of `modalUniverse φ0` for the ambient `φ0`;
    (c) the persistence/measure hooks the FMP measure consumes (mirror
    `modalApplyOne_persistent_props`, `modalWork_drop_persistent` obligations).
  - [ ] Derive the exact field list from what `FmpMeasure.lean`'s `modalStepBranch_potential_step`
    (line 2146) and `modalStepBranch_worldBound` (line 2376) actually use about `modalApplyOne` —
    read those lemmas' proofs and lift each concrete `modalApplyOne` fact into a bundle field.
  - [ ] Prove `modalApplyOne_spec : RuleApplicationSpec modalApplyOne` (trivial witness — each field
    holds by the existing K lemmas / reflexivity).
  - [ ] Cross-check the field set against the S5-universal and B-backward rule shapes (spawn
    analysis §Task 2/§Task 3): confirm each can *in principle* discharge every field (document a
    one-line note per field), so the interface is not over-fit to T. Do not implement S5/B here.
  - [ ] Docstring every field explaining what it guarantees and why the measure needs it; `lake
    build`; full CI.
- **Timing:** 2 hours
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/GenericDriver.lean` (new) — `RuleApplicationSpec`, `modalApplyOne_spec`.
  - `Cslib.lean` — register new file via `lake exe mk_all --module`.
- **Verification:**
  - `lake build` green; `modalApplyOne_spec` type-checks sorry-free; interface docstrings present.
  - `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`, `lake shake` clean.

---

### Phase 3: Generalize the FMP / termination measure over the interface [NOT STARTED]

- **Goal:** Parametrize `FmpMeasure.lean`'s termination measure and its step lemmas over
  `(apply, spec : RuleApplicationSpec apply)` and re-derive K's termination as the trivial
  instantiation. This is the crux; everything delivered is zero-sorry or the phase is [BLOCKED].
- **Tasks:**
  - [ ] Generalize `modalStepBranch_potential_step` (line 2146), `modalStepBranch_worldBound`
    (line 2376), and `modalExpMeasure_step_lt` (line 2873) to take `apply` + `spec` and discharge
    each former `modalApplyOne`-specific step from the corresponding `spec` field.
  - [ ] Keep `modalUniverse`/`modalWork`/`modalExpMeasure`/`modalFuel` (world-agnostic size bounds)
    unchanged; only the *rule-dependent* step lemmas move behind the interface. Confirm the fuel
    bound `modalExpMeasure_entry_le_fuel` (line 208) still applies (catalog is rule-independent).
  - [ ] Re-instantiate K: obtain the original K termination lemmas as
    `<generic> modalApplyOne modalApplyOne_spec`; confirm `FmpMeasure.lean`'s existing K corollaries
    and `CompletenessLoop.lean`'s uses still typecheck (defeq via Phase-1 unfolding lemmas).
  - [ ] `lake build` the Tableau tree; `lean_verify` no sorry/axiom on the generalized measure.
- **Timing:** 3 hours (exceeds the 1–2h guideline by design — the 2,959-line measure is the crux;
  single-agent-run bounded; write an 80%-context handoff if approaching the limit).
- **Depends on:** 2
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` — generalize the rule-dependent step lemmas;
    re-derive K instances.
- **Verification:**
  - `lake build` green; zero sorry/axiom; K termination corollaries unchanged in statement.
  - Full CI clean.
- **[BLOCKED] fallback:** If the generic measure cannot be closed sorry-free in the run, mark this
  phase **[BLOCKED]** with the exact open lemma name and goal state, note which `spec` field is
  insufficient, and recommend a dedicated `generic-tableau-termination` task. Preserve Phases 1–2
  green. Never introduce `sorry`/`axiom`.

---

### Phase 4: Generalize CompletenessLoop + instantiate the T driver [NOT STARTED]

- **Goal:** Thread `apply` + `spec` through `CompletenessLoop.lean`'s fuel loop and its top
  theorems, re-derive K, then instantiate the generic stack with `modalApplyOneT` to obtain
  `modalStepBranchT`/`modalExpandBranchesT`/`modalTableauT` and discharge the T structural
  hypotheses (`modalApplyOneT_spec : RuleApplicationSpec modalApplyOneT`).
- **Tasks:**
  - [ ] Generalize the loop-invariant plumbing in `CompletenessLoop.lean` (75 call sites:
    `ModalLoopInv`, `modalExpandBranches_hintikka`, `modalExpandBranches_openBranch_initial_mem`,
    and the `modalTableau_complete`/`modalTableau_decides` bodies at lines 1290/1334) over
    `apply`/`spec`, re-deriving the K versions as trivial instances (statements unchanged).
  - [ ] In a new `Cslib/Logics/Modal/Tableau/TDriver.lean` (or an agreed file per ORGANISATION.md),
    define `modalStepBranchT := modalStepBranchGen modalApplyOneT`, `modalExpandBranchesT`,
    `modalTableauT` (each `= …Gen modalApplyOneT`).
  - [ ] Prove `modalApplyOneT_spec : RuleApplicationSpec modalApplyOneT`: discharge
    world-creation-confinement and catalog-membership using `modalApplyOneT_eq_of_not_boxPos_diaNeg`
    (T agrees with `modalApplyOne` outside the two T-relevant persistent shapes, so all minting
    happens in the shared K arms) and the T rules' "outputs at existing worlds, drawn from the
    enlarged `modalUniverse`" property; enlarge `modalUniverse` if a T output formula is not yet a
    member (add a `modalUniverse` closure lemma, keeping the finite bound).
  - [ ] Obtain the terminating `modalTableauT` decision procedure (fuel sufficiency) as
    `<generic> modalApplyOneT modalApplyOneT_spec`.
  - [ ] `lake build`; `lean_verify` no sorry/axiom; full CI.
- **Timing:** 2.5 hours
- **Depends on:** 3
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` — generalize loop + top theorems; re-derive K.
  - `Cslib/Logics/Modal/Tableau/TDriver.lean` (new) — T driver instances + `modalApplyOneT_spec`.
  - `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` — a `modalUniverse` enlargement/closure lemma if a
    T output formula needs catalog membership (bounded).
  - `Cslib.lean` — register new file.
- **Verification:**
  - `lake build` green; K top theorems unchanged; `modalApplyOneT_spec` sorry-free;
    `modalTableauT` terminates. Full CI clean.

---

### Phase 5: T truth lemma and `tValid` completeness [NOT STARTED]

- **Goal:** Prove the T Hintikka/truth lemma over the reflexive-closed model and derive `tValid`
  completeness (`modalTableauT φ = .openBranch b a → ¬ tValid φ`), mirroring
  `modalTableau_complete` (line 1290).
- **Tasks:**
  - [ ] Define/adapt `modalHintikkaSetT` (the T-Hintikka predicate: K-saturation plus the reflexive
    box-positive self-conjunct) and prove `modalExpandBranchesT` produces a `modalHintikkaSetT`
    branch (reuse the generalized `modalExpandBranches_hintikka` from Phase 4 for the K conjuncts;
    add the T self-propagation conjunct from the `modalApplyOneT` self-rule).
  - [ ] Prove the T truth lemma against `extractModelT` (already in `FrameCompleteness.lean`, with
    free `Std.Refl` via `Relation.ReflGen`): for the **box-positive** case at the reflexive
    self-edge, use `extractModelT_refl` + the T self-propagation conjunct; reduce **all other**
    cases (diamond-pos, box-neg, diamond-neg, propositional) to the existing K bridge lemmas via
    `modalApplyOneT_eq_of_not_boxPos_diaNeg` (T output = K output outside the two T shapes) and
    `extractModelT_hasEdge_imp_r`.
  - [ ] State and prove `tValid` completeness using the T truth lemma + the terminating
    `modalTableauT` from Phase 4 (analog of `modalTableau_complete`).
  - [ ] `lake build`; `lean_verify` no sorry/axiom; full CI.
- **Timing:** 2 hours
- **Depends on:** 4
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — `modalHintikkaSetT`, T truth lemma,
    `tValid` completeness (reusing committed `extractModelT`/`extractModelT_refl`/
    `extractModelT_hasEdge_imp_r`).
- **Verification:**
  - `lake build` green; zero sorry/axiom; T truth lemma + `tValid` completeness type-check. CI clean.
- **[BLOCKED] fallback:** If the box-positive reflexive-self-edge case cannot be closed sorry-free,
  mark this phase **[BLOCKED]** with the documented open goal state (the exact truth-lemma case and
  hypotheses available), preserve Phases 1–4 green, and recommend continuation. Never `sorry`/`axiom`.

---

### Phase 6: `Decidable (tValid φ)` [NOT STARTED]

- **Goal:** Combine T soundness (rule-level soundness committed in `FrameSoundness.lean`, lifted to
  branch-level via the terminating `modalTableauT`) with the Phase-5 completeness to state
  `tValid_decides` and `instDecidableTValid`, mirroring `modalTableau_decides` /
  `instDecidableKValid` (lines 1334/1346).
- **Tasks:**
  - [ ] Prove `modalTableauT φ = .closed → tValid φ` (T soundness at the driver level): lift the
    committed rule-level T soundness (`modalTBoxSelf_sound`/`modalTDiaNegSelf_sound`,
    `branchSatisfiableIn reflFC`) through the generalized fuel loop (the generic
    `modalExpandBranches` soundness instantiated at `modalApplyOneT` + `branchSatisfiableIn reflFC`).
  - [ ] State `tValid_decides : modalTableauT φ = .closed ↔ tValid φ` (two-constructor dichotomy of
    `ModalTableauResult`, as in `modalTableau_decides`).
  - [ ] Define `instDecidableTValid (φ) : Decidable (tValid φ)` by running `modalTableauT φ` and
    consulting `tValid_decides` (no `Fintype Atom` assumption — the tableau computation is the
    decision procedure, exactly as `instDecidableKValid`).
  - [ ] `lake build`; `lean_verify` no sorry/axiom on `tValid_decides` and `instDecidableTValid`;
    full CI.
- **Timing:** 1.5 hours
- **Depends on:** 5
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` — driver-level T soundness lift.
  - `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — `tValid_decides`, `instDecidableTValid`.
- **Verification:**
  - `lake build` green; `Decidable (tValid φ)` type-checks; `lean_verify` zero sorry/axiom. CI clean.

---

### Phase 7: Interface documentation, downstream contract, and final CI [NOT STARTED]

- **Goal:** Document the reusable `RuleApplicationSpec` interface for tasks 504/505, run the full
  CSLib CI end-to-end, and write the completion summary.
- **Tasks:**
  - [ ] Add a module docstring to `GenericDriver.lean` describing how a new frame rule instantiates
    the generic driver (define `apply`, prove `RuleApplicationSpec apply`, obtain
    `modalTableau<X>` + termination), with T as the worked example and explicit pointers for S5
    (universal rule, `EqvGen`, task 504) and B (backward rule, `SymmGen`, task 505). State
    explicitly that S4 (task 506) is **not** an instance (transitive-box termination differs).
  - [ ] Run the full CSLib CI in order: `lake build`, `lake exe checkInitImports`, `lake lint`,
    `lake exe lint-style`, `lake test`, `lake exe mk_all --module`,
    `lake shake --add-public --keep-implied --keep-prefix`. Fix any lint on new decls.
  - [ ] Final `lean_verify` sweep on all new/changed top decls (`modalTableauGen`,
    `RuleApplicationSpec`, `modalApplyOne_spec`, `modalApplyOneT_spec`, `modalTableauT`,
    `tValid_decides`, `instDecidableTValid`): confirm zero sorry / zero axiom.
  - [ ] Write `specs/503_.../summaries/01_generalize-tableau-driver-tsystem-summary.md`.
- **Timing:** 1 hour
- **Depends on:** 6
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/GenericDriver.lean` — module docstring / downstream contract.
  - `specs/503_generalize_k_tableau_driver_and_complete_tsystem_decidabilit/summaries/01_generalize-tableau-driver-tsystem-summary.md` (new).
- **Verification:**
  - Full CI green; zero sorry/axiom repository-wide for the touched files; interface documented.

---

## Testing & Validation

Run the full CSLib CI pipeline at the end of **every** phase (order per `cslib.md`):
- [ ] `lake build` — green, and **zero `sorry` / zero new `axiom`** in all delivered decls
  (`lean_verify` on each new top decl).
- [ ] `lake exe checkInitImports` — every new file imports `Cslib.Init`.
- [ ] `lake lint` — docstrings on every new decl (docBlame); Prop-valued results as
  `lemma`/`theorem` (defLemma); lowerCamelCase names; `@[simp]` only with verified LHS (simpNF);
  `omit`/`include` unused section vars.
- [ ] `lake exe lint-style` — style clean.
- [ ] `lake test` — CslibTests suite passes.
- [ ] `lake exe mk_all --module` — new files (`GenericDriver.lean`, `TDriver.lean`) registered.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — dependency analysis clean.
- [ ] Zero-regression gate: `modalTableau_decides`/`instDecidableKValid` unchanged in statement and
  still green (K is the trivial instantiation).
- [ ] Acceptance: `Decidable (tValid φ)` type-checks and is sorry-free/axiom-free.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Tableau/Saturation.lean` — generic `modalStepBranchGen`/`modalExpandBranchesGen`/
  `modalTableauGen`; K re-derived as trivial instances.
- `Cslib/Logics/Modal/Tableau/GenericDriver.lean` (new) — `RuleApplicationSpec` interface bundle,
  `modalApplyOne_spec`, downstream-contract docstring.
- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` — termination/FMP step lemmas generalized over the
  interface; K re-derived; bounded `modalUniverse` enlargement if needed for T.
- `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` — fuel loop + top theorems generalized; K
  re-derived.
- `Cslib/Logics/Modal/Tableau/TDriver.lean` (new) — `modalStepBranchT`/`modalExpandBranchesT`/
  `modalTableauT`, `modalApplyOneT_spec`.
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — `modalHintikkaSetT`, T truth lemma,
  `tValid` completeness, `tValid_decides`, `instDecidableTValid`.
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` — driver-level T soundness lift.
- `specs/503_.../summaries/01_generalize-tableau-driver-tsystem-summary.md` (on completion).

## Rollback/Contingency

- Each phase is a self-contained, task-scoped commit at a green milestone; revert an individual
  phase's commit to roll back without disturbing prior phases.
- The generalization is behavior-preserving for K: K's public theorems keep their exact
  statements, so reverting the generic-driver files restores the original hard-coded K tableau
  intact. New files (`GenericDriver.lean`, `TDriver.lean`) are additive.
- Preferred contingency for the two crux items (Phase 3 generic termination, Phase 5 T truth lemma)
  is a documented **[BLOCKED]** handoff with the open goal state and a recommended task split —
  never a `sorry` or `axiom`. Phases 1–2 (driver defs + interface) stand alone and unblock the
  interface design for tasks 504/505 even if 3–6 must be deferred.
