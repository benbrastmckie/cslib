# Implementation Plan: Modal K Tableau FMP Fuel Measure (Task 442)

- **Task**: 442 - Modal K Tableau FMP Fuel Measure (unblocks task 299 Phase 6/7)
- **Status**: [IMPLEMENTING]
- **Effort**: ~18-26 hours across 9 phase dispatches (~1500-2600 lines Lean)
- **Dependencies**: None (parent task 299 is [BLOCKED] pending this work)
- **Research Inputs**: reports/01_fmp-fuel-measure-research.md (Tier 1, adversarially verified)
- **Artifacts**: plans/01_fmp-fuel-measure-plan.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/git-workflow.md
- **Type**: cslib
- **Mode**: --hard (H7 territory, H8 phase sizing, postmortem constraints, wave declarations)

## Execution Log (updated as phases finish)

| Phase | Status | Commit | Notes |
|-------|--------|--------|-------|
| Pre  | repair | `4153f885` | Pre-existing task-384 regression in `SoundnessStep.lean` (`Proposition.beqToEq`) fixed — `Proposition` derives `DecidableEq` not `BEq`; replaced hand-rolled recursion with `LawfulBEq.eq_of_beq`. `Soundness`/`SoundnessStep` now green (required for P6 whole-library green). Not in original plan; discovered during Wave 2. |
| P0   | ✅ COMPLETED | `ef68c642` | FmpMeasure defs + exponential `modalFuel`; entry bridge lemma. Green, axiom-clean. `import Mathlib.Tactic.Ring` added (ring not transitive via Init). |
| P1a  | ✅ COMPLETED | `325a8e8a` | Subformula closure (world-preserving rules). Green, axiom-clean. **Added `import Completeness` into `FmpMeasure.lean`** to reuse `tryAllPropRules_*`/`modal*Of?_eq` → forces architecture adjustment below. |
| P4   | ✅ COMPLETED | `3766e609` | Saturation characterisation (`Completeness.lean`). Green. Finding: Łukasiewicz diamond patterns never reach `acc`-dependent arms (prop dispatch exhaustive over `.imp`); only `boxNeg` needs invariant carve-out. |
| P1b  | ✅ COMPLETED | `5d07fedf` | Fresh-world rule closure (`diamondPos`/`boxNeg`) + top-level `modalApplyOne_outputs_subset` dispatch. Green, axiom-clean (propext/Quot.sound only). Added `public import SoundnessStep` (acyclic) for `accFreshInv`; five small glue lemmas factored out (subformula transitivity, `modalUniverse` membership chars, `successorsOf`/`hasEdge` bridge, shared `boxProps`/`diaNegProps` closure). |
| P2 (CRUX) | ✅ COMPLETED | `2f7a4d22` | World-count bound proved via potential-function invariant (plan's terse target was disproved; strengthened signature used). Obligations a–e all green: `expandedNodup` (`9f9134ad`), `rank'` invariant (`cd1cf73a`), `outDeg≤Sf` (`00ad6986`), potential defs+recurrence (`cb0c3e76`), Δ=0 step lemma `modalStepBranch_potential_step` (`70ca9693`), final `modalStepBranch_worldBound` (`2f7a4d22`). Exports reusable `ModalPotentialInv` (8-field structure) for P5a. Zero sorry, standard axioms only. Two design corrections banked (isMintingShaped=boxNeg-only; potential term 0-at-leaf). |
| P3   | 🔄 IN PROGRESS | — | Strict-decrease engine `modalExpMeasure_step_lt` (port of classical :834). |
| P5a/P5b/P6 | ⏳ pending | — | Relocated to new `CompletenessLoop.lean` (see architecture adjustment). |

### Architecture adjustment (settled during execution — supersedes P5 file placement)
P1a introduced `FmpMeasure.lean → import Completeness.lean` (acyclic: Completeness does **not**
import FmpMeasure). The plan's original P5 placed `modalExpandBranches_hintikka` in
`Completeness.lean` *using* the measure, which would require `Completeness → FmpMeasure` and create
an **import cycle**. Resolution: **P5a, P5b, and P6 targets** (`modalExpandBranches_hintikka`,
`modalTableau_complete`, `modalTableau_decides`, `instance Decidable (kValid φ)`, and the
combined-invariant preservation lemma) land in a **new module
`Cslib/Logics/Modal/Tableau/CompletenessLoop.lean`** importing `FmpMeasure` + `Completeness` +
`Soundness`, added to the `Cslib.lean` aggregator. The Definition of Done only requires these
theorems to compile sorry-/axiom-free; their file location is not load-bearing. P4 remains in
`Completeness.lean` and does **not** import `FmpMeasure`.

## Overview

Task 299's modal K tableau completeness is blocked at Phase 6: the current polynomial
`modalFuel = (4n+4)(n+2)+2` (`Saturation.lean:89`) is provably insufficient (K's exponential
minimal-model lower bound forces `fuel = 0` at an unsaturated open branch). This plan raises
`modalFuel` to a (triple-)exponential closed form and formalizes the finite-model-property
termination measure — a counting measure `3^R` over a world-bounded finite signed-formula
universe `U(φ)` — that discharges the `fuel = 0` case, proving five sorry-free / axiom-free
target theorems.

**Measure decision (settled, from research §2):** the exponent is a **counting** measure
`R(b,e) = |U(φ) \ set(b)| + |U(φ) \ set(e)|`, NOT a complexity measure. The persistent modal
rules (`boxPos`, `diamondNeg`, `Saturation.lean:116-117`) leave `expanded` unchanged, so any
`3^complexity` sum over `b\e` is non-decreasing; the counting measure over a fixed finite `U`
restores strict decrease on all four modal rule kinds. The whole task is a faithful port of two
already-green proofs (`classicalExpandBranches_hintikka`, `modalExpandBranches_closed_unsat`)
plus one genuinely hard obligation: the a-priori world-count bound (Phase 2, the CRUX).

**Import-cycle resolution (settled design decision — see Postmortem Constraints):** the report's
`modalFuel := 3^(2·|modalUniverse φ|)` cannot live in `Saturation.lean` because `modalUniverse`
lives in the new `FmpMeasure.lean` which *imports* `Saturation` (cycle). Resolution: redefine
`modalFuel` in `Saturation.lean` using the research's fully-expanded **closed form**, which
depends only on `modalComplexity` (already in `Saturation`'s scope). `FmpMeasure.lean` then proves
a bridge lemma `3^(2·|modalUniverse φ|) ≤ modalFuel φ` connecting the two, giving the entry
measure bound. No import cycle; no datatype/rule change.

### Definition of Done (whole task)

`modalStepBranch_none_saturated`, `modalExpandBranches_hintikka`, `modalTableau_complete`,
`modalTableau_decides`, and `instance : Decidable (kValid φ)` all compile with ZERO sorry and
ZERO new axioms; `#print axioms` on each shows only standard axioms; whole-library `lake build`
green; CI pipeline green (`lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
`lake shake --add-public --keep-implied --keep-prefix`).

### Preserved Assets

The following work is GREEN and must not regress. No phase may edit these declarations; they are
read-only references consumed downstream.

| Component | File:Line | Status | Role in this task |
|-----------|-----------|--------|-------------------|
| `modalTableau_sound` / `modalExpandBranches_closed_unsat` | Soundness.lean:165,226 | [GREEN] | Fuel-agnostic; consumed by P6. P0 must verify still green after `modalFuel` value change. |
| `modalStepBranch_preserves_accFreshInv` | Soundness.lean:111 | [GREEN] | Invariant-survives-branching precedent for P2/P5. Read-only. |
| `modalApplyOne_fresh` | Soundness.lean:87 | [GREEN] | "Only linear rules mint worlds" — consumed by P1b/P2. Read-only. |
| `modalTruthLemma` | Completeness.lean:383 | [GREEN] | Consumed unchanged downstream of Hintikka. Read-only. |
| `modalOpenBranch_countermodel` | Completeness.lean:560 | [GREEN] | `modalTableau_complete` (P6) is its contrapositive wrapper. Read-only. |
| `forall₂_*` worklist helpers | LoopInduction.lean:44,66,87,96,104 | [GREEN] | Public (hoisted task-299); threaded through P5 induction verbatim. Read-only. |
| `modalHintikkaSet` (def + 3 conjuncts) | Saturation.lean:218-234 | [GREEN] | Target of P4/P5. Read-only definition. |

**Preserved-asset guard:** P0 ends by rebuilding `Cslib.Logics.Modal.Tableau.Soundness`. Because
`modalFuel` never appears in soundness (research §6/C6: soundness quantifies over `fuel : Nat` and
never unfolds `modalFuel`), this must be immediate; if Soundness breaks, the `modalFuel` edit is
wrong — stop and fix before P1.

### Source-to-Implementation Mapping (Tier 1 — research §1, §Source-to-Implementation)

| Source claim | BibKey | Lean target (phase) | Template line ported |
|--------------|--------|---------------------|----------------------|
| K has FMP; satisfiable K-formula has model ≤ subformula-tree bound | Fitting1983 Ch.2 | `modalWorldBound`, `modalStepBranch_maxWorld_lt` (P2) | Formalized *syntactically* as world-label bound `Sf^(d+1)` via depth stratification — NOT a semantic model-size theorem (non-circular, §6/C3). |
| Signed-tableau saturation / Hintikka set yields countermodel | Smullyan1968 Ch.V; Fitting1983 | `modalHintikkaSet` (exists), `modalOpenBranch_countermodel` (green) consumed by P5/P6 | Task only proves the loop *reaches* a Hintikka set. |
| α/β rule complexity-decrease drives termination | Smullyan1968 | replaced by counting measure `R` (P0/P3) | Persistent re-firing rules break α/β complexity-decrease; counting over finite `U` restores it. |
| Strict-decrease step engine | (code) | `modalExpMeasure_step_lt` (P3) | `classicalExpMeasure_step_lt` (Classical/Completeness.lean:834). |
| Base-3 damping of ≤2-way branching | (code) | `pow3_add_one_le` / `pow3_two_add_one_le` (P3) | Classical/Completeness.lean:684 / :674. |
| Measure-bound ⇒ Hintikka loop | (code) | `modalExpandBranches_hintikka` (P5) | `classicalExpandBranches_hintikka` (Classical/Completeness.lean:924) + acc-threading `modalExpandBranches_closed_unsat` (Soundness.lean:165). |
| Saturated-leaf characterisation | (code) | `modalStepBranch_none_saturated` (P4) | `classicalStepBranch_none_saturated` (Classical/Completeness.lean:694). |
| Hintikka expanded-set invariant | (code) | `modalStepBranch_hintikka_inv` (P4) | `classicalStepBranch_hintikka_inv` (Classical/Completeness.lean:722). |

**BibKey caveat (research §7):** `references.bib` was not located at repo root; in-source keys
`Fitting1983` / `Smullyan1968` are used consistently. Confirm at PR time; no new external source
is required (transcription of an existing algorithm's termination, not a new theorem).

## Postmortem Constraints

Binding rules for every implementation dispatch. Derived from the task scope constraints, the
task-299 Phase-6 blocker history, and the research adversarial section (§6).

**Do NOT:**
- Do NOT change any datatype, rule output shape, or `modalNextWorld`'s world-reuse behaviour.
  World-subset blocking is task 441 and is OUT OF SCOPE. If you feel the proof "needs" an
  algorithm change, you are on the wrong path — re-read research §2 (the counting measure is
  chosen *precisely* to avoid this).
- Do NOT introduce any `sorry` or new `axiom` in the final result. A `sorry` is permitted only
  as transient in-dispatch scaffolding and MUST be removed before the phase's green checkpoint.
  A phase does not complete while any `sorry` remains in its owned declarations.
- Do NOT make `modalFuel`'s new body depend on `modalUniverse` (import cycle — see below). Use the
  closed form over `modalComplexity` only.
- Do NOT reopen the measure choice: a `3^complexity` exponent is PROVABLY non-decreasing on the
  persistent modal rules (research §2.1). Any attempt to "add a world term to the complexity
  measure" is the exact imprecision corrected in research §5 Correction 1.
- Do NOT attempt the semantic finite-model-property theorem for the world bound. The world bound
  is a *syntactic* combinatorial forest-depth argument on `modalDepth φ` (research §6/C3);
  invoking semantic model size is circular with the termination being proved.
- Do NOT weaken the world bound to escape P2. If P2's depth-stratification invariant stalls after
  one genuine attempt, invoke the in-plan fallback (per-world rank map, P2 contingency) — do NOT
  add a `sorry`, do NOT re-plan, do NOT mark done.

**MUST preserve** (see Preserved Assets table): soundness, `modalTruthLemma`,
`modalOpenBranch_countermodel`, `modalApplyOne_fresh`, `forall₂_*` helpers, `modalHintikkaSet`.
No edits to these; they are consumed read-only.

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):
- **Measure = counting, base-3 damped:** `modalExpMeasure = Σ 3^R`, `R = |U\b| + |U\e|`. Rejected
  alternative (`3^complexity`) fails on persistent rules (§2.1, verified in code).
- **`modalFuel` = closed-form over `modalComplexity`, defined in `Saturation.lean`:**
  `modalFuel φ := 3 ^ (4 * (2*modalComplexity φ + 1) * ((2*modalComplexity φ + 1)^(modalComplexity φ + 1) + 1))`
  (a provably-sufficient over-count; sufficiency, not tightness, is required). The universe
  `modalUniverse`, measure, and all measure lemmas live in `FmpMeasure.lean` which imports
  `Saturation`. The bridge lemma `3^(2·|modalUniverse φ|) ≤ modalFuel φ` (P0) connects them. This
  breaks the import cycle that a `modalFuel := 3^(2·|U|)` definition would create.
- **File layout:** pure universe defs + measure + all measure/closure/world-bound/step lemmas →
  new `FmpMeasure.lean`; the five target theorems + `modalStepBranch_none_saturated` +
  `modalStepBranch_hintikka_inv` → `Completeness.lean`; `modalFuel` value → `Saturation.lean`.
- **P2 gates P3-P5, serial.** P4 is the only parallel opportunity (disjoint file territory).

## Goals & Non-Goals

- **Goals**: Redefine `modalFuel` (exponential); define finite world-bounded universe `U(φ)` and
  the counting measure `3^R`; prove subformula-closure, world-count bound, output-freshness, and
  per-rule strict-decrease; prove `modalStepBranch_none_saturated`,
  `modalExpandBranches_hintikka`, `modalTableau_complete`, `modalTableau_decides`, and
  `Decidable (kValid φ)`; keep whole library + CI green.
- **Non-Goals**: World-subset blocking (task 441); any datatype/rule change; tightening the fuel
  bound; a semantic FMP theorem; touching soundness proofs; `Fintype Atom` (decidability is via
  the `.closed`/`.openBranch` dichotomy, not enumeration).

## Risks & Mitigations

- **Risk (CRUX, P2):** the a-priori world bound `W = Sf^(d+1)` proved as a loop invariant against
  the flat `modalNextWorld = maxWorld+1` naming may be intractable (research §6/C3, MEDIUM
  confidence — the only genuine dead-end candidate). **Mitigation:** isolate P2 in its own phase,
  gate P3-P5 behind it, and provide an in-plan fallback (per-world rank map as proof-only
  invariant data — no algorithm change) invokable WITHOUT re-planning. If P2 stalls after one
  genuine attempt at both primary and fallback, mark P2 [BLOCKED] and escalate; do NOT weaken the
  bound or add a `sorry`.
- **Risk:** measure-decrease is *equivalent to* the world bound — if any emission lands outside
  `U`'s world range, the `R`-drop fails. **Mitigation:** P1 (closure) is conditioned on the
  world-bound hypothesis and P2 supplies it; P3 consumes both. Ordering enforced by the wave map.
- **Risk:** `modalFuel` value change silently breaks a downstream proof that unfolds it.
  **Mitigation:** P0 rebuilds Soundness immediately (research §6/C6 says it cannot break); grep
  for `modalFuel` unfolds before committing P0.
- **Risk:** `pow3_*` lemmas are `private` in the classical file. **Mitigation:** P3 hoists or
  re-proves them (1-liners; label-agnostic Nat lemmas).
- **Risk (LOW):** `Decidable (kValid φ)` without `Fintype Atom`. **Mitigation:** P6 derives it from
  the `.closed ∨ ∃ b acc, .openBranch b acc` dichotomy + sound + P5 (standard once P5 lands).

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | P0 | -- |
| 2 | P1a, P4 | P0 |
| 3 | P1b | P1a |
| 4 | P2 (CRUX) | P1b |
| 5 | P3 | P2 |
| 6 | P5a | P3 |
| 7 | P5b | P5a, P4 |
| 8 | P6 | P5b |

Phases within the same wave run in parallel. **Only Wave 2 has parallelism** (P4 is disjoint from
the P1-P3 critical path: it edits `Completeness.lean` while P1a edits `FmpMeasure.lean`, depends
only on P0, and touches no measure infrastructure). **Critical path:**
P0 → P1a → P1b → **P2** → P3 → P5a → P5b → P6. **P2 (the CRUX) sits on the critical path and gates
P3-P5.**

Territory legend: **[OWN]** = phase may create/edit; **[RO]** = read-only reference.

---

### Phase 0: Universe/measure definitions + exponential modalFuel [COMPLETED]
- **Goal:** Land the pure syntactic defs, the measure, the redefined `modalFuel`, and the entry
  bridge lemma; verify soundness stays green.
- **Territory:**
  - [OWN] `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` (new file; imports `Saturation`, `LoopInduction`)
  - [OWN] `Cslib/Logics/Modal/Tableau/Saturation.lean` (only the `modalFuel` def body at :89)
  - [RO] `Classical/Completeness.lean` (measure-additivity shapes), `Branch.lean` (`modalComplexity`, `modalMaxWorld`)
- **Declarations to add** (signatures from research §3.1-3.2):
  - [x] `modalSubfmls : Proposition Atom → List (Proposition Atom)` (imp/box recursion)
  - [x] `modalDepth : Proposition Atom → Nat` (`box` adds 1; `imp` takes `max`)
  - [x] `modalWorldBound (φ) : Nat := (2*modalComplexity φ + 1) ^ (modalComplexity φ + 1)`
  - [x] `modalUniverse (φ) : List (SignedFormula (Proposition Atom) WorldIndex)` (both signs × subfmls × world labels `[0..W]`)
  - [x] `modalWork (U b e) : Nat := U.countP (¬ b.contains) + U.countP (¬ e.contains)`
  - [x] `modalExpMeasure (U branches expandedSets) : Nat := Σ 3^(modalWork U bᵢ eᵢ)` over `zip`
  - [x] Redefine in `Saturation.lean`: `modalFuel φ := 3 ^ (4 * (2*modalComplexity φ + 1) * ((2*modalComplexity φ + 1)^(modalComplexity φ + 1) + 1))`
  - [x] `modalSubfmls_length_le : (modalSubfmls φ).length ≤ 2*modalComplexity φ + 1`
  - [x] `modalDepth_le_complexity : modalDepth φ ≤ modalComplexity φ`
  - [x] `modalUniverse_length_le : (modalUniverse φ).length ≤ 2*(2*modalComplexity φ+1)*(modalWorldBound φ + 1)`
  - [x] **Bridge:** `modalExpMeasure_entry_le_fuel : modalExpMeasure (modalUniverse φ) [[⟨.neg,φ,0⟩]] [[]] ≤ modalFuel φ` (via `R ≤ 2|U|`, `Nat.pow_le_pow_right`, arithmetic — research §2.3/§6-C4)
- **Reference template:** `classicalExpMeasure_split/_append/_const_exp` (Classical/Completeness.lean:641/656/666) for the measure shape; entry bound mirrors `:677`.
- **Depends on:** none
- **Timing:** ~2-3 h (~120-180 lines)
- **Done = green:** `lake build Cslib.Logics.Modal.Tableau.FmpMeasure` AND
  `lake build Cslib.Logics.Modal.Tableau.Soundness` both succeed; `grep -rn "modalFuel" Cslib/Logics/Modal/Tableau/` shows no proof unfolds it. Commit `task 442 phase 0: FMP defs + exponential modalFuel`.
- **DEVIATION (pre-existing, unrelated blocker):** `lake build Cslib.Logics.Modal.Tableau.FmpMeasure`
  succeeds (zero sorry, zero new axioms — `#print axioms modalExpMeasure_entry_le_fuel` shows only
  `propext`/`Quot.sound`). `lake build Cslib.Logics.Modal.Tableau.Soundness` fails, but NOT because of
  the `modalFuel` edit: `Soundness.lean` imports `SoundnessStep.lean`, which has a pre-existing
  `Application type mismatch` compile error at `SoundnessStep.lean:82,85,91` inside the private
  `Proposition.beqToEq` helper (a `LawfulBEq`/`BEq` mismatch introduced by task 384's split of
  `Soundness.lean`, unrelated to fuel/measure work). Verified via `git stash` on `Saturation.lean`:
  the identical error reproduces with `modalFuel` reverted to its original polynomial value, proving
  this predates and is independent of this phase's edit. `grep -rn "modalFuel"
  Cslib/Logics/Modal/Tableau/` confirms the only proof-context use is `Soundness.lean:347`
  (`modalExpandBranches_closed_unsat (modalFuel φ)`), which passes it as an opaque `Nat` and never
  unfolds it — matching the plan's expectation. Recommend a separate task to fix
  `SoundnessStep.lean`'s `Proposition.beqToEq` before task 442 can claim a fully green
  `Soundness.lean` rebuild; this does not block P1a/P1b/P2/P3/P4 (none of which import
  `Soundness.lean`/`SoundnessStep.lean` transitively — confirmed via import graph: `FmpMeasure` →
  `Saturation`/`LoopInduction` → `Closure`/`Rules`, none reach `Soundness`).

---

### Phase 1a: Subformula-closure — world-preserving / existing-world rules [COMPLETED]
- **Goal:** Prove per-rule closure for the rule kinds that do NOT mint a fresh world (they cannot
  breach the world bound), so no world-bound hypothesis is consumed yet.
- **Territory:**
  - [OWN] `FmpMeasure.lean` (new declaration block after P0 defs)
  - [RO] `Rules.lean` (rule emissions), `Branch.lean` (`boxPositivesOf`, `boxPropagation`), `Saturation.lean`
- **Declarations to add** (per-rule sub-lemmas; each fully proved / green):
  - [ ] `modalApplyOne_prop_outputs_subset` — prop α/β: outputs are structural subformulas of `sf.formula` at world `sf.label` (an existing `b`-label). Template: shape of `classicalApplyOne_output_complexity` (Classical/Completeness.lean:609), membership not complexity.
  - [ ] `modalApplyOne_boxPos_outputs_subset` — `T(□ψ)@w` emits `T(ψ)@w'`, `ψ` from same box node, `w' ∈ successorsOf w` (existing ≤ maxWorld). (`Rules.lean:83-88`)
  - [ ] `modalApplyOne_diamondNeg_outputs_subset` — `F(◇ψ)@w` emits `F(ψ)@w'`, existing `w'`. (`Rules.lean:142-151`)
- **Reference template:** `Rules.lean:83-88, 142-151`; `Branch.lean:180-187`.
- **Depends on:** P0
- **Timing:** ~2-3 h (~120-200 lines)
- **Done = green:** `lake build Cslib.Logics.Modal.Tableau.FmpMeasure` succeeds with the three sub-lemmas sorry-free. Commit `task 442 phase 1a: subformula closure (world-preserving rules)`.

---

### Phase 1b: Subformula-closure — fresh-world rules + top lemma [COMPLETED]
- **Goal:** Prove closure for the two fresh-world-minting linear rules (which consume
  `maxWorld+1 ≤ W`) and assemble the top-level closure lemma by rule dispatch.
- **Territory:**
  - [OWN] `FmpMeasure.lean` (continues the P1a block)
  - [RO] `Rules.lean:91-139`, `Soundness.lean:87` (`modalApplyOne_fresh`)
- **Declarations to add** (research §3.3):
  - [x] `modalApplyOne_diamondPos_outputs_subset` — `T(◇φ)@w` emits witness `T(φ)@w'` + `boxProps` + `diaNegProps` all at fresh `w' = maxWorld+1`; **needs hypothesis `maxWorld b < modalWorldBound φ0`** so `w' ≤ W`. (`Rules.lean:91-114`)
  - [x] `modalApplyOne_boxNeg_outputs_subset` — identical with `witness = ⟨.neg,φ,w'⟩`. (`Rules.lean:117-139`)
  - [x] **Top:** `modalApplyOne_outputs_subset (φ0 sf b acc) (hb : ∀ x∈b, x∈modalUniverse φ0) (hW : modalMaxWorld b < modalWorldBound φ0) : ∀ x ∈ (emitted formulas), x ∈ modalUniverse φ0` — dispatch over `modalApplyOne` cases into the five sub-lemmas.
- **Reference template:** `Rules.lean:91-114, 117-139`; dispatch mirrors `Rules.lean:68-153`.
- **Depends on:** P1a
- **Timing:** ~3-4 h (~150-250 lines)
- **Done = green:** `lake build Cslib.Logics.Modal.Tableau.FmpMeasure` succeeds; `modalApplyOne_outputs_subset` sorry-free. Commit `task 442 phase 1b: subformula closure (fresh-world rules + top lemma)`.
- **Deviations from plan (documented, not design reopening):** (1) added `hsf : sf ∈ b` (and
  the analogous `⟨sign,formula,w⟩ ∈ b` hypothesis on the two fresh-world lemmas) — necessary
  because the source signed formula's own subformula bound must come from somewhere; the plan's
  terse signature omitted it but every real invocation draws `sf` from `b`. (2) added
  `hInv : accFreshInv b acc` (imported from `SoundnessStep.lean` via a new `public import`,
  acyclic) to the top lemma only — needed to bound `acc.successorsOf w` by `modalMaxWorld b` for
  the `boxPos`/`diamondNeg` dispatch cases, which P1a's lemmas only bound by `∈ acc.successorsOf w`
  (not numerically). (3) added five small private glue lemmas: `modalSubfmls_trans` (subformula
  transitivity), `mem_modalUniverse_of`/`mem_modalUniverse_of'`/`modalUniverse_mem_formula`/
  `modalUniverse_mem_label` (`modalUniverse` membership characterization), `mem_boxPositivesOf`
  (inverts `boxPositivesOf`), `mem_successorsOf_hasEdge` (bridges `successorsOf` to `hasEdge`),
  and `boxProps_outputs_subset`/`diaNegProps_outputs_subset` (factored out since `boxProps`/
  `diaNegProps` are byte-identical between `diamondPos` and `boxNeg`, avoiding duplicating the
  trickiest proof twice).

---

### Phase 2: World-count bound (CRUX — highest risk, isolated, serial) [COMPLETED]

> **CONTINUATION (supersedes the [BLOCKED] escalation below — design is complete + hand-verified, so
> per H8 we split the formalization rather than escalate to the user).** The plan's original terse
> target `modalStepBranch_maxWorld_lt` (hb+hW only) is FALSE; the corrected target carries the
> rank/out-degree invariant (a documented, precedented signature deviation — cf. P1b's added
> hypotheses). Formalize the verified potential-function fallback in dependency order, **committing
> after each obligation compiles green** (banked/resumable). The same rank/out-degree invariant will
> be threaded by P5a, so define its predicate(s) cleanly for reuse.
>
> - [x] **P2-obl-a** `modalBranchNodup`: landed as `modalStepBranch_preserves_expandedNodup`
>   (`FmpMeasure.lean`) — a precision refinement of the plan's "branch Nodup" shorthand: `b`
>   itself is NOT generally `Nodup` (unfiltered propositional α/β outputs, e.g. `andPos`, can
>   duplicate an already-present formula), but the invariant actually load-bearing for P2-obl-c
>   is `Nodup` of the **expanded set** `e`, which IS exactly maintained (append-gated by
>   `¬(expanded.any (·==sf))`). Commit `672a940e`+1 (task 442 phase 2a).
> - [x] **P2-obl-b** landed as `modalStepBranch_exists_rank'` (`FmpMeasure.lean`): given `rank`
>   satisfying `rankBound` (`∀x∈b, modalDepth x.formula ≤ rank x.label`) and `rankEdge`
>   (`∀w w', acc.hasEdge w w' → rank w'+1 = rank w`, the "frozen at creation" fact), produces
>   `rank'` satisfying both on every child branch / `newAcc`, updating only at the fresh point
>   `modalNextWorld b` via `Function.update` when `diamondPos`/`boxNeg` mint. Supporting lemmas:
>   `modalDepth_le_of_mem_modalSubfmls`, `boxProps_rank_bound`, `diaNegProps_rank_bound`,
>   `boxPos_rank_bound`, `diamondNeg_rank_bound`, `hasEdge_addEdge_cases_local`.
>   Commit (task 442 phase 2b).
> - [x] **P2-obl-c** landed as `modalStepBranch_preserves_outDegEq` +
>   `outDeg_le_of_expandedNodup` (`FmpMeasure.lean`). Design correction discovered and applied
>   during formalization: `diamondPos`/`diamondNeg` are dead code — `modalNegOf?` matches
>   `.imp _ .bot` unconditionally (`Defs.lean:110-113`, no exclusion for a `.box` antecedent),
>   so `tryAllPropRules`'s `negPos`/`negNeg` arms are *always* applicable first for the
>   T-diamond shape (verified by `rfl`, both directions checked computationally); only
>   `boxNeg`'s `.neg, .box _` shape ever mutates `acc`. `isMintingShaped` (P2-obl-a's file
>   section) is corrected to track only this one shape (was: both shapes, "no factor of 2"
>   merge — now provably unnecessary, not merely simplified: the T-diamond shape would have
>   broken the exact-equality invariant, since it fires via a non-edge-creating prop rule).
>   Same overall `outDeg ≤ Sf` bound, no bound weakened, no sorry/axiom added. Commit
>   (task 442 phase 2c).
> - [~] **P2-obl-d** PARTIAL: `modalPotentialTerm`, `modalPotential`, and
>   `modalCap_mul_eq_succ_sub_one` (the recurrence identity) landed in `FmpMeasure.lean`
>   (definitions + one closed numeric lemma, sorry-free, green). **Design correction found and
>   fixed** (documented in the section doc comment): the naive term
>   `(Sf−outDeg w)·modalCap Sf(rank w−1)` is WRONG at a rank-0 leaf world — `Nat` truncated
>   subtraction silently turns `rank w−1` into `0`, giving a spurious nonzero term `Sf` instead
>   of `0`, which would break the hand-verified "exact Δ=0" claim specifically in the
>   `rank=1`-parent/`rank=0`-child mint sub-case (hand-traced: naive gives net Δ=`Sf≠0`, fixed
>   piecewise term gives net Δ=`0`, matching the design). `modalPotentialTerm` now returns `0`
>   when `rank w = 0`. **Remaining for this obligation**: the single-step lemma itself
>   (`modalStepBranch`-preserves `modalMaxWorld b + modalPotential Sf b acc rank` exactly,
>   composing P2-obl-b's `rank'` and P2-obl-c's `outDegEq` — needs an additional
>   `modalKnownWorlds`-under-`modalStepBranch` lemma: unchanged for non-mint steps, prepends
>   `modalNextWorld b` for the one mint step). Estimated 150-250 more lines, same case-split
>   shape as (a)-(c). Commit (task 442 phase 2d partial).
> - [ ] **P2-obl-e** final composition → world bound `modalMaxWorld b' < modalWorldBound φ0` under the strengthened rank/outDeg-carrying signature, from (a)–(d) + `modalCap_le_pow` + `modalSubfmls_length_le` + `modalDepth_le_complexity`.
>
> **Done = green (revised):** `lake build …FmpMeasure` succeeds; the strengthened world-bound lemma
> sorry-free + axiom-clean. Escalate to user ONLY if a NEW mathematical falsity is found in the
> hand-verified design (not mere formalization effort).

- **Goal:** Prove the a-priori world bound as a per-step loop invariant. This is the single
  research-hard obligation; it gates P3-P5. Isolated in its own phase with a generous budget.
- **Territory:**
  - [OWN] `FmpMeasure.lean` (new declaration block; may add a proof-only rank-map def if fallback invoked)
  - [RO] `Branch.lean:104,135,146,169` (`modalNextWorld_gt`, `label_le_modalMaxWorld`, `modalMaxWorld_le_append`, `modalNextWorld_le_append`), `Soundness.lean` (`accFreshInv`, `modalStepBranch_preserves_accFreshInv`)
- **Declarations to add** (research §3.5):
  - [ ] `modalStepBranch_maxWorld_lt (φ0) (hb : ∀ x∈b, x∈modalUniverse φ0) (hW : modalMaxWorld b < modalWorldBound φ0) (hstep : modalStepBranch b e acc = some (newBs,newExps,newAcc)) : ∀ b'∈newBs, modalMaxWorld b' < modalWorldBound φ0`
  - [ ] Initial-condition lemma: `modalMaxWorld [⟨.neg,φ,0⟩] = 0 < modalWorldBound φ` (trivial since `W ≥ 1`).
  - [ ] **Primary approach:** depth-stratification invariant — worlds form a forest of depth ≤ `modalDepth φ0` (child worlds carry strict-subformula bodies, so strictly smaller modal depth) with branching ≤ `Sf(φ0)`, giving `#worlds ≤ Σ_{i≤d} Sf^i ≤ Sf^(d+1) = W`. Attach a depth field to `accFreshInv`'s edge-endpoint encoding; carry in the same `∀`-invariant used later by P5.
- **CONTINGENCY (in-plan fallback — invoke WITHOUT re-planning; research §6/C3 residual risk):**
  If the depth-stratification invariant proves intractable against the flat `maxWorld+1` naming
  after one genuine attempt, strengthen the tracked invariant to a **per-world rank map**
  (`label ↦ remaining modal-depth budget`) threaded alongside `acc` **as proof-only data inside
  the induction's `∀`-invariant — NOT inside `modalStepBranch`** (no algorithm/datatype change,
  scope-compliant). This adds proof bulk but preserves the bound. If BOTH primary and fallback
  stall after genuine attempts, mark this phase **[BLOCKED]**, write the blocker to state, and
  escalate — do NOT weaken the bound, do NOT add a `sorry`, do NOT proceed to P3.
- **Reference template:** `modalStepBranch_preserves_accFreshInv` (Soundness.lean:111) — the
  invariant-survives-branching pattern this proof must follow.
- **Depends on:** P1b (closure gives "emitted worlds are fresh/existing"; stratification gives the count cap)
- **Timing:** ~5-8 h (~250-450 lines) — budget generously; adversarial audit before proceeding
- **Done = green:** `lake build Cslib.Logics.Modal.Tableau.FmpMeasure` succeeds; `modalStepBranch_maxWorld_lt` sorry-free. Commit `task 442 phase 2: world-count bound (CRUX)`. **Gate: do not start P3 until this commit lands green.**
- **BLOCKED (both primary and the in-plan contingency genuinely attempted; see `.handoff-P2.json` for
  full detail):**
  1. **Primary approach is mathematically false as literally specified.** Concrete counterexample:
     `b = [⟨.pos, .imp (.box (.imp ψ .bot)) .bot, W-1⟩]` for any diamond-subformula `ψ` of `φ0`
     (`W := modalWorldBound φ0`) satisfies `hb` and `hW : modalMaxWorld b < W` (`W-1 < W`), but
     `modalStepBranch` fires `diamondPos` on the sole element, minting world `W`, giving
     `modalMaxWorld b' = W`, which does **not** satisfy `< W`. A single-step invariant carrying only
     "current `maxWorld < W`" cannot be strengthened to "next `maxWorld < W`" — confirmed exactly as
     research §6/C3 flags ("NOT a one-step monotonicity"; residual risk realized).
  2. **Contingency (rank-map) fully designed and hand-verified, not fully formalized.** The correct
     invariant is a potential-function argument: a proof-only rank map `rank : WorldIndex → Nat`
     (remaining modal-depth budget, frozen at world-creation as `parent_rank − 1`), an out-degree
     counter derived from `acc`, and a scalar potential `Φ := Σ_w (Sf − outDeg w) · modalCap Sf
     (rank w − 1)` (`Sf := (modalSubfmls φ0).length`). Hand-verified: `modalMaxWorld b + Φ ≤ modalCap
     Sf (modalDepth φ0) − 1` is preserved with **exact `Δ = 0`** at every step — mint steps net to
     zero via the recurrence `Sf · modalCap Sf k = modalCap Sf (k+1) − 1`; non-mint steps (prop
     rules, `boxPos`, `diamondNeg`) touch neither `maxWorld`, `rank`, nor `outDeg`, so `Φ` is
     structurally untouched (this is the key design choice: `Φ` depends only on `(rank, outDeg)`,
     **not** on which minting-shaped formulas are currently visible in `b`, sidestepping the
     "prop-rule reveals a new diamond subformula" growth hazard). An initial concern that
     out-degree needs bound `2·Sf` (T-diamond and F-box shapes counted separately) was resolved:
     both shapes are simply disjoint subsets of the *same* `modalSubfmls φ0` node list (which
     already counts every node — box, imp, atom, bot — indiscriminately), so their combined count
     is still `≤ (modalSubfmls φ0).length`, no factor-of-2 gap.
  3. **What is committed and green** (`FmpMeasure.lean`, new `## World-Count Bound (Phase 2)`
     section): `modalCap` (exact geometric-sum capacity, `modalCap Sf k := Σ_{i≤k} Sf^i` via the
     `1 + Sf * modalCap Sf (k-1)` recursion) and its three closing numeric lemmas
     (`modalCap_add_one_le_pow`, `modalCap_zero_le_pow`, `modalCap_le_pow`), giving
     `modalCap Sf k ≤ Sf^(k+1)` unconditionally (handling the `Sf=1 ⟹ k=0` boundary case
     separately, since `Sf=1` forces `modalComplexity φ0 = 0` hence `modalDepth φ0 = 0`). Sorry-free,
     axiom-clean (`propext`/`Quot.sound` only).
  4. **Remaining technical obligations** (not started; each is a genuine multi-case dispatch through
     `modalStepBranch`'s five rule kinds, mirroring but extending P1a/P1b's ~350-line dispatch
     pattern): (a) `b.Nodup` invariant maintenance; (b) `FormulaRankBound` (`∀x∈b, modalDepth
     x.formula ≤ rank x.label`) invariant maintenance, assigning `rank` to freshly-minted worlds as
     `parent_rank − 1`; (c) `outDeg(w) ≤ (modalSubfmls φ0).length` via an injective map "minting
     signed formula at `w` ↦ its `.formula` component" into `modalSubfmls φ0`, using (a); (d) the
     `Φ`-potential single-step `Δ=0` lemma (the hand-verified arithmetic above, formalized); (e)
     final composition deriving `modalStepBranch_maxWorld_lt`'s conclusion from (a)-(d) plus
     `modalCap_le_pow` and `modalSubfmls_length_le`. Estimated 300-500 additional lines.
  5. **Escalating per plan's own protocol** ("If BOTH primary and fallback stall after genuine
     attempts, mark P2 [BLOCKED] and escalate; do NOT weaken the bound, do NOT add a sorry, do NOT
     proceed to P3"). No `sorry`, no new axiom, no datatype/rule change, no bound weakening.

---

### Phase 3: Output-freshness + per-rule R-drop + strict-decrease [IN PROGRESS]
- **Goal:** Prove the counting measure strictly decreases on every `some` step (the engine), using
  closure (P1) and the world bound (P2).
- **Territory:**
  - [OWN] `FmpMeasure.lean` (new declaration block)
  - [RO] `Branch.lean:194-199` (`boxPropagation` freshness guard), `Classical/Completeness.lean:509,641-666,674,684,834`
- **Declarations to add** (research §3.4, §3.6, §2.2):
  - [ ] Hoist/re-prove `pow3_add_one_le`, `pow3_two_add_one_le` (Classical:684/674; currently `private` — hoist or 1-line re-prove) and `modalExpMeasure_split/_append/_const_exp` (Classical:641/656/666, with `R`)
  - [ ] `modalPersistent_outputs_fresh (hstep …) (hpers) : ∀ b'∈newBs, ∀ sf'∈(b'.diff b), sf' ∉ b` (research §3.4) ⇒ `set(b') ⊋ set(b)`
  - [ ] `modalWork_drop_linear : R(child) ≤ R − 1` (linear/branching add `sf` to `e`)
  - [ ] `modalWork_drop_persistent : R(child) ≤ R − 1` (persistent grows `set(b)`, `e` unchanged)
  - [ ] **Engine:** `modalExpMeasure_step_lt (hstep : modalStepBranch bh e acc = some (newBs,newExp,newAcc)) : modalExpMeasure U (done++newBs++bt) (…) + 1 ≤ modalExpMeasure U (done++bh::bt) (…)` — port of `classicalExpMeasure_step_lt` (:834), case-split via §2.2 + `pow3_*`. `1 ≤ R` discharged from consumed `sf∈b\e` or nonempty `newForms⊆U\b` (research §6/C5).
- **Reference template:** `classicalExpMeasure_step_lt` (Classical/Completeness.lean:834); `classicalBranchComplexity_drop` (:509).
- **Depends on:** P2 (and P1b via P2)
- **Timing:** ~3-5 h (~200-350 lines)
- **Done = green:** `lake build Cslib.Logics.Modal.Tableau.FmpMeasure` succeeds; `modalExpMeasure_step_lt` sorry-free. Commit `task 442 phase 3: R-drop + strict-decrease engine`.

---

### Phase 4: Saturation characterisation (PARALLEL with Wave 2) [COMPLETED]
- **Goal:** Prove the saturated-leaf characterisation and the single-step Hintikka expanded-set
  invariant. Disjoint from the P1-P3 critical path.
- **Territory:**
  - [OWN] `Cslib/Logics/Modal/Tableau/Completeness.lean` (new declaration block, before P5; do NOT add the `FmpMeasure` import yet — P4 needs only `Saturation`)
  - [RO] `Classical/Completeness.lean:694,722`, `Saturation.lean:116-117,167,218-234`
- **Declarations to add** (research §3.6, §4):
  - [ ] `modalStepBranch_none_saturated (hstep : modalStepBranch b e acc = none) (sf) (hsfb : sf ∈ b) : sf ∈ e ∨ modalApplyOne sf b acc = .notApplicable` — port of `classicalStepBranch_none_saturated` (:694), threaded with `acc`, splitting the `sf∈e` disjunct against modal `modalApplyOne sf b acc`.
  - [ ] `modalStepBranch_hintikka_inv` — port of `classicalStepBranch_hintikka_inv` (:722), **handling the `.persistent` clause where `newExp = e` (unchanged)** (research §3.1 caveat).
- **Reference template:** `classicalStepBranch_none_saturated` (:694), `classicalStepBranch_hintikka_inv` (:722).
- **Depends on:** P0 only (parallelizable with P1a; H7 territory: different file from P1-P3, so naturally disjoint — this is the one parallel wave the research identifies, §4)
- **Timing:** ~2-3 h (~120-200 lines)
- **Done = green:** `lake build Cslib.Logics.Modal.Tableau.Completeness` succeeds with the two lemmas sorry-free (Completeness still builds without the FmpMeasure import at this point). Commit `task 442 phase 4: saturation characterisation`.

---

### Phase 5a: Combined-invariant single-step preservation [NOT STARTED]
- **Goal:** Prove that one `modalStepBranch` preserves the full bundled loop invariant (lengths,
  `Forall₂ accFreshInv`, world-bound, measure bound, Hintikka expanded-set inv), consuming P2 + P3
  + P4. This is the heavy inductive step, isolated from the fuel recursion.
- **Territory:**
  - [OWN] `Completeness.lean` (add `import Cslib.Logics.Modal.Tableau.FmpMeasure` here; new block)
  - [RO] `Soundness.lean:190-262` (the `processNext` inner shape), `LoopInduction.lean:44-104` (`forall₂_*`)
- **Declarations to add** (research §3.6):
  - [ ] `modalStep_preserves_invariant` — a single lemma (or small bundle) stating: given the combined invariant holds pre-step and `modalStepBranch = some (…)`, it holds on each child, AND `modalExpMeasure` drops by ≥1. Composes P2 (`modalStepBranch_maxWorld_lt`), P3 (`modalExpMeasure_step_lt`), P4 (`modalStepBranch_hintikka_inv`), and `modalStepBranch_preserves_accFreshInv` (green).
- **Reference template:** acc-threading shape of `modalExpandBranches_closed_unsat` (Soundness.lean:165, inner `processNext` :190-262); classical measure-carry of `classicalExpandBranches_hintikka` (:924).
- **Depends on:** P3 (and transitively P2, P4)
- **Timing:** ~3-4 h (~150-250 lines)
- **Done = green:** `lake build Cslib.Logics.Modal.Tableau.Completeness` succeeds; preservation lemma sorry-free. Commit `task 442 phase 5a: combined-invariant step preservation`.

---

### Phase 5b: Top loop lemma modalExpandBranches_hintikka [NOT STARTED]
- **Goal:** Run the fuel / `processNext` induction to conclude that an open leaf returned before
  `fuel = 0` is a Hintikka set, discharging the entry measure bound via P0's bridge.
- **Territory:**
  - [OWN] `Completeness.lean` (continues P5a block)
  - [RO] `Classical/Completeness.lean:924`, `Soundness.lean:165`, `LoopInduction.lean`
- **Declarations to add** (research §3.6, §4-P5):
  - [ ] `modalExpandBranches_hintikka (fuel) : ∀ branches expandedSets accs, lengths → modalExpMeasure U branches expandedSets ≤ fuel → (Hintikka-inv on expanded) → Forall₂ accFreshInv branches accs → world-bound-inv → ∀ b a, modalExpandBranches … fuel = .openBranch b a → modalHintikkaSet b a` — fuse `modalExpandBranches_closed_unsat` (acc-threading + `Forall₂` accs) with `classicalExpandBranches_hintikka` (measure-bound ⇒ Hintikka), carrying all five invariants via P5a, closing the leaf with P4 (`none_saturated` ⇒ all three `modalHintikkaSet` conjuncts, Saturation.lean:218-234).
- **Reference template:** `classicalExpandBranches_hintikka` (:924) + `modalExpandBranches_closed_unsat` (Soundness.lean:165).
- **Depends on:** P5a, P4
- **Timing:** ~3-5 h (~200-350 lines)
- **Done = green:** `lake build Cslib.Logics.Modal.Tableau.Completeness` succeeds; `modalExpandBranches_hintikka` sorry-free; `#print axioms modalExpandBranches_hintikka` standard only. Commit `task 442 phase 5b: modalExpandBranches_hintikka`.

---

### Phase 6: Public theorems + Decidable instance + full CI [NOT STARTED]
- **Goal:** Land the three public theorems and the `Decidable` instance; verify axiom-clean and
  whole-library + CI green.
- **Territory:**
  - [OWN] `Completeness.lean` (public theorem block)
  - [RO] `Completeness.lean:560` (`modalOpenBranch_countermodel`, green), `Soundness.lean` (`modalTableau_sound`)
- **Declarations to add** (research §4-P6):
  - [ ] `modalTableau_complete` — contrapositive wrapper: `modalTableau φ = .openBranch b a ⇒ ¬kValid φ`, via `modalExpandBranches_hintikka` (P5b) ⇒ `modalHintikkaSet` ⇒ `modalOpenBranch_countermodel` (green)
  - [ ] `modalTableau_decides` — `modalTableau φ = .closed ↔ kValid φ`, combining `modalTableau_sound` (green) + `modalTableau_complete`
  - [ ] `instance : Decidable (kValid φ)` — from the `.closed ∨ ∃ b a, .openBranch b a` dichotomy + `modalTableau_decides` (no `Fintype Atom`)
  - [ ] `#print axioms` on all five DoD targets
- **Reference template:** `modalOpenBranch_countermodel` (Completeness.lean:560).
- **Depends on:** P5b
- **Timing:** ~2-3 h (~120-200 lines)
- **Done = green:** whole-library `lake build` green; CI pipeline all green (`lake test`; `lake exe checkInitImports`; `lake exe lint-style`; `lake shake --add-public --keep-implied --keep-prefix`); `#print axioms` on all five targets shows standard axioms only. Commit `task 442 phase 6: public theorems + Decidable + CI green` then `task 442: complete implementation`.

---

## Testing & Validation

- [ ] Per-phase: the exact `lake build <module>` target in each phase's "Done = green" line.
- [ ] No `sorry` in any owned declaration at any phase's green checkpoint: `grep -rn "sorry" Cslib/Logics/Modal/Tableau/{FmpMeasure,Completeness}.lean` returns nothing.
- [ ] No new `axiom`: `#print axioms` on `modalStepBranch_none_saturated`, `modalExpandBranches_hintikka`, `modalTableau_complete`, `modalTableau_decides`, and the `Decidable (kValid φ)` instance — standard axioms only.
- [ ] Preserved-asset guard (P0): `lake build Cslib.Logics.Modal.Tableau.Soundness` green after `modalFuel` change.
- [ ] Whole-library: `lake build` green (P6).
- [ ] CI pipeline (P6): `lake test`; `lake exe checkInitImports`; `lake exe lint-style`; `lake shake --add-public --keep-implied --keep-prefix`.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` (new): universe defs, measure, closure, world bound, R-drop engine (P0-P3)
- `Cslib/Logics/Modal/Tableau/Saturation.lean` (edit): `modalFuel` value only (P0)
- `Cslib/Logics/Modal/Tableau/Completeness.lean` (edit): P4, P5a, P5b, P6 declarations
- `specs/442_modal_tableau_fmp_fuel_measure/plans/01_fmp-fuel-measure-plan.md` (this file)
- `specs/442_modal_tableau_fmp_fuel_measure/summaries/01_fmp-fuel-measure-summary.md` (on completion)

## Rollback/Contingency

- Every phase ends at a compiling, committed green checkpoint; rollback = `git revert` the phase
  commit(s). Phases are additive (new declarations); reverting a later phase never breaks an
  earlier green checkpoint. The one non-additive edit is the `modalFuel` body (P0); reverting it
  restores the polynomial value and the pre-task-442 state (Soundness unaffected either way).
- **P2 (CRUX) contingency** is in-plan (per-world rank map fallback, see Phase 2). If both primary
  and fallback stall after genuine attempts, mark P2 [BLOCKED] and escalate rather than weaken the
  bound or add a `sorry`. Because P2 gates P3-P5, a P2 block halts the critical path but leaves P0,
  P1a, P1b, and P4 landed and green (partial progress preserved).
