# Implementation Plan: Task #317 (Unified, post-369)

- **Task**: 317 - Fill the propositional tableau completeness sorries (unified parametric path)
- **Status**: [NOT STARTED]
- **Effort**: 9 hours
- **Dependencies**: 316 (soundness, complete), 323, 363 (classical build repair, landed), 369 (parameterization, landed) — all satisfied
- **Research Inputs**: specs/317_propositional_tableau_completeness/reports/01_tableau-completeness-research.md
- **Artifacts**: plans/02_tableau-completeness-unified.md (this file); supersedes plans/01_tableau-completeness-plan.md
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Task 369 parameterized the intuitionistic and minimal tableau over `(closurePred, modelBot)`
into `Intuitionistic/Scheme.lean`, **unifying** what were previously duplicated int/min
completeness obligations. The int and min truth-lemma/countermodel proofs are now discharged
**once** through the parametric `IntMinScheme`. The classical completeness proof took a
separate, already-completed path. This plan targets the **6 concrete remaining sorries**
(verified by reading the sources), sequencing the structural expansion-loop lemmas first, then
the single parametric truth lemma, then the two per-logic validity bridges, then a classical +
`Decidable` + CI confirmation pass.

### Current sorry inventory (verified against sources)

| # | File | Line | Obligation |
|---|------|------|------------|
| 1 | `Intuitionistic/Scheme.lean` | ~242 | `truthLemma S` — single parametric truth lemma (formula induction), shared by int + min |
| 2 | `Intuitionistic/Scheme.lean` | ~280 | `openBranch_countermodel S` `hopen` — `intExpandBranches_openBranch_closed` (closurePred b = false) |
| 3 | `Intuitionistic/Scheme.lean` | ~288 | `openBranch_countermodel S` `hsat` — `intExpandBranches_openBranch_sat` (saturation) |
| 4 | `Intuitionistic/Scheme.lean` | ~296 | `openBranch_countermodel S` `hFmem` — `intExpandBranches_openBranch_initial_mem` (F(φ)@0 preserved) |
| 5 | `Intuitionistic/Completeness.lean` | ~112 | per-logic bridge `IValid φ → ∀ b, IForces (intExtractValuation b) (fun _ => False) 0 φ` |
| 6 | `Minimal/Completeness.lean` | ~110 | per-logic bridge `MValid φ → ∀ b, MForces … (minBranchBotForces b) 0 φ` |

`openBranch_countermodel S` and `tableau_complete S` are already wired and become **sorry-free
automatically** once sorries 1–4 are filled (their bodies are complete; only the inline `sorry`s
remain). `intTruthLemma`, `minTruthLemma`, `intuitionisticOpenBranch_countermodel`,
`minOpenBranch_countermodel` are thin delegators and need no edits.

### IMPORTANT — Classical is already complete (deviation from delegation brief)

The delegation brief listed a 5th obligation, `classicalExpandBranches_hintikka`
(`Classical/Completeness.lean` ~L462), as remaining work. **It is already proved.** A read of the
current source confirms `Classical/Completeness.lean` contains **zero `sorry`** (the structural
induction `classicalExpandBranches_hintikka` is at L924 and `classicalTableau_complete` at L1328,
both sorry-free; `Classical/DecisionProcedure.lean` documents both directions as sorry-free).
Task 363 + later tableau work landed it. This plan therefore treats classical as a
**verification-only** step (Phase 5), not new proof work. If a regression surfaces during CI, it
is handled there.

### Research Integration

The research report's decomposition (truth lemma → countermodel → completeness; Hintikka-set
argument; F-atom case needs no T(p)/F(p) coexistence) still holds, now refactored through the
scheme. Both `isIntuitionisticallyClosed` and `isMinimallyClosed` close on complementary atomic
pairs, which is exactly why the F-atom case of the **single** `truthLemma S` works for both
instances (`minOpen_no_contradiction` provides the int/min-shared no-contradiction fact). The old
blockers B1/B2 are now localized inside `truthLemma S` (B1: F-atom under closure — resolved by the
shared complementary-pair closure) and the structural `hsat` lemma (B2: saturation-form mismatch).

### Prior Plan Reference

Plan 01 (4 phases: classical-truth / classical-countermodel / intuitionistic / minimal) is now
**largely stale**: classical is done, and the int/min duplication it assumed was removed by 369.
Lessons carried forward: (a) the deep expansion-loop induction must be its own tightly-scoped pass
with commit-after-each-step, never a single broad dispatch (plan 01 + the 316 analog both
overflowed otherwise); (b) territory contract — 317 owns `*/Completeness.lean`, `*/Scheme.lean`
(its sorries), and `*/DecisionProcedure.lean`; 316 owns `*/Soundness.lean`. Do not edit
`Minimal/Soundness.lean` or `Intuitionistic/Soundness.lean` (`minBranchBotForces`,
`intExtractValuation`, `minOpen_no_contradiction` are consumed as-is).

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Fill all 6 remaining tableau-completeness sorries (4 in `Scheme.lean`, 1 in each per-logic `Completeness.lean`).
- Make `truthLemma S`, `openBranch_countermodel S`, `tableau_complete S` sorry-free for both `intScheme` and `minScheme`.
- Make `intuitionisticTableau_complete` and `minimalTableau_complete` sorry-free.
- Confirm the tableau `Decidable` instances (`instDecidableIValid`, `instDecidableMValid`, `instDecidableDerivable*`) are genuinely sorry-free.
- Full CI green: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake`.
- No new axioms beyond the standard set (verify with `lean_verify`).

**Non-Goals**:
- Re-proving classical completeness (already sorry-free).
- Editing any `*/Soundness.lean` (316 territory).
- Refactoring the expansion loop or `IntMinScheme` interface beyond what the bridge obligation may require (see Phase 4 risk).
- Strong completeness (only weak: validity ⇒ closure).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| **R1 (dominant): per-logic bridge quantifies `∀ b`** but `intExtractValuation b` / `minBranchBotForces b` are upward-closed only for *persistence-saturated* branches, not arbitrary `b`. Under the ambient `Nat` `≤` Preorder, `intExtractValuation [T(p)@5]` is not upward-closed. So `∀ b, IForces (intExtractValuation b) … 0 φ` may be literally unprovable from `IValid`/`MValid`. | H | H | Phase 4 begins with a lean-lsp spike: inspect the exact goal + the `Preorder Nat` instance actually in scope for `IForces` in `Scheme.lean`/`Completeness.lean`. If `∀ b` is unprovable, **refine `tableau_complete`'s `hvalid` hypothesis** to range over the *open saturated* branch (the only branch it ever applies `hvalid` to). The saturation/openness facts are already produced by Phases 1–3, so threading them is mechanical. This signature refinement is within 317's remit (it is repairing the 369 obligation). Document the chosen path. |
| **R2: structural saturation lemma** (`intExpandBranches_openBranch_sat`) must connect the actual return-site saturation `intStepBranch bPers e nw = none` (accumulated expanded set `e`, next-world `nw`) to the truth-lemma's simplified `∀ sf ∈ b, intStepBranch b [] 0 = none`; also the fuel=0 path returns `.openBranch` *without* a saturation check. | H | M | Prove a fuel-sufficiency lemma (fuel bound `2^(2·complexity+2)` is never exhausted before saturation, so the fuel=0 open-return is unreachable for the initial call), OR weaken the truth-lemma `hsat` form to match the real return-site saturation. Use the classical analog `classicalExpandBranches_hintikka` (L924) as the structural-induction template. Tightly scoped, commit-after-green. |
| **R3: truth-lemma imp/world case** needs fresh-world (`nw`) reasoning the simplified `hsat` may not directly supply (old blocker B2). | M | M | If `hsat`'s `[]/0` form is insufficient for the imp case, adjust the `truthLemma`/structural `hsat` statements in tandem (both are 317-owned) to carry the expanded set / next-world, mirroring `intExpandBranches_closed_unsat`'s use of `applyPersistenceFixpoint_sat`. |
| R4: same-file (`Scheme.lean`) edits across Phases 1–3 risk churn. | M | L | Sequence Phases 1→2→3 (no parallel writes to `Scheme.lean`); commit after each phase reaches green. |
| R5: classical regression during CI. | L | L | Phase 5 confirms classical sorry-free; if a regression appears, fix in place (317 owns `Classical/Completeness.lean`). |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases are sequenced linearly: Phases 1–3 all edit `Intuitionistic/Scheme.lean` (same-file
territory, so no parallelism); Phase 4 needs the parametric core (Phase 3) green to verify the
bridges; Phase 5 is the final CI/confirmation gate. (Note: `truthLemma S` is *logically*
independent of the structural lemmas — it takes `hopen`/`hsat` as hypotheses — but is sequenced
after them to avoid concurrent `Scheme.lean` edits.)

---

### Phase 1: Structural openness + branch-monotonicity lemmas [NOT STARTED]

**Goal**: Discharge the `hopen` and `hFmem` sorries in `openBranch_countermodel S` (Scheme.lean
~L280, ~L296) by proving two structural lemmas about `intExpandBranches`.

**Tasks**:
- [ ] Read the goal states at `Scheme.lean` ~L280 (`hopen`) and ~L296 (`hFmem`) with `lean_goal`.
- [ ] Prove `intExpandBranches_openBranch_closed`: if `intExpandBranches … closurePred = .openBranch b` then `closurePred b = false`. Induction on `fuel` + inner `go`. At every `.openBranch` return site the guard `if closurePred bPers then … else …` (Expansion.lean L183) and the fuel=0 `findSome?` predicate (L164) ensure the returned branch is open. Use this to close the `hopen` sorry.
- [ ] Prove `intExpandBranches_openBranch_initial_mem`: if every initial branch contains `sf` then the returned open branch contains `sf`. Direct analog of the classical template `classicalExpandBranches_openBranch_initial_mem` (`Classical/Completeness.lean` L1164). Branch monotonicity: `Branch.extendMany` and `applyPersistenceFixpoint` only add formulas. Instantiate at `sf = ⟨.neg, φ, 0⟩` to close the `hFmem` sorry.
- [ ] Keep both as `private` helper lemmas in `Scheme.lean`, placed before `openBranch_countermodel`.

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — add the two structural lemmas; replace the `hopen` (~L280) and `hFmem` (~L296) sorries with applications of them.

**Verification** (implementer runs; do not run during planning):
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` succeeds.
- `grep -n sorry` on `Scheme.lean` shows the `hopen` and `hFmem` sorries gone (truthLemma + hsat sorries remain).

---

### Phase 2: Structural saturation lemma [NOT STARTED]

**Goal**: Discharge the `hsat` sorry in `openBranch_countermodel S` (Scheme.lean ~L288) via
`intExpandBranches_openBranch_sat`.

**Tasks**:
- [ ] Read the `hsat` goal at `Scheme.lean` ~L288 with `lean_goal`; confirm the exact target form `∀ sf ∈ b, intStepBranch b [] 0 = none`.
- [ ] Prove the return-site saturation: in the `fuel'+1` path, `.openBranch bPers` is returned only when `intStepBranch bPers e nw = none` (Expansion.lean L188–191). Capture this by induction on `intExpandBranches` + `go`.
- [ ] Handle the fuel=0 path (Expansion.lean L162–166): the open branch there is returned *without* a saturation check. Resolve via a fuel-sufficiency argument (the bound `2^(2·φ.complexity+2)` is large enough that the initial call never reaches fuel=0 before saturating), OR by weakening the truth-lemma `hsat` hypothesis form to the real return-site saturation (coordinate with Phase 3 if so — both `truthLemma` and this lemma are 317-owned). See R2/R3.
- [ ] Bridge the accumulated `(e, nw)` saturation to the simplified `([], 0)` form required by `truthLemma`'s `hsat`, or adjust both statements consistently.
- [ ] Use the classical `classicalExpandBranches_hintikka` (`Classical/Completeness.lean` L924) as the structural-induction template.

**Timing**: 2.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — add `intExpandBranches_openBranch_sat`; replace the `hsat` sorry (~L288). If the `hsat` form must change, update the `truthLemma` signature consistently (defer the proof body to Phase 3).

**Verification** (implementer runs):
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` succeeds.
- Only the `truthLemma` sorry (~L242) remains in `Scheme.lean`.

---

### Phase 3: Parametric truth lemma `truthLemma S` [NOT STARTED]

**Goal**: Discharge the single parametric truth-lemma sorry (`Scheme.lean` ~L242) by formula
induction, completing `openBranch_countermodel S` and `tableau_complete S` for both schemes.

**Tasks**:
- [ ] Read the `truthLemma` goal (~L242) with `lean_goal`; note hypotheses `hopen : S.closurePred b = false`, `hsat`, and the `IForces (intExtractValuation b) (S.modelBot b) w φ` target.
- [ ] Induct on `φ` (and on world `w` where needed), using the classical `BoolEvaluate` truth-lemma induction (`Classical/Completeness.lean` ~L300–429) as a structural template, adapted to intuitionistic `IForces`:
  - **atom p**: T-direction by `intExtractValuation` definition; F-direction from `S.closurePred b = false` ruling out T(p)/F(p) at the same world (use `minOpen_no_contradiction` / the int closure's complementary-pair check — shared by both schemes).
  - **bot**: discharge via the scheme field `S.bot_truth b hopen w` (already proved in `intScheme`/`minScheme`).
  - **and / or**: alpha/beta decomposition from `hsat` (Hintikka conditions) + IH.
  - **imp**: T-direction via persistence saturation (for all `w' ≥ w` with T(φ), T(ψ)); F-direction via the world-creating rule (∃ fresh `w'` with T(φ), F(ψ)). This is the case most likely to need the `(e, nw)` form of saturation — coordinate with Phase 2 (R3).
- [ ] Prove any needed upward-closure of `S.modelBot b` inline (the `Scheme.lean` docstring notes `modelBot_uc` is deliberately proved inside the truth lemma, using saturation).
- [ ] Confirm `openBranch_countermodel S` and `tableau_complete S` now build with no sorry (their bodies are already complete).

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — fill `truthLemma`.

**Verification** (implementer runs):
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` succeeds with **zero sorry** in `Scheme.lean`.
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness` and `…Minimal.Completeness` still build (their delegators `intTruthLemma`/`minTruthLemma`/`*OpenBranch_countermodel` now resolve cleanly; only their bridge sorries remain).

---

### Phase 4: Per-logic validity bridges (int + min) [NOT STARTED]

**Goal**: Discharge the two per-logic bridge sorries — `Intuitionistic/Completeness.lean` ~L112
and `Minimal/Completeness.lean` ~L110 — making `intuitionisticTableau_complete` and
`minimalTableau_complete` sorry-free.

**Tasks**:
- [ ] **Spike (R1)**: with `lean_goal`, read the exact goal at `Completeness.lean` ~L112 and the `Preorder Nat` instance in scope for `IForces`. Decide whether `∀ b, IForces (intExtractValuation b) (fun _ => False) 0 φ` is provable as stated, or whether `tableau_complete`'s `hvalid` must be refined to the open saturated branch (see R1). Record the decision in the commit message and a code comment.
- [ ] Prove the upward-closure helper(s):
  - `intExtractValuation_uc`: `w ≤ w' → intExtractValuation b w p → intExtractValuation b w' p` (holds for persistence-saturated branches; if `∀ b` is needed and unprovable, this drives the R1 signature refinement).
  - `minBranchBotForces_uc`: analogous for `minBranchBotForces b` (the `Minimal/Soundness.lean` docstring asserts this upward-closure via persistence — confirm whether reusable directly or needs the saturated-branch hypothesis).
- [ ] **Int bridge** (`Completeness.lean` ~L112): instantiate `h : IValid φ` at `World = ℕ`, `val = intExtractValuation b`, supplying `intExtractValuation_uc`, at `w = 0`; `bot_forces = fun _ => False` is trivially upward-closed. Close the sorry.
- [ ] **Min bridge** (`Minimal/Completeness.lean` ~L110): instantiate `h : MValid φ` with `val = intExtractValuation b`, `bot_forces = minBranchBotForces b`, supplying both upward-closure proofs, at `w = 0`. Close the sorry.
- [ ] If R1's refinement was taken, apply the corresponding `tableau_complete`/`openBranch_countermodel` signature change in `Scheme.lean` and re-verify Phases 1–3 targets still build.

**Timing**: 2 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` — fill the bridge sorry (~L112); add `intExtractValuation_uc` helper if local.
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` — fill the bridge sorry (~L110); add `minBranchBotForces_uc` helper if local.
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — only if R1 signature refinement is required.

**Verification** (implementer runs):
- `lake build` for `…Intuitionistic.Completeness` and `…Minimal.Completeness` succeeds with **zero sorry**.
- `grep -rn sorry Cslib/Logics/Propositional/Tableau/` returns nothing (excluding doc-comment mentions).

---

### Phase 5: Classical confirmation, Decidable instances, and CI [NOT STARTED]

**Goal**: Confirm classical completeness is (still) sorry-free, that the tableau `Decidable`
instances are genuinely sorry-free, and that the full CI pipeline is green with no new axioms.

**Tasks**:
- [ ] Confirm `Classical/Completeness.lean` has zero `sorry` (expected: already sorry-free; no edits). If a regression surfaced, repair in place (317 owns this file).
- [ ] Confirm the `Decidable` instances build sorry-free: `instDecidableIValid`, `instDecidableDerivableIntPropAxiom` (Intuitionistic/DecisionProcedure.lean), `instDecidableMValid`, `instDecidableDerivableMinPropAxiom` (Minimal/DecisionProcedure.lean), `instDecidableTautologyTableau` (Classical/DecisionProcedure.lean).
- [ ] `lean_verify` each top-level completeness theorem and `Decidable` instance — no `sorryAx`, no non-standard axioms.
- [ ] Run full CI: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] Fix any lint/shake findings (unused imports, style) in 317-owned files only.

**Timing**: 0.5 hours

**Depends on**: 4

**Files to modify**:
- None expected. Possible touch-ups in 317-owned `*/Completeness.lean` / `*/DecisionProcedure.lean` for lint/shake.

**Verification** (implementer runs):
- `lake build` (full project) succeeds.
- `lake test` passes.
- `lake exe checkInitImports`, `lake exe lint-style`, `lake shake` all pass.
- No `sorry` anywhere under `Cslib/Logics/Propositional/Tableau/`.

## Testing & Validation

- [ ] Zero `sorry` under `Cslib/Logics/Propositional/Tableau/` (code, not doc comments).
- [ ] `truthLemma`, `openBranch_countermodel`, `tableau_complete` (parametric) sorry-free.
- [ ] `intuitionisticTableau_complete`, `minimalTableau_complete` sorry-free.
- [ ] `lake build` (full) succeeds.
- [ ] `lake test` passes.
- [ ] `lake exe checkInitImports`, `lake exe lint-style`, `lake shake` pass.
- [ ] `lean_verify` confirms no new axioms on all completeness theorems + `Decidable` instances.

## Artifacts & Outputs

- `specs/317_propositional_tableau_completeness/plans/02_tableau-completeness-unified.md` (this file)
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean`
- Modified: `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean`
- Possibly touched (lint/shake): `*/DecisionProcedure.lean`, `Classical/Completeness.lean`

## Rollback/Contingency

- Each phase commits at green. Git-revert a phase commit if it regresses.
- If R1 cannot be resolved even with the `tableau_complete` signature refinement (i.e., upward-closure is genuinely unavailable for the returned branch), mark sorries 5–6 [BLOCKED] and spawn a follow-up to revisit the 369 countermodel/accessibility design; the parametric core (sorries 1–4) and classical remain a real partial deliverable.
- Phases 1–3 are self-contained in `Scheme.lean`; reverting them does not affect classical.
- Do not edit `*/Soundness.lean` under any contingency (316 territory).
