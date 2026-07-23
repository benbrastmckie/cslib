# Implementation Plan: LTL-to-Temporal Semantic Preservation Bridge

- **Task**: 541 - ltl_temporal_semantic_preservation_bridge
- **Status**: [COMPLETED]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: specs/541_ltl_temporal_semantic_preservation_bridge/reports/01_ltl-temporal-bridge-research.md
- **Artifacts**: plans/01_temporal-preservation-bridge.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; cslib.md; lean4.md; plan-compliance.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

`Cslib/Logics/LTL/Embedding.lean` defines `Formula.toTemporal` (a 5-case syntactic map from
`LTL.Formula` to `Temporal.Formula`) but contains zero theorems, no semantic file imports it, and
its docstring's semantic-preservation claim is unproven. This plan connects the island by adding a
new semantics-only file `Cslib/Logics/LTL/EmbeddingSemantics.lean` that (1) defines the bridge
model `toTemporalModel`, (2) proves the main satisfaction-preservation theorem
`satisfies_toTemporal` by induction on the formula generalizing the time index, and (3) proves the
consumer corollary `satisfiable_toTemporal` (LTL satisfiability transfers to Temporal
satisfiability) wired at `n = 0` via `drop_zero`. Research confirms the docstring claim is correct
as written and the entire bridge is provable with zero sorry, zero new axioms, using only existing
library API. Definition of done: the new file compiles, the two theorems are sorry-free, the module
is added to the `Cslib.lean` barrel, and the CSLib CI gates (`checkInitImports`, `lake build`,
`lake lint`, `lake exe lint-style`) pass.

### Research Integration

The research report (`reports/01_ltl-temporal-bridge-research.md`) supplies the full,
case-verified proof strategy and is the contract for this plan:

- **Reuse-first**: Every ingredient already exists. Sequence reindexing lemmas are `@[simp]`:
  `ωSequence.head_drop`, `drop_drop`, `tail_drop'`, `get_drop`, `drop_zero`
  (`Foundations/Data/OmegaSequence/Init.lean`). Target predicate is `Temporal.Satisfiable`
  (`Temporal/Semantics/Validity.lean:112`).
- **Import-weight decision**: `sat_or_iff` / `sat_and_iff` live in `Temporal/Metalogic/Soundness.lean`
  (lines 43, 54), which transitively drags in the whole ProofSystem. To keep a *semantics-only*
  bridge, this plan copies the two ~6-line classical helper proofs locally rather than importing
  Metalogic. Both proofs were read and confirmed to depend only on `simp only [Satisfies]` +
  classical `by_contra` reasoning — no proof-system dependency.
- **Namespace**: `Cslib.Logic.LTL` (singular `Logic`), matching `Embedding.lean:37`.
- **Key proof facts**: `next` maps to `.untl .bot (toTemporal φ)`; ℕ discreteness (via `omega`)
  forces the strict-until witness `s = n+1`. `untl` maps to `reflexiveUntl = b ∨ (a ∧ (a U b))`;
  the reflexive/strict reconciliation is the `j = 0` vs `j ≥ 1` case split with the `r = n+k`
  index bijection discharged by `omega`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (roadmap flag not set).

## Goals & Non-Goals

**Goals**:
- Create `Cslib/Logics/LTL/EmbeddingSemantics.lean` as a semantics-only bridge file (no Metalogic
  import).
- Define `toTemporalModel : (Atom → State → Prop) → ωSequence State → Temporal.TemporalModel ℕ Atom`.
- Prove `satisfies_toTemporal` (main bridge, sorry-free, induction on formula generalizing `n`).
- Prove `satisfiable_toTemporal` (consumer corollary, sorry-free) making `toTemporal` a used
  definition.
- Register the new module in the `Cslib.lean` barrel and pass all CSLib CI gates.

**Non-Goals**:
- No change to `Formula.toTemporal` or its docstring — the translation is correct as written; the
  contingency "if unprovable, correct the translation" is not triggered.
- No reverse-direction validity result (`Temporal.Valid φ.toTemporal → LTL.Valid φ`) — noted as an
  optional bonus in research, out of scope here.
- No import of `Temporal/Metalogic/Soundness.lean` — helpers are copied locally by design.
- No new axioms, no `sorry`, no vacuous definitions.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `untl` case index bijection (`r ↔ n+k`) resists `omega` | M | L | Research verified the `k := r - n` substitution closes under `omega`; use `lean_multi_attempt` on the assembled witness before committing the edit |
| `next` discreteness argument mis-encoded (wrong witness) | M | L | Follow research: witness `s := n+1`; `by_contra` on `s ≠ n+1` feeds `hguard (n+1)` to `False`; verify with `lean_goal` per branch |
| Local `sat_or`/`sat_and` helpers diverge from Soundness proofs | L | L | Copy the exact proof bodies confirmed at `Soundness.lean:43,54`; keep them private/local to the bridge namespace |
| Lint failures (docBlame, defLemma, unusedSectionVars) | L | M | Add docstrings to every declaration; keep Prop-valued results as `theorem`; use `omit` for any unused section variable per research lint notes |
| Barrel/import-minimization drift after adding file | L | M | Run `lake exe mk_all --module` and `lake shake` as the final phase; re-run `checkInitImports` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel. This plan is fully sequential (each phase
consumes the prior phase's declarations).

### Phase 1: Scaffold file, bridge model, and local semantic helpers [COMPLETED]

- **Goal:** Create the new semantics-only file with its module header, imports, namespace, the
  `toTemporalModel` definition, and the two local `sat_or` / `sat_and` classical helpers — the
  file compiles with these declarations before any bridge theorem is attempted.
- **Tasks:**
  - [x] Create `Cslib/Logics/LTL/EmbeddingSemantics.lean` beginning with `import Cslib.Init`
        (transitively required) and the `module` + `public import` style of neighboring bridge
        files (`Temporal/FromPropositional.lean`).
  - [x] Add `public import` lines for: `Cslib.Logics.LTL.Embedding`,
        `Cslib.Logics.LTL.Semantics.Satisfies`, `Cslib.Logics.Temporal.Semantics.Satisfies`,
        `Cslib.Logics.Temporal.Semantics.Validity`. Do NOT import `Temporal/Metalogic/Soundness`.
  - [x] Open `namespace Cslib.Logic.LTL` and add a `@[expose] public section` matching neighbors.
  - [x] Define `toTemporalModel (v : Atom → State → Prop) (w : ωSequence State) :
        Temporal.TemporalModel ℕ Atom := ⟨fun n p => v p (w n)⟩` with a docstring (correct to use
        `def` — it returns data).
  - [x] Add two local Prop helpers with docstrings, copying the exact proof bodies from
        `Temporal/Metalogic/Soundness.lean:43` (`sat_and_iff`) and `:54` (`sat_or_iff`), specialized
        to the bridge's needs: `Satisfies M t (φ ∨ ψ) ↔ (Satisfies M t φ ∨ Satisfies M t ψ)` and the
        `∧` analogue. Keep them `theorem`/`lemma` (not `def`). *(deviation: altered -- each helper
        needed `open scoped Cslib.Logic.Temporal in` immediately before it, since `∧`/`∨` notation
        is ambiguous between LTL's own scoped `Formula.and`/`.or` (active by virtue of being
        inside `namespace Cslib.Logic.LTL`) and Temporal's; opening Temporal's scoped notation
        locally resolves the overload via the expected `Temporal.Formula Atom` type. No proof-body
        change.)*
  - [x] Keep section variables minimal (`{Atom State : Type*}`); apply `omit` if an
        unused-section-variable lint would fire.
  - [x] `lake build Cslib.Logics.LTL.EmbeddingSemantics` to confirm the scaffold compiles.
- **Timing:** ~45 min
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Logics/LTL/EmbeddingSemantics.lean` (new) — module header, imports, `toTemporalModel`,
    local `sat_or`/`sat_and` helpers.
- **Verification:**
  - `lake build Cslib.Logics.LTL.EmbeddingSemantics` succeeds.
  - `lean_verify` on `toTemporalModel` and the two helpers reports no `sorry` / no unexpected axioms.

### Phase 2: Prove the main bridge theorem `satisfies_toTemporal` [COMPLETED]

- **Goal:** Prove the satisfaction-preservation theorem sorry-free by `induction φ generalizing n`,
  following the research's case-by-case discharge path exactly (plan-compliance: do not substitute
  an alternative strategy).
- **Tasks:**
  - [x] State `theorem satisfies_toTemporal (v : Atom → State → Prop) (w : ωSequence State) (n : ℕ)
        (φ : LTL.Formula Atom) : LTL.Satisfies v (w.drop n) φ ↔
        Temporal.Satisfies (toTemporalModel v w) n φ.toTemporal` with a docstring.
  - [x] `induction φ generalizing n`.
  - [x] **atom p** case: rewrite LHS `v p (w.drop n).head` with `head_drop` to `v p (w n)`;
        close by `simp [head_drop]` / `Iff.rfl` against `(toTemporalModel v w).valuation n p`.
        *(deviation: altered -- required adding `public import
        Cslib.Foundations.Data.OmegaSequence.Init` (the four reindexing simp lemmas live there, not
        in `.Defs`, which is all that was transitively available) and using the fully-qualified
        `Cslib.ωSequence.head_drop` name to disambiguate against `Stream'.head_drop`/
        `RelSeries.head_drop`. No change to the discharge strategy.)*
  - [x] **bot** case: both `False`, `Iff.rfl`.
  - [x] **imp φ ψ** case: discharge via the two IHs at the same `n`.
  - [x] **next φ** case (`toTemporal = .untl .bot (toTemporal φ)`): rewrite LHS to
        `Satisfies v (w.drop (n+1)) φ` via `tail_drop'`; apply IH at `n+1`; use `omega`-backed ℕ
        discreteness to force the strict-until witness `s = n+1` (guard `⊥` forbids any strictly
        intermediate point). Use `lean_multi_attempt` to validate both directions before editing.
        *(deviation: altered -- `lean_multi_attempt` produced malformed match-arm errors on this
        multi-line tactic block; validated instead via direct `Edit` + `lean_goal` inspection per
        edit, same net verification discipline.)*
  - [x] **untl φ₁ φ₂** case (`toTemporal = reflexiveUntl a b = b ∨ (a ∧ (a U b))`): reindex LHS with
        `drop_drop` and the two IHs; unfold RHS with the local `sat_or` / `sat_and` helpers plus the
        Temporal `untl` unfolding; perform the `j = 0` (left disjunct) vs `j ≥ 1` (right disjunct)
        reconciliation; discharge the `r = n + k` index bijection with `omega` (`k := r - n`).
  - [x] Confirm no goals remain via `lean_goal`; then `lake build Cslib.Logics.LTL.EmbeddingSemantics`.
- **Timing:** ~75 min
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Logics/LTL/EmbeddingSemantics.lean` — add `satisfies_toTemporal`.
- **Verification:**
  - `lake build Cslib.Logics.LTL.EmbeddingSemantics` succeeds.
  - `lean_verify Cslib.Logic.LTL.satisfies_toTemporal` reports no `sorry` and only standard axioms.

### Phase 3: Prove the consumer corollary `satisfiable_toTemporal` [COMPLETED]

- **Goal:** Prove the satisfiability transfer corollary, wiring the main theorem at `n = 0` so
  `toTemporal` gains a genuine downstream consumer.
- **Tasks:**
  - [x] State `theorem satisfiable_toTemporal {Atom State : Type*} (φ : LTL.Formula Atom)
        (h : LTL.Satisfiable (State := State) φ) : Temporal.Satisfiable φ.toTemporal` with a
        docstring (note the explicit `(State := State)` binder — `State` is an implicit module
        variable of `LTL.Satisfiable`). *(deviation: altered -- `{Atom State : Type*}` are not
        re-bound on the theorem's own line since they are already the file's ambient section
        `variable`s (auto-included since both appear in the statement); redeclaring them would
        just shadow the same names. The `(State := State)` explicit binder is present as planned.)*
  - [x] `obtain ⟨v, w, hsat⟩ := h`.
  - [x] Provide `D := ℕ` with its `LinearOrder ℕ` / `Nontrivial ℕ` instances, `M := toTemporalModel v w`,
        `t := 0`.
  - [x] Reduce the goal `Satisfies M 0 φ.toTemporal` to `hsat` via `satisfies_toTemporal` at `n = 0`
        and `drop_zero : w.drop 0 = w`.
  - [x] `lean_goal` to confirm closure; `lake build Cslib.Logics.LTL.EmbeddingSemantics`.
- **Timing:** ~20 min
- **Depends on:** 2
- **Files to modify:**
  - `Cslib/Logics/LTL/EmbeddingSemantics.lean` — add `satisfiable_toTemporal`.
- **Verification:**
  - `lake build Cslib.Logics.LTL.EmbeddingSemantics` succeeds.
  - `lean_verify Cslib.Logic.LTL.satisfiable_toTemporal` reports no `sorry`.

### Phase 4: Barrel registration and CSLib CI verification [COMPLETED]

- **Goal:** Register the new module in the `Cslib.lean` barrel and pass the full CSLib CI gate
  sequence.
- **Tasks:**
  - [x] Run `lake exe mk_all --module` to add `Cslib.Logics.LTL.EmbeddingSemantics` to `Cslib.lean`
        (verify the new import line appears near the existing `Cslib.Logics.LTL.Embedding` entry).
        *(deviation: altered -- per explicit orchestrator delegation instruction (concurrent-work
        notice: two other agents were editing this checkout), performed a targeted single-line
        `Edit` insertion of `public import Cslib.Logics.LTL.EmbeddingSemantics` immediately after
        the `Embedding` line in `Cslib.lean` instead of running `mk_all`, which would regenerate
        the whole barrel file and risk clobbering concurrent sessions' in-flight edits. The
        resulting line placement is identical to what `mk_all` would have produced
        (alphabetical, directly after `Embedding`, before `ModelChecking`).)*
  - [x] Run `lake exe checkInitImports` (confirm the new file imports `Cslib.Init`).
  - [x] Run `lake build` (full project) — syntax linters run during build.
  - [x] Run `lake lint` — resolve any docBlame / defLemma / defsWithUnderscore / unusedSectionVars
        warnings on the new declarations (add docstrings, keep Prop results as `theorem`, `omit`
        unused section vars). *(zero warnings for `EmbeddingSemantics.lean`; `lake lint` reported
        "Linting passed for Cslib" repo-wide.)*
  - [x] Run `lake exe lint-style` (use `--fix` for text-lint autofixes if needed). *(zero
        violations for `EmbeddingSemantics.lean`.)*
  - [x] Run `lake shake --add-public --keep-implied --keep-prefix` to confirm imports are minimal
        (or `--fix`). *(no entry for `EmbeddingSemantics.lean` in the shake report -- imports
        already minimal; the report's other entries are pre-existing repo-wide suggestions for
        files outside this task's scope, left untouched per the concurrent-work notice.)*
  - [x] Additionally ran `lake test` (full `CslibTests/` suite per the mandatory 8-step CI
        pipeline) -- passed with exit 0.
- **Timing:** ~40 min
- **Depends on:** 3
- **Files to modify:**
  - `Cslib.lean` — barrel entry for the new module (added by `mk_all`).
  - `Cslib/Logics/LTL/EmbeddingSemantics.lean` — any lint-driven touch-ups.
- **Verification:**
  - `lake build`, `lake exe checkInitImports`, `lake lint`, `lake exe lint-style` all pass.
  - `Cslib.lean` contains `public import Cslib.Logics.LTL.EmbeddingSemantics`.

## Testing & Validation

- [x] `lake build Cslib.Logics.LTL.EmbeddingSemantics` compiles the new file with zero errors.
- [x] `lake build` (full project) succeeds after barrel registration.
- [x] `lean_verify` confirms `satisfies_toTemporal` and `satisfiable_toTemporal` are sorry-free and
      axiom-clean.
- [x] `lake exe checkInitImports` passes (new file imports `Cslib.Init`).
- [x] `lake lint` reports no environment-linter warnings on the new declarations.
- [x] `lake exe lint-style` reports no text-lint violations.
- [x] Grep confirms `Cslib.Logics.LTL.EmbeddingSemantics` now imports `Cslib.Logics.LTL.Embedding`
      (the island has a consumer).

## Artifacts & Outputs

- `Cslib/Logics/LTL/EmbeddingSemantics.lean` — new semantics-only bridge file with
  `toTemporalModel`, local `sat_or`/`sat_and` helpers, `satisfies_toTemporal`,
  `satisfiable_toTemporal`.
- `Cslib.lean` — updated barrel including the new module.
- `specs/541_ltl_temporal_semantic_preservation_bridge/summaries/01_temporal-preservation-bridge-summary.md`
  — implementation summary (produced by /implement).

## Rollback/Contingency

- The change is additive and isolated: revert by deleting
  `Cslib/Logics/LTL/EmbeddingSemantics.lean` and re-running `lake exe mk_all --module` to remove
  its barrel entry. No existing declarations are modified, so rollback cannot break current
  downstream code.
- If the `untl` reconciliation or `next` discreteness case proves unexpectedly resistant despite
  the research's verified path, mark the affected phase `[BLOCKED]` (per plan-compliance for
  `.lean` files: escalate rather than silently substitute a strategy or introduce a `sorry`),
  record the reached goal state, and return `status: "partial"`.
