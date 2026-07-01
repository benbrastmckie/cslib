# Implementation Plan (v2, streamlined): Task #427 — imp case of `temporalTruthLemma_propositional_aux`

- **Task**: 427 - Prove `temporalTruthLemma_propositional` (atom/bot/imp cases) sorry-free
- **Status**: [IN PROGRESS] — scaffold landed green; one isolated hole remains
- **Effort**: 3-5 hours (the single imp case)
- **Dependencies**: None. **Territory**: shares `Completeness.lean` with task 426 — serialize, never parallelize (see `.memory/10-Memories/temporal-tableau-426-427-file-territory.md`).
- **Research Inputs**: reports/01_propositional-truth-lemma.md (§4a decision table, §4c per-rule closing logic)
- **Supersedes**: plans/01_propositional-truth-lemma.md (phases 1-2 + base cases of phase 3 are DONE)
- **Type**: cslib · **Lean Intent**: true

## Why this v2 exists

Four `cslib-implementation-agent` dispatches each overflowed context ("prompt too long",
~110 min total) attempting the imp case as one monolithic interactive proof. The orchestrator
hand-landed all mechanical scaffolding and validated the strong-induction approach. This v2
discards the now-complete phases and re-scopes the work to the **single remaining hole**, with a
decomposition designed so no individual agent step holds the whole case in context.

## Already DONE (committed green — do NOT redo)

All in `Cslib/Logics/Temporal/Tableau/Completeness.lean`:
- `IsPropositional` inductive predicate.
- `Formula.one_le_complexity` (`unfold Formula.complexity; split <;> omega`).
- Bridge lemmas `any_pos_mem`, `any_neg_mem`, `mem_to_any_pos`, `mem_to_any_neg` (each with `omit [Hashable Atom]`).
- `temporalTruthLemma_propositional_aux` — strong induction on `Formula.complexity` via Nat fuel;
  **zero / atom / bot cases proved sorry-free**.
- Public `temporalTruthLemma_propositional` — wired as a one-liner over the aux; typechecks.

The only `sorry` in the file's compiled code is the `| imp hφ' hψ' =>` case of the aux
(currently ~line 366). All hypotheses are in scope: `ih` (strong IH over smaller complexity),
`hrule` (saturation condition), `hopen`, `hφ'`, `hψ'`, `hle`, `t`.

## Remaining work — the imp case ONLY

### `hrule` shape (the saturation condition, from `Saturation.lean:259`)
```
hrule : ∀ sf ∈ b, let (result,_) := temporalApplyOne sf b ord; match result with
  | .linear nf      => ∀ sf' ∈ nf, sf' ∈ b
  | .branching brs  => ∃ br ∈ brs, ∀ sf' ∈ br, sf' ∈ b
  | .persistent nf  => ∀ sf' ∈ nf, sf' ∈ b
  | .notApplicable  => True
```

### Rule-firing decision table (report §4a) — for positive `T(imp φ' ψ')`
| Shape of `imp φ' ψ'` | Rule | Output | IH needed |
|---|---|---|---|
| `φ'=imp a (imp b bot)`, `ψ'=bot` (= `and a b`) | `andPos` | linear `T(a),T(b)` | IH `a`,`b` (deep) |
| `φ'=imp a bot` (= `or a ψ'`) | `orPos` | branch `T(a)`\|`T(ψ')` | IH `a` (deep), `ψ'` |
| proper imp (`ψ'≠bot`, `φ'≠imp _ bot`) | `impPos` | branch `F(φ')`\|`T(ψ')` | IH `φ'`,`ψ'` |
| `ψ'=bot`, not `and`-shape (= `neg φ'`) | `negPos` | linear `F(φ')` | IH `φ'` |
F-direction is dual (`andNeg`/`orNeg`/`impNeg`/`negNeg`); leaves portable from WIP lines 721-1000.

### Phases (each ends green + committed — bounds context per step)

#### Phase A: split T/F directions [NOT STARTED]
- [ ] Replace the imp `sorry` with `refine ⟨fun hpos => ?_, fun hneg => ?_⟩` then `· sorry` `· sorry`.
- [ ] `lake build Cslib.Logics.Temporal.Tableau.Completeness 2>&1 | grep -E 'error|completed'` → green (2 sorries).
- [ ] Commit `task 427: imp case split T/F (partial)`.

#### Phase B: T-direction, one rule-shape at a time [NOT STARTED]
- [ ] From `hpos`, get membership via `any_pos_mem b t (.imp φ' ψ') hpos`; apply `hrule _ that`.
- [ ] `cases ψ'` then `cases φ'` (one more level for `imp a (imp b bot)`) to detect and/or/imp/neg per §4a.
- [ ] At each leaf reduce the rule result with
  `simp only [tryAllPropRules, applyPropRule, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?, RuleResult.isApplicable, List.map, List.find?]`.
- [ ] Pull outputs via `mem_to_any_*`; apply `ih χ (by omega) χ_prop t` per output subformula
  (complexity bound from `hle` via `omega`; `IsPropositional χ` of deep parts via `cases hφ'`/`cases hψ'`);
  close with `simp only [Satisfies.imp_iff, Satisfies.bot_false]`.
- [ ] **Build + commit after EACH rule shape closes** (`andPos`, then `orPos`, then `impPos`, then `negPos`).

#### Phase C: F-direction [NOT STARTED]
- [ ] Mirror Phase B for `andNeg`/`orNeg`/`impNeg`/`negNeg`, porting WIP 721-1000 leaves (targeted reads only),
  drawing IHs from `ih`. Build + commit after each shape.

#### Phase D: finalize [NOT STARTED]
- [ ] `grep -nE '\bsorry\b|\badmit\b' Completeness.lean` → only pre-existing comment lines.
- [ ] `lake build` full + `lake test 2>&1 | tail -5` green; `lake exe checkInitImports` pass.
- [ ] Update state → completed; write summary; commit `task 427: complete imp case (sorry-free)`.

## Hard constraints (lessons from the 4 overflows)
- NEVER call `lean_diagnostic_messages` (hangs). Use `lean_goal` + `lean_multi_attempt`.
- ALWAYS pipe builds through `grep -E 'error|warning|completed successfully|failed'`.
- Read ONLY targeted offset/limit ranges; never the whole WIP or whole report.
- Build + commit after every sub-shape — do NOT attempt multiple rule shapes before a build.
- On context pressure: leave the deepest unfilled sub-shape as one documented `sorry`, ensure green, commit, write a partial handoff naming remaining shapes + last green commit hash, STOP.
- No new axioms, no vacuous defs, no `sorry` beyond intermediate scaffolding.
