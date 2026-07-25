# Summary 01: BX⁺ Completeness over the Uniform Class + Dense→ℚ Bridge (Task 451)

## Outcome

`[COMPLETED]` — all 6 plan phases implemented, sorry-free, zero new axioms, full CSLib CI
pipeline green.

## What landed

New file `Cslib/Logics/Temporal/Metalogic/MetricCompleteness.lean`:

- `Satisfies_orderIso` — general satisfaction-transport lemma along an order isomorphism
  `e : D ≃o E` (reusable; the concrete artifact unlocking a semantic route for related tasks).
- `axiom_sound_uniform`, `uniformFrameCondition_dual`, `swap_valid_of_valid_uniform`,
  `soundness_uniform`, `soundness_thderivable_uniform` — soundness of `BX⁺` over the uniform
  class `U`.
- `validMetricUniform_imp_oag` — the `oag ⊆ U` corollary recovering task 449's oag-soundness
  statement as a consequence of `U`-validity.
- `metric_mcs_implies_base_mcs`, `metric_theorem_in_all_limit_points`,
  `satisfies_bot_top_indep`, `chronicleUniformMetric` — the chronicle built from a Metric-MCS
  satisfies the four uniformity axioms at every point (direct G/H-propagation from the fact that
  the axioms are theorems — no C4 trichotomy needed, simpler than the dense case).
- `completeness_metric` — **the honest completeness theorem**: `validMetricUniform φ →
  BXPlusDerivable φ`.
- `denseCountermodel_transport_rat`, `denseFragment_countermodel_rat` — the dense→ℚ bridge:
  a countable dense serial countermodel transports to the ordered-abelian-group ℚ via Cantor's
  isomorphism theorem (`Order.iso_of_countable_dense`) and `Satisfies_orderIso`.

Modified:
- `Cslib/Logics/Temporal/Semantics/Validity.lean` — added `uniformFrameCondition` and
  `validMetricUniform` definitions.
- `Cslib/Logics/Temporal/Metalogic.lean`, `Cslib.lean` — barrel wiring (`mk_all --module`).

## Research verdict honored

Per `reports/01_bxplus-completeness-frame-class.md`, literal BX⁺-completeness over the full
ordered-abelian-group class (the discrete sub-case) was **not attempted** — it is very likely
false (BX⁺ lacks a discreteness/archimedean axiom, so a non-homogeneous `ℤ ×ₗ A` block-index
frame validates BX⁺ but is not an oag). This is recorded as an escalated open item in the module
docstring, citing `Burgess1984` §6.1 and `Xu1988` Thm 2.9 as durable anchors — no `sorry`, no
axiom, no vacuous definition stands in for it.

## Plan Deviations

None. All phases executed in the order and shape specified by the plan; no steps skipped or
substituted.

## Verification

```
lake build Cslib.Logics.Temporal.Metalogic.MetricCompleteness   -- green
lake build                                                       -- full project green (3253 jobs)
lake exe checkInitImports                                        -- clean (exit 0)
lake lint                                                         -- zero findings in touched files
lake exe lint-style                                               -- clean (exit 0)
lake test                                                         -- green (exit 0)
lake exe mk_all --module                                          -- wired MetricCompleteness into Cslib.lean
lake shake --add-public --keep-implied --keep-prefix              -- zero findings in touched files
grep -rn "\bsorry\b" Cslib/Logics/Temporal/Metalogic/MetricCompleteness.lean Cslib/Logics/Temporal/Semantics/Validity.lean  -- none
grep -n "^axiom " Cslib/Logics/Temporal/Metalogic/MetricCompleteness.lean Cslib/Logics/Temporal/Semantics/Validity.lean     -- none
```

`lean_verify` on all new public declarations (`Satisfies_orderIso`, `soundness_thderivable_uniform`,
`validMetricUniform_imp_oag`, `metric_theorem_in_all_limit_points`, `chronicleUniformMetric`,
`completeness_metric`, `denseCountermodel_transport_rat`, `denseFragment_countermodel_rat`) →
only `propext`, `Classical.choice`, `Quot.sound` (standard), zero `sorry`.

Pre-existing, unrelated warnings/`sorry`s surfaced by the full-project `lake lint`/`lake shake`/
`lake test` runs (e.g. `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`,
`Cslib/Logics/Modal/Tableau/FrameSoundness.lean`, `Cslib/Logics/Temporal/Tableau/Saturation.lean`)
are outside this task's scope and were left untouched.

## Note on commit history

One intermediate commit (`task 535 phase 5: modalFuelS4 ...`) unintentionally bundled this
task's Phase-1/2 staged changes alongside a concurrently-running agent's task-535 commit, due to
both agents sharing the same git working tree. Content is correct and fully verified (confirmed
via `git show --stat` and a clean `git status` for the affected files); history was not rewritten
to avoid disrupting the other agent's in-flight work. All subsequent phases (3-6) committed
cleanly with correctly scoped diffs.
