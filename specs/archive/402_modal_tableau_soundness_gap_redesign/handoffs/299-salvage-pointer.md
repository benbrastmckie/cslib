# Pointer: salvageable lemmas from the stopped task-299 Soundness refactor

A task-299 orchestrate run (modal-K tableau) attempted to complete `Soundness.lean` on the
**old global-`Accessibility` architecture** that this redesign (per-branch `Accessibility`)
supersedes. That attempt was stopped; its full rewrite is **UNBUILT** and must **not** be merged
wholesale (it rewrites `modalStepBranch_preserves_sat` on the disproven architecture).

However, it left some **architecture-independent** proof-engineering lemmas that may help when this
redesign hits the propositional-rule recognizer friction described in
`specs/364_modal_tableau_soundness_drift_repair/handoffs/BLOCKED-repair-guide.md` §4
("stuck on variable antecedent" / consumed-scrutinee).

- **Branch (canonical):** `wip/task-299-soundness-refactor` (commit `27d93e2d`)
- **Follow-up task:** main #396 `salvage_299_soundness_lemmas`
- **Inspect:** `git show wip/task-299-soundness-refactor:Cslib/Logics/Modal/Tableau/Soundness.lean`

## Strongest candidates — `Soundness.lean` (acc-free, portable)

These directly implement repair-guide §4a ("use characterization lemmas instead of unfolding the
recognizer defs"):

| Decl | What it gives you |
|------|-------------------|
| `modalNegOf?_eq_some`, `modalAndOf?_eq_some`, `modalOrOf?_eq_some`, `modalImpOf?_eq_some` | Characterization lemmas: fire on partially-symbolic terms so `simp`/`obtain` no longer get stuck on a free-variable antecedent. |
| `sfSat`, `sfSat_pos`, `sfSat_neg` | Single-world signed-formula satisfaction predicate + intro lemmas. No `Accessibility` dependence. |
| `RuleResultSat` | Satisfiability predicate over a `RuleResult` (linear / branching / persistent / notApplicable). |
| `applyPropRule_sat`, `tryAllPropRules_sat` | Propositional-rule preservation lemmas — propositional rules never touch accessibility, so these should port directly. |

Also: the refactor changed `branchSatisfiable` to `∃ (W : Type) …` (was `Type*`) to kill the
universe-inference errors (repair-guide §4f / errors ~937–963). Worth considering independent of
the per-branch change.

## Review-before-porting — `Branch.lean` (likely acc-coupled)

`maxWorld`, `modalFreshWorld`, `nextWorld`, `lt_nextWorld`, `modalFreshWorld_gt_acc`,
`modalFreshWorld_gt_label` — fresh-world numbering/freshness helpers. Relevant to fresh-world
management, but `modalFreshWorld_gt_acc` references the global `acc`; restate against per-branch
`accs` before reuse.

## Bottom line

Cherry-pick the four `modal*Of?_eq_some` lemmas and `sfSat`/`RuleResultSat`/`*PropRule_sat` **only
if** the recognizer layer becomes a bottleneck. Do not port the world-numbering helpers verbatim
(global-acc coupling). The accessibility *architecture* work stays 100% with this redesign.
