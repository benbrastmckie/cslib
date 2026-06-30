# Task 407 — Pre-submission decisions (resolved 2026-06-30)

| Q | Decision | Effect |
|---|----------|--------|
| Q1 ND reconciliation | **Option C** (confirm default) | Reframe task-398 gate as explosion-property module; option B stays deferred to task 409. No proof churn. |
| Q2 Scope | **Waves 1-4 only** (confirm default) | Tasks 408 (LM) / 409 (option B ND) remain separate stacked PRs. |
| Q3 Categorical/initiality | **INCLUDE NOW** (deviation from default) | Add explicit initial-object / InitialBot universal-property witness (0 -> A) over OrderBot/PointedBrouwerian. NEW MATH — requires implementation before /pr. |
| Q4 Property naming | **Keep HasLeastBot** (confirm default) | bot_val = designated-constant role; IsIntuitionistic = explosion role. |
| Q5 Coordination w/ 400/#607 | **Adequate** (confirm default) | Connective typeclasses out of scope; Connectives.lean untouched; defer to task 400. |

## Gating work before /pr 407
Q3 requires implementing the explicit initial-object witness layer (see report 01
§lines 176, 203). After it lands green, finalize pr-description.md (expand scope to
note categorical/initiality included) and flip 407 to ready-for-/pr.
