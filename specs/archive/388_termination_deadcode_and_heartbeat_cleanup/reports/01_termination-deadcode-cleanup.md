# Research Report: Task 388 — Termination Dead-Code & Heartbeat Cleanup

**Task type:** cslib (Tier-2 cleanup)
**Date:** 2026-06-29
**Status:** researched
**Sequencing note:** Task 398 is/was actively editing Termination.lean. All line numbers below were
captured live and are current as of this research pass; re-verify with `grep -n` at implementation
time if 398 lands further edits.

## 1. File Locations

| File | Path | Lines |
|------|------|-------|
| Termination.lean | `Cslib/Logics/Propositional/NaturalDeduction/Normalization/Termination.lean` | 1518 |
| Reduction.lean | `Cslib/Logics/Propositional/NaturalDeduction/Normalization/Reduction.lean` | 108 |

Both live under `Cslib/Logics/Propositional/NaturalDeduction/Normalization/`. The dead code is
entirely in **Termination.lean**; Reduction.lean defines the live `normalize`/`normalizeAux`
(see §3) and needs **no deletions**.

## 2. Dead Private Declarations — Verified (0 callers)

All three named decls exist and have **zero external references** (repo-wide grep over `Cslib/`
and `CslibTests/`, excluding the defining file). Current line numbers (the description's
305/492/775 were stale-ish; actuals below):

| Decl | Current line | Kind | Callers |
|------|-------------|------|---------|
| `Theory.Derivation.normalizeAux_fixpoint` | **305** | `theorem` (NOT private — description mislabels it) | 0 (only module docstring at 18) |
| `Theory.Derivation.subs_maximalFormulas_mem` | **492** | `private theorem` | 1 internal: `subsOne_new_redex_complexity_lt` at line 782 — becomes 0 once that decl is deleted |
| `Theory.Derivation.subsOne_new_redex_complexity_lt` | **775** | `private theorem` | 0 |

### Dead-code is a CASCADE — two deletion groups

**Group A — `normalizeAux_fixpoint` chain (lines 204–308, ~105 lines).**
Deleting the named `normalizeAux_fixpoint` (305) orphans its entire private support chain. All have
0 external refs:

| Decl | Line | Notes |
|------|------|-------|
| `normalizeAux_ax` | 204 | `@[simp] private theorem`. Only referenced inside `normalizeAux_fixpoint_aux` (lines 259, 284). |
| `normalizeAux_ass` | 210 | `@[simp] private theorem`. Same — only used inside `_aux`. |
| `normalizeAux_fixpoint_aux` | 216 | `private theorem`. Only caller is `normalizeAux_fixpoint` at line 308. |
| `normalizeAux_fixpoint` | 305 | The named target. 0 callers. Ends at line 308. |

Delete the whole block **204–308** as a unit. Then update the module docstring: lines **18–19**
reference `normalizeAux_fixpoint` ("Strongly normal derivations are fixpoints of `normalizeAux`")
and must be removed/rewritten. The section header `/-! ## Normalization Termination Lemmas -/`
(~line 202) precedes the block — review whether it still describes the remaining content or should
go too.

> **@[simp] caution:** `normalizeAux_ax`/`normalizeAux_ass` are `@[simp]` lemmas. No other proof in
> the file applies `normalizeAux` (the only `normalizeAux` proof references are the fixpoint chain),
> so they should be safe to delete with the chain. **Verify with a scoped `lake build` of the module
> after deletion** — if any unrelated `simp`/`simp_all` silently depended on them, the build will
> surface it. This is the only deletion in the task with a (low) regression risk.

**Group B — `subs`/`subsOne` redex pair (lines 492–794, ~300 lines).**

| Decl | Lines | Notes |
|------|-------|-------|
| `subs_maximalFormulas_mem` | 492–766 | `private theorem`. Sole caller is the next decl. |
| `subsOne_new_redex_complexity_lt` | 768–791 (docstring 768–774, decl 775–791) | `private theorem`. 0 callers. Calls `subs_maximalFormulas_mem` at line 782. |

Delete **492–794** as a unit (next live decl is `commutingSum` at line 796). Because the only caller
of `subs_maximalFormulas_mem` is `subsOne_new_redex_complexity_lt`, the two are jointly dead and
must be removed together — removing one without the other either leaves a dead decl (B1 alone) or a
broken reference (B2 alone).

**Total removal: ~405 lines** (Group A ~105 + Group B ~300), plus the 18–19 docstring edit.

## 3. `normalize` / `normalizeAux` ARE LIVE — DO NOT DELETE

Confirmed per task instruction. Both are **public** `def`s in **Reduction.lean**:

- `Theory.Derivation.normalizeAux : Nat → T.Derivation G A → T.Derivation G A` — Reduction.lean **84**
- `Theory.Derivation.normalize (d) := d.normalizeAux (2 ^ d.height)` — Reduction.lean **105–106**

Both include the `efq` arm added by task 398 (Reduction.lean:99). They currently have **no downstream
theorem callers** (the only theorem that referenced `normalizeAux`, namely `normalizeAux_fixpoint`,
is being deleted), but they are **public API** and the task explicitly forbids deleting them. Public
defs with 0 callers do **not** trip the dead-code/unusedPrivate linters, so keeping them is clean.
**Implementer must NOT delete these and must NOT delete the Reduction.lean defs.**

## 4. Residual Lint Debt — Findings

| Category | Status | Detail |
|----------|--------|--------|
| Long lines (>100) | **NONE** | `awk 'length>100'` over both files returns zero hits. |
| Text linter (`lake exe lint-style`) | **NONE** | Ran clean; no output filtered to Termination/Reduction. |
| `set_option maxHeartbeats` | **1 override, ALREADY justified** | Line **1195**: `set_option maxHeartbeats 2000000 in` guarding the `snImpEForm`/`snOrEForm`/`snSubst` mutual block. A justifying comment already exists at lines 1196–1198 ("large equation-compiler goal; raise the heartbeat limit so the (sorry-free) termination proof elaborates within budget"). The task says "remove or comment-justify" — this **already satisfies the comment-justify branch**. No mandatory action. Optional: attempt to lower/remove after decomposing the mutual block (see below) — but treat as low-priority, high-risk. |
| `sorry` / `admit` | **NONE** | The two `sorry` grep hits (lines 1140, 1198) are inside comments asserting code is "sorry-free". |
| bare/flexible `simp` | **Mostly self-resolving** | Bare `simp` at lines 508, 555, 593, 666, 731, and `by simp; tauto` at 781 all sit **inside the Group B deletion region (492–794)** and vanish with the dead code. None remain in live code after deletion. |
| unused simp args / no-op/dead tactics (env linter) | **Needs `lake lint` post-deletion** | These are `lake lint` (environment-linter) categories that require a full build to surface and cannot be reliably grepped. Much of the suspected debt lived in the deleted regions. **Recommendation:** after Groups A+B are deleted, run `lake build` then `lake lint` on the module and fix only what remains. Do not pre-enumerate — the deletion changes the surface. |

### Heavy proofs / decomposition
The single genuinely heavy proof is the **mutual well-founded recursion** `snImpEForm` /
`snOrEForm` / `snSubst` (starts line 1199, guarded by the 1195 heartbeat override). The L6 driver
`normalize`-style structural driver begins ~line 1472. Decomposing a *mutual* well-founded
recursion is high-risk (the equation compiler treats the block as one unit; splitting it can break
termination inference) and is unlikely to let the heartbeat override drop. **Recommendation:** treat
decomposition as **optional / out-of-scope-unless-cheap**. The primary, safe, high-value work of
this task is the ~405-line dead-code removal; the heartbeat override is already justified.

## 5. Actionable Plan Skeleton (for the planner)

The task decomposes into small, independent, build-verifiable phases:

- **Phase 1 — Delete Group A** (`normalizeAux_fixpoint` chain, lines 204–308) + update module
  docstring lines 18–19 + review section header ~202. Then `lake build` the module to confirm the
  `@[simp]` removals (ax/ass) broke nothing.
- **Phase 2 — Delete Group B** (`subs_maximalFormulas_mem` + `subsOne_new_redex_complexity_lt`,
  lines 492–794). `lake build` the module.
- **Phase 3 — Lint sweep.** Run `lake lint` + `lake exe lint-style` on the module; fix any residual
  unused-simp-arg / no-op-tactic / flexible-simp warnings that survive the deletions. Confirm the
  1195 heartbeat override remains comment-justified (no action unless decomposition is attempted).
- **Phase 4 (optional, low-priority) —** consider decomposing the heavy mutual block only if it
  yields a clean heartbeat reduction without endangering termination inference; otherwise skip.
- **Final verification —** full CI order: `lake build`, `lake exe checkInitImports`, `lake lint`,
  `lake exe lint-style`, `lake test`. Zero-debt: no sorries, no new axioms (none present now).

## 6. Reuse / Standards Notes
- No new definitions or abstractions are introduced by this task — it is pure deletion + lint, so
  the reuse-first protocol is satisfied vacuously.
- Zero-debt: the codebase is currently sorry-free in these files; deletions cannot introduce sorries.
- All deletions are of **private** decls (except `normalizeAux_fixpoint`, a public `theorem` with 0
  callers) — no public-API breakage for the named six decls.

## 7. Verification Commands Used
```bash
grep -rn "<decl>" Cslib/ CslibTests/        # 0 external refs for all six decls
awk 'length>100' <file>                      # no long lines
lake exe lint-style | grep Termination       # clean
grep -n "set_option maxHeartbeats" <file>     # 1 hit, line 1195, already justified
```
