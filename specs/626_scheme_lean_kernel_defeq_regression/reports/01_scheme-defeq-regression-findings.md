# Scheme.lean Kernel-Defeq Non-Termination: Investigation Findings

**Status**: root cause localized, mechanism NOT proven
**Investigated**: 2026-08-11
**Subject**: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
**Trigger**: the Connectives/Operators reconciliation, phase 8 (branch `task-619-phase8-wip`, commit `1e88ad3e`)

---

## 1. Summary

Applying the phase 8 connectives migration makes `Scheme.lean` fail to compile. The failure is a
**non-terminating (or pathologically slow) elaboration of a single private lemma**, not an error.
No diagnostic is ever emitted; the compiler simply spins.

The affected declaration is `intExpandBranches_openBranch_sat` at `Scheme.lean:8327` — a
1321-line private lemma with 22 hypotheses and 187 `simp` invocations.

---

## 2. Reproduction

Against the branch `task-619-phase8-wip`:

```bash
lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
```

Hangs indefinitely. Observed for >34 minutes with no completion and no `.olean` produced.

**Control** — revert only the three files in `Scheme.lean`'s import closure that the migration
touches, then rebuild:

```bash
git checkout HEAD -- \
  Cslib/Foundations/Logic/Connectives.lean \
  Cslib/Logics/Propositional/Defs.lean \
  Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean
lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
```

| Dependency state | Result |
|---|---|
| Pre-migration | **Builds clean in 14s** (932/932 jobs, 0 errors) |
| With migration | **No completion in >34 min** |

Same file, same Mathlib, same toolchain (`v4.33.0-rc1`). The only variable is those three files.

---

## 3. Localization method

Binary search over the file's 245 top-level declarations, compiling truncated prefixes with
`lake env lean` (import cost is only ~5s, so probes are cheap):

| Prefix | Result |
|---|---|
| decls ≤ 123 | 3s |
| decls ≤ 214 | 22s |
| decls ≤ 237 | 22s |
| decls ≤ 239 | 22s |
| **decls ≤ 240** | **23s** |
| **decls ≤ 241** | **timeout (>200s)** |

Declaration 241 is `intExpandBranches_openBranch_sat` (line 8327). Everything before it
elaborates in well under half a minute.

---

## 4. The runaway work is kernel-level, not tactic-level

This is the most important constraint on any candidate fix.

Setting a finite heartbeat budget on the offending lemma:

```lean
set_option maxHeartbeats 40000 in
private lemma intExpandBranches_openBranch_sat ...
```

produces **no deterministic timeout after 400 seconds**. A heartbeat-checked tactic loop would
have errored almost immediately at that budget.

Supporting process observations during a 34-minute run:

- CPU: 102% — exactly one core pegged; cputime tracked wall-time 1:1 (genuinely computing, not
  blocked on I/O)
- RSS: **flat at 455 MB** across every sample (rules out runaway allocation/term-size explosion)
- Only worker: every other module in the build had completed; the build sat waiting on this one file

**Consequence**: `set_option maxHeartbeats <bigger>` cannot fix this. That remedy was applied
elsewhere in the same migration (e.g. `Modal/Tableau/LoopChecking.lean`) and does not transfer
here.

---

## 5. Hypotheses tested and REFUTED

### 5.1 Simp normal-form direction — REFUTED

The migration adds `rfl` bridge lemmas in `Defs.lean`:

```lean
@[scoped grind =] lemma Proposition.and_def (A B : Proposition Atom) :
    A.and B = HasAnd.and A B := rfl
```

These point *from* the cheap constructor form *to* the typeclass-projection form, which looked
backwards for normalization. Injecting the reverse direction as local simp lemmas:

```lean
@[local simp] private theorem probe_and_eq {A : Type*} [DecidableEq A] (x y : Proposition A) :
    HasAnd.and x y = x.and y := rfl
-- likewise for HasOr.or / HasImp.imp
```

**Result: still hangs (>400s).** This is consistent with section 4 — `simp` lemmas cannot
influence kernel defeq. Do not re-attempt this approach.

### 5.2 Reverting `Defs.lean` alone — NOT VIABLE as a fix

```
error: Cslib/Logics/Propositional/Defs.lean:184:42: Ambiguous term
error: Cslib/Logics/Propositional/Defs.lean:189:32: Ambiguous term
error: Cslib/Logics/Propositional/Defs.lean:198:32: Ambiguous term
```

Restoring the `scoped infix` notations while `Operators.lean`'s scoped `HasAnd`/`HasOr`/`HasImp`
notation is also in scope makes `∧`/`∨`/`→` ambiguous. This is precisely why the migration
deleted those 12 notation declarations, so "just put the notation back" is not available as a
standalone remedy.

---

## 6. Leading unproven hypothesis

The migration changes how `∧`, `∨`, `→` elaborate on `Proposition`:

**Before** — `Defs.lean` bound the notation directly to the constructors:

```lean
@[inherit_doc] scoped infix:36 " ∧ " => Proposition.and
@[inherit_doc] scoped infix:35 " ∨ " => Proposition.or
@[inherit_doc] scoped infix:30 " → " => Proposition.imp
```

`a ∧ b` elaborated to `Proposition.and a b` — a bare constructor application, zero indirection.

**After** — those three lines are deleted and `∧`/`∨`/`→` resolve through `Operators.lean`'s
typeclass notation, reaching the constructor only via an instance projection:

```lean
instance : HasAnd (Proposition Atom) where and := .and
instance : HasOr  (Proposition Atom) where or  := .or
instance : PropositionalConnectives (Proposition Atom) where bot := .bot; imp := .imp
```

**Hypothesis**: every connective occurrence now carries a typeclass-projection layer that kernel
defeq must unfold. In a lemma with deeply nested formula terms and 187 `simp` calls each doing
discrimination-tree matching and defeq checks, this could compound combinatorially. The flat
memory profile fits projection unfolding (cheap per step, no large term retained) better than it
fits term-size explosion.

**This is NOT established.** It is consistent with all observations but was not directly
confirmed. Confirm or refute it before building a fix on it.

Note the class declarations themselves are structurally identical between the old
`Connectives.lean` and the upstream `Operators.lean` (same field arity and types), so the class
*shape* is not the differentiator — only the notation routing is.

---

## 7. Suggested next steps

1. **Confirm the mechanism.** Bisect *inside* the lemma (the body is one large
   `suffices key : ∀ ...` block). Narrow to the specific tactic step that spins, then inspect the
   goal term at that point. `set_option trace.profiler true` and `set_option diagnostics true`
   are the natural instruments; note that anything heartbeat-based will not trip.
2. **Test instance reducibility.** If the projection-layer hypothesis holds, making the
   `HasAnd`/`HasOr`/`PropositionalConnectives` instances reducible (or otherwise making the
   projections unfold cheaply at defeq level) is the most targeted fix. Untested.
3. **Consider rewriting the lemma's connective occurrences** to explicit `.and`/`.or`/`.imp` dot
   notation, bypassing the notation layer at the call sites that matter. Targeted but invasive.
4. **Consider splitting the lemma.** At 1321 lines with 22 hypotheses it is fragile independent
   of this bug; decomposition would reduce the defeq surface and improve diagnosability. Largest
   effort, most durable.

---

## 8. Why this was not caught earlier

The migration's downstream repairs were verified with **per-module scoped builds**
(`lake build <module>`), each confirming an individual file compiles. `Scheme.lean` was never
among the modules built that way, and a scoped per-module strategy structurally cannot surface a
file that is not in its target set.

Compounding this, an interrupted full build produced **zero errors while stopping at 3314/3331
targets** — a killed process leaves no error output, so "no errors" was briefly and wrongly read
as a pass. Any future verification of this migration should treat *reaching the final target
count* as part of the pass condition, not the absence of error lines.

---

## 9. Wider context

`main` currently does **not** build its top-level barrel: `Connectives.lean` and `Operators.lean`
both declare the same five classes (`HasImp`, `HasBox`, `HasDiamond`, `HasAnd`, `HasOr`) and
`Cslib.lean` imports both. The migration's phase 8 is what removes that duplication, so this
regression blocks the barrel repair as well as its own feature work. It also blocks the deferred
whole-repo CI re-run recorded as a follow-up by the propositional-coverage work.
