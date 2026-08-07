# Research Report: `RuleApplySt σ` Additive Introduction

**Task**: 562 — tableau_ruleapplyst_additive_introduction
**Session**: sess_1785926778_90c7a6_562
**Date**: 2026-08-05
**Scope**: Steps 1–3 of the six-step migration order (consumer audit; add the `St` ladder as new
declarations; prove the bridges). Steps 4–6 (S4 Keyed migration, retiring the double derivation,
retiring the unordered stepper) are explicitly NOT in scope and were not attempted.

---

## Executive Summary

- **The mandatory consumer audit is complete** (§1). It found **16 `rfl` bridges** downstream of
  the generic ladder, not the six named in the task description. The extra ten are
  `modalStepBranch{T,B,S5,Five,Kb5,Kb5''}_eq`, `modalExpandBranches{T,Five,Kb5,Kb5''}_eq`
  and `modalTableauKb5_eq_modalTableauFive`. This does not change the plan — additive-only
  protects all sixteen equally — but it means the blast radius of any future *edit* to
  `modalExpandBranchesGen` / `modalStepBranchGen` is roughly 2.7× what the description records.
- **The whole task has been prototyped and machine-verified end to end.** A complete, sorry-free,
  lint-clean implementation of `RuleApplySt`, `liftRuleApply`, `modalStepBranchGenSt`,
  `modalExpandBranchesGenSt`, `modalTableauGenSt` and all three bridges was inserted into
  `Saturation.lean` and the **full `lake build Cslib` came back green at exactly 3313 jobs**, the
  recorded baseline. `lake test` exit 0, `checkInitImports` exit 0, `lint-style` exit 0,
  `lake lint` findings **145 → 145 (byte-identical diff)**, `lake shake` exit 1 with **exactly 9
  findings, none in Modal/Tableau**. Saturation.lean was then restored; `git diff` against HEAD is
  empty. The verified source is at
  `/home/benjamin/Projects/cslib/specs/562_tableau_ruleapplyst_additive_introduction/artifacts/st-ladder-verified.lean`.
- **Full downstream rebuild cost is 52 seconds** on a warm cache. This task is cheap to verify;
  the implementer should gate on the full build, not a scoped one.
- **One correction to the task description.** `RuleApply = RuleApplySt Unit` is **not achievable
  as a definitional equality** and must not be attempted (§3). `RuleApplySt Unit` has an extra
  `Unit →` argument and an extra `× Unit` in its result; `Unit → X` is not `X`. The relationship
  is an explicit `liftRuleApply : RuleApply Atom → RuleApplySt Atom Unit` embedding plus the three
  bridge theorems. Any attempt to make it a defeq would also require *editing* the existing
  `RuleApply`, which the additive constraint forbids outright.
- **Two proof-engineering facts the planner needs** (§5): the loop-level bridge's `fuel = 0` case
  is `simp only [modalExpandBranchesGen, modalExpandBranchesGenSt]` **when the declarations live
  inside `Saturation.lean`**, but needs an extra `cases` on the `findSome?` value when they live
  in a separate module (Lean shares the auxiliary matcher within a module but not across one).
  And the step-level bridge needs a new general `List.findSome?`/`Option.map` commutation lemma
  that does not exist in Mathlib or the project (verified by Loogle and local search).
- **Zero debt**: no `sorry`, no new `axiom`, no vacuous definition. The three bridges depend only
  on `propext` and `Quot.sound`.

---

## 1. Consumer Audit of `Saturation.lean` (mandatory gate — COMPLETE)

`Saturation.lean` exports 15 declarations. Below is the consumer count per symbol, measured by
`grep -rn '\b<symbol>\b'` over `Cslib/**/*.lean` and `CslibTests/**/*.lean`, excluding
`Saturation.lean` itself. Counts are *reference occurrences*, not distinct consumers.

### 1.1 The six symbols the migration order names

| Symbol | Consuming files | Refs |
|---|---|---|
| `RuleApply` | CompletenessLoop 26, GenericDriver 13, FmpMeasure 13, FrameSoundness 10, Completeness 8, FiveSimplification 5, BDriver 4, LoopChecking 3, Soundness 1, S5Simplification 1, FrameCompleteness 1 | 85 |
| `modalStepBranchGen` | CompletenessLoop 36, FrameSoundness 31, FmpMeasure 25, GenericDriver 18, FiveSimplification 16, LoopChecking 15, S5Simplification 14, BDriver 10, FrameCompleteness 8, Completeness 6, TDriver 5, Soundness 3 | 187 |
| `modalExpandBranchesGen` | FrameSoundness 31, CompletenessLoop 16, BDriver 14, FiveSimplification 9, FrameCompleteness 8, LoopChecking 7, S5Simplification 6, TDriver 5, GenericDriver 1, **CslibTests/ModalFrameSeparation 1** | 98 |
| `modalTableauGen` | FiveSimplification 9, TDriver 5, S5Simplification 5, BDriver 5, LoopChecking 4, FrameSoundness 3, GenericDriver 1 | 32 |
| `modalHintikkaSetGen` | FrameCompleteness 36, CompletenessLoop 8, LoopChecking 7, S5Simplification 5, Completeness 5, TDriver 3, BDriver 2, GenericDriver 1 | 67 |
| `ModalTableauResult` | LoopChecking 15, FiveSimplification 6, **CslibTests/S4LoopGuardRegression 2**, TDriver 2, S5Simplification 2, FrameCompleteness 2, BDriver 2, CompletenessLoop 1 | 32 |

### 1.2 The remaining nine exports (K-specific, for completeness)

| Symbol | Refs | Notable |
|---|---|---|
| `modalStepBranch` | 60 | CompletenessLoop 23, FmpMeasure 21 — the largest `unfold`-shape dependency in the subsystem |
| `modalExpandBranches` | 14 | Soundness 6, CompletenessLoop 6 |
| `modalTableau` | 18 | — |
| `modalHintikkaSet` | 25 | Completeness 12 |
| `modalFuel` | 54 | FrameCompleteness 29 |
| `modalStepBranch_eq`, `modalExpandBranches_eq`, `modalTableau_eq`, `modalHintikkaSet_eq` | — | the four existing K bridges (see §1.4) |

### 1.3 Import topology

Only **four** files import `Saturation.lean` directly — `Soundness.lean`, `SoundnessStep.lean`,
`FmpMeasure.lean`, `Completeness.lean` — but everything else reaches it transitively. Saturation
itself imports only `Closure` and `Rules`. Consequence: **any change to `Saturation.lean` forces a
rebuild of the entire Modal/Tableau subsystem** (measured: 52 s warm, §6).

### 1.4 Bridge census: `rfl` vs proved — the load-bearing audit output

The task description names six `rfl` bridges. The measured count is **sixteen**.

**True `:= rfl` (break if the generic ladder's definitional shape changes):**

| Bridge | File |
|---|---|
| `modalStepBranchT_eq`, `modalExpandBranchesT_eq`, `modalTableauT_eq` | TDriver.lean |
| `modalStepBranchB_eq`, `modalExpandBranchesB_eq`\*, `modalTableauB_eq`\* | BDriver.lean |
| `modalStepBranchS5_eq`, `modalExpandBranchesS5_eq`, `modalTableauS5_eq`\* | S5Simplification.lean |
| `modalStepBranchFive_eq`, `modalExpandBranchesFive_eq`, `modalTableauFive_eq`\* | FiveSimplification.lean |
| `modalStepBranchKb5_eq`, `modalExpandBranchesKb5_eq`, `modalTableauKb5_eq`\* | FiveSimplification.lean |
| `modalStepBranchKb5''_eq`, `modalExpandBranchesKb5''_eq`, `modalTableauKb5''_eq`\* | FiveSimplification.lean |
| `modalTableauKb5_eq_modalTableauFive` | FiveSimplification.lean |
| `modalStepBranch_eq`, `modalHintikkaSet_eq` | Saturation.lean |

(\* = one of the six named in the task description. Total `rfl` bridges touching the generic
ladder: 19 rows above, of which 16 are driver bridges and 3 are Saturation-internal or
cross-driver.)

**Proved, not `rfl`:**

| Bridge | File | Proof |
|---|---|---|
| `modalExpandBranches_eq` | Saturation.lean | induction on `fuel` + inner induction on the worklist |
| `modalTableau_eq` | Saturation.lean | `simp only` + `modalExpandBranches_eq` |
| `hintikka_congr` | S5Simplification.lean | tactic proof |
| `hintikka_congr_S4` | LoopChecking.lean | tactic proof |

**Non-`rfl` unkeyed S4 line**: `modalStepBranchS4`, `modalExpandBranchesS4` and `modalTableauS4`
(`LoopChecking.lean`) are *defined as* direct instantiations of the generic ladder, so they need no
bridge at all. This is the existence proof, cited in the decision record, that the generic ladder
already handles S4-with-guard — the Keyed fork exists only for the missing state slot.

### 1.5 Audit verdict

The additive constraint is sound and sufficient. **Nothing in this task edits, re-orders, or
re-attributes any existing declaration**, so all 19 `rfl` bridges and all 4 proved bridges are
green by construction — and this was confirmed empirically, not merely argued (§6).

---

## 2. Reuse Check (CSLib reuse-first, mandatory)

| Candidate | Checked | Verdict |
|---|---|---|
| Existing state-threading abstraction in `Cslib.Foundations.*` | `lean_local_search` + grep | **None.** No `RuleApplySt`, no state-monad-flavoured driver abstraction anywhere in the repo. |
| An existing `StateM`/`StateT`-based formulation | grep over `Cslib/Logics/Modal/` | **Not used.** The subsystem is deliberately monad-free and computable; introducing `StateM` here would change the elaborated term shape of every downstream `unfold`. **Do not do this.** |
| `List.findSome?` / `Option.map` commutation lemma | Loogle (`List.findSome? (fun x => Option.map _ _) _ = Option.map _ (List.findSome? _ _)`) → 0 hits; `lean_local_search "List.findSome?_"` → 0 hits | **Does not exist.** Must be added (§5.1). |
| `Support/Accessibility.lean`, `Support/KnownWorlds.lean` | read | **Not relevant here** and correctly *not* imported: `Saturation.lean` imports only `Closure` and `Rules`, and this task adds no import. No re-derivation is introduced. |
| A third `Support/` module for the new helper | considered | **Rejected**, consistent with the standing decision that two Support modules is the final shape. The helper has exactly one consumer, in the same file. |

**No new abstraction is recommended beyond the one the decision record already accepted.**

---

## 3. Correction: `RuleApply = RuleApplySt Unit` is not a definitional equality

The task description and the decision record both write `RuleApply = RuleApplySt Unit`. Taken
literally as a type-level defeq this is **false and unimplementable**:

```
RuleApply Atom      = SF → List SF → Accessibility → RuleResult × Accessibility
RuleApplySt Atom σ  = SF → List SF → Accessibility → σ → RuleResult × Accessibility × σ
```

At `σ := Unit` the second still has an extra `Unit →` argument and an extra `× Unit` component.
`Unit → X` is not defeq to `X`, and `X × Unit` is not defeq to `X`. Furthermore, making `RuleApply`
*be* `RuleApplySt Unit` would require editing the existing `RuleApply` declaration, which the
additive constraint forbids and which would break the 19 `rfl` bridges.

**The correct reading**, which the decision record's own §5 text already uses ("`modalStepBranchGen
apply = modalStepBranchGenSt (liftRuleApply apply)` projected at `σ := Unit`"), is an explicit
embedding plus proved bridges. This is what was implemented and verified. The planner must state
the ladder's relationship as *bridged*, never as *definitional*.

---

## 4. Recommended Implementation (verified)

Six new declarations plus three bridge theorems, inserted immediately before
`end Cslib.Logic.Modal.Tableau` in `Saturation.lean`. Verbatim verified source:
`specs/562_tableau_ruleapplyst_additive_introduction/artifacts/st-ladder-verified.lean`.

### 4.1 Design decisions and their justification

**(a) Argument order `RuleApplySt (Atom) [insts] (σ)`.** Matches the decision record's proposed
signature and keeps `RuleApplySt Atom Unit` reading as "`RuleApply Atom`, state-threaded".
`@[nolint unusedArguments]` is required, exactly as on `RuleApply`.

**(b) `σ` is threaded per-branch, as `sts : List σ` parallel to `accs`.** This is forced by the
eventual consumer: `modalExpandBranchesS4Keyed` carries `keyss : List (List (WorldIndex × Finset
(Sign × Proposition Atom)))` parallel to `accs`, and splits propagate one `keys'` to every child
via `List.replicate newBs.length keys'`. A single global `σ` would not fit and would have to be
redesigned at step 4. The `St` loop replicates this shape declaration-for-declaration.

**(c) The state from a `.notApplicable` probe is discarded.** `modalStepBranchGenSt` calls
`apply sf b acc st` inside `b.findSome?`, so failed probes' states are dropped, exactly as failed
probes' `newAcc` is dropped today. This matches `modalStepBranchS4Keyed`, which computes `keys'`
before matching on `result` and discards it in the `.notApplicable` arm. **No behavioural
divergence is introduced.**

**(d) `modalTableauGenSt` takes an explicit `st0 : σ`.** Required by the S4 Keyed entry point,
which seeds `keys := [(0, ∅)]` (not `[]` — see `modalTableauS4Keyed`'s docstring on the
`keysTotal` correction). At `σ := Unit`, `st0 = ()`.

**(e) The loop-level bridge instantiates the state list as `accs.map fun _ => ()`, not
`List.replicate accs.length ()`.** This is the load-bearing choice that makes the induction go
through with **no side hypothesis at all**. The `.map` form commutes through the three `++`
appends and the `List.replicate` the loop performs (`List.map_append`, `List.map_replicate`,
`List.map_cons`), so the invariant "the state list is the accessibility list mapped to units" is
preserved definitionally by `simpa`. A `List.replicate`-based statement would need an explicit
`sts.length = accs.length` hypothesis threaded through both the pending and done lists.

### 4.2 Bridge statements (all verified)

```lean
theorem modalStepBranchGen_eq_St (apply : RuleApply Atom) (b expanded : …) (acc : Accessibility) :
    modalStepBranchGenSt (liftRuleApply apply) b expanded acc () =
      (modalStepBranchGen apply b expanded acc).map (fun x => (x.1, x.2.1, x.2.2, ()))

theorem modalExpandBranchesGen_eq_St (apply : RuleApply Atom) (branches expandedSets …)
    (accs : List Accessibility) (fuel : Nat) :
    modalExpandBranchesGen apply branches expandedSets accs fuel =
      modalExpandBranchesGenSt (liftRuleApply apply) branches expandedSets accs
        (accs.map fun _ => ()) fuel

theorem modalTableauGen_eq_St (apply : RuleApply Atom) (φ : Proposition Atom) :
    modalTableauGen apply φ = modalTableauGenSt (liftRuleApply apply) () φ
```

The task description names only `modalExpandBranchesGen_eq_St`. The step-level bridge is a
prerequisite (the loop bridge's `cons` case rewrites by it) and the entry-point bridge is a
two-line corollary; recommend landing all three.

---

## 5. Proof-Engineering Findings

### 5.1 A new `findSome?`/`Option.map` commutation lemma is required

The step-level bridge cannot be proved by induction on the branch `b`: `apply sf b acc` closes over
the **whole** branch, not the tail, so the induction hypothesis is about the wrong function. (This
was attempted and failed; the goal state confirms the mismatch.) The working route factors the
`Option.map` out of the `findSome?` first:

```lean
theorem findSome?_map_comm {α β γ : Type*} (f : α → Option β) (g : β → γ) (l : List α) :
    l.findSome? (fun x => (f x).map g) = (l.findSome? f).map g := by
  induction l with
  | nil => simp
  | cons a t ih => cases h : f a <;> simp [h, ih]
```

Verified absent from Mathlib (Loogle, 0 hits) and from the project (`lean_local_search`, 0 hits).

**Placement**: it lands in the `Cslib.Logic.Modal.Tableau` namespace, which is a mild organisation
smell for a general `List` fact. Three options, in recommended order:
1. Keep it where it is with a docstring saying it is a local helper for the step bridge. Zero new
   imports, zero new modules, minimal surface. **Recommended** — this is an additive-only task.
2. Declare it `private`. Rejected: `private` is the exact import-reachability failure the Support
   extraction was created to fix, and a future `St`-ladder consumer outside `Saturation.lean` will
   want it.
3. Put it in the `List` namespace / a Support module. Rejected for this task: `Saturation.lean`
   imports only `Closure` and `Rules`, so a Support module is unreachable without an import
   change, which is not additive.

### 5.2 The `fuel = 0` case is module-position-sensitive

`modalExpandBranchesGen` and `modalExpandBranchesGenSt` have byte-identical `fuel = 0` bodies, but
each `def` generates its **own auxiliary matcher**. Consequently:

- **Inside `Saturation.lean`** (the recommended placement), Lean reuses the existing matcher and
  `simp only [modalExpandBranchesGen, modalExpandBranchesGenSt]` **closes the goal outright**.
- **In a separate module**, the two matchers are distinct constants that *print identically*, so
  `simp only` leaves an apparently-reflexive goal that `rfl` refuses. The fix is an explicit
  `cases hf : (branches.zip accs).findSome? (fun x => if isModalClosed x.fst = true then none else
  some (x.fst, x.snd))` followed by `rfl` in each arm.

Both variants are recorded in the artifacts directory (`st-ladder-verified.lean` is the in-file
form; `st_probe.lean` is the separate-module form). **The implementer will hit a confusing
"unsolved goals: X = X" if they develop in a scratch module and paste in without re-checking.**
This is the single most likely source of wasted time in the task.

### 5.3 Everything else transports from `modalExpandBranches_eq`

The loop bridge's skeleton — `induction fuel generalizing …`, a `suffices key : ∀ pending …`
inner statement over `processNext`, then `induction pending` with `cases` on `pendingExp` and
`pendingAccs` — is `modalExpandBranches_eq`'s proof at a different pair, exactly as the decision
record predicted. Two deltas: the `cons` case rewrites by `modalStepBranchGen_eq_St` (instead of a
`rfl` `show`) and then `cases` on the `Option`, and each recursive appeal closes with `simpa`
rather than `exact` because the `.map`-of-units has to be pushed through the `++`/`replicate`.

---

## 6. Verification — measured, not asserted

The complete implementation was inserted into `Saturation.lean`, the full pipeline was run, and
the file was then restored (`git diff Cslib/Logics/Modal/Tableau/Saturation.lean` is empty).

| Gate | Baseline (recorded) | With the `St` ladder | Verdict |
|---|---|---|---|
| `lake build Cslib` | green, 3313 jobs | **green, 3313 jobs** | PASS, identical |
| Modal/Tableau sorry census | exactly 1 (`FrameSoundness.lean:1227`) | **exactly 1**, same site | PASS |
| New `axiom` declarations | 0 | **0** | PASS |
| Bridge axiom dependencies | — | `propext`, `Quot.sound` only (no `Classical.choice`, no `sorryAx`) | PASS |
| `lake exe checkInitImports` | exit 0 | **exit 0** | PASS |
| `lake exe lint-style` | exit 0 | **exit 0** | PASS |
| `lake lint` | 145 findings | **145 findings, `diff` empty** | PASS, zero delta |
| `lake lint` findings in `Saturation.lean` | 0 | **0** | PASS |
| `lake shake --add-public --keep-implied --keep-prefix` | exit 1, 9 findings, none in Modal/Tableau | **exit 1, 9 findings, none in Modal/Tableau** | PASS (gate on the count + absence, per the description) |
| `lake test` (incl. `S4LoopGuardRegression`, `ModalFrameSeparation`) | — | **exit 0**, 9378 jobs | PASS |
| Full downstream rebuild time | — | **52 s** warm | — |

Note on `lake lint`: it exits **1** at baseline (145 pre-existing `unusedArguments` findings across
the repo, including 6 in `FrameSoundness.lean`). Gate on the **delta**, not on exit 0. The
recorded baseline correctly says only `checkInitImports` and `lint-style` exit 0.

---

## 7. Residual Work for the Implementer

The verified artifact is complete as *code*, but two things were deliberately left minimal:

1. **Docstrings are placeholders.** `Saturation.lean`'s existing declarations carry long
   explanatory docstrings (the `modalStepBranch` / `modalExpandBranches` pair each document why the
   original definition is retained verbatim). The new declarations need docstrings of comparable
   depth: what `σ` is for, why the state is per-branch, why `RuleApply` is *bridged into* rather
   than *equal to* `RuleApplySt Unit` (§3), and a forward pointer that `modalExpandBranchesS4Keyed`
   is the intended first consumer. `docBlame` passes on the placeholders, so this is a quality
   obligation, not a lint one.
2. **A module-docstring `## Main Definitions` entry.** `Saturation.lean`'s header lists
   `modalHintikkaSetGen` explicitly; the `St` ladder should be listed the same way.

Neither affects verification. Everything else is done and machine-checked.

---

## 8. Explicit Non-Scope Boundaries

Confirmed NOT started, per the task description:

- No `modalExpandBranchesS4Keyed` re-expression as `modalExpandBranchesGenSt` (step 4).
- No retirement of the `keys'` double derivation at `modalStepBranchS4Keyed` (step 5).
- No retirement of `modalStepBranchS4Keyed` in favour of the ordered stepper (step 6).
- No `S4LoopInv.outDegEq` removal (owned by the migration task).
- No `modalHintikkaSetGenSt`. Recommended **against** for now: `modalHintikkaSetGen` takes the
  state baked into `apply` (`modalHintikkaSetGen (modalApplyOneS4Keyed φ₀ keys)` is the live
  pattern) and threads nothing, so a `St` variant would have zero consumers today. Add it in the
  migration task if and only if it is needed.
- No box-plus key enrichment (separate task).
- `Rules.lean` and `Branch.lean` untouched, as required.

---

## 9. Zero-Debt Compliance

No recommendation in this report introduces a `sorry`, an `axiom`, or a vacuous definition. The
entire recommended change was compiled sorry-free and axiom-free before this report was written.
There is no `[BLOCKED]` condition and no deferral.

---

## Artifacts

| Path | Contents |
|---|---|
| `specs/562_tableau_ruleapplyst_additive_introduction/artifacts/st-ladder-verified.lean` | The exact block verified in-file against `Saturation.lean`. Paste-ready modulo docstrings (§7). |
| `specs/562_tableau_ruleapplyst_additive_introduction/artifacts/st_probe.lean` | Standalone-module variant (imports `Saturation`), showing the `fuel = 0` case's separate-module form (§5.2) and the `#print axioms` checks. |
