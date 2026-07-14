# Research Report: Task 462 — Dedup Case-Arms + Eliminate Private-Lemma Re-Derivation (Modal Tableau)

- **Task**: 462 (`vet_299_dedup_refactor_reuse`)
- **Type**: cslib (Lean 4 refactoring)
- **Session**: sess_1783922075_911857_462
- **HEAD**: e04a2894 (post task-461 omit-clause edits; line numbers below are current)
- **Scope**: Two non-blocking maintainability items from the task-299 vet. Build/lint currently green (per vet). Preserve zero sorry/axioms.

## Executive Summary

Both items are **feasible, low-risk, mechanical refactors** that preserve statements and proof
semantics (no new axioms, no sorry).

- **Item 1** (SoundnessStep.lean): ~22 near-verbatim leaf arms in the negative-implication
  α-rule family share a **fully uniform post-`subst` tail**. Extract **two helper lemmas**
  (positive-antecedent + negation-antecedent shape). Net ~150 lines removed; each arm shrinks
  from ~12 lines to ~4. The leading `simp [tryAllPropRules, …]` normalization is structurally
  forced per-constructor but textually identical and can optionally be wrapped in a local tactic
  macro.
- **Item 2** (CompletenessLoop.lean): Three local copies re-derive lemmas that are `private` in
  Completeness.lean / FmpMeasure.lean. **Two are exact copies** (clean deletions after removing
  `private`); **one flagged "worldBound" facet is NOT a private-blocked copy** — its base
  (`modalStepBranch_worldBound`) is already public and the local lemma is a legitimate
  generalization that should stay. A **bonus pair** of trivial helpers is also exactly duplicated
  and can be collapsed the same way.

**Critical correction to the task description**: The task says "mark those lemmas `protected`".
In Lean 4's module system, `protected` does **not** enable cross-module reuse — it only forces
qualified access after `open`. The mechanism that blocks reuse is `private` (non-export). Since
these files use `@[expose] public section`, the fix is to **remove the `private` keyword** (which
makes the lemma exported/public). Adding `protected` is an optional style choice, not the fix.

---

## Item 1 — Duplicated Leaf Case-Arms in `modalStepBranch_preserves_sat`

### Location and shape
`Cslib/Logics/Modal/Tableau/SoundnessStep.lean`, theorem `modalStepBranch_preserves_sat`
(now ~lines 179–1702). The duplicated arms live in the `sign = .neg`, `formula = .imp a c`
subtree — the **negative-implication α-rule** (`F(a→c)` decomposes to `T(a)` and `F(c)` on the
same branch). The code cases on the syntactic structure of `c` (atom/bot/imp/box) and of `a`
(atom/bot/box/imp, with `imp` further split on its consequent), producing one leaf arm per
concrete `(a,c)` constructor combination.

Measured duplication (grep on current HEAD):
- `18` arms with the **positive-antecedent** tail (`exact ⟨fun _ => hsa, …⟩` + `by_contra`
  `hsa`).
- `4` arms with the **negation-antecedent** variant (`a = imp a1 bot`, i.e. `¬a1`): pushes
  `⟨.neg, a1, lbl⟩` and uses `hna1 : ¬Satisfies … a1` instead of `hsa`.
- Total ≈ **22 arms** in this family (the vet's "~15" undercounts; it cited only the
  `c = imp c1 c2` / `c = box cb` sub-region 1402–1626).

### The uniform tail (positive-antecedent, all 18 identical modulo `A`, `C`)
```lean
simp only [Satisfies] at hneg
have hsa : Satisfies m (f lbl) A := by
  by_contra h; exact hneg (fun ha => absurd ha h)
have hnc : ¬Satisfies m (f lbl) C := fun hC => hneg (fun _ => hC)
refine ⟨[⟨.pos, A, lbl⟩, ⟨.neg, C, lbl⟩] ++ b,
  List.mem_cons_self, W, m, f, hacc, ?_⟩
intro sf' hmem'
simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
rcases hmem' with (rfl | rfl) | hmem_old
· exact ⟨fun _ => hsa, fun h => by simp at h⟩
· exact ⟨fun h => by simp at h, fun _ => hnc⟩
· exact hb sf' hmem_old
```
Preceding each arm (also identical text, 3 lines) is the constructor-specific normalization:
```lean
simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
  modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
  Option.some.injEq, Prod.mk.injEq] at hsf
obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
subst hnewBs hnewAcc
```

### Why the arms cannot be merged directly
The leading `simp … at hsf` reduces `modalApplyOne`/`tryAllPropRules`/`applyPropRule`, which are
defined by pattern-matching on the concrete constructors of `a` and `c`. The definitional
reduction genuinely differs per constructor, so the `cases` split and the per-arm simp are
structurally required. **However**, after `subst hnewBs hnewAcc` the goal is uniform:
```
⊢ ∃ b' ∈ [[⟨.pos, A, lbl⟩, ⟨.neg, C, lbl⟩] ++ b], branchSatisfiable b' acc
```
with `hacc`, `hb`, `hneg` in scope — so the **12-line tail is fully extractable**.

### Recommended concrete refactor

**Helper 1 (positive antecedent).** Add near the top of the theorem's supporting lemmas
(same namespace/section). `branchSatisfiable` is defined at SoundnessStep.lean:64 as
`∃ W m f, (acc respected) ∧ ∀ sf ∈ b, (pos→Sat) ∧ (neg→¬Sat)`; the helper reconstructs that
witness:
```lean
omit [DecidableEq Atom] [Hashable Atom] in   -- verify: branchSatisfiable/Satisfies use neither
private lemma negImp_alpha_preserved
    {A C : Proposition Atom} {lbl : WorldIndex}
    {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {acc : Accessibility}
    {W : Type v} {m : Model W Atom} {f : WorldIndex → W}
    (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b, (sf.sign = .pos → Satisfies m (f sf.label) sf.formula) ∧
                    (sf.sign = .neg → ¬Satisfies m (f sf.label) sf.formula))
    (hneg : ¬Satisfies m (f lbl) (Proposition.imp A C)) :
    branchSatisfiable.{v, u} ([⟨.pos, A, lbl⟩, ⟨.neg, C, lbl⟩] ++ b) acc := by
  simp only [Satisfies] at hneg
  have hsa : Satisfies m (f lbl) A := by by_contra h; exact hneg (fun ha => absurd ha h)
  have hnc : ¬Satisfies m (f lbl) C := fun hC => hneg (fun _ => hC)
  refine ⟨W, m, f, hacc, ?_⟩
  intro sf' hmem'
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
  rcases hmem' with (rfl | rfl) | hmem_old
  · exact ⟨fun _ => hsa, fun h => by simp at h⟩
  · exact ⟨fun h => by simp at h, fun _ => hnc⟩
  · exact hb sf' hmem_old
```
Each of the 18 arms then collapses to:
```lean
simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
  modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
  Option.some.injEq, Prod.mk.injEq] at hsf
obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
subst hnewBs hnewAcc
exact ⟨_, List.mem_cons_self, negImp_alpha_preserved hacc hb hneg⟩
```

**Helper 2 (negation antecedent, `a = imp a1 bot`).** Same body but pushes `⟨.neg, a1, lbl⟩`
and derives `hna1 : ¬Satisfies m (f lbl) a1`; conclusion
`branchSatisfiable ([⟨.neg, a1, lbl⟩, ⟨.neg, C, lbl⟩] ++ b) acc`. Collapses the 4 variant arms.

**Optional — collapse the identical `simp` skeleton.** The 3-line normalization is byte-identical
across all 22 arms (and appears ~66× across the whole theorem for other families). A local
`syntax`/`macro` tactic, e.g. `local macro "prop_step" : tactic => …`, or a `simp` set alias
would remove that repetition too. Lower priority than the tail extraction; do it only if it does
not perturb other families' arms.

### Universe-polymorphism note
The theorem is universe-annotated (`branchSatisfiable.{v, u}`, SoundnessStep.lean:187–189). The
helper must carry the same universe variables (`W : Type v`) so `exact` unifies. Use explicit
`.{v, u}` on `branchSatisfiable` in the helper conclusion as shown.

### Feasibility / risk (Item 1)
- **Feasibility: HIGH.** Pure proof-term factoring; statement unchanged; verified by `lake build`.
- **Risk: LOW.** Only risks are (a) getting the universe annotation right, (b) the `omit` clause
  matching what `branchSatisfiable`/`Satisfies`/`Model` actually use (the `unusedSectionVars`
  linter — silenced via `omit` per task 461 — will flag a wrong choice), (c) confirming Helper 2's
  exact `a1` decomposition matches the `imp a1 bot` arms. All caught at build time.
- **Estimated reduction**: ~264 lines of tail → 2 helpers (~24 lines) + 22 four-line calls
  (~88 lines) ≈ **150 lines removed**; more if the `simp` macro is added.
- **Zero-debt**: compliant — no sorry, no axiom, no vacuous defs.

---

## Item 2 — Private-Lemma Re-Derivation in CompletenessLoop.lean

### Import graph (blast radius)
```
Completeness.lean  ←  FmpMeasure.lean  ←  CompletenessLoop.lean  ←  (nobody)
```
`CompletenessLoop` is a leaf module. De-privatizing lemmas in Completeness/FmpMeasure exposes them
only to `CompletenessLoop`. Grep confirms **no other file references** these names and **no name
collisions** exist anywhere in `Cslib/`. Blast radius is minimal.

### Module-system mechanics (important)
All three files open with `@[expose] public section` (e.g. CompletenessLoop.lean:40). In the Lean
module system, declarations in a `public section` are exported **unless** marked `private`. So:
- **The fix is to delete the `private` keyword** on the base lemmas. They then become
  cross-module-reusable via the existing `public import`.
- `protected` is orthogonal (name-resolution only) and does **not** enable reuse — do not rely on
  it as the task text suggests.
- **Lemmas/theorems are safe to de-privatize regardless of proof body.** `@[expose]` affects
  `def` bodies only; proofs of `Prop`s are never part of the public interface (proof
  irrelevance), so a de-privatized lemma whose proof calls other `private` lemmas compiles fine.

### Clean wins (exact copies → remove `private` + delete local copy + repoint calls)

1. **`modalStepBranch_none_saturated`** — Completeness.lean:703 (`private lemma`).
   Local copy: `modalLoop_stepBranch_none_saturated`, CompletenessLoop.lean:107–131
   (**character-for-character identical** proof).
   - Remove `private` at Completeness.lean:703.
   - Delete CompletenessLoop.lean:107–131 (and its doc-comment 102–106).
   - Repoint ~5 call sites in CompletenessLoop (lines ~739, 746, 753, 763, 772):
     `modalLoop_stepBranch_none_saturated` → `modalStepBranch_none_saturated`.

2. **`modalStepBranch_eClosure`** — FmpMeasure.lean:2092 (`private lemma`).
   Local copy: `modalLoop_eClosure`, CompletenessLoop.lean:247–295 (**identical signature**,
   comment self-describes as "an exact copy … reproduced here since that declaration is not
   reusable across files").
   - Remove `private` at FmpMeasure.lean:2092.
   - Delete CompletenessLoop.lean:247–295 (and doc-comment ~245–246).
   - Repoint call site CompletenessLoop.lean:587 (`modalLoop_eClosure` → `modalStepBranch_eClosure`).

3. **Bonus — trivial duplicate pair** (not called out by the vet but same pattern):
   `modalSf_pos` (FmpMeasure.lean:2331) and `modalSf_one_imp_depth_zero` (FmpMeasure.lean:2339)
   are exactly duplicated as `modalLoopSf_pos` / `modalLoopSf_one_imp_depth_zero`
   (CompletenessLoop.lean:133–140+). De-privatize the FmpMeasure originals, delete the loop
   copies, repoint calls.
   - **docBlame caveat**: `modalSf_pos` has **no docstring**. A public declaration triggers the
     `docBlame` linter (weekly cron, not PR CI), so add a one-line docstring when de-privatizing.
     `modalSf_one_imp_depth_zero` already has one.

### NOT a clean win — leave as-is (correcting the task's "worldBound/bClosure" framing)

- **`modalMaxWorld_lt_worldBound_of_phiBound`** (CompletenessLoop.lean:160–192). Its base
  `modalStepBranch_worldBound` (FmpMeasure.lean:2377) is **already public** (no `private`). The
  local lemma is a deliberate **generalization** over an arbitrary potential term `Φ` (applies to
  the pre-step branch `b`, not just a step's output), so it is not eliminable by de-privatization.
  **Keep it.** The task's "worldBound" facet is therefore a non-issue for reuse.
- **`modalLoop_bClosure`** (CompletenessLoop.lean:195–244). Self-documented as mirroring
  `modalStepBranch_eClosure`'s case-split *shape* but "driven by `modalApplyOne_outputs_subset`
  instead" — a **different proof for a different statement** (branch-side vs expanded-set closure).
  No private base lemma proves this; de-privatizing eClosure does not remove it. **Keep it.**
  (A deeper refactor could try to share structure, but that is higher-risk and out of scope for a
  copy-elimination task.)

### Feasibility / risk (Item 2)
- **Feasibility: HIGH** for the two/three clean wins.
- **Risk: LOW.** Minimal blast radius, no collisions, module-system semantics well-understood.
  Only follow-ups: add a docstring to `modalSf_pos`; confirm the repointed call-site argument
  order matches (signatures are identical, so it will).
- **Zero-debt**: compliant.

---

## Verification Plan (for implementer)
Scoped builds after each item (fast path, in dependency order):
```
lake build Cslib.Logics.Modal.Tableau.SoundnessStep      # Item 1
lake build Cslib.Logics.Modal.Tableau.Completeness       # Item 2 step 1
lake build Cslib.Logics.Modal.Tableau.FmpMeasure         # Item 2 steps 2–3 (slow, ~3k lines)
lake build Cslib.Logics.Modal.Tableau.CompletenessLoop   # consumes all de-privatized lemmas
```
Then `lake exe checkInitImports`, `lake exe lint-style`, and (optional, cron-only) `lake lint`
to confirm docBlame on the newly-public `modalSf_pos`. Confirm zero sorry/axioms with
`lean_verify` on `modalStepBranch_preserves_sat` and `modalStep_preserves_invariant`.

## Suggested phase split (for planner)
1. **Phase 1 — Item 1 helpers** (SoundnessStep.lean only; isolated territory).
2. **Phase 2 — Item 2 de-privatization** (Completeness.lean + FmpMeasure.lean edits; disjoint
   files from Phase 1).
3. **Phase 3 — Item 2 copy deletion + repointing** (CompletenessLoop.lean; depends on Phase 2).
Phases 1 and 2 touch disjoint files and could run in parallel; Phase 3 depends on Phase 2.

## Territory / concurrency note
All target files are under `Cslib/Logics/Modal/Tableau/` — disjoint from task 317
(Propositional/Intuitionistic). No conflict expected. Work from current HEAD e04a2894.
