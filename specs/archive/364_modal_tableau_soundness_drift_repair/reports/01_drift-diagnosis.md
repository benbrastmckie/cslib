# Modal.Tableau.Soundness — Mathlib/Toolchain Drift Diagnosis

**Target file:** `Cslib/Logics/Modal/Tableau/Soundness.lean` (947 lines)
**Toolchain:** `leanprover/lean4:v4.31.0`
**Status at diagnosis:** 77 build errors (pre-existing drift; the file is sorry-free but
broke under a Lean/Mathlib bump). All other originally-failing CSLib modules have been repaired.

This file defeated three single-pass repair agents — each overflowed its context because
`lean_goal` here returns very large hypothesis contexts (~1 KB per call) and the file needs
far more than ~40 such probes. **Fix it in CHUNKS, committing after each cluster**, so no single
pass needs to hold the whole file. Do NOT call `lean_diagnostic_messages` (it hangs in this
repo); use `lean_goal` + scoped `lake build Cslib.Logics.Modal.Tableau.Soundness` only, and
read the file in ≤120-line slices.

The 77 errors are inflated by cascades from a smaller number of ROOT failures, grouped into
the families below. Fixing the roots should collapse most downstream errors.

## Family 1 — `cases X.sign` no longer substitutes the `isPos` hypothesis

Sites: lines ~99, ~124, ~511, and similar.

Pattern:
```lean
(by cases sf.sign with
    | pos => rfl
    | neg => simp [Sign.isPos] at hpos)   -- goal becomes `Sign.neg = Sign.pos`; FAILS
```
Confirmed via `lean_goal` at line 99: the goal is `⊢ Sign.neg = Sign.pos` but the hypothesis
stays `hpos : sf.sign.isPos = true` (NOT rewritten to `Sign.neg.isPos`). Under the new
toolchain `cases X.sign` no longer reverts/substitutes the dependent `isPos` hypothesis, so
`simp [Sign.isPos] at hpos` can't reduce it to `False`.

`Sign.isPos` is `def isPos : Sign → Bool | pos => true | neg => false`
(`Cslib/Foundations/Logic/Tableau/Sign.lean:76`); there is no characterization lemma.

**Fix idiom** (replace each such block): use the equation form so the hypothesis is rewritten:
```lean
(by cases h : sf.sign <;> simp_all [Sign.isPos])
```
or, where the goal is to *derive* `False` from the isPos hypothesis in the neg case:
```lean
| neg => rw [h] at hpos; simp [Sign.isPos] at hpos   -- after `cases h : sf.sign`
```
Adjust per-site to whether the block proves `X.sign = .pos` or derives a contradiction.

## Family 2 — `simp only [Satisfies] at h` ordering / no-op

Sites: lines ~100, ~218, ~261, ~287, ~306, ~336, ~363, and others.

`Modal.Satisfies` (`Cslib/Logics/Modal/Basic.lean:145`) is the recursive def
`.atom→v`, `.bot→False`, `.imp→(→)`, `.box→∀`. `simp only [Satisfies]` only fires when the
formula head is a CONSTRUCTOR. Two sub-cases:
- **No-op (e.g. line 100):** `hsat : Satisfies m _ sf.formula` with `sf.formula` still a
  variable. The unfold must come AFTER the `rw [hformbot]` that turns the formula into `⊥`.
  **Fix:** reorder — do `rw [hformbot] at hsat` first, then `simp only [Satisfies] at hsat`
  (yielding `hsat : False`), then `exact hsat`.
- **Negation:** for `¬φ`/`◇φ` use the provided lemmas `Satisfies.neg_iff`,
  `Satisfies.diamond_iff` (Modal/Basic.lean:152/156) and/or add `Proposition.neg_def`
  (the `@[simp]` lemma used in the sibling `Modal/Denotation.lean` repair) so `¬φ` reduces to
  `.imp φ .bot` before `simp only [Satisfies]`.

Many Family-2 errors are DOWNSTREAM of Family 1/3 (a failed earlier tactic leaves `hsat`
malformed). Re-check counts after fixing roots.

## Family 3 — `simp [tryAllPropRules, …] at hsf` then `obtain ⟨⟨hnewBs,_⟩,hnewAcc⟩ := hsf`

Sites: lines ~229, ~275, ~302, ~334, ~361 (inside `modalStepBranch_preserves_sat`, the core
semantic-preservation theorem). These produce the ~60 `Unknown identifier hnewBs` errors plus
`cases failed` / `unsolved goals` / `No goals` cascades — ALL because the `obtain` fails to
bind `hnewBs`, so every later `subst hnewBs` references an unbound name.

Root: `simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?, modalImpOf?,
modalNegOf?, …] at hsf` no longer normalizes `hsf` (an equation
`modalApplyOne … = some (newBs, newExps, newAcc)`) to the nested-conjunction equality shape
`((newBs = …) ∧ _) ∧ (newAcc = …)` that the `obtain ⟨⟨hnewBs,_⟩,hnewAcc⟩` pattern expects.
The connective recognizers (`modalNegOf?`/`modalImpOf?`/`modalOrOf?`) and/or the
`Option.some.injEq`/`Prod.mk.injEq` normalization drifted.

**Fix procedure (per site, requires `lean_goal` placed immediately BEFORE the `obtain`):**
1. Inspect the post-`simp` shape of `hsf`.
2. Adjust either the simp lemma set (add the missing `*.injEq` / recognizer-unfold lemmas) or
   the `obtain` pattern so it binds `newBs`/`newAcc` again.
3. The corrected idiom should then transcribe to all five parallel sites (box / negPos /
   orPos / impPos-with-`a2=⊥` / impPos-general). Commit after each.

## Family 4 — `LawfulBEq.eq_of_beq` type mismatch / failed instance synthesis

Sites: lines ~126 (and the `rw`/`absurd` at ~129, ~131 that depend on its output).

`have hformfeq : sf_neg.formula = sf.formula := LawfulBEq.eq_of_beq hformEq` fails to
synthesize the `LawfulBEq (Proposition Atom)` instance and/or `hformEq`'s `==` shape changed.
**Fix:** find the current decidable-eq / `LawfulBEq` route for `Proposition Atom`
(`lean_local_search`/`lean_hover_info` on `eq_of_beq`, `beq_iff_eq`); likely
`by simpa using hformEq` or `(beq_iff_eq …).mp hformEq` works once the instance is in scope.

## Recommended order
1. Fix the self-contained closed-branch lemma cluster first (lines ~80–132): Families 1, 2, 4.
   Build + commit.
2. Fix `modalStepBranch_preserves_sat` Family 3 sites one constructor-case at a time (box →
   negPos → orPos → impPos×2), building + committing after each. Family 2 negation unfolds
   resolve alongside.
3. Handle the F-side (neg-sign) cases later in the file (~400–700), same families.
4. Final: `lake build Cslib.Logics.Modal.Tableau.Soundness` clean; `lake exe lint-style`;
   confirm zero `sorry` / zero new axioms with `#print axioms`.

## Constraints
Zero `sorry`, zero new axioms, no `admit`, no vacuous placeholders. Preserve all theorem
statements. This is faithful drift repair, not redesign.
