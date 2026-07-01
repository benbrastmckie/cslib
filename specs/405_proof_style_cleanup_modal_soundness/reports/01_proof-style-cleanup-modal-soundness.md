# Research Report: Proof-Style Cleanup for Modal Tableau Soundness (Task 405)

- **Task**: 405 — Simplify proof machinery in the task-402 modal tableau soundness redesign
- **Session**: sess_1782924983_6bcecb_405
- **Target file**: `Cslib/Logics/Modal/Tableau/Soundness.lean`
- **Scope**: Readability/robustness only. No statement/signature changes. Zero sorry, full build green, lint-style pass.
- **Baseline**: task 404 is COMPLETED; the file builds green (`lake build Cslib.Logics.Modal.Tableau.Soundness` → 493 jobs, success). All candidate edits below were applied, verified green with a scoped build, then reverted (file is settled at baseline).

## Summary of Findings

Two named targets, both simplifiable with **verified** before/after tactic blocks:

1. `modalApplyOne_fresh` (lines 87–104): replace the `unfold + extract_lets + repeat' first | … | split` followed by the `all_goals first | … | (apply_ite/ite_self)` cleanup with a structured `split`-based proof that routes each rule arm to its minimal closing tactic. **Verified green.**
2. `modalExpandBranches_closed_unsat` (lines 165–321), the `hnewExpLen` sub-block (lines 249–267): merge the three near-identical `cases result` arms (`linear`/`branching`/`persistent`) into a single `| _ =>` arm. **Verified green.**

Plus one **linter-authoritative** robustness fix:

3. Add `omit [Hashable Atom] in` before `modalApplyOne_fresh`. The baseline build emits an `unusedSectionVars` warning at `Soundness.lean:87` naming exactly `[Hashable Atom]` and suggesting this exact fix.

A fourth item (the three `hunsat_*` Forall₂ take/drop extraction blocks, lines 289–312) was investigated but is **not recommended** for aggressive rewriting — see "Investigated, not recommended".

---

## Target 1: `modalApplyOne_fresh` (lines 87–104)

### Current proof (baseline)

```lean
  unfold modalApplyOne
  extract_lets w propResult
  repeat' first
    | exact Or.inl rfl
    | exact Or.inr ⟨_, _, rfl, rfl⟩
    | split
  -- remaining goals are acc-unchanged arms whose nested `if` has `acc` on both sides
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr ⟨_, _, rfl, rfl⟩
    | (left; simp only [apply_ite Prod.snd, ite_self])
```

### Why it is hard to read / fragile

- `repeat' first | … | split` interleaves goal-closing and case-splitting in one opaque loop; a reader cannot tell which alternative fires on which rule arm.
- It requires a **second** `all_goals` cleanup pass for the residual goals the loop could not close, duplicating the `Or.inl rfl` / `Or.inr …` alternatives across two blocks.
- `extract_lets w propResult` names only the first two let-binders positionally; the rest are extracted but left inaccessible, so the explicit names carry no real information.

### Goal structure (established via `lean_goal` at line 96)

After `unfold; extract_lets`, `split` on the outer `if propResult.isApplicable` gives:
- `isTrue` → propositional rule fired, `(propResult, acc)`; left disjunct by `rfl`.
- `isFalse` → the modal-rule `match`, which `split` breaks into 5 arms:
  - `h_1` boxPos `T□`: `(if newForms.isEmpty then (.notApplicable, acc) else (.persistent _, acc)).snd = acc` — accessibility unchanged, guarded by an `if` **hidden under a `have`**.
  - `h_2` diamondPos `T◇`: `.linear (witness :: boxProps ++ diaNegProps)`, snd `= acc.addEdge …` — **fresh edge** → right disjunct.
  - `h_3` boxNeg `F□`: fresh edge → right disjunct.
  - `h_4` diamondNeg `F◇`: `if …`-guarded, accessibility unchanged (like `h_1`).
  - `h_5` `.notApplicable`: `(.notApplicable, acc)` → left disjunct by `rfl`.

Key subtlety (drives the tactic choice): in the `h_1`/`h_4` arms the `if` sits under a `have newForms := …;` binder, so **`split` cannot see it** ("Could not split an `if` or `match`"). The residual `(if … ).snd = acc` must be discharged with `simp only [apply_ite Prod.snd, ite_self]` (push `Prod.snd` through the `if`, then both branches are `acc` so `ite_self` closes). This is why the original needed the separate cleanup pass — and why a naive `split <;> rfl` fails.

### Recommended replacement (VERIFIED GREEN)

```lean
  unfold modalApplyOne
  extract_lets
  split
  · exact Or.inl rfl
  · split <;>
      first
        | exact Or.inl rfl
        | exact Or.inr ⟨_, _, rfl, rfl⟩
        | (left; simp only [apply_ite Prod.snd, ite_self])
```

Optionally prepend a short comment (kept it in the tested edit):

```lean
  -- `modalApplyOne` first tries propositional rules (accessibility unchanged), then dispatches
  -- on the modal rule. Split the outer `if` and the rule `match`; the two existential arms
  -- (◇⁺, □⁻) add a fresh edge (right disjunct), every other arm leaves `acc` untouched (left).
```

### Why this is better

- **One split per real case distinction** (outer `if`, then the rule `match`), mirroring the definition's own structure.
- The `first | … | … | …` is **order-independent across the 5 match arms** — reordering `modalApplyOne`'s arms will not break it (unlike an explicit `· … · …` per-arm script).
- Each `first` alternative runs on exactly the arms it fits, so `simp only [apply_ite Prod.snd, ite_self]` fires **only** on the `if`-guarded arms where both lemmas are actually used → **no `unusedSimpArgs` warning**.
- `extract_lets` (no positional names) is retained deliberately: it lifts the `have witness := …;` / `have newForms := …;` binders so the `Or.inr ⟨_, _, rfl, rfl⟩` witness and `rfl` can reduce. **Do not drop `extract_lets`** — without it the fresh-edge arms fail with an application type mismatch (verified: the `unfold; split` variant without `extract_lets` errors at the `Or.inr` step).

### Robustness add-on (VERIFIED by linter)

The baseline build reports:
```
Soundness.lean:87:8: automatically included section variable(s) unused … modalApplyOne_fresh:
  [Hashable Atom] … consider … omit [Hashable Atom] in theorem …
```
So add, immediately before `private lemma modalApplyOne_fresh`:
```lean
omit [Hashable Atom] in
```
This matches the pattern already used for `accFreshInv_append` and `hasEdge_addEdge_cases` in the same file (lines 61, 73), removing an existing warning. `[DecidableEq Atom]` is still used (via `propResult`/`boxPropagation`) and must **not** be omitted.

---

## Target 2: `modalExpandBranches_closed_unsat` — `hnewExpLen` block (lines 249–267)

### Current proof (baseline)

```lean
                cases result with
                | notApplicable => simp at hf
                | linear nf =>
                  split_ifs at hf
                  simp only [Option.some.injEq, Prod.mk.injEq] at hf
                  obtain ⟨rfl, rfl, _⟩ := hf; simp
                | branching bs =>
                  split_ifs at hf
                  simp only [Option.some.injEq, Prod.mk.injEq] at hf
                  obtain ⟨rfl, rfl, _⟩ := hf; simp [List.length_map]
                | persistent nf =>
                  split_ifs at hf
                  simp only [Option.some.injEq, Prod.mk.injEq] at hf
                  obtain ⟨rfl, rfl, _⟩ := hf; simp
```

### Recommended replacement (VERIFIED GREEN)

```lean
                -- Every applicable rule sets `newExps := List.replicate newBs.length e`,
                -- so the lengths agree; only `.notApplicable` is impossible here.
                cases result with
                | notApplicable => simp at hf
                | _ =>
                  split_ifs at hf
                  simp only [Option.some.injEq, Prod.mk.injEq] at hf
                  obtain ⟨rfl, rfl, _⟩ := hf; simp [List.length_map]
```

### Why this is better

- Collapses three verbatim-identical arm bodies (the only difference was `simp` vs `simp [List.length_map]`) into one `| _ =>` arm. Using `simp [List.length_map]` for the merged arm is safe: `List.length_map` is used by the `branching` goal and simply ignored by the others, and because the merged arm is one `simp` invocation the `unusedSimpArgs` linter does **not** fire (verified: build green, no new warnings).
- Net −8 lines; the intent ("all applicable rules produce equal-length `newExps`/`newBs`") is stated once in a comment rather than being re-derived three times.

Whole-file impact of Targets 1+2 together: `1 file changed, 15 insertions(+), 19 deletions(-)`, scoped build green, `grep sorry` = none, `lake exe lint-style` = clean for `Soundness.lean`.

---

## Investigated, not recommended (per-branch accs / Forall₂ extraction, lines 289–312)

The task mentions "the modalExpandBranches_closed_unsat per-branch accs/Forall2 reformulation". The three extraction blocks `hunsat_newBs_bt`, `hunsat_bt`, `hunsat_newBs` peel a `List.Forall₂` over triple-appends using `List.forall₂_drop`/`forall₂_take` + manual `drop_left`/`take_left`/`drop_left'`/`take_left'` rewrites keyed on the length hypotheses.

- **Reuse check (Mathlib `Mathlib/Data/List/Forall2.lean`)**: available lemmas are `forall₂_take`, `forall₂_drop`, `forall₂_take_append`, `forall₂_drop_append`, `rel_append`, `forall₂_iff_zip`, `forall₂_cons_{left,right}_iff`. There is **no** `forall₂_append_iff`/`forall₂_append_append` that splits a `Forall₂` over appends given a length hypothesis.
- `forall₂_drop_append l l₁ l₂ h : Forall₂ R (drop l₁.length l) l₂` splits by the length of the *right* list's first component. Substituting it still requires a `length_replicate`/`hdoneAccsLen` rewrite plus `drop_left` to normalize the left list, so it does **not** shorten the blocks meaningfully.
- **Optional** (only if a reviewer wants the three peels as one line): introduce a small `private` helper in this file
  ```lean
  private lemma forall₂_split_mid {R} {xs ys zs} {as bs cs}
      (h : List.Forall₂ R (xs ++ ys ++ zs) (as ++ bs ++ cs))
      (hx : as.length = xs.length) (hy : bs.length = ys.length) :
      List.Forall₂ R ys bs ∧ List.Forall₂ R zs cs
  ```
  and replace the three `have hunsat_*` blocks with one `obtain ⟨hunsat_newBs, hunsat_bt⟩ := forall₂_split_mid hunsat_all …`. This is a genuine readability win but **adds a declaration** (needs its own docstring per `docBlame`) and is a larger structural change; treat as lower priority / optional. Not verified in this session.

The `suffices key : …` inner-induction scaffold (lines 190–206) is inherent to the fuel + pending double induction and should be left as-is; its length is structural, not stylistic debt.

---

## Tactic Survey Results

- `grind` as a whole-proof replacement for `modalApplyOne_fresh`: **not evaluated to completion**. `lean_multi_attempt` could not test it cleanly because the target's multi-line `first | …` body left residual `|` tokens that produced spurious parse errors; a definitive test would require a full-block edit. The structured `split` version is preferred regardless: it is explicit, fast, and self-documenting, avoiding reliance on a heavy automation tactic for a purely structural case analysis.
- `split <;> rfl` for the acc-unchanged arms: **fails** — the guarding `if` is under a `have` binder, so `split` reports "Could not split". Must use `simp only [apply_ite Prod.snd, ite_self]` (as the recommended block does).
- `simp_all [apply_ite Prod.snd, ite_self]` after a single `split`: **fails** (leaves the `isFalse` match unsolved) and additionally triggers `unusedSimpArgs` warnings. Rejected.

## Verification Commands (for the implementation phase)

```bash
lake build Cslib.Logics.Modal.Tableau.Soundness       # scoped, expect green (was 493 jobs)
grep -nE '\bsorry\b|\badmit\b' Cslib/Logics/Modal/Tableau/Soundness.lean   # expect none
lake exe lint-style 2>&1 | grep Soundness.lean         # expect no output
lake build                                             # final full build
```

After adding `omit [Hashable Atom] in`, confirm the `Soundness.lean:87` `unusedSectionVars` warning is gone.

## Zero-Debt Compliance

All recommendations preserve statements/signatures, introduce no `sorry`, no `axiom`, and no vacuous definitions. Every recommended edit (Targets 1, 2, and the `omit`) was verified to build green via a scoped `lake build` before the file was reverted to its settled baseline.
