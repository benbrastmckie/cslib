# PR #648 Branch Analysis: feat/propositional-v2 vs upstream/main (post-#536)

## 1. Current State of feat/propositional-v2

The branch is based on commit `87c249da` (the merge base with upstream/main). It has 2 commits ahead:

1. `b041ae76` — feat(Logics/Propositional): five-primitive formula type with connective typeclasses
2. `6083b4ca` — feat(Logics/Propositional): add Bool semantics and minor attribution fixes

### Files Changed (6 total)

| File | Status | +/- | Description |
|------|--------|-----|-------------|
| `Cslib.lean` | Modified | +3 | Added imports for Connectives, Semantics.Basic, Semantics.Bool |
| `Cslib/Foundations/Logic/Connectives.lean` | **New** | +79 | Typeclass hierarchy: HasBot, HasImp, HasAnd, HasOr, PropositionalConnectives |
| `Cslib/Logics/Propositional/Defs.lean` | Modified | +67/-35 | Five-primitive Proposition type, constraint-free derived connectives |
| `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | Modified | +82/-70 | Renamed constructors (impl→imp, subscript→ASCII), removed type constraints |
| `Cslib/Logics/Propositional/Semantics/Basic.lean` | **New** | +64 | Valuation, Evaluate, Tautology (Prop-valued bivalent semantics) |
| `Cslib/Logics/Propositional/Semantics/Bool.lean` | **New** | +110 | BoolValuation, BoolEvaluate, bridge lemma, decidability |

## 2. What PR #536 Changed

PR #536 ("refactor: classical and intuitionistic inference systems") by @thomaskwaring merged on 2026-06-16 (commit `70c5bf58`). It modified 4 files:

| File | Status | +/- | Description |
|------|--------|-----|-------------|
| `Cslib.lean` | Modified | +1 | Added `NaturalDeduction.Theory` import |
| `Cslib/Logics/Propositional/Defs.lean` | Modified | +29/-42 | Refactored IsIntuitionistic/IsClassical to inference-system-based |
| `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | Modified | +1/-1 | Changed `MPL` to `MPL Atom` (explicit argument) |
| `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean` | **New** | +101 | Theory instances, derived rules, LEM, Pierce's law |

### Key Changes in #536

1. **IsIntuitionistic/IsClassical refactored**: Changed from theory-parameterized classes to inference-system-parameterized:
   - Old: `class IsIntuitionistic [Bot Atom] (T : Theory Atom)`
   - New: `class IsIntuitionistic (Atom : Type u) [Bot Atom] (S : Type*) [InferenceSystem S (Proposition Atom)]`

2. **New import**: `Defs.lean` now imports `Cslib.Foundations.Logic.InferenceSystem` instead of `Cslib.Init`

3. **Theory definitions explicit**: `MPL`, `IPL`, `CPL` now take explicit `(Atom : Type u)` parameter

4. **Theory.lean extracted**: Instances like `instIsIntuitionisticIPL`, `instIsClassicalCPL`, derived rules (`efqCtx`, `efqRule`, `contra`, `byContra`), and alternative axiom systems (`LEM`, `Pierce`) moved to a new file

5. **Removed from Defs.lean**: `isIntuitionisticIff`, `isClassicalIff`, `instIsIntuitionisticExtention`, `instIsClassicalExtention`, `instIsIntuitionisticIntuitionisticCompletion`, and all the old theory-parameterized infrastructure

## 3. Merge Conflicts

Running `git merge upstream/main` on feat/propositional-v2 produces **3 conflicts**:

### Conflict 1: `Cslib.lean` (trivial)

```
<<<<<<< HEAD
public import Cslib.Logics.Propositional.Semantics.Basic
public import Cslib.Logics.Propositional.Semantics.Bool
=======
public import Cslib.Logics.Propositional.NaturalDeduction.Theory
>>>>>>> upstream/main
```

**Resolution**: Keep all three imports (both Semantics files and Theory). Note: reviewers requested splitting Semantics to a follow-up PR, so if Semantics files are removed, only Theory needs adding.

### Conflict 2: `Cslib/Logics/Propositional/Defs.lean` — imports (trivial)

```
<<<<<<< HEAD
import Cslib.Init
public import Cslib.Foundations.Logic.Connectives
=======
public import Cslib.Foundations.Logic.InferenceSystem
>>>>>>> upstream/main
```

**Resolution**: Need both imports:
```
import Cslib.Init
public import Cslib.Foundations.Logic.Connectives
public import Cslib.Foundations.Logic.InferenceSystem
```

### Conflict 3: `Cslib/Logics/Propositional/Defs.lean` — Theory section (substantial)

The entire Theory section from `IPL` through the end of the file conflicts. feat/propositional-v2 has the old theory-parameterized `IsIntuitionistic`/`IsClassical` classes (with `[Bot Atom]` constraints removed because `bot` is now primitive). Upstream has the new inference-system-parameterized versions.

**Resolution requires**:
1. Adopt upstream's inference-system-based `IsIntuitionistic`/`IsClassical` classes (parameterized by `S : Type*` with `[InferenceSystem S (Proposition Atom)]`)
2. Remove `[Bot Atom]` constraints from `IPL`, `CPL`, etc. since `bot` is now a primitive constructor (no longer needs `[Bot Atom]`)
3. The old theory-parameterized helpers (`isIntuitionisticIff`, `instIsIntuitionisticExtention`, etc.) are gone in upstream — do NOT restore them
4. Keep feat/propositional-v2's `MPL` without explicit `Atom` parameter (since `bot` is primitive, `MPL` needs no constraints), OR adopt upstream's `MPL (Atom : Type u)` pattern — the latter is safer to match #536's convention

### Conflict 4: `NaturalDeduction/Basic.lean` — merged cleanly with one key issue

The auto-merge succeeded, but #536 reverted feat/propositional-v2's constructor renaming:
- #536 uses `implI`/`implE`/`andE₁`/`andE₂`/`orI₁`/`orI₂` (the original names)
- feat/propositional-v2 uses `impI`/`impE`/`andE1`/`andE2`/`orI1`/`orI2` (renamed)

The auto-merge accepted feat/propositional-v2's names since it was the more extensive change, but `Theory.lean` (from #536) uses `implI`/`implE`/`orI₁`/`orI₂` — so either:
- (a) Adopt #536's naming and revert the rename, OR
- (b) Keep feat/propositional-v2's naming and update `Theory.lean` to match

**Recommendation**: Option (a) — keep upstream's constructor names (`impl`, `implI`, `implE`, subscript elim/intro). The reviewers didn't request the rename, and consistency with the merged codebase is more important. The `imp` naming can be proposed separately if desired.

## 4. Bot Refactor Specifics

feat/propositional-v2 adds `bot` as a fifth primitive constructor to `Proposition`:

```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (x : Atom)
  | bot              -- NEW: primitive falsum
  | imp (a b : Proposition Atom)   -- renamed from impl
  | and (a b : Proposition Atom)
  | or (a b : Proposition Atom)
```

### Downstream changes required by primitive `bot`:

1. **Removed `instBotProposition`/`instInhabitedOfBot`**: Old `Bot` instance was `⟨.atom ⊥⟩` requiring `[Bot Atom]`. New `Bot` instance is `⟨.bot⟩` — no constraint needed.

2. **Derived connectives now constraint-free**:
   - `Proposition.neg : Proposition Atom → Proposition Atom := (Proposition.imp · .bot)` — no `[Bot Atom]`
   - `Proposition.top : Proposition Atom := .imp .bot .bot` — no `[Inhabited Atom]`
   - `Proposition.iff` added as `(A.imp B).and (B.imp A)` — new

3. **Substitution preserves `bot`**: `subst` maps `bot => .bot` instead of `bot => f ⊥`

4. **Typeclass instances registered**: `PropositionalConnectives`, `HasAnd`, `HasOr` instances

5. **Theory definitions lose `[Bot Atom]`**: `IPL`, `CPL` no longer need `[Bot Atom]` since `⊥` is `.bot` not `.atom ⊥`

6. **NaturalDeduction**: `derivationTop`, `derivableIn_top`, `derivable_iff_equiv_top` lose `[Inhabited Atom]` constraint

7. **Derivation constructors**: No `botE` constructor — bottom elimination is still a derived rule via the theory

### Reconciliation with #536:

The key tension: #536 keeps `[Bot Atom]` constraints on `IPL`, `CPL`, `IsIntuitionistic`, `IsClassical` because upstream still uses `.atom ⊥` for bottom. With primitive `bot`, these constraints should be removed. The reconciled version must:
- Use #536's `InferenceSystem`-parameterized `IsIntuitionistic`/`IsClassical`
- But remove the `[Bot Atom]` constraints since `⊥` is now `.bot`

## 5. Semantics Files

### `Semantics/Basic.lean` (64 lines)
- Defines `Valuation` (`Atom → Prop`), `Evaluate` (recursive), `Tautology`
- Five `@[simp]` lemmas for each constructor case
- Clean, self-contained, depends only on `Defs.lean`

### `Semantics/Bool.lean` (110 lines)
- Defines `BoolValuation`, `BoolEvaluate`
- Bridge lemma `BoolEvaluate_eq_iff`, negation form `BoolEvaluate_eq_false_iff`
- `Evaluate_eq_BoolEvaluate` and `instDecidableBoolEvaluate`

### Reviewer feedback on Semantics

**ctchou**: "I don't understand why we need both Semantics/Basic.lean and Semantics/Bool.lean. I think the latter alone is enough."

**thomaskwaring**: "Please split the semantics development into a separate PR." Also: "the right way to resolve the Bool/Prop issue is to define the interpretation in any (generalised) Heyting algebra — this captures both of those as well as non-classical versions."

**Recommendation**: Split Semantics to a follow-up PR as requested. This simplifies PR #648 to focus on the core bot-as-primitive refactor + Connectives.lean.

## 6. Reviewer Feedback Summary

### ctchou (CHANGES_REQUESTED)

1. **Likes adding `⊥` as primitive** — supports the core change
2. **Semantics duplication**: Wants only Bool.lean, not both
3. **German-language references**: "not helpful to refer to old papers from the 1930s, some of which are in German"
4. **Modern reference**: Recommends Avigad's *Mathematical Logic and Computation* (chapters 2-3)
5. **Coordinate with other PRs**: #607, #587, #536

### thomaskwaring (comment, not formal review)

1. **Philosophical pushback on primitive `bot`**:
   - "If `⊥` is included in minimal logic it behaves precisely like the atomic formulae, so why not represent it as such?"
   - "Minimal logic works perfectly well without `⊥`"
   - "`[Bot Atom]` assumptions where necessary is not a big deal"
   - "Adding an extra constructor makes all proofs more verbose"
   - "`⊤` being `a → a` for arbitrary formula is a feature not a bug"
   - Notes substitution argument but thinks non-bottom-preserving maps are sometimes useful

2. **Naming**: "citing CSLib's existing formula types as your own as-yet-unmerged work is not exactly convincing. Indeed the actually existing example (Modal) uses 'impl'."

3. **Semantics**: Split to separate PR. Recommends Heyting algebra approach.

4. **References**: Agrees with ctchou about English-language literature.

## 7. Build Status

The branch is in `mergeable_state: dirty` on GitHub, meaning it has merge conflicts with main (confirmed: conflicts in `Cslib.lean` and `Defs.lean`).

The branch cannot build as-is against upstream/main because:
1. Merge conflicts must be resolved first
2. After resolution, `Theory.lean` (from #536) uses `implI`/`implE` names that conflict with the branch's `impI`/`impE` rename
3. The `InferenceSystem`-parameterized `IsIntuitionistic`/`IsClassical` must be adapted to work with primitive `bot` (remove `[Bot Atom]` constraints)

## 8. German-Language References

### References with German titles on feat/propositional-v2:

**Defs.lean** (lines 43-44):
- `[Johansson1937]` — "Der Minimalkalkül, ein reduzierter intuitionistischer Formalismus"
- `[Gentzen1935]` — "Untersuchungen über das logische Schließen"

**Connectives.lean** (lines 37-38, 45):
- `[Johansson1937]` — same
- `[Wajsberg1938]` — "Untersuchungen über den Aussagenkalkül von A. Heyting"
- `[Gentzen1935]` — same

**NaturalDeduction/Basic.lean** (lines 58, 62-63):
- `[Johansson1937]` — same
- `[Gentzen1935]` — same

All citations have valid BibTeX keys in `references.bib`. The reviewer objection is about the German titles being unhelpful to readers, not about the references being wrong. The recommended fix is to replace them with ctchou's suggested reference (Avigad's *Mathematical Logic and Computation*) or other English-language sources.

Note: thomaskwaring acknowledges "the Gentzen paper is my bad, I read it in translation." The upstream `NaturalDeduction/Basic.lean` (post-#536) already replaced the German references with English ones (Prawitz, Troelstra & van Dalen, Sorensen & Urzyczyn).

## 9. Reconciliation Plan

### Step 1: Rebase or merge upstream/main into feat/propositional-v2

Resolve the 3 conflicts as described in Section 3.

### Step 2: Remove Semantics files from PR scope

Per reviewer request, delete `Semantics/Basic.lean` and `Semantics/Bool.lean` from the branch. Remove their imports from `Cslib.lean`. These go in a follow-up PR.

### Step 3: Reconcile constructor naming

**Two options**:
- **(a) Revert rename**: Keep upstream's `impl`/`implI`/`implE`/`andE₁`/`andE₂`/`orI₁`/`orI₂`. This avoids fighting the reviewers and keeps consistency with `Theory.lean` and Modal logic.
- **(b) Keep rename**: Update `Theory.lean` to use `imp`/`impI`/`impE`/`andE1`/`andE2`/`orI1`/`orI2`. Requires modifying a file authored by thomaskwaring.

**Recommendation**: Option (a). The `imp` rename is contentious and not core to the PR's value (adding primitive `bot`). It can be proposed separately.

### Step 4: Reconcile IsIntuitionistic/IsClassical

Adopt #536's inference-system-parameterized versions but remove `[Bot Atom]` constraints. The reconciled signatures:

```lean
class IsIntuitionistic (Atom : Type u) (S : Type*)
    [InferenceSystem S (Proposition Atom)] where
  efq (A : Proposition Atom) : S⇓(⊥ → A)

class IsClassical (Atom : Type u) (S : Type*)
    [InferenceSystem S (Proposition Atom)] where
  dne (A : Proposition Atom) : S⇓(¬¬A → A)
```

Note: No `[Bot Atom]` needed since `⊥` resolves to `.bot` via the primitive constructor, not via `[Bot Atom]` instance on `Atom`.

### Step 5: Reconcile Theory.lean

`Theory.lean` from #536 uses `[Bot Atom]` constraints and `implI`/`implE` naming. Must be updated:
- Remove `[Bot Atom]` from all signatures
- If keeping `impl` naming (Step 3a): no constructor changes needed
- If keeping `imp` naming (Step 3b): rename `implI`→`impI`, `implE`→`impE` throughout

### Step 6: Replace German references

Replace Johansson1937, Gentzen1935, Wajsberg1938 citations with:
- Avigad's *Mathematical Logic and Computation* (ctchou's suggestion)
- Keep Prawitz1965 and TroelstraVanDalen1988 (English, already in upstream's references)
- Keep Church1956 (English)

### Step 7: Address thomaskwaring's philosophical concerns

thomaskwaring's pushback on primitive `bot` is substantive. The response should:
1. Acknowledge the substitution trade-off (non-bottom-preserving maps)
2. Emphasize the constraint-elimination benefit (no more `[Bot Atom]` everywhere)
3. Note alignment with the literature (Bentzen2023, Trufas2024)
4. The fact that ctchou "likes the idea" provides support

### Step 8: Address Connectives.lean and PR #607

`Connectives.lean` overlaps with PR #607 (fmontesi's per-operator typeclass files). The PR body already notes this. The reconciliation strategy depends on #607's status — if it merges first, align with its structure; otherwise, proceed as-is.

## 10. File-by-File Change Summary

| File | Action | Priority | Notes |
|------|--------|----------|-------|
| `Cslib/Foundations/Logic/Connectives.lean` | Keep, update references | High | Replace German refs with English |
| `Cslib/Logics/Propositional/Defs.lean` | Merge conflict resolution | High | Adopt #536's InferenceSystem pattern, remove [Bot Atom] |
| `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | Decide naming | High | Revert to impl/subscript OR update Theory.lean |
| `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean` | Adapt to primitive bot | High | Remove [Bot Atom], possibly rename constructors |
| `Cslib/Logics/Propositional/Semantics/Basic.lean` | Remove from PR | Medium | Split to follow-up PR |
| `Cslib/Logics/Propositional/Semantics/Bool.lean` | Remove from PR | Medium | Split to follow-up PR |
| `Cslib.lean` | Resolve conflict, adjust imports | Low | Add Theory import, conditionally keep/remove Semantics imports |
