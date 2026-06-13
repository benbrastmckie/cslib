# Task 168: pr3/temporal-formula Branch Syntactic Sugar and Quality Review

## Research Summary

The `pr3/temporal-formula` branch diverges from `main` at commit `a8dbe81be` with 21 commits ahead. Main has 30 commits since divergence, including all of task 165's systematic syntactic sugar refactoring. There are **136 merge conflicts** across 25 files, but the majority are syntactic sugar conflicts (main has sugar, branch has raw constructors) that resolve straightforwardly in favour of main's sugar.

---

## 1. Complete File List

38 files changed on `pr3/temporal-formula` vs `main` (4,389 insertions, 378 deletions).

### Category A: Files Needing Syntactic Sugar (overlapping with task 165)

These files were changed on both the branch and by task 165 on main. The branch versions still use raw constructors where main now uses notation.

| # | File | Conflict Count | Sugar Replacements Needed |
|---|------|---------------|--------------------------|
| 1 | `Cslib/Logics/Temporal/Syntax/Formula.lean` | 7 | `.neg`→`¬`, `.and`→`∧`, `.or`→`∨`, `.untl`→`U`, `.snce`→`S`, `.allFuture`→`𝐆`, `.allPast`→`𝐇`, `.someFuture`→`𝐅`, `.somePast`→`𝐏` in operator bodies (lines 399-443) |
| 2 | `Cslib/Logics/Propositional/Metalogic/Completeness.lean` | 7 | `φ.imp ψ`→`φ → ψ`, `Proposition.neg φ`→`¬φ`/`(¬φ)`, `Proposition.bot`→`⊥` |
| 3 | `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` | 4 | Minimal: mostly `.imp` in Pi-type binder (exempt) |
| 4 | `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` | 2 | `φ.imp ψ`→`φ → ψ` |
| 5 | `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` | 9 | `Proposition.neg φ`→`(¬φ)`, `Proposition.bot`→`⊥`, `φ.imp ψ`→`φ → ψ` |
| 6 | `Cslib/Logics/Propositional/Metalogic/MCS.lean` | 5 | `Proposition.neg φ`→`(¬φ)`, `Proposition.imp`→`→`, `Proposition.bot`→`⊥` |
| 7 | `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` | 3 | Minimal sugar changes |
| 8 | `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` | 7 | Same pattern as IntLindenbaum |
| 9 | `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean` | 31 | Heavy: `Proposition.neg A`→`(¬A)`, `.and B`→`∧ B`, `.or B`→`∨ B`, `.imp C`→`→ C` |
| 10 | `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` | 6 | Moderate: `.imp` and `Proposition.bot` replacements |
| 11 | `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` | 28 | Heavy: same pattern as DerivedRules |
| 12 | `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` | 4 | `φ.imp ψ`→`φ → ψ` |
| 13 | `Cslib/Logics/Propositional/Defs.lean` | 1 | Single: add `↔` notation declaration |
| 14 | `Cslib/Logics/Modal/Basic.lean` | 6 | **STRUCTURAL CONFLICT** (see below) |
| 15 | `Cslib/Logics/Modal/LogicalEquivalence.lean` | 3 | **STRUCTURAL CONFLICT** (see below) |

### Category B: Files With No Syntactic Sugar Needed (branch-only changes, no task 165 overlap)

| # | File | Diff from Main | Notes |
|---|------|---------------|-------|
| 16 | `Cslib/Foundations/Logic/ProofSystem.lean` | 128 lines | Main has expanded modal system classes; branch has older version. **STRUCTURAL** |
| 17 | `Cslib/Foundations/Logic/Theorems.lean` | 0 lines | Identical to main |
| 18 | `Cslib/Foundations/Logic/Theorems/BigConj.lean` | 0 lines | Identical to main |
| 19 | `Cslib/Foundations/Logic/Theorems/Combinators.lean` | 0 lines | Identical to main |
| 20 | `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean` | 0 lines | Identical to main |
| 21 | `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` | 0 lines | Identical to main |
| 22 | `Cslib/Foundations/Logic/Theorems/Temporal/FrameConditions.lean` | 0 lines | Identical to main |
| 23 | `Cslib/Foundations/Data/HasFresh.lean` | 12 lines | optConfig syntax diffs (`-flag` vs `(flag := false)`) |
| 24 | `Cslib/Foundations/Data/ListHelpers.lean` | 0 lines | Identical to main |
| 25 | `Cslib/Logics/Modal/Denotation.lean` | 71 lines | **STRUCTURAL** (different formula primitives) |
| 26 | `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean` | 6 lines | Reference format only |
| 27 | `Cslib/Logics/Propositional/Metalogic/MinSoundness.lean` | 6 lines | Reference format only |
| 28 | `Cslib/Logics/Propositional/Metalogic/Soundness.lean` | 4 lines | Reference format only |
| 29 | `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | 10 lines | Reference format only |
| 30 | `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` | 6 lines | Reference format (doc list style) |
| 31 | `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` | 0 lines | Identical to main |
| 32 | `Cslib/Logics/Propositional/ProofSystem/Instances.lean` | 0 lines | Identical to main |
| 33 | `Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean` | 0 lines | Identical to main |
| 34 | `Cslib/Logics/Propositional/Semantics/Basic.lean` | 6 lines | Reference format only |
| 35 | `Cslib/Logics/Propositional/Semantics/Kripke.lean` | 15 lines | Reference format only |
| 36 | `CslibTests/HasFresh.lean` | 17 lines | optConfig syntax + extra test |
| 37 | `Cslib.lean` | 2 conflicts | Import list (branch has fewer imports than main) |
| 38 | `.github/CODEOWNERS` | 8 lines | Branch adds `@chenson2018` more broadly |
| 39 | `references.bib` | 1 conflict | Branch has SorensenUrzyczyn2006; main has Church1956, Gentzen1935, Heyting1930 |

### Category C: Foundations Files Using HasImp/HasBot (Typeclass Level -- No Sugar Applicable)

Files 17-22 use `HasImp.imp`/`HasBot.bot` at the typeclass level. These are intentionally written with raw typeclass accessors (Lukasiewicz encoding) and task 165 deliberately left them unchanged. No syntactic sugar should be applied to Foundations files.

---

## 2. Syntactic Sugar Replacements Per File

### Pi-type Binder Constraint

`.imp` calls in Pi-type binder positions (function type annotations, axiom parameters) must NOT be replaced. Example:
```lean
-- KEEP as-is (Pi-type binder):
(h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
```

### `change` Tactic Constraint

`change` tactic arguments require the exact definitional form, so `.imp`/`.bot` there must be kept.

### Replacements Needed

**Formula.lean (Temporal)** -- 12 replacements in operator body definitions:
- `Formula.and φ (Formula.allFuture φ)` → `φ ∧ 𝐆φ` (weakFuture)
- `Formula.and φ (Formula.allPast φ)` → `φ ∧ 𝐇φ` (weakPast)
- `Formula.and (Formula.allPast φ) (Formula.and φ (Formula.allFuture φ))` → `𝐇φ ∧ (φ ∧ 𝐆φ)` (always)
- `Formula.neg (always (Formula.neg φ))` → `¬(always (¬φ))` (sometimes)
- `Formula.neg (Formula.untl (Formula.neg ψ) (Formula.neg φ))` → `¬((¬ψ) U (¬φ))` (release)
- `Formula.neg (Formula.snce (Formula.neg ψ) (Formula.neg φ))` → `¬((¬ψ) S (¬φ))` (trigger)
- `Formula.or (Formula.untl φ ψ) (Formula.allFuture φ)` → `(φ U ψ) ∨ 𝐆φ` (weakUntil)
- `Formula.or (Formula.snce φ ψ) (Formula.allPast φ)` → `(φ S ψ) ∨ 𝐇φ` (weakSince)
- `Formula.untl (Formula.and ψ φ) ψ` → `(ψ ∧ φ) U ψ` (strongRelease)
- `Formula.snce (Formula.and ψ φ) ψ` → `(ψ ∧ φ) S ψ` (strongTrigger)

**Propositional files** -- Standard replacements across metalogic, ND, and proof system files:
- `φ.imp ψ` → `φ → ψ` (in proof terms, not Pi-type binders)
- `Proposition.neg φ` → `(¬φ)` or `¬φ`
- `Proposition.bot` → `⊥`
- `A.and B` → `A ∧ B`
- `A.or B` → `A ∨ B`
- `.imp` in constructor applications → `→` notation where scoped

---

## 3. What's Already Applied vs What Needs Applying

### Already Applied (on main, identical on branch)

The following areas are ALREADY identical between main and branch:
- All Foundations files (17-22) -- no sugar needed, already aligned
- Formula.lean header (notation declarations, inductive type, derived abbrevs at lines 1-120) -- identical
- Formula.lean proofs (countability, BEq, swapTemporal theorems) -- identical except body operators

### Needs Applying (branch behind main)

The sugar delta is specifically:
1. **Formula.lean lines 399-443**: 10 derived operator bodies (weakFuture through strongTrigger)
2. **Propositional Metalogic files**: ~50 `.imp`→`→`, `Proposition.neg`→`¬`, `Proposition.bot`→`⊥` replacements across 8 files
3. **ND files (DerivedRules, HilbertDerivedRules, FromHilbert)**: ~60 replacements, heavily concentrated in DerivedRules.lean and HilbertDerivedRules.lean
4. **ProofSystem/Derivation.lean**: ~4 `.imp`→`→` replacements
5. **Propositional/Defs.lean**: 1 addition (↔ notation declaration)

---

## 4. Temporal Notation Availability

All temporal notations are already defined on the branch in Formula.lean:

| Notation | Symbol | Definition | Status |
|----------|--------|------------|--------|
| `¬` | prefix:40 | `Formula.neg` | Defined |
| `∧` | infix:36 | `Formula.and` | Defined |
| `∨` | infix:35 | `Formula.or` | Defined |
| `→` | infix:30 | `Formula.imp` | Defined |
| `↔` | infix:30 | `Formula.iff` | Defined |
| `U` | infix:40 | `Formula.untl` | Defined |
| `S` | infix:40 | `Formula.snce` | Defined |
| `𝐅` | prefix:40 | `Formula.someFuture` | Defined |
| `𝐆` | prefix:40 | `Formula.allFuture` | Defined |
| `𝐏` | prefix:40 | `Formula.somePast` | Defined |
| `𝐇` | prefix:40 | `Formula.allPast` | Defined |
| `△` | prefix:80 | `Formula.always` | Defined |
| `▽` | prefix:80 | `Formula.sometimes` | Defined |

All needed notations are available. No new notation definitions required.

---

## 5. Quality Issues Beyond Syntactic Sugar

### 5a. Structural Conflicts (BLOCKING)

Three files have **fundamental structural divergences** between main and branch that are NOT syntactic sugar issues:

1. **`Cslib/Logics/Modal/Basic.lean`** (6 conflicts, 405-line diff): The branch uses `{atom, not, and, diamond}` as formula primitives while main uses `{atom, bot, imp, box}`. These are completely different formula types. The branch's version predates the main refactoring.

2. **`Cslib/Logics/Modal/LogicalEquivalence.lean`** (3 conflicts, 197-line diff): Branch has class-parameterized `Proposition.Equiv S` approach; main has universal `LogicallyEquivalent` with one-hole contexts. Entirely different implementations.

3. **`Cslib/Logics/Modal/Denotation.lean`** (1 conflict, 71-line diff): Follows from the formula type divergence in Basic.lean. Branch matches on `not`/`and`/`diamond`; main matches on `bot`/`imp`/`box`.

4. **`Cslib/Foundations/Logic/ProofSystem.lean`** (0 conflicts but 128-line diff): Main has expanded modal system hierarchy classes (T, D, S4, KB, K4, K5, K45, TB, KB5, D4, D5, D45, DB with tag types). Branch has only S5 from these.

**Resolution**: These files must be resolved during merge. The correct approach is to take main's versions for Modal files (since main has the authoritative formula type) and rebase the branch's modal-specific additions on top. However, since the branch's modal content is being superseded by main's implementations, the simplest approach is:
- For Modal/Basic.lean, Modal/Denotation.lean: take main's version (branch's modal formula type is obsolete)
- For Modal/LogicalEquivalence.lean: take main's version (branch's approach was experimental, main's is canonical)
- For ProofSystem.lean: take main's version (has the complete modal hierarchy)

### 5b. Reference Format Inconsistencies

Multiple files use older BibKey reference formatting that differs from main:

| File | Branch Format | Main Format |
|------|--------------|-------------|
| IntSoundness.lean | `[A. Chagrov, ...][ChagrovZakharyaschev1997], Theorem 2.43...` | `CZ Theorem 2.43...` |
| MinSoundness.lean | Same expanded format | Same short format |
| Soundness.lean | Same expanded format | Same short format |
| Semantics/Basic.lean | Same expanded format | Same short format |
| Semantics/Kripke.lean | Same expanded format | Same short format |
| NaturalDeduction/Basic.lean | Different Sorensen reference | Different Gentzen reference |

**Note**: Main uses abbreviated `CZ` shorthand in some files while branch uses full BibKey `[Author, *Title*][Key]` format. The BibKey format is actually the project standard (see Defs.lean, Cube.lean, HML/Basic.lean). Main's Completeness.lean `CZ` abbreviation appears to be an inconsistency ON MAIN. The branch's longer format is actually more correct.

**Recommendation**: Align to full BibKey format `[A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997]` which is the project standard. Where main shortened these during task 136 citation conformance, the branch version is preferred. However, for merge simplicity and to avoid unnecessary conflicts, keeping main's versions is pragmatic.

### 5c. Cslib.lean Import Ordering

Branch has only 2 new imports (Modal/LogicalEquivalence, Temporal/Syntax/Formula) while main has many more (full temporal metalogic, modal metalogic, etc.). The merge must combine both import sets.

### 5d. optConfig Syntax

`HasFresh.lean` and `CslibTests/HasFresh.lean` use old `(flag := false)` syntax on the branch vs main's `-flag` syntax. Take main's version.

### 5e. CODEOWNERS

Branch adds `@chenson2018` to more areas. This is a valid change that should be preserved during merge.

### 5f. references.bib

Branch has `SorensenUrzyczyn2006` (needed by NaturalDeduction/Basic.lean on the branch). Main has `Church1956`, `Gentzen1935`, `Heyting1930`. Both sets need to be merged.

---

## 6. Merge Conflict Analysis

### Conflict Summary

| Category | Files | Conflicts | Resolution Strategy |
|----------|-------|-----------|-------------------|
| Cslib.lean imports | 1 | 2 | Combine both import sets |
| Modal structural | 3 | 10 | Take main's versions (branch modal type is obsolete) |
| Propositional sugar | 10 | 76 | Apply main's sugar to branch content |
| Propositional refs | 6 | 5 | Align to main's format (pragmatic) |
| Temporal/Formula.lean | 1 | 7 | Apply main's sugar to branch content |
| ProofSystem.lean | 1 | 0* | Take main's expanded version |
| references.bib | 1 | 1 | Merge both entry sets |
| HasFresh/Tests | 2 | 0* | Take main's optConfig syntax |
| CODEOWNERS | 1 | 0 | Take branch version (expanded owners) |

*These have diffs but no merge conflicts per `merge-tree`.

### Recommended Approach

**Strategy: Merge main into the branch, then apply sugar**

1. **Merge main into `pr3/temporal-formula`**: This will surface all 136 conflicts. Most resolve by taking main's version (sugar changes) or combining content.

2. **Resolve Modal conflicts**: Take main's versions entirely for `Basic.lean`, `Denotation.lean`, `LogicalEquivalence.lean`. The branch's alternative modal formula type is obsolete.

3. **Resolve Propositional conflicts**: For each conflict, take main's sugar version. The branch's raw constructor versions are the "before" of task 165's work.

4. **Resolve Temporal/Formula.lean**: Apply the 10 operator body sugar changes (these are clean replacements).

5. **Resolve ProofSystem.lean**: Take main's version with expanded modal hierarchy.

6. **Resolve infrastructure**: Cslib.lean (combine imports), references.bib (merge entries), CODEOWNERS (take branch's expanded version).

7. **Run full CI**: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`

8. **Commit**: Do NOT submit PR (branch not ready for submission).

**Alternative strategy: Cherry-pick sugar onto branch without merging main**

This avoids merging main but is less clean:
1. Manually apply all sugar replacements to branch files
2. Skip Modal structural changes (since those aren't sugar)
3. Risk: branch drifts further from main

**Recommendation**: Use the merge strategy. It is more comprehensive and results in a branch that is up-to-date with main, making the eventual PR submission cleaner. The 136 conflicts sound daunting but most are mechanical (take main's sugar version).

---

## 7. Excluded Patterns (Do NOT Apply Sugar)

The following patterns must be preserved as raw constructors:

1. **Pi-type binder positions**: `(h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))` -- keep `.imp`
2. **`change` tactic arguments**: Must match definitional form exactly
3. **`simp only [...]` lemma sets**: `Formula.and`, `Formula.neg`, etc. used as simp lemma names -- keep qualified
4. **Pattern match arms**: `| .imp`, `| .bot`, `| .untl`, `| .snce` -- keep raw constructors
5. **`congrArg₂ Formula.imp`**: Constructor references for congruence -- keep qualified
6. **Foundations files**: `HasImp.imp`/`HasBot.bot` are typeclass level, not formula notation
7. **Notation definitions themselves**: `scoped infix:30 " → " => Formula.imp` -- keep `.imp` on RHS
8. **Instance definitions**: `bot := .bot`, `imp := .imp` -- keep raw constructors
