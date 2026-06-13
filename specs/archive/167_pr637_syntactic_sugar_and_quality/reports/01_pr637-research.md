# PR #637 Syntactic Sugar and Quality Review -- Research Report

## 1. Complete File List

PR #637 (branch `refactor/modal-primitives`) touches 13 files relative to main:

| # | File | Category | PR Changes |
|---|------|----------|------------|
| 1 | `.github/CODEOWNERS` | Config | Add @chenson2018 to logic/languages areas |
| 2 | `Cslib.lean` | Root import | Add 2 new imports (Connectives, LogicalEquivalence) |
| 3 | `Cslib/Foundations/Data/HasFresh.lean` | Data | `optConfig` syntax update (`-singleton` etc.) |
| 4 | `Cslib/Foundations/Logic/Connectives.lean` | **New file** | Connective typeclass hierarchy + `ImpBotDerived` class |
| 5 | `Cslib/Foundations/Logic/InferenceSystem.lean` | Shared | No content diff vs main (identical) |
| 6 | `Cslib/Logics/Modal/Basic.lean` | **Core** | Expanded primitives doc, new ↔ notation, bi-implication axiom (dual), axiom proofs |
| 7 | `Cslib/Logics/Modal/Denotation.lean` | **Core** | Proof style changes in `neg_denotation` |
| 8 | `Cslib/Logics/Modal/LogicalEquivalence.lean` | **New file** | Context, fill, LogicallyEquivalent, congruence |
| 9 | `Cslib/Logics/Propositional/Defs.lean` | Shared | Doc update, remove ↔ notation |
| 10 | `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | Shared | Doc update only |
| 11 | `CslibTests/GrindLint.lean` | Tests | New grind test entries |
| 12 | `CslibTests/HasFresh.lean` | Tests | `optConfig` test updates + new test |
| 13 | `references.bib` | References | New bibliography entries |

## 2. Syntactic Sugar Analysis Per File

Task 165 systematically replaced raw constructors (`.imp`, `.bot`, `.neg`, `.and`, `.or`, `.box`, `.diamond`) with scoped notation (`→`, `⊥`, `¬`, `∧`, `∨`, `□`, `◇`) in expression positions across the codebase on main.

**Pi-type binder constraint**: `∀`-quantified parameter types and `change` tactic positions with `→` must keep raw `.imp` constructors because Lean's parser treats `→` as the function type arrow in those positions.

### 2.1 Files Needing Syntactic Sugar Application

#### `Cslib/Logics/Modal/Basic.lean` -- 18 replacements needed

The PR branch uses raw constructors where main uses notation. All conflicts are sugar-related:

| Location | Branch (raw) | Main (sugar) | Safe? |
|----------|-------------|-------------|-------|
| `neg_iff` signature | `.neg φ` | `¬φ` | Yes |
| `diamond_iff` signature | `.diamond φ` | `◇φ` | Yes |
| `and_iff` signature | `.and φ₁ φ₂` | `φ₁ ∧ φ₂` | Yes |
| `or_iff` signature | `.or φ₁ φ₂` | `φ₁ ∨ φ₂` | Yes |
| `Satisfies.t` change | `.diamond φ` | `◇φ` | Yes |
| `t_box_diamond` change | `.diamond φ` | `◇φ` | Yes |
| `Satisfies.b` change | `.diamond φ` | `◇φ` | Yes |
| `b_symm` have type | `.diamond (.atom a)` | `◇(.atom a)` | Yes |
| `Satisfies.four` change | `.diamond (.diamond φ)` / `.diamond φ` | `◇◇φ` / `◇φ` | Yes |
| `four_trans` have types (3 locations) | `.diamond (.diamond ...)` / `.diamond (...)` | `◇◇(...)` / `◇(...)` | Yes |
| `Satisfies.five` change | `.diamond φ` (twice) | `◇φ` (twice) | Yes |
| `five_rightEuclidean` have types (3) | `.diamond (.atom a)` | `◇(.atom a)` | Yes |
| `Satisfies.d` change | `.diamond φ` | `◇φ` | Yes |
| `d_serial` have type | `.diamond (.atom a)` | `◇(.atom a)` | Yes |

**Note**: All `change` tactic positions here use prefix operators (`◇`, `¬`), which are safe. The `→` inside `change` would be unsafe, but those are kept as raw `.imp` in both branches already.

#### `Cslib/Logics/Modal/LogicalEquivalence.lean` -- 3 replacements needed

| Location | Branch (raw) | Main (sugar) | Safe? |
|----------|-------------|-------------|-------|
| `Context.fill` `.impL` arm | `.imp (c.fill φ) ψ` | `c.fill φ → ψ` | Yes (match arm expression, not Pi binder) |
| `Context.fill` `.impR` arm | `.imp ψ (c.fill φ)` | `ψ → c.fill φ` | Yes |
| `Context.fill` `.box` arm | `.box (c.fill φ)` | `□(c.fill φ)` | Yes |

#### `Cslib/Logics/Modal/Denotation.lean` -- 3 replacements needed (PR direction preferred)

Main version uses `push_neg` and `simp [Proposition.neg, Proposition.denotation]`. The PR branch uses `push Not` and `simp only [Proposition.denotation]` / `simp`. These are functionally equivalent but the PR version is more concise. **Resolution**: Take the PR version's proof style here -- it is cleaner.

Wait -- re-examining the diff:
- Main: `simp only [Proposition.neg, Proposition.denotation, ...]` + `push_neg` + `simp [Proposition.denotation]`
- PR: `simp only [Proposition.denotation, ...]` + `push Not` + `simp`

The main version explicitly mentions `Proposition.neg` in simp. The PR version does not (since `.neg` unfolds through `Proposition.diamond` etc.). Both work. **Resolution**: Use the PR version's proof form (no `Proposition.neg` in simp, `push Not`, bare `simp`).

### 2.2 Files With No Syntactic Sugar Changes Needed

| File | Reason |
|------|--------|
| `.github/CODEOWNERS` | Not Lean code |
| `Cslib.lean` | Import list only |
| `Cslib/Foundations/Data/HasFresh.lean` | No logic connectives |
| `Cslib/Foundations/Logic/Connectives.lean` | Typeclass definitions, no notation usage |
| `Cslib/Foundations/Logic/InferenceSystem.lean` | Identical on both branches |
| `Cslib/Logics/Propositional/Defs.lean` | Already uses notation on both branches |
| `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | Already uses notation on both branches |
| `CslibTests/GrindLint.lean` | Test file, no notation issues |
| `CslibTests/HasFresh.lean` | Test file for HasFresh, no logic connectives |
| `references.bib` | Not Lean code |

## 3. Already Applied vs Needs Applying

### Sugar already applied on main but NOT on branch:

**Modal/Basic.lean**: 18 locations (all `◇`/`¬`/`∧`/`∨` replacements in theorem signatures and change tactics)

**Modal/LogicalEquivalence.lean**: 3 locations (`.imp→→` and `.box→□` in `Context.fill` match arms)

**Modal/Denotation.lean**: Different proof approach (main includes `Proposition.neg` in simp; branch does not). Not a sugar issue per se -- it is a proof style choice.

### Sugar from branch that IS NOT on main:

None. The branch does not introduce any new sugar applications that main lacks.

## 4. Merge Conflict Analysis

**29 conflict markers** across 7 files:

| File | Conflicts | Nature | Resolution Strategy |
|------|-----------|--------|---------------------|
| `Cslib.lean` | 2 | Import list ordering (branch lacks many files added on main) | Take main's imports, add PR's new imports |
| `Cslib/Foundations/Logic/Connectives.lean` | 3 | `LukasiewiczDerived` vs `ImpBotDerived`, docstring differences | Take PR's `ImpBotDerived` rename + extended docstring |
| `Cslib/Logics/Modal/Basic.lean` | 15 | Sugar vs raw constructors (see section 2.1) + docstring | Take main's sugar, PR's docstring |
| `Cslib/Logics/Modal/Denotation.lean` | 2 | Proof style in `neg_denotation` | Take PR's cleaner proof |
| `Cslib/Logics/Modal/LogicalEquivalence.lean` | 5 | Copyright, docstring, `Context.fill` sugar | Take PR's copyright/docstring, main's sugar |
| `Cslib/Logics/Propositional/Defs.lean` | 2 | Docstring + `↔` notation line | Take PR's docstring, main's `↔` notation |
| `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | 1 | Docstring wording | Take PR's docstring |

### Recommended Conflict Resolution

The cleanest approach is to rebase the PR branch on main and manually resolve:

1. **Docstring conflicts**: Always take PR's version (richer, more precise)
2. **Sugar conflicts**: Always take main's version (task 165 sugar)
3. **`Cslib.lean` imports**: Take main's full import list, add PR's new entries
4. **`ImpBotDerived` rename**: Take PR's rename (this is the semantic content of the PR)
5. **`Denotation.lean` proof style**: Take PR's cleaner proof
6. **`Defs.lean` `↔` notation**: Take main's version (keep the `↔` notation line)

## 5. Quality Issues Found

### 5.1 Naming Consistency

- **`instIsIntuitionisticExtention`** and **`instIsClassicalExtention`**: The word "Extention" should be "Extension" (typo). However, this exists on both branches and renaming it may break downstream. **Recommendation**: Flag for a separate PR, not in scope here.

### 5.2 Proof Style Issues

- **`Denotation.lean` `neg_denotation`**: The main branch uses `push_neg` where `push Not` is more precise. The PR branch's version using `push Not` and bare `simp` is cleaner. Take PR's version.

### 5.3 Documentation Quality

- **`Modal/Basic.lean` module doc**: PR's expanded primitives section is superior to main's terse version. It clearly explains the `{atom, bot, imp, box}` primitive basis and why derived connectives exist.
- **`Connectives.lean` `ImpBotDerived` docstring**: PR's version explaining why `{imp, bot}` is functionally complete is superior.
- **`LogicalEquivalence.lean` design notes**: PR adds an excellent paragraph explaining why this file does not instantiate the shared `LogicalEquivalence` typeclass.
- **`Propositional/Defs.lean` module doc**: PR's explanation of functional completeness is more precise than main's "Lukasiewicz convention" phrasing.

### 5.4 Remaining Raw Constructors (beyond sugar scope)

In `Modal/Basic.lean`, the following raw constructors are used in positions where they MUST remain raw:

- **Pattern match arms in `Satisfies`**: `.atom`, `.bot`, `.imp`, `.box` -- these are pattern positions, not expressions
- **`change` tactic with `.imp`**: The `→` is unsafe in `change` positions (parsed as function arrow)
- **`have` type annotations with `.atom`**: `.atom a` has no notation, correct as-is

No unnecessary raw constructors found in expression positions after applying the sugar from section 2.1.

### 5.5 `Defs.lean` `↔` Notation

The PR branch **removes** the `@[inherit_doc] scoped infix:20 " ↔ " => Proposition.iff` line. Main has it. The PR likely removed it intentionally (perhaps `↔` conflicts with Lean's built-in iff in some contexts). **Recommendation**: Keep main's version with the `↔` notation line, since it was added intentionally on main and the PR should not regress it.

### 5.6 Copyright Headers

`LogicalEquivalence.lean` has different copyright:
- Main: `Benjamin Brast-McKie`
- PR: `Fabrizio Montesi, Benjamin Brast-McKie`

**Recommendation**: Take PR's copyright (Fabrizio contributed to this file in the PR).

## 6. Recommended Approach

### Strategy: Interactive Rebase onto Main

1. **Checkout the PR branch**: `git checkout refactor/modal-primitives`
2. **Rebase onto main**: `git rebase main` (will trigger conflicts)
3. **Resolve conflicts using the rules in section 4** (take PR docstrings, main sugar, PR rename, PR proof style for Denotation)
4. **After rebase completes, verify no remaining raw constructors in expression positions**
5. **Run full CI**: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`
6. **Force push to the PR branch**: `git push --force-with-lease`

### Risk Assessment

- **Low risk**: The sugar replacements are all mechanical and well-understood from task 165
- **Medium risk**: The `Cslib.lean` merge may be tricky due to the large number of imports on main that the branch lacks
- **Low risk**: The `ImpBotDerived` rename is purely a name change with no functional impact

### Estimated LOC Impact

- Sugar application: ~21 lines changed (net 0 LOC, just notation swaps)
- Conflict resolution: ~30 lines of merge resolution
- Quality improvements: Already incorporated through conflict resolution choices
- Total: ~0 net new lines, ~50 lines touched
