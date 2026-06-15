# Research Report: PR #649 Comparison and Classical Signature Analysis

- **Task**: 197 - Scope initial Modal/ upstream PR (~300 LOC)
- **Started**: 2026-06-14T20:00:00Z
- **Completed**: 2026-06-14T21:00:00Z
- **Effort**: 1 hour
- **Dependencies**: Reports 01, 02, 03 (prior research rounds)
- **Sources/Inputs**:
  - `gh pr view 649 --repo leanprover/cslib` (PR body, files, commits, reviews)
  - `gh api repos/leanprover/cslib/pulls/649/files` (per-file patches)
  - `gh api repos/leanprover/cslib/pulls/649/commits` (commit history including quality fixes)
  - `Cslib/Foundations/Logic/Connectives.lean` (local, with HasBox + ModalConnectives)
  - `Cslib/Logics/Modal/Basic.lean` (local, 424 LOC, primitives {atom, bot, imp, box})
  - `Cslib/Logics/Modal/LogicalEquivalence.lean` (local, 84 LOC, Context for {imp, box})
  - `upstream/main:Cslib/Logics/Modal/Basic.lean` (278 LOC, primitives {atom, not, and, diamond})
  - `upstream/main:Cslib/Logics/Modal/LogicalEquivalence.lean` (133 LOC, Context for {not, and, diamond})
  - Reports 01, 02, 03 in `specs/197_modal_upstream_initial_pr/reports/`
- **Artifacts**:
  - `specs/197_modal_upstream_initial_pr/reports/04_pr649-comparison-classical-signature.md`
- **Standards**: status-markers.md, artifact-formats.md, report-format.md

## Executive Summary

- PR #649 (`feat(Logics/Temporal)`) is the closest upstream analogue to our Modal PR: it introduces a new formula type with `{atom, bot, imp, untl, snce}` primitives on top of a `Connectives.lean` foundation, using the same five-primitive design philosophy. It is OPEN with no reviews yet.
- PR #649's `Connectives.lean` (93 LOC) is a strict subset of local `Connectives.lean`: it has `HasBot`, `HasImp`, `HasAnd`, `HasOr`, `HasUntil`, `HasSince`, `PropositionalConnectives`, `TemporalConnectives` but **no `HasBox` and no `ModalConnectives`**. The Modal PR must add those two classes.
- PR #649 introduced a quality-convention fix commit after initial submission: converting references from prose to Mathlib BibKey format, adding `## Main definitions` and `## Notation` sections, and polishing derived operator docs. These are requirements the Modal PR must meet from the start.
- The classical-only signature `{atom, bot, imp, box}` for `Modal.Proposition` is architecturally correct and already fully implemented locally. The nonclassical extensibility rationale (no `and`/`or` as primitives) is explicitly motivated in `Basic.lean`'s module docstring and the `ModalConnectives` docstring in `Connectives.lean`.
- The `LogicalEquivalence.lean` update remains mandatory (as confirmed by team research Report 03): upstream has `Context` constructors for `{not, andL, andR, diamond}`; the Modal PR must update these to `{impL, impR, box}` to match the new primitives. This makes the three-file scope (Basic + Denotation + LogicalEquivalence, ~355 LOC) the correct target.
- **Key lesson from PR #649**: the PR was submitted with complete CI verification (`lake build`, `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`, `lake shake`) passing before submission, and a quality-fix commit was still required. The Modal PR must apply all quality checks plus docstring conventions proactively.

## Context & Scope

This report focuses specifically on comparing PR #649's patterns, conventions, and structure against what the Modal PR needs to do, given the constraint of using the classical-only signature `{atom, bot, imp, box}` and postponing `and`, `or`, and `dia` to accommodate nonclassical modal logics later. Reports 01-03 established the baseline scope and risks; this report extracts actionable lessons from the upstream PR.

## Findings

### 1. PR #649 Structure and What It Establishes as Precedent

PR #649 (`feat(Logics/Temporal): temporal formula type with propositional structure`) established the following upstream pattern for introducing a new logic formula type:

**Commit sequence**:
1. `feat(Logics/Propositional)`: Five-primitive formula type with connective typeclasses (propositional part + Connectives.lean)
2. `feat(references)`: Add bibliography entries for the new logic domain
3. `feat(Logics/Temporal)`: Temporal formula type with propositional structure (~334 LOC new file)
4. `fix(Logics/Temporal)`: Quality convention fixes — BibKey format, `## Main definitions`, `## Notation` sections

**Key design decisions adopted from PR #649 (directly applicable to Modal PR)**:

| Pattern | PR #649 Temporal | Modal PR (ours) |
|---------|-----------------|-----------------|
| Formula primitives | `{atom, bot, imp, untl, snce}` | `{atom, bot, imp, box}` |
| Derived connectives | `neg`, `top`, `and`, `or`, `iff` as `abbrev` | `neg`, `top`, `or`, `and`, `diamond`, `iff` as `abbrev` |
| `Bot`/`Top` instances | `instance : Bot (Formula α) := ⟨.bot⟩` | `instance : Bot (Proposition Atom) := ⟨.bot⟩` |
| `deriving` | `deriving DecidableEq, BEq` | `deriving DecidableEq, BEq` |
| Connective typeclass | `TemporalConnectives` instance | `ModalConnectives` instance |
| Module docstring sections | `## Main definitions`, `## Notation`, `## References` | Same required |
| Reference format | Mathlib BibKey `[Author1969]` style | Same required |
| Scoped notation | All operators scoped to `Cslib.Logic.Temporal` | All operators scoped to `Cslib.Logic.Modal` |
| Copyright | "2026 Benjamin Brast-McKie" | "2026 Fabrizio Montesi, Benjamin Brast-McKie" (Basic.lean co-authored) |

### 2. Connectives.lean Gap Analysis: What the Modal PR Must Add

PR #649's `Connectives.lean` (the version that is now upstream after the propositional commit) contains:

```
HasBot, HasImp, HasUntil, HasSince, HasAnd, HasOr
PropositionalConnectives (extends HasBot, HasImp)
TemporalConnectives (extends PropositionalConnectives, HasUntil, HasSince)
```

The Modal PR must extend `Connectives.lean` with:

```
HasBox
ModalConnectives (extends PropositionalConnectives, HasBox)
```

This is a net addition of ~25 LOC to `Connectives.lean`. The docstring rationale for `HasBox` already exists in local `Connectives.lean` (lines 76-86): box as universal quantification over accessible worlds, diamond derived classically via `¬□¬φ`, and the nonclassical extensibility note about future `HasDia` when intuitionistic/minimal modal logics are formalized.

**Critical design point for the classical-only signature**: the `ModalConnectives` docstring explicitly states that `and`/`or` are NOT included in `ModalConnectives` — the `Modal.Proposition` type uses Łukasiewicz encodings for `and`/`or` as derived `abbrev`s. This is intentional: classical `{atom, bot, imp, box}` supports all extensions (nonclassical modal, bimodal, temporal+modal), while adding `HasAnd`/`HasOr` to `ModalConnectives` would force all modal formula types to provide native `and`/`or` constructors even in systems where they are derived.

The `Connectives.lean` docstring already documents this rationale (the `ModalConnectives` docstring in local uses "Non-classical modal logics require extending this class with a primitive `HasDia`"). For the Modal PR, the rationale should also note that `HasAnd`/`HasOr` are available as optional standalone classes for formula types that provide native conjunction/disjunction.

### 3. Upstream LogicalEquivalence.lean: Mandatory Update

Upstream `LogicalEquivalence.lean` (133 LOC) contains:

1. `Proposition.Context` with constructors: `hole | not | andL | andR | diamond`
2. `Proposition.Context.fill` matching those constructors
3. `Congruence (Proposition Atom) (Proposition.Equiv S)` using `Satisfies.iff_iff_iff` (which depends on the `iff` biconditional characterization)
4. `Satisfies.Context` and `HasHContext` (judgemental context)
5. `LogicalEquivalence` instance for Modal Logic K

**Breaking changes from our `{atom, bot, imp, box}` refactoring**:
- `not c` → `impL c .bot` (negation as imp-with-bot)
- `andL c φ` and `andR φ c` → `impL`/`impR` patterns for Łukasiewicz and
- `diamond c` → `box c`

**Local `LogicalEquivalence.lean`** (84 LOC) has already been rewritten:
- `Context` constructors: `hole | impL | impR | box` (4 instead of upstream's 5)
- Drops the `Cslib.Foundations.Logic.LogicalEquivalence` import (self-contained)
- Drops `Satisfies.iff_iff_iff` dependency (no longer needed)
- Drops `Satisfies.Context`, `HasHContext`, and the `LogicalEquivalence` instance (to be rewritten separately)
- Net: shorter (84 vs 133 LOC) and simpler

The local version drops the `LogicalEquivalence` instance because `Satisfies.iff_iff_iff` was removed (it was used in `equiv_iff`). The Modal PR should either: (a) provide a replacement `equiv_iff` proof without `iff_iff_iff`, or (b) include only the `Context`/`fill`/`congruence` content and defer the `Equiv` infrastructure to a follow-up.

### 4. Quality Convention Requirements Extracted from PR #649

The quality-fix commit (commit 4 of 4, `fix(Logics/Temporal)`) reveals what was required after initial submission. These requirements must be met from the start for the Modal PR:

**Module docstring requirements** (from the fix commit):
- `## Main definitions` section listing each definition/theorem with its purpose and type signature
- `## Notation` section listing all scoped operators with precedence and type mapping
- `## References` section using Mathlib BibKey format: `* [Author, *Title*][BibKey]`
- Inline references within docstrings: `[BibKey]` not prose author/year
- Derived operator docs should include Unicode notation in the description (e.g., `(𝐅 φ)`)

**BibKey format requirement**: the initial commit used prose references ("Kamp, H. (1968)...") which were converted to `[H. Kamp, *Tense Logic*][Kamp1968]`. All references in the Modal PR must use the BibKey format from the start.

**Derived operator documentation pattern** (from temporal Formula.lean):
```
/-- `someFuture φ` (𝐅 φ): `φ U ⊤` — φ holds at some future point (Burgess: `untl φ ⊤`) -/
abbrev Formula.someFuture (φ : Formula Atom) : Formula Atom := φ.untl .top
```
For modal derived connectives, this pattern translates to:
```
/-- Negation: `¬φ` is `φ → ⊥` in the Johansson/Łukasiewicz convention [Johansson1937]. -/
abbrev Proposition.neg (φ : Proposition Atom) : Proposition Atom := .imp φ .bot
```

### 5. Classical-Only Signature Rationale: How to Frame It

PR #649 provides a template for how to frame the "minimal primitives" design in the PR description. The temporal PR's `Connectives.lean` explains:

> "Conjunction (`HasAnd`) and disjunction (`HasOr`) are treated as independent primitives rather than Łukasiewicz-derived connectives. The classical encodings `φ ∧ ψ := ¬(φ → ¬ψ)` and `φ ∨ ψ := ¬φ → ψ` are only propositionally equivalent to `∧` and `∨` in classical logic ([Wajsberg1938], [McKinsey1939]); they fail in intuitionistic and minimal logic."

For the Modal PR, the analogous rationale for NOT including `and`/`or` in `Modal.Proposition` is:

> "The `Modal.Proposition` type uses `{atom, bot, imp, box}` as primitives. Conjunction (`∧`) and disjunction (`∨`) are derived via Łukasiewicz encodings (`φ ∧ ψ := ¬(φ → ¬ψ)`) and appear as `abbrev`s rather than constructors. Diamond (`◇φ := ¬□¬φ`) is similarly derived. This minimal signature is intentional: classical modal logic is complete for `{bot, imp, box}` ([ChagrovZakharyaschev1997] S. 1.1), and the Łukasiewicz encodings preserve all classical equivalences. Keeping `and`/`or` derived prevents the `ModalConnectives` typeclass from requiring native conjunction/disjunction from formula types that naturally derive them — this matters for intuitionistic and minimal modal logics where `∧` and `∨` may still be primitive but `◇` is independent of `□`. When non-classical modal logics are formalized, `HasDia` would be added as an independent typeclass alongside `HasBox`, without requiring changes to `ModalConnectives`."

This framing also appears in `Basic.lean`'s existing module docstring (lines 28-38 in local), which is well-written and should be preserved in the PR.

### 6. What PR #649 Did NOT Do (Avoiding in Modal PR)

- Did NOT include `HasBox` or `ModalConnectives` — these are new additions for the Modal PR
- Did NOT update any existing Modal files (temporal PR is purely additive)
- Did NOT modify `Propositional/Defs.lean` after the first commit (the Propositional changes were part of commit 1 of 4 in the same PR stack)
- Did NOT need to update `LogicalEquivalence.lean` (temporal is a new file, not a refactoring)

The Modal PR is structurally more complex than PR #649 because it modifies existing files rather than adding new ones. This means it will cause breaking changes for `LogicalEquivalence.lean` and potentially affect downstream code.

### 7. NaturalDeduction/Basic.lean Patterns (Not Applicable to Modal)

PR #649 updated `Propositional/NaturalDeduction/Basic.lean` (+82/-70 LOC) to work with the new `{atom, bot, imp, and, or}` Proposition type. These changes (renaming `andE₁`/`andE₂` to `andE1`/`andE2`, `orI₁`/`orI₂` to `orI1`/`orI2`, adding explicit `Γ` argument to constructors) are specific to the propositional natural deduction system and do not apply to the Modal PR, which does not touch `NaturalDeduction/`.

### 8. Dependency Graph for Modal PR (Updated)

Given PR #649 is now OPEN and not yet merged:

```
Connectives.lean (PR #649: PropositionalConnectives, HasBot, HasImp, HasAnd, HasOr)
    ↓ extends with HasBox, ModalConnectives (~25 LOC addition)
Modal/Basic.lean (refactored to {atom, bot, imp, box}, ~355 total with derived connectives)
    ↓ imports
Modal/Denotation.lean (updated match cases, ~85 LOC)
    ↓
Modal/LogicalEquivalence.lean (updated Context constructors, ~84 LOC)
```

The Modal PR thus requires PR #649 to have merged (or be stacked on it) because it extends `Connectives.lean` with `HasBox`/`ModalConnectives`. If PR #649 has not merged, the Modal PR must bundle the `Connectives.lean` additions.

**Stack ordering**: PR #649 (temporal formula type) → Modal PR (extends Connectives.lean + refactors Modal/)

This ordering is architecturally sound: Temporal PR establishes the `Connectives.lean` foundation; Modal PR extends it with the modal typeclass hierarchy.

### 9. Specific Code Patterns from PR #649 to Adopt

**Pattern 1: Module docstring reference format**
```lean
/-! # Modal Logic
## References
* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997]
-/
```

**Pattern 2: Derived connective documentation with Unicode**
```lean
/-- Diamond (`◇φ`): `¬□¬φ = (□(φ → ⊥)) → ⊥`. Diamond is a derived connective in classical
modal logic ([Blackburn2001] Chapter 1, [ChagrovZakharyaschev1997] Section 1.1). -/
abbrev Proposition.diamond (φ : Proposition Atom) : Proposition Atom := .neg (.box (.neg φ))
```

**Pattern 3: Connective typeclass instance with comment**
```lean
/-- Register `Modal.Proposition` as an instance of `ModalConnectives`. -/
instance : ModalConnectives (Proposition Atom) where
  bot := .bot
  imp := .imp
  box := .box
```

**Pattern 4: `## Notation` section in module docstring**
```lean
## Notation

Propositional connectives (scoped to `Cslib.Logic.Modal`):
- `¬` (prefix, 40) : negation (`Proposition.neg`)
- `∧` (infix, 36) : conjunction (`Proposition.and`)
- `∨` (infix, 35) : disjunction (`Proposition.or`)
- `→` (infix, 30) : implication (`Proposition.imp`)
- `↔` (infix, 30) : biconditional (`Proposition.iff`)

Modal operators (scoped to `Cslib.Logic.Modal`):
- `□` (prefix, 40) : necessity (`Proposition.box`)
- `◇` (prefix, 40) : possibility (`Proposition.diamond`)
```

**Pattern 5: `@[expose] public section` block structure**
All content should be wrapped in `@[expose] public section ... end Cslib.Logic.Modal` matching the temporal formula file pattern.

## Decisions

1. **Three-file scope confirmed**: `Basic.lean` + `Denotation.lean` + `LogicalEquivalence.lean` (~355 LOC). Team research (Report 03) established this; PR #649 analysis confirms `LogicalEquivalence.lean` must be updated since it depends on the now-changed `Context` constructors.

2. **Connectives.lean additions (~25 LOC)**: The Modal PR must add `HasBox` and `ModalConnectives` to `Connectives.lean`. This is a 4th file in the PR but very small. It should be submitted as part of the same PR, not a separate one, since `ModalConnectives` is the type-theoretic payoff for the signature change.

3. **Defer `and`/`or` from `ModalConnectives`**: The signature `{atom, bot, imp, box}` is the right choice. `and`/`or` remain Łukasiewicz `abbrev`s in `Modal.Proposition`, not primitives. `ModalConnectives` does not extend `HasAnd`/`HasOr`. This preserves compatibility with future nonclassical modal logics.

4. **Apply PR #649 quality conventions from the start**: All module docstring sections (`## Main definitions`, `## Notation`, `## References`), BibKey format, and Unicode in derived operator docs must be present in the initial submission to avoid a quality-fix follow-up commit.

5. **Stack on PR #649**: Submit after PR #649 merges (or stack the branch on `feat/temporal-formula-propositional`). Do not bundle `PropositionalConnectives` again; the Modal PR adds only `HasBox`/`ModalConnectives`.

## Recommendations

1. **Verify `LogicalEquivalence.lean` drops the `HasHContext`/`LogicalEquivalence` instance cleanly**: The upstream `LogicalEquivalence.lean` provides a `LogicalEquivalence` instance (lines 125-130) that uses `Satisfies.iff_iff_iff`. The local version drops both. Verify that no downstream file in upstream CSLib imports and uses this instance before submitting (it would cause a regression). Check `Cslib.lean` and `Cslib/Logics/Modal/*.lean` for downstream imports.

2. **Add `## Main definitions` and `## Notation` sections to all three modified files**: Based on PR #649's quality-fix pattern, this is a required convention. The current local files do not uniformly include these sections. Add them before PR submission.

3. **Revert `Cslib.Foundations.Data.Relation` → `Cslib.Foundations.Relation.Euclidean`**: Import path fix (previously identified). Confirmed still required since PR #632 moved the module upstream.

4. **Connectives.lean PR description framing**: Frame the `HasBox`/`ModalConnectives` addition explicitly as extending PR #649's foundation: "This PR extends `Connectives.lean` (introduced in PR #649) with `HasBox` and `ModalConnectives` for the modal typeclass hierarchy." This creates a clear narrative.

5. **Cite `ChagrovZakharyaschev1997` for classical-only signature**: The `{atom, bot, imp, box}` signature completeness for classical modal logic is in S. 1.1. This citation should appear in the PR description's Design Rationale section.

6. **Test `Cube.lean` compilation on the PR branch**: The `grind =_` vs `grind =` direction difference on `derivation_def` (upstream uses `=_`, local uses `=`) may affect Cube.lean proofs. Must verify on a branch built from upstream/main.

7. **Draft PR description to reference PR #649**: "This PR follows the approach established by PR #649 (temporal formula type), using the same `Connectives.lean` typeclass foundation and `{atom, bot, imp}` propositional base, adding `{box}` as the modal primitive."

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| PR #649 not merged when Modal PR is ready | H | M | Stack on `feat/temporal-formula-propositional` branch, or submit parallel and note the stacking dependency |
| `LogicalEquivalence` instance regression (upstream downstream code) | M | L | Search all upstream `Cslib/Logics/Modal/` files for import of `LogicalEquivalence`; check Cslib.lean for exports |
| Missing `## Main definitions`/`## Notation` sections triggers quality review | M | H | Apply proactively following PR #649 template |
| `grind =_` vs `grind =` on derivation_def breaks Cube.lean | L | L | Build `Cslib.Logics.Modal.Cube` on PR branch before submission |
| PR #607 (fmontesi) activity resumes with incompatible primitives | H | M | Zulip outreach continues; frame Modal PR as convergence proposal |

## Context Extension Recommendations

- **Topic**: PR quality convention requirements for CSLib contributions
- **Gap**: The quality convention fixes required after PR #649 submission are not documented in `.claude/context/` — specifically, the requirement for `## Main definitions`, `## Notation`, and BibKey reference format in all module docstrings.
- **Recommendation**: Create `.claude/context/cslib/pr-quality-checklist.md` capturing the CI verification pipeline plus docstring conventions, drawing from PR #649's fix commit.

## Appendix

### A. PR #649 File Statistics

| File | +Lines | -Lines | Status |
|------|--------|--------|--------|
| `Cslib.lean` | 2 | 0 | modified |
| `Cslib/Foundations/Logic/Connectives.lean` | 93 | 0 | added |
| `Cslib/Logics/Propositional/Defs.lean` | 66 | 35 | modified |
| `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | 82 | 70 | modified |
| `Cslib/Logics/Temporal/Syntax/Formula.lean` | 334 | 0 | added |
| `references.bib` | 101 | 0 | modified |
| **Total** | **678** | **105** | |

Note: 334 LOC for `Formula.lean` exceeded the ~300 LOC target but was accepted because it cuts cleanly at the `end BEqLaws` section boundary.

### B. Connectives.lean Content Comparison

| Class | PR #649 | Local | Modal PR Adds |
|-------|---------|-------|---------------|
| `HasBot` | Yes | Yes | No (existing) |
| `HasImp` | Yes | Yes | No (existing) |
| `HasUntil` | Yes | Yes | No (existing) |
| `HasSince` | Yes | Yes | No (existing) |
| `HasAnd` | Yes | Yes | No (existing) |
| `HasOr` | Yes | Yes | No (existing) |
| `PropositionalConnectives` | Yes | Yes | No (existing) |
| `TemporalConnectives` | Yes | Yes | No (existing) |
| `HasBox` | No | Yes | YES -- add to Connectives.lean |
| `ModalConnectives` | No | Yes | YES -- add to Connectives.lean |
| `BimodalConnectives` | No | Yes | Deferred (after temporal PR merges) |

### C. Modal PR Estimated File Statistics (Updated)

| File | +Lines | -Lines | Status |
|------|--------|--------|--------|
| `Cslib/Foundations/Logic/Connectives.lean` | ~25 | 0 | modified |
| `Cslib/Logics/Modal/Basic.lean` | 248 | 101 | modified |
| `Cslib/Logics/Modal/Denotation.lean` | 43 | 9 | modified |
| `Cslib/Logics/Modal/LogicalEquivalence.lean` | 84 | 133 | modified (net -49) |
| `references.bib` | 0-20 | 0 | modified (if new BibKeys needed) |
| **Total** | **~400** | **~243** | net ~+157 |

This exceeds the 300 LOC insertion target but net change is positive ~157. The 300 LOC target should be understood as a guideline for reviewability, not a hard limit. The PR is self-consistent (no broken upstream files) and covers a complete semantic unit (the formula type refactoring and its downstream consequences).

### D. PR #649 Branch and Status

- Branch: `feat/temporal-formula-propositional`
- State: OPEN (as of 2026-06-14)
- Reviews: 0 formal reviews; 0 comments
- CI: All checks passed (lake build, checkInitImports, lint, lint-style, test, shake)
- Commits: 4 (propositional, bib entries, temporal formula, quality fixes)

### E. References

- PR #649: https://github.com/leanprover/cslib/pull/649
- PR #607: https://github.com/leanprover/cslib/pull/607 (fmontesi, operator typeclasses -- OPEN)
- PR #648: https://github.com/leanprover/cslib/pull/648 (propositional connectives, stacked on, now part of PR #649)
- `[ChagrovZakharyaschev1997]`: S. 1.1 for classical modal logic completeness with {bot, imp, box}
- `[Johansson1937]`: Minimalkalkül origin of `neg φ := φ → ⊥` convention
- `[Blackburn2001]`: Chapter 1 for box-as-primitive in classical modal logic
- `[Wajsberg1938]`, `[McKinsey1939]`: Łukasiewicz encoding validity in classical but not nonclassical logic
