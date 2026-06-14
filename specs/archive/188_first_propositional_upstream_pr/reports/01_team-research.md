# Research Report: Task #188

**Task**: first_propositional_upstream_pr
**Date**: 2026-06-14
**Mode**: Team Research (4 teammates)

- **Started**: 2026-06-14T10:53:00Z
- **Completed**: 2026-06-14T11:30:00Z
- **Effort**: Team research (4 teammates, standard mode)
- **Dependencies**: None
- **Sources/Inputs**:
  - `specs/188_first_propositional_upstream_pr/reports/01_teammate-a-findings.md` (Upstream inventory and gap analysis)
  - `specs/188_first_propositional_upstream_pr/reports/01_teammate-b-findings.md` (PR scoping options with LOC analysis)
  - `specs/188_first_propositional_upstream_pr/reports/01_teammate-c-findings.md` (Risks, reviewer expectations, conflict analysis)
  - `specs/188_first_propositional_upstream_pr/reports/01_teammate-d-findings.md` (PR strategy and contribution roadmap)
- **Artifacts**: `specs/188_first_propositional_upstream_pr/reports/01_team-research.md`
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

---

## Summary

The upstream CSLib has only 4 files relevant to propositional logic (2 in Propositional/, 2 in Foundations/Logic/). Our fork adds ~8,600 LOC across 35 new files — the entire Hilbert proof system hierarchy, bivalent and Kripke semantics, soundness and completeness for all three logics (min/int/cl), and the ND/Hilbert equivalence. The first PR must navigate a critical structural mismatch: upstream's `Proposition` type uses `{atom, and, or, impl}` (no primitive `bot`), while ours uses `{atom, bot, imp, and, or}`. Two open PRs (#536, #607) conflict directly with our planned changes. A Zulip pre-discussion is mandatory before any PR submission.

---

## Key Findings

### 1. Upstream CSLib Inventory (HIGH Confidence)

Upstream (`https://github.com/leanprover/cslib.git`, branch `main`) has exactly:

**Propositional/** (2 files):
| File | LOC | Description |
|------|-----|-------------|
| `Defs.lean` | 154 | `Proposition` type `{atom, and, or, impl}`, theories, typeclasses |
| `NaturalDeduction/Basic.lean` | ~312 | 10-constructor ND system, weakening, cut, equivalence |

**Foundations/Logic/** (2 files):
| File | LOC | Description |
|------|-----|-------------|
| `InferenceSystem.lean` | 68 | `InferenceSystem` typeclass, `DerivableIn` |
| `LogicalEquivalence.lean` | ~50 | Generic logical equivalence |

No ProofSystem/, Metalogic/, or Semantics/ subdirectories exist upstream for any logic.

### 2. Local Fork Additions (~8,600 LOC, 35 New Files) (HIGH Confidence)

**Foundations/Logic/** — 14 new files, ~3,900 LOC:
- `Connectives.lean` (114) — `HasBot`, `HasImp`, `HasAnd`, `HasOr` typeclasses + bundled classes
- `Axioms.lean` (344) — Generic `HasAxiomImplyK/S/EFQ/Peirce` + connective axiom typeclasses
- `ProofSystem.lean` (524) — `MinimalHilbert`, `IntuitionisticHilbert`, `ClassicalHilbert` hierarchy
- `Metalogic/Consistency.lean` (285) — Generic MCS framework with Lindenbaum lemma
- `Theorems/` (1,690) — Combinators, propositional core, connectives, modal, temporal

**Logics/Propositional/** — 21 new files, ~4,700 LOC:
- `ProofSystem/` (672) — Axioms, DerivationTree, Instances for all 3 logics
- `Semantics/` (414) — Bivalent valuations, Kripke forcing, semantic consequence
- `Metalogic/` (3,174) — Soundness + completeness for CPL, IPL, MPL (all strong)
- `NaturalDeduction/` (1,440) — DerivedRules, FromHilbert, HilbertDerivedRules, Equivalence

### 3. Critical Structural Mismatch: `Defs.lean` (HIGH Confidence)

**Upstream** `Proposition` type:
```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (x : Atom) | and (a b) | or (a b) | impl (a b)
-- Bot via: instance [Bot Atom] : Bot (Proposition Atom) := ⟨.atom ⊥⟩
```

**Our** `Proposition` type:
```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (x : Atom) | bot | imp (a b) | and (a b) | or (a b)
-- Bot via: instance : Bot (Proposition Atom) := ⟨.bot⟩
```

Differences: (1) we add `bot` as a native constructor; (2) we rename `impl` to `imp`; (3) upstream's `Bot` requires `[Bot Atom]` constraint on the atom type, ours doesn't. Any PR touching `Defs.lean` is a **refactoring PR**, not purely additive.

### 4. Conflicting Open PRs (HIGH Confidence)

| PR | Author | Conflict | Severity |
|----|--------|----------|----------|
| #536 | thomaskwaring | Modifies `Defs.lean` and `NaturalDeduction/Basic.lean` | HIGH |
| #607 | fmontesi | Introduces `HasAnd`/`HasOr` in `Operators/` — same class names as our `Connectives.lean` | HIGH |
| #542 | thomaskwaring | Adds theory ordering, depends on #536 | MEDIUM |
| #587 | thomaskwaring | `Models` typeclass for semantics | LOW |

### 5. Reviewer Expectations (HIGH Confidence)

From CONTRIBUTING.md and PR review history:
- **~300-500 LOC maximum** for first contributions (PR #633 explicitly rejected as "very large")
- **AI disclosure mandatory** (Mathlib policy, must explain which tools and how)
- **Zulip discussion required** for major architectural changes
- **Strong completeness expected** alongside weak completeness (xcthulhu comment on PR #633)
- **Literature citations must be accurate** (ctchou verified against primary sources on PR #635)
- **PR titles**: `feat|fix|doc|style|refactor|test|chore|perf[(<area>)]: <description>`
- **CODEOWNERS**: `@arademaker` and `@fmontesi` must both approve logic PRs

### 6. The ctchou Objection Is Fully Resolved (HIGH Confidence)

ctchou's PR #635 objection was that `{imp, bot}` is not functionally complete for intuitionistic logic. Our current 5-primitive `{atom, bot, imp, and, or}` with 10 ND rules directly matches the Gentzen/Prawitz tradition ctchou cited. The PR description must explicitly note this resolution.

---

## Synthesis

### Conflicts Resolved

**Conflict 1: Foundations dependencies needed?**
- Teammate B claimed Foundations files are "already in CSLib" — this is partially incorrect. Only `InferenceSystem.lean` and `LogicalEquivalence.lean` are upstream. `Connectives.lean`, `Axioms.lean`, `ProofSystem.lean` are NOT upstream.
- **Resolution**: Connectives.lean must be contributed separately (PR 0) before Propositional PRs that depend on it.

**Conflict 2: First PR scope — additive vs refactoring**
- Teammate B proposes Defs + Axioms + Semantics/Basic (~487 LOC, treats as additive)
- Teammate C warns that touching Defs.lean makes it a refactoring PR (higher scrutiny)
- Teammate D proposes PR 1 as modified Defs.lean + NaturalDeduction/Basic.lean changes (~300 LOC)
- **Resolution**: The Defs.lean structural change (adding `bot`, renaming `impl` to `imp`) is unavoidable — all downstream files depend on it. It should be the core of PR 1, kept small and well-justified. Purely additive files (ProofSystem/Axioms, Semantics/Basic) should be PR 2.

**Conflict 3: PR 1 content**
- Teammate A: Connectives + Axioms + Semantics/Basic
- Teammate B: Defs + Axioms + Semantics/Basic
- Teammate D: Modified Defs + Modified NaturalDeduction/Basic + minimal Axioms
- **Resolution**: PR 1 should be the Defs.lean refactor + NaturalDeduction/Basic.lean update ONLY (~168 LOC of modifications). This is the minimal change that establishes the foundation. Adding new files inflates the PR and mixes concerns (structural refactor + new content).

### Gaps Identified

1. **Naming convention: `imp` vs `impl`** — Upstream uses `impl`, we use `imp`. This must be justified in the PR description or we must adopt `impl`. The standard (Gentzen, Prawitz) uses "imp" or "→" notation; "impl" is non-standard.

2. **`Bot` instance architecture** — Upstream derives `Bot` from `[Bot Atom]` on the atom type. Our approach uses an explicit `bot` constructor. The PR must argue why explicit `bot` is better (enables `bot` in formula induction without atom-level constraints).

3. **Need to verify CI against upstream HEAD** — Our fork may be behind on Mathlib bumps. Must rebase on upstream `main` and verify `lake build` passes before PR submission.

### Recommendations

**Pre-PR: Zulip Discussion (MANDATORY)**

Post to CSLib Zulip (#Propositional Logic topic) covering:
1. The 5-primitive formula type resolving PR #635's ctchou objection
2. The `Connectives.lean` typeclass approach (building on PR #607 direction)
3. The 6-PR contribution roadmap toward completeness + ND equivalence
4. Ask: preference on `imp` vs `impl` naming

**PR Sequence:**

| PR | Title | Content | LOC | Key Decision |
|----|-------|---------|-----|--------------|
| 0 | `feat(Foundations/Logic): connective typeclass hierarchy` | `Connectives.lean` (new file) | ~115 | Aligns with PR #607 direction |
| 1 | `feat(Logics/Propositional): five-primitive formula type` | Modified `Defs.lean` + `NaturalDeduction/Basic.lean` | ~170 | The structural foundation |
| 2 | `feat(Logics/Propositional): Hilbert axiom schemata and bivalent semantics` | `ProofSystem/Axioms.lean` + `Semantics/Basic.lean` | ~283 | Axiom hierarchy + valuations |
| 3 | `feat(Logics/Propositional): Hilbert proof engine and soundness` | `ProofSystem/Derivation.lean` + `Metalogic/Soundness.lean` | ~257 | Sound Hilbert system |
| 4 | `feat(Logics/Propositional): deduction theorem and classical completeness` | `DeductionTheorem.lean` + `MCS.lean` + `Completeness.lean` + `StrongCompleteness.lean` | ~963 | Classical completeness (split if needed) |
| 5 | `feat(Logics/Propositional): ND extensions and Hilbert-ND equivalence` | `DerivedRules` + `FromHilbert` + `HilbertDerivedRules` + `Equivalence` | ~1,440 | The ND/Hilbert bridge |
| 6 | `feat(Logics/Propositional): Kripke semantics and Int/Min completeness` | Kripke + Int/Min soundness/completeness | ~2,255 | Full three-logic metatheory |

**For THIS task (188)**: The scope is designing and preparing PR 1 (~170 LOC of modifications to Defs.lean and NaturalDeduction/Basic.lean). The implementation should:
1. Create a feature branch based on upstream `main`
2. Apply the `Defs.lean` modifications (add `bot`, rename `impl` to `imp`, register instances)
3. Update `NaturalDeduction/Basic.lean` for the new type signature
4. Verify `lake build` passes against upstream
5. Draft the PR description with ctchou resolution, roadmap, and AI disclosure

---

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Upstream inventory + gap analysis | completed | high |
| B | PR scoping options with LOC | completed | high |
| C | Risks, reviewer expectations, conflicts | completed | high |
| D | PR strategy and contribution roadmap | completed | high |

## References

- CSLib upstream: `https://github.com/leanprover/cslib.git`
- PR #635: Previous propositional logic contribution (ctchou objection)
- PR #607: fmontesi's operator typeclass approach
- PR #536: thomaskwaring's Defs.lean modifications
- CONTRIBUTING.md: CSLib contribution guidelines
- [Gentzen1935], [Prawitz1965], [TroelstraVanDalen1988], [Johansson1937]: Standard references for 5-primitive connective basis
