# Research Report: Task #219

**Task**: Address PR #648 review: merge Semantics/Basic.lean and Bool.lean
**Date**: 2026-06-16
**Mode**: Team Research (4 teammates)

## Summary

The team investigated the concrete refactoring approach, PR coordination strategy, critical gaps in the existing plan, and long-term upstream contribution strategy. The core recommendation is: merge files into `Semantics/Basic.lean` (zero import changes), explicitly address the ambiguity in ctchou's comment, add the Avigad reference after resolving a pre-existing `references.bib` merge conflict, and perform active cross-PR coordination by tagging authors rather than just writing notes.

## Key Findings

### 1. File Merge: Keep `Semantics/Basic.lean` as the Target Name

**Recommendation**: Absorb `Bool.lean` content into `Basic.lean`, then delete `Bool.lean`.

The 5 files that import `Semantics.Basic` need zero changes:
- `Temporal/ConservativeExtension.lean`
- `Modal/FromPropositional.lean`
- `Metalogic/Soundness.lean`
- `Metalogic/StrongCompleteness.lean`
- `Semantics/SemanticConsequence.lean`

No files outside `Bool.lean` itself import `Semantics.Bool`. The only change needed is removing the `Semantics.Bool` line from `Cslib.lean`.

The merged file (~175 lines) should be organized: Prop-valued section (Valuation, Evaluate, simp lemmas, Tautology) → Bool-valued section (BoolValuation, BoolEvaluate, simp lemmas) → Bridge section (BoolEvaluate_eq_iff, decidability). The Design Notes from `Bool.lean`'s docstring should be promoted to the merged file's module docstring.

**Confidence**: HIGH

### 2. ctchou's Comment Is Ambiguous — Must Address Both Interpretations

The Critic (Teammate C) identified a critical gap: ctchou's "I think the latter alone is enough" has two readings:

- **Interpretation A**: Merge both evaluators into one file (what we plan to do)
- **Interpretation B**: Drop `Evaluate` entirely; `BoolEvaluate` alone suffices for classical PL

The PR response **must explicitly name and rebut Interpretation B**. Suggested framing:

> "We've merged both files into `Semantics/Basic.lean`. If you meant 'drop `Evaluate` entirely': the canonical model construction in `StrongCompleteness.lean` uses `fun p => atom p ∈ S` which is inherently `Prop`-valued — the MCS set membership has no `DecidablePred`. `BoolEvaluate` serves the computable layer for DPLL/SAT (Matthew Doty's work on Zulip). The bridge lemma `BoolEvaluate_eq_iff` connects them."

Without this, we risk a third review cycle if ctchou intended Interpretation B.

**Confidence**: HIGH — this is the single most important recommendation.

### 3. Avigad Reference: Blocking Prerequisites

The Avigad textbook (*Mathematical Logic and Computation*, Cambridge, 2023) must be added to `references.bib` with key `Avigad2023` following CSLib convention (`{AuthorSurname}{Year}`).

**Blocking issue**: `references.bib` has a live git merge conflict (contains `<<<<<<< Updated upstream` markers for `Fitting1969` and `Trufas2024`). This must be resolved before any commit touching that file.

**CI concern**: Verify whether `lake exe lint-style` validates docstring `[BibKey]` references against `references.bib`. If so, the Avigad entry is a CI prerequisite.

Replace in merged file docstring:
```
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Section 1.2
```
with:
```
* [J. Avigad, *Mathematical Logic and Computation*][Avigad2023], Chapters 2-3
```

Note: `SemanticConsequence.lean` (not in this PR) also cites ChagrovZakharyaschev1997. The PR response should note those citations reference specific theorems (1.16, 2.43) and will be addressed in a follow-up.

**Confidence**: HIGH

### 4. PR Coordination: Concrete Actions Required

ctchou listed "coordinate" as a CHANGES_REQUESTED item. The existing plan only proposed notes in the PR description, but the Critic argues this may not satisfy the reviewer — active cross-PR engagement is likely expected.

#### PR #536 (thomaskwaring): Wait and Rebase
- Status: Clean, mergeable (`mergeable: true`), ctchou explicitly says "wait for it"
- Both #536 and #648 modify `IsIntuitionistic`/`IsClassical` in `Defs.lean` and `NaturalDeduction/Basic.lean`
- **Action**: Wait for merge, then rebase. The conceptual changes (bot as primitive, imp rename) are compatible with #536's inference-system refactor

#### PR #607 (fmontesi): Tag and Flag Naming Divergence
- Status: Dirty (merge conflict), CHANGES_REQUESTED
- **Naming conflict**: #607 uses `HasImpl` and `HasNot`; #648 uses `HasImp` and omits `HasNot`
- **Constructor conflict**: #607 keeps `Proposition.impl`; #648 renames to `Proposition.imp`
- #607 and #587 both use `HasImpl` (2 vs 1) — community converging on `HasImpl`
- **Action**: Tag fmontesi in PR #648 flagging the `HasImp`/`HasImpl` divergence. Consider adopting `HasImpl` in #648 to align with the converging direction.

#### PR #587 (thomaskwaring): Flag Incompatibility
- Status: Open DRAFT with design questions. Has two versions of `Model.lean` (old/new)
- **File collision**: Both #648 and #587 create `Cslib/Foundations/Logic/Connectives.lean` at the same path with different content and class names — a direct conflict
- **Incompatibility**: #587's `Valuation.interp` handles only 4 constructors (atom, and, or, impl) — missing `bot` case and using old `impl` name. It **cannot compile** against post-#648 `Proposition` type
- **Action**: Tag thomaskwaring noting: (1) the `Connectives.lean` path collision, (2) `Valuation.interp` needs updating for the five-primitive `Proposition` type

**Confidence**: HIGH for #536 sequencing, MEDIUM-HIGH for coordination approach

### 5. The `Connectives.lean` Path Collision Is the Critical Coordination Issue

Both PR #648 and PR #587 create `Cslib/Foundations/Logic/Connectives.lean` with different content:

| | PR #648 | PR #587 |
|---|---------|---------|
| `HasImp`/`HasImpl` | `HasImp` | `HasImpl` |
| `HasBot` | Yes | No |
| `HasNot` | No | Yes |
| Bundled class | `PropositionalConnectives` | None |

If either merges first, the other needs a complete rewrite of that file. Since #587 is DRAFT and has been flagged as incompatible with the post-#648 `Proposition` type, PR #648 should proceed. But the PR response should acknowledge this collision explicitly.

**Confidence**: HIGH

### 6. Modal Primitive Type Conflict — The Biggest Strategic Risk

For the long-term goal of upstreaming Modal/Temporal/Bimodal:

- **Upstream** `Modal/Basic.lean` (Montesi): primitives are `{atom, not, and, diamond}`
- **Fork** `Modal/Basic.lean`: primitives are `{atom, bot, imp, box}`

These are fundamentally incompatible. The fork's design is better for proof systems (Hilbert axioms, necessitation, K axiom are naturally stated with `box`+`imp` as primitive). But fmontesi is an active contributor who may resist changing his formula type.

PR #607 compounds this: it adds `HasBox`/`HasDiamond` instances on top of Montesi's design, making a later refactor harder if #607 merges first.

**Action (post-#648)**: Open a Zulip thread proposing `{atom, bot, imp, box}` as the modal formula primitive type before writing any Modal PR. Get fmontesi/ctchou buy-in first.

**Confidence**: HIGH that this is the main strategic risk; MEDIUM on resolution approach

### 7. Kripke.lean Is Not in PR #648 — Use This Proactively

ctchou says "Later we can add (for example) Kripke semantics for intuitionistic propositional logic." The PR file list confirms `Kripke.lean` is NOT in #648.

The PR response should proactively mention: "Correct — Kripke semantics for intuitionistic/minimal PL exists locally (`Semantics/Kripke.lean`) and is planned as a follow-up, pending classical semantics landing first." This turns ctchou's forward-looking comment into a positive coordination signal.

**Confidence**: HIGH

### 8. Recommended PR Sequencing for Upstream

```
#536 merges (ready) → PR #648 (Semantics, current)
→ Propositional Metalogic PR (Soundness + StrongCompleteness)
→ [Zulip: resolve modal primitive type with fmontesi]
→ Modal Semantics PR (requires primitive type resolution)
→ Modal Metalogic PR (13 systems)
→ Temporal PR
→ Bimodal PR
```

Do NOT submit Temporal or Bimodal PRs until the Modal primitive formula type is resolved upstream. Both use `FromPropositional` embedding that depends on `{atom, bot, imp, box}`.

**Confidence**: MEDIUM (depends on upstream merge timelines)

## Synthesis

### Conflicts Resolved

1. **File naming** (A: `Semantics/Basic.lean` vs D: `Semantics/Semantics.lean`): Resolved in favor of **`Semantics/Basic.lean`** — zero import changes across 5 files is the decisive advantage.

2. **Interpretation of ctchou** (A/B/D assume merge; C flags ambiguity): Resolved by **addressing both interpretations in the PR response**. The merge proceeds as Interpretation A, but the response explicitly names and rebuts Interpretation B.

3. **Coordination approach** (A: PR description notes; C: active tagging): Resolved in favor of **active cross-PR tagging** — ctchou's "coordinate" as a CHANGES_REQUESTED item likely expects evidence of actual inter-PR communication.

4. **HasImp vs HasImpl naming**: Not resolved — requires Zulip discussion. Two PRs (#607, #587) use `HasImpl`; only #648 uses `HasImp`. The PR response should flag this and ask whether adopting `HasImpl` is preferred.

### Gaps Identified

1. **`references.bib` merge conflict** must be resolved before any commit touching that file
2. **`lake exe lint-style` BibTeX validation** needs verification — unknown whether CI checks docstring references
3. **`@[expose] public section`** — confirmed standard in CSLib (392 occurrences) but the merged file should use a single wrapper, not two
4. **Import chain**: Merged file must use only `public import Cslib.Logics.Propositional.Defs` — do NOT accidentally self-import the deleted `Semantics.Basic`

### Recommendations

**Immediate actions for PR #648 revision:**
1. Wait for #536 to merge, then rebase
2. Merge `Bool.lean` into `Basic.lean` (keep name, delete `Bool.lean`, update `Cslib.lean`)
3. Resolve `references.bib` merge conflict, add `Avigad2023` entry
4. Update docstring references to Avigad chapters 2-3
5. Promote `## Design Notes` from Bool.lean docstring to merged file header
6. Tag fmontesi and thomaskwaring in PR #648 comments (not just PR description)
7. In PR response: explicitly address both interpretations of "Bool.lean alone is enough"
8. In PR response: mention Kripke.lean exists locally as planned follow-up
9. In PR response: note `SemanticConsequence.lean` retains Chagrov references for specific theorems

**Post-#648 strategic actions:**
10. Open Zulip thread on modal formula primitive type before writing Modal PRs
11. Consider adopting `HasImpl` over `HasImp` if community consensus emerges

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary Implementation | completed | high |
| B | PR Coordination | completed | high |
| C | Critical Analysis | completed | high |
| D | Strategic Horizons | completed | medium-high |

## References

- PR #648: https://github.com/leanprover/cslib/pull/648
- PR #536: https://github.com/leanprover/cslib/pull/536 (thomaskwaring, ready to merge)
- PR #587: https://github.com/leanprover/cslib/pull/587 (thomaskwaring, DRAFT)
- PR #607: https://github.com/leanprover/cslib/pull/607 (fmontesi, dirty/CHANGES_REQUESTED)
- Zulip: https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/with/603538889
- Avigad, *Mathematical Logic and Computation*, Cambridge University Press, 2023
