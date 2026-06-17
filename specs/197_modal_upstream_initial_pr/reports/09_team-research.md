# Research Report: Task #197

**Task**: Scope initial Modal/ upstream PR (~300 LOC)
**Date**: 2026-06-17
**Mode**: Team Research (4 teammates)

## Summary

The PR landscape around task 197 has shifted materially since the pr-description.md was written. PR #648 now has CHANGES_REQUESTED with active debate on bot-as-primitive vs bot-as-atom, PR #607 is no longer stalled (fmontesi responded 2026-06-16), and PR #587 (thomaskwaring) creates a three-way file conflict on `Connectives.lean`. The pr-description.md is technically accurate against local code but needs targeted updates. The Modal PR should not be submitted until PR #648 resolves its review cycle.

## Key Findings

### Primary Approach (from Teammate A)

**The local code is correct and the pr-description.md broadly matches it.** The four-file scope (~355 insertions / ~222 deletions) remains accurate. `Basic.lean` already uses `{atom, bot, imp, box}`, `Denotation.lean` and `LogicalEquivalence.lean` are updated, and `Connectives.lean` has `HasBox`/`ModalConnectives`.

**Three targeted revisions needed** in pr-description.md:
1. **HIGH**: Add PR #587 (thomaskwaring, DRAFT) to "Relationship to Other PRs" — creates the same `Connectives.lean` file path with different content (semantic typeclasses). PR #648's description already acknowledges this three-way coordination need (#607, #648, #587), but the Modal PR description does not.
2. **MEDIUM**: Soften the "one-line change" language for `imp` vs `impl` — it's a rename throughout Modal files, and thomaskwaring confirmed upstream Modal/ uses `impl`. Frame it as: "the Modal PR adopts whatever naming convention #648 settles on."
3. **LOW-MEDIUM**: Note PR #648's CHANGES_REQUESTED status to set reviewer expectations.

### Alternative Approaches (from Teammate B)

**Critical new intelligence:**
- PR #607 is active again — fmontesi commented "Should be ok now" on 2026-06-16 responding to ctchou's 3-file consolidation suggestion. PR #607 is no longer stalled.
- PR #649 also has CHANGES_REQUESTED from ctchou (future-only operators, LTS integration).
- PR #587 creates the same `Connectives.lean` file path as PR #648.

**Primary alternative: Decouple from #648, rebase on main, 3-file scope.** Drop all `Connectives.lean` changes from the Modal PR. Scope to Basic.lean + Denotation.lean + LogicalEquivalence.lean only. This eliminates exposure to the bot-as-primitive debate, the imp/impl naming war, and the three-way `Connectives.lean` file conflict. The `ModalConnectives` typeclass instance can come in a follow-up once the Connectives architecture settles.

Advantages: Completely decoupled from #648 review cycle; can be submitted immediately; survives if #648 is rejected entirely. Disadvantage: Loses the unified typeclass hierarchy, making `ModalConnectives` less elegant as a follow-up.

### Gaps and Shortcomings (from Critic)

**CRITICAL — FromPropositional.lean is missing from the PR description.** The local `Cslib/Logics/Modal/FromPropositional.lean` (165 lines) exists, imports `Basic.lean`, and is explicitly referenced in `Basic.lean`'s module docstring ("The embedding `PL.Proposition.toModal` (in `FromPropositional`)..."). The pr-description.md lists only 4 files. Either `FromPropositional.lean` must be included in scope, or it must be verified to compile against the new primitives and explicitly excluded.

**Scope isolation risk.** The local `Cslib/Logics/Modal/` contains ~3,467+ lines in `ProofSystem/` and `Metalogic/` that must NOT appear in this PR. The user's PR #633 was CLOSED for being too large. The pr-description.md gives no guidance on branch isolation for `/pr`.

**Additional gaps:**
- Kyle Miller's S5 completeness work (adjacent to roadmap "PR 3") is not mentioned
- Proposition vs Formula naming debate (Malvin Gattinger, Zulip) is unaddressed
- The imp/impl naming rationale could be strengthened

### Strategic Horizons (from Teammate D)

**Task 227 (algebraic completeness) strengthens the bot-as-primitive case.** The algebraic completeness proofs require `⊥` as a primitive nullary operation for substitution invariance (free algebra property). This is directly applicable to the open PR #648 review from thomaskwaring. Action: Reference this argument in PR #648's review thread.

**Optimal sequencing confirmed:** Wait for PR #648 approval → submit Modal PR stacked on it. Do not help PR #607 (wrong primitive direction). Do not collaborate with Kyle Miller before the Modal PR establishes the primitive set (Kyle Miller is explicitly waiting for this).

**fmontesi's InferenceSystem suggestion is an opportunity.** fmontesi wrote on Zulip: "define a mega-inductive with all the axioms in the Modal Cube and instantiate InferenceSystem for each fragment." The Modal PR description should reference this for the proof system roadmap item, signaling that the user values fmontesi's architectural guidance.

**Drop 1930s citations from the PR body.** ctchou pushed back on German-language 1930s references in PR #648. The Modal pr-description.md cites Johansson1937, Wajsberg1938, McKinsey1939 — these will receive the same pushback. Lead with Blackburn2001 and ChagrovZakharyaschev1997.

## Synthesis

### Conflicts Resolved

**Stacking vs. decoupling (A/C/D vs B):** Teammate B recommends decoupling entirely from PR #648 (3-file scope on main). Teammates A, C, D recommend keeping the stacking approach but waiting for #648 to stabilize. **Resolution:** The stacking approach remains primary because the `ModalConnectives` typeclass integration is a key selling point of the PR (it connects Modal/ to the shared connective hierarchy). However, the 3-file decoupled approach should be prepared as a contingency if PR #648 stalls beyond ~4 weeks or if the Connectives.lean architecture changes significantly. Both paths are viable; the stacking path produces a better PR if #648 merges as-is.

**FromPropositional.lean (C only):** Only the Critic flagged this. **Resolution:** This is a legitimate gap. Before `/pr` runs, `FromPropositional.lean` must be checked — either it needs to be in the diff (if it was modified for the new primitives) or explicitly verified to compile unchanged.

### Gaps Identified

1. **PR #587 coordination** — Not in any previous research. Three-way Connectives.lean conflict needs resolution.
2. **FromPropositional.lean** — Absent from pr-description.md scope despite being referenced by Basic.lean.
3. **Kyle Miller S5 work** — Not mentioned in pr-description.md despite adjacent roadmap overlap.
4. **Proposition vs Formula naming** — Active community discussion, not preemptively addressed.
5. **1930s citations** — Will receive same pushback ctchou gave on PR #648.
6. **PR #607 is active again** — Previous assessment of "stalled" is outdated.

### Recommendations

**Before submitting the Modal PR:**

1. **Wait for PR #648 to reach approval.** This is the consensus blocker. The Connectives.lean dependency, imp/impl naming, and bot-as-primitive debate must settle first.
2. **Update pr-description.md** with the 3 targeted revisions from Teammate A (add PR #587, soften imp/impl language, note CHANGES_REQUESTED status).
3. **Resolve FromPropositional.lean** — check if it needs to be in scope.
4. **Drop or move 1930s citations** to references.bib only; lead with modern references in the PR body.
5. **Add Kyle Miller S5 mention** to the contribution roadmap section.
6. **Reference fmontesi's InferenceSystem suggestion** in the proof system roadmap item.
7. **Post a Zulip update** when the Modal PR is submitted, inviting Kyle Miller and SnO2WMaN to review.

**To accelerate PR #648:**

8. **Use task 227's algebraic argument** in the PR #648 review thread to close the bot-as-primitive debate. The free algebra / substitution invariance argument is the strongest technical case.

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary (revision assessment) | completed | high |
| B | Alternatives (decoupling strategy) | completed | high |
| C | Critic (gaps and blind spots) | completed | high |
| D | Horizons (strategic alignment) | completed | high |

## References

- PR #648: https://github.com/leanprover/cslib/pull/648 (OPEN, CHANGES_REQUESTED)
- PR #607: https://github.com/leanprover/cslib/pull/607 (OPEN, CHANGES_REQUESTED)
- PR #587: thomaskwaring DRAFT, creates Connectives.lean with semantic typeclasses
- PR #528: https://github.com/leanprover/cslib/pull/528 (MERGED)
- PR #535: https://github.com/leanprover/cslib/pull/535 (MERGED)
- PR #633: https://github.com/leanprover/cslib/pull/633 (CLOSED — too large)
- PR #649: https://github.com/leanprover/cslib/pull/649 (OPEN, CHANGES_REQUESTED)
- Kyle Miller S5 Gist: https://gist.github.com/kmill/f4649908a8eb1b8e6f5cf6a2d1dee553
- FFL: https://github.com/FormalizedFormalLogic/Foundation
- Zulip thread: specs/197_modal_upstream_initial_pr/zulip.md
