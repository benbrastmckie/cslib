# Research Report: Task #197

**Task**: Scope initial Modal/ upstream PR (~300 LOC)
**Date**: 2026-06-17
**Mode**: Team Research (4 teammates)
**Assumption**: PR #648 merges as-is. Design choices (bot-as-primitive, `imp` naming, Connectives.lean architecture) are settled. PR #649 is a sibling, not a dependency.

## Summary

The pr-description.md is accurate against local code but needs targeted updates before submission. The Modal PR stacks on PR #648 only and can be submitted once #648 merges. Six concrete action items remain: resolve `FromPropositional.lean` scope, add PR #587 mention, drop 1930s citations, add Kyle Miller and fmontesi references, and strengthen the imp naming rationale.

## Key Findings

### Primary Approach (from Teammate A)

**The local code is correct and the pr-description.md broadly matches it.** The four-file scope (~355 insertions / ~222 deletions) remains accurate. `Basic.lean` already uses `{atom, bot, imp, box}`, `Denotation.lean` and `LogicalEquivalence.lean` are updated, and `Connectives.lean` has `HasBox`/`ModalConnectives`.

**Three targeted revisions needed** in pr-description.md:
1. **HIGH**: Add PR #587 (thomaskwaring, DRAFT) to "Relationship to Other PRs" — creates the same `Connectives.lean` file path with different content (semantic typeclasses). PR #648's description already acknowledges this three-way coordination need (#607, #648, #587), but the Modal PR description does not.
2. **MEDIUM**: Strengthen the `imp` naming rationale — the current "one-line change" framing understates the scope. Since `imp` is settled via #648, state this directly: "This PR uses `imp` consistent with PR #648's convention."
3. **LOW**: Minor — the PR description references PR #648 as "(open)" without noting that the Modal PR submits after #648 merges.

### Alternative Approaches (from Teammate B)

**New intelligence gathered:**
- PR #607 is active again — fmontesi commented "Should be ok now" on 2026-06-16 responding to ctchou's 3-file consolidation suggestion.
- PR #587 creates the same `Connectives.lean` file path as PR #648.

**Noted alternative (not recommended):** A 3-file scope (Basic + Denotation + LogicalEquivalence) rebased on main without Connectives.lean changes would decouple the Modal PR from #648 entirely. This sacrifices the `ModalConnectives` typeclass integration, which is a key selling point. With #648's design settled, stacking is the correct approach.

### Gaps and Shortcomings (from Critic)

**CRITICAL — FromPropositional.lean is missing from the PR description.** The local `Cslib/Logics/Modal/FromPropositional.lean` (165 lines) exists, imports `Basic.lean`, and is explicitly referenced in `Basic.lean`'s module docstring ("The embedding `PL.Proposition.toModal` (in `FromPropositional`)..."). The pr-description.md lists only 4 files. Either `FromPropositional.lean` must be included in scope, or it must be verified to compile against the new primitives and explicitly excluded.

**Scope isolation risk.** The local `Cslib/Logics/Modal/` contains ~3,467+ lines in `ProofSystem/` and `Metalogic/` that must NOT appear in this PR. The pr-description.md should note branch isolation requirements for `/pr`.

**Additional gaps:**
- Kyle Miller's S5 completeness work (adjacent to roadmap "PR 3") is not mentioned
- Proposition vs Formula naming debate (Malvin Gattinger, Zulip) is unaddressed

### Strategic Horizons (from Teammate D)

**Task 227 (algebraic completeness) confirms bot-as-primitive is algebraically sound.** The algebraic completeness proofs require `⊥` as a primitive nullary operation for substitution invariance (free algebra property). This can be cited in the PR description's design rationale if needed.

**fmontesi's InferenceSystem suggestion is an opportunity.** fmontesi wrote on Zulip: "define a mega-inductive with all the axioms in the Modal Cube and instantiate InferenceSystem for each fragment." The Modal PR description should reference this for the proof system roadmap item, signaling that the user values fmontesi's architectural guidance.

**Drop 1930s citations from the PR body.** ctchou pushed back on German-language 1930s references in PR #648. The Modal pr-description.md cites Johansson1937, Wajsberg1938, McKinsey1939 — these will receive the same pushback. Lead with Blackburn2001 and ChagrovZakharyaschev1997.

**Kyle Miller is waiting on the Modal PR.** He explicitly said on Zulip he'd port his S5 completeness to CSLib "once this PR is merged." Mentioning his work in the contribution roadmap signals coordination.

## Synthesis

### Gaps to Address

1. **FromPropositional.lean** — Absent from pr-description.md scope despite being referenced by Basic.lean. Must be resolved before `/pr`.
2. **PR #587 coordination** — Not in any previous research. The three-way Connectives.lean situation (#607, #648, #587) should be mentioned in the PR description.
3. **Kyle Miller S5 work** — Should be mentioned in the contribution roadmap section.
4. **1930s citations** — Replace with modern references in the PR body (keep in references.bib for attribution).
5. **fmontesi InferenceSystem reference** — Add to proof system roadmap item.
6. **PR #607 status update** — Previous assessment of "stalled" is outdated; fmontesi responded 2026-06-16.

### Action Items for pr-description.md Revision

| # | Action | Priority |
|---|--------|----------|
| 1 | Resolve `FromPropositional.lean` — include in scope or verify it compiles unchanged | High |
| 2 | Add PR #587 to "Relationship to Other PRs" section | High |
| 3 | Replace 1930s citations with modern references in PR body | Medium |
| 4 | Add Kyle Miller S5 mention to contribution roadmap | Medium |
| 5 | Reference fmontesi's InferenceSystem suggestion in proof system roadmap | Medium |
| 6 | Strengthen `imp` naming rationale — state it directly as #648's convention | Low |
| 7 | Update PR #607 status from "stalled" to "active" | Low |
| 8 | Add branch isolation note for `/pr` (exclude ProofSystem/, Metalogic/) | Low |

### Sequencing

Submit the Modal PR after PR #648 merges. No dependency on PR #649 (sibling). Post a Zulip update when submitted, inviting Kyle Miller and SnO2WMaN to review.

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary (revision assessment) | completed | high |
| B | Alternatives (decoupling strategy) | completed | high |
| C | Critic (gaps and blind spots) | completed | high |
| D | Horizons (strategic alignment) | completed | high |

## References

- PR #648: https://github.com/leanprover/cslib/pull/648 (stacking dependency)
- PR #607: https://github.com/leanprover/cslib/pull/607 (OPEN, active again as of 2026-06-16)
- PR #587: thomaskwaring DRAFT, creates Connectives.lean with semantic typeclasses
- PR #528: https://github.com/leanprover/cslib/pull/528 (MERGED)
- PR #535: https://github.com/leanprover/cslib/pull/535 (MERGED)
- PR #633: https://github.com/leanprover/cslib/pull/633 (CLOSED — too large)
- PR #649: https://github.com/leanprover/cslib/pull/649 (sibling, not a dependency)
- Kyle Miller S5 Gist: https://gist.github.com/kmill/f4649908a8eb1b8e6f5cf6a2d1dee553
- FFL: https://github.com/FormalizedFormalLogic/Foundation
- Zulip thread: specs/197_modal_upstream_initial_pr/zulip.md
