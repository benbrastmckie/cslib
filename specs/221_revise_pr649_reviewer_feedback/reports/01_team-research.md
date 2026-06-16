# Research Report: Task #221

**Task**: Revise PR #649 (feat/temporal-formula-propositional) based on reviewer feedback
**Date**: 2026-06-16
**Mode**: Team Research (4 teammates)

## Summary

PR #649 needs six categories of revision based on reviewer feedback from PR #648 and #649 reviews. Team research reveals the situation is both more nuanced and more tractable than the task description suggests: three of ctchou's four PR #649 objections are already addressed, the `imp` naming is correct and only needs a better justification, and the bot-as-primitive design has strong prior art support. However, several gaps exist: the reference replacement scope is larger than anticipated (14 citations in Lean file docstrings, not just the PR description), IsClassical/IsIntuitionistic definitions may be inconsistent with merged PR #536, PR #648 has a merge conflict, and coordination with PR #607 is a technical risk, not just a PR description note.

## Key Findings

### 1. LTL Semantics Split (All teammates agree: HIGH confidence)

**Action**: Remove `Cslib/Logics/LTL/Semantics/Satisfies.lean` from PR #649 and its import from `Cslib.lean`.

thomaskwaring's request is explicit and principled: "Please split the semantics development into a separate PR. The point of requesting that large contributions are split up is not just length, but also so that conceptually separate issues can be discussed independently."

**Strategic context** (Teammate D): thomaskwaring's draft PR #587 (`feat(Foundations/Logic): Notation typeclasses and models`) is building a `Models α β` typeclass framework. His request to split semantics is partly motivated by wanting the semantic layer to land via his framework, not as an ad hoc addition. Splitting avoids a future conflict with #587.

**Gap identified** (Teammate C): The task description does not note that a follow-up task/issue is needed for the semantics PR. Without this, the semantics work may be orphaned.

### 2. `imp` vs `impl` Naming (All teammates agree: keep `imp`. HIGH confidence)

thomaskwaring's objection is about the *justification*, not the name itself. He says "I think this is fine, but citing 'CSLib's existing formula types' as your own as-yet-unmerged work is not exactly convincing."

**The fix is narrow**: Change the PR description justification, not the name.

**Independent justifications for `imp`**:
- CSLib's upstream merged code uses `imp`: `Propositional/Defs.lean:87` has `| imp (a b : Proposition Atom)` — thomaskwaring's own merged code
- FormalizedFormalLogic/Foundation (major Lean 4 logic library) uses `| imp` in both propositional and modal formula types
- The constructor/derived distinction matters: `imp` names a *constructor* (primitive); `impl` in upstream Modal is a *derived definition* (`¬P ∨ Q`), not a constructor
- CSLib's Bimodal and Temporal formula types already use `imp`

**Note**: PR #607 (fmontesi) and draft #587 (thomaskwaring) use `HasImpl`/`impl` — the community may be converging on `impl` for typeclasses, but settled merged code uses `imp` for constructors. If the community later converges on `impl`, a renaming PR can handle it uniformly.

### 3. Bot-as-Primitive Design (Acknowledge trade-offs, don't concede. HIGH confidence)

**Reviewer positions**:
- **ctchou**: "I like the idea of adding ⊥ as a primitive" — supportive
- **thomaskwaring**: Substantive objections (5 specific points) — argues for the existing design

**Teammate C's critical insight**: thomaskwaring's position argues for *design change*, not just tone adjustment. "Acknowledging trade-offs" in the PR description risks being received as defensive. The real audience is ctchou (who is supportive); thomaskwaring's buy-in is desirable but not strictly blocking if ctchou approves.

**Prior art supporting bot-as-primitive** (Teammate B):
- FormalizedFormalLogic/Foundation: `| falsum : Formula α`
- Avigad LAMR: `| fls : PropForm`
- Bentzen (arxiv 2310.01916): `| bot : form`
- All major Lean 4 logic formalizations treat bot/falsum as a separate constructor from atoms

**Strongest response to thomaskwaring's objections**:

| Objection | Response |
|-----------|----------|
| Bot behaves like atom in minimal logic | True for MPL alone, but bot is special in IPL/CPL. Primitive bot enables uniform treatment across all three logic strengths. |
| Extra constructor makes proofs verbose | Measured: `\| .bot => False` is one line. No more verbose than `[Bot Atom]` instance handling. |
| WithBot.some substitution should be allowed | Valid point. Current design accommodates this: `intuitionisticCompletion` already uses `WithBot.some`. Bot-as-primitive and WithBot.some-as-embedding are complementary, not mutually exclusive. |
| `⊤ = a → a` is a feature | Both designs are defensible. `⊤ := ⊥ → ⊥` gives a unique normal form independent of `Inhabited`. |
| Minimal logic works without ⊥ | True for implication-only fragment, but CSLib's `Proposition` already includes `and`/`or`. Including `bot` alongside `and`/`or` is standard five-primitive NJ (Prawitz 1965). |

**PR description approach**: Present as a deliberate design choice optimizing for (a) uniform treatment across classical/intuitionistic/minimal, (b) temporal/modal embedding where `bot` appears in derived definitions (`neg φ := φ → ⊥`, `top := ⊥ → ⊥`), and (c) compatibility with CSLib's Modal formula type. Explicitly acknowledge thomaskwaring's WithBot.some point as valid and explain how the design accommodates it.

### 4. German Reference Replacement (HIGH confidence, scope larger than expected)

**Scope finding** (Teammates A + C): The German references appear in 14 citations across Lean file docstrings, not just the PR description:
- `Cslib/Foundations/Logic/Connectives.lean`: Johansson1937, Wajsberg1938, McKinsey1939, Heyting1930, Gentzen1935
- `Cslib/Logics/Propositional/Defs.lean`: Johansson1937, Gentzen1935
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`: Johansson1937, Gentzen1935
- `Cslib/Logics/Propositional/Axioms.lean`: additional references

**Replacement strategy**:

| Current (German) | Replacement (English) |
|-------------------|----------------------|
| Gentzen1935 | Prawitz1965 (covers same ND content) + Avigad2022 Ch. 2-3 |
| Johansson1937 | Avigad2022 (as primary reading ref); retain Johansson1937 in `references.bib` as historical source but remove from docstrings |
| Wajsberg1938, Heyting1930 | Avigad2022 |

**New bib entry needed**:
```bibtex
@book{Avigad2022,
  author    = {Avigad, Jeremy},
  title     = {Mathematical Logic and Computation},
  publisher = {Cambridge University Press},
  address   = {Cambridge},
  year      = {2022},
  isbn      = {978-1-108-84072-1}
}
```

**Keep** (English, already in bib): Prawitz1965, Church1956, TroelstraVanDalen1988, McKinsey1939, Kamp1968, Pnueli1977, Burgess1984, VardiWolper1986.

### 5. PR #536 Consistency (MEDIUM confidence — needs verification)

**Finding** (Teammates A + C): The branch's `Defs.lean` still uses theory-parameterized `IsIntuitionistic`/`IsClassical`:
```lean
-- Branch (old form):
class IsIntuitionistic (T : Theory Atom) where
  efq (A : Proposition Atom) : (⊥ → A) ∈ T

-- Upstream post-#536 (new form):
class IsIntuitionistic (Atom : Type u) [Bot Atom] (S : Type*)
    [InferenceSystem S (Proposition Atom)] where
  efq (A : Proposition Atom) : S⇓(⊥ → A)
```

The branch is cleanly rebased on `70c5bf58` (the #536 merge commit) — three commits on top. But `Defs.lean` in the branch still defines the old theory-based classes, which contradicts what PR #536 merged. This needs `lake build` verification to determine if there's an actual type error or if both definitions coexist.

### 6. PR #648 Merge Conflict (HIGH confidence)

**Finding** (Teammate C): PR #648 has `MERGEABLE_STATE: dirty` — it currently has a merge conflict with `main` after PR #536 merged. PR #649 (`MERGEABLE: True, MERGEABLE_STATE: blocked`) is clean but blocked by CHANGES_REQUESTED reviews. PR #648's conflict must be resolved before #649 can proceed.

### 7. ctchou's PR #649 Review — Partially Already Addressed (HIGH confidence)

**Finding** (Teammate C): The task description treats ctchou's review as fully open, but three of four points are already addressed:
- Future-only temporal operators: DONE
- Encodable/Countable removal: DONE
- Omega-executions of LTS: Punted to future work (documented)
- **LTS transitions**: NOT addressed — ctchou separates this from omega-executions

**Gap**: The task description conflates LTS transitions with omega-executions. The PR description revision should explicitly acknowledge transitions as deferred.

### 8. PR #607 Coordination Risk (MEDIUM confidence)

**Finding** (Teammates C + D): PR #607 (fmontesi, `feat(Logic): logical operators`) introduces typeclass hierarchies for logical operators with `HasImpl` naming. PR #649's `Connectives.lean` explicitly credits PR #607's direction. If #607 merges first with a different design, `Connectives.lean` conflicts or becomes redundant.

**Action needed**: Active outreach to fmontesi, not just a PR description mention.

### 9. and/or Primitives Inconsistency (HIGH confidence)

**Finding** (Teammate C): `Connectives.lean` claims a five-primitive signature with `HasAnd`/`HasOr`, but `LTL.Formula` and `Temporal.Formula` implement only three primitives (`atom`, `bot`, `imp`) and derive `and`/`or` via abbreviations (Lukasiewicz encoding). The formula types do not instantiate `HasAnd`/`HasOr`. This inconsistency is present in the current PR and unaddressed in the task description.

### 10. Strategic PR Sequencing (Teammate D)

Recommended sequence:
1. **NOW**: PR #649 revision — temporal + LTL formula syntax ONLY (remove semantics, update refs, acknowledge trade-offs)
2. **NEXT**: PR #648 conflict resolution (resolve merge conflict with main post-#536)
3. **THEN**: Propositional metalogic PR (Soundness + StrongCompleteness)
4. **THEN**: LTL Semantics PR (coordinate with #587 Models typeclass)
5. **FUTURE**: Zulip thread on modal formula type standardization

## Synthesis

### Conflicts Resolved

1. **Avigad year (2022 vs 2023)**: Teammates A/B say 2022, Teammate D says 2023. Cambridge publication date is 2022; BibKey should be `Avigad2022`.

2. **Whether to keep German refs in bib**: Teammate B says remove, Teammate C says keep as co-reference. **Resolution**: Keep German refs in `references.bib` (they are historically correct sources) but replace them in Lean file docstrings with Avigad2022 + Prawitz1965. The bib serves as a reference archive; the docstrings are what readers see.

3. **Depth of bot-as-primitive response**: Teammate C warns "acknowledging trade-offs" may not satisfy thomaskwaring. Teammates A/B/D recommend honest acknowledgment without concession. **Resolution**: Present balanced case targeting ctchou as primary audience. Acknowledge thomaskwaring's strongest point (WithBot.some) specifically and explain compatibility. Don't assert superiority; frame as a deliberate design choice with documented trade-offs.

### Gaps Identified

1. **No follow-up task for split-out LTL semantics** — needs creation
2. **LTS transitions request (ctchou point 3)** — not addressed in task description
3. **PR #648 merge conflict** — blocking prerequisite not mentioned
4. **and/or primitives inconsistency** — Connectives.lean vs actual formula types
5. **Modal formula type conflict** — long-term strategic risk (future, not blocking)

### Recommendations

**Implementation priority order**:

1. **Remove `LTL/Semantics/Satisfies.lean`** from PR #649 branch and `Cslib.lean` import
2. **Replace German references** in all Lean file docstrings (14 citations across 4 files) with Avigad2022 + Prawitz1965
3. **Add `Avigad2022`** bib entry to `references.bib`
4. **Verify IsClassical/IsIntuitionistic consistency** with PR #536 (run `lake build`)
5. **Revise PR description**:
   - Stack on merged #536
   - Semantics split out (with follow-up plan noting #587 coordination)
   - Balanced bot-as-primitive rationale (acknowledge WithBot.some, explain temporal/modal motivation)
   - `imp` justified by merged upstream code + FormalizedFormalLogic precedent (not unmerged PRs)
   - LTS transitions explicitly deferred
   - Updated references
6. **Fix `imp` justification** in PR description (narrow change)
7. **Coordinate with fmontesi** on PR #607 overlap before finalizing

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary implementation approach | completed | high |
| B | Alternative approaches and prior art | completed | high |
| C | Critic — gaps and blind spots | completed | high |
| D | Strategic horizons | completed | high |

## References

### Already in references.bib (English — keep)
- Prawitz1965 — Natural Deduction (English, covers Gentzen ND)
- Church1956 — Introduction to Mathematical Logic
- TroelstraVanDalen1988 — Constructivism in Mathematics
- McKinsey1939 — English
- Kamp1968 — English phdthesis (temporal logic)
- Pnueli1977 — FOCS (LTL)
- Burgess1984 — Handbook of Philosophical Logic
- VardiWolper1986 — LICS

### Needs addition
- Avigad2022 — Mathematical Logic and Computation (Cambridge)

### External prior art cited
- FormalizedFormalLogic/Foundation — Lean 4 logic library using `imp`/`falsum`
- Bentzen (arxiv 2310.01916) — Lean formalization using `bot`/`impl`
- Avigad LAMR — Lean textbook companion using `impl`/`fls`
