# Teammate D (Horizons) Findings: PR Strategic Assessment

**Role**: Horizons — strategic evaluation of the PR description for upstream acceptance
**Task**: 192 — Research and verify literature references in PR #188 description
**Date**: 2026-06-14
**Confidence**: HIGH for citation analysis and structural recommendations;
MEDIUM for Lean/Mathlib community norms (based on prior PR review evidence)

---

## Key Findings

### 1. Reviewer Persuasion: Literature Justifications

The PR description uses literature citations in two separate sections: the "Why `bot` Should Be Primitive" section (lines 35-53) and the "Naming: `imp` vs `impl`" section (lines 55-58).

**The `bot` justification (lines 35-53) is STRONG.**
Three citations appear: [Church1956] §24, [TroelstraVanDalen1988] Chapter 2, [Johansson1937]. These
support three distinct claims:

- [Church1956] §24: "choice of primitive connectives for propositional logic is discussed here."
  This is accurate: §24 is explicitly titled "Primitive connectives for the propositional calculus."
  However, Church's primary system uses {~, ⊃} (negation, material conditional), not {⊥, →, ∧, ∨}.
  A reviewer who reads Church will find that §24 discusses alternative bases but does not present
  or endorse the five-primitive set. The citation is defensible as pointing to the canonical
  discussion of the topic, but could invite pushback if a reviewer knows Church well.

- [TroelstraVanDalen1988] Chapter 2: "the five-primitive signature with ⊥ is the standard one for
  intuitionistic and minimal logic." This is **accurate**. Chapter 2 of TvD covers intuitionistic
  propositional logic with the standard {⊥, →, ∧, ∨} signature (negation defined as A → ⊥).
  This citation is well-placed and unlikely to attract reviewer objection.

- [Johansson1937]: "defines negation as ¬A := A → ⊥ using ⊥ as an undefined primitive symbol."
  This is **fully accurate and directly supported by the primary source**. Johansson's §1
  explicitly calls the absurdity constant an "undefiniertes Grundzeichen" (undefined primitive
  symbol) and defines negation as a → A without any assumptions on A.

**The `imp` naming justification (lines 55-56) is PROBLEMATIC and likely to draw reviewer pushback.**

The PR states: "The name `imp` is standard in Lean formalization practice (e.g., Lean's own `Prop`
operations and modal logic formalizations)."

The PR previously stated (in an earlier version documented in task 190's literature verification):
"The name `imp` is standard in both the proof theory literature ([Gentzen1935], [Prawitz1965],
[Church1956]) and Lean formalization practice."

The current version in the PR description (lines 55-56) DROPS the literature citations from the
naming section and only says "standard in Lean formalization practice." This is an improvement
over the earlier version, but the claim is still weakly supported:
- Lean's core library does not prominently use a function/constructor named `imp`
- Modal logic formalizations vary: some use `impl`, some `imp`, some `implies`
- The claim "no major proof theory reference uses this abbreviation for implication" (line 57)
  is correct (they use symbols, not English abbreviations), but the alternative claim that `imp`
  is standard Lean practice is not established

A reviewer familiar with Lean/Mathlib conventions may push back: "What is your evidence that
`imp` rather than `impl` is the Lean standard?" The PR description does not provide convincing
evidence. The actual strongest argument (which is not stated) is that `impl` was already
non-standard — changing it to `imp` is justified by "less bad" rather than "standard."

---

### 2. Citation Format

**The citation format is CORRECT for CSLib/doc-gen4 use.**

All BibKeys used in the PR description ([Church1956], [TroelstraVanDalen1988], [Johansson1937])
exist in `/home/benjamin/Projects/cslib/references.bib`. The doc-gen4 cross-linking format
`[Author, *Title*][BibKey]` is used correctly in the Lean source files (e.g., `Connectives.lean`,
`Defs.lean`).

However, the **PR description itself** does not use BibKey hyperlink format — it uses bare brackets
like `[Church1956]` and `[TroelstraVanDalen1988]`. This is acceptable: PR descriptions are
Markdown, not Lean docstrings, so doc-gen4 link syntax is not applicable. The BibKey references
in the description serve as visual identifiers matching the references.bib keys.

**Mathlib PRs do not use structured citation sections.** Mathlib PR descriptions are informal;
reviewers do not expect a References section or formal bibliography. However, CSLib's own PR
conventions (based on prior PR #635 and PR #633 review feedback) show that reviewers do check
literature claims for accuracy. The PR's inline citation style ([BibKey]) is appropriate.

**One gap**: The PR description says "The planned roadmap mirrors the structure of Troelstra & van
Dalen [TroelstraVanDalen1988] Chapter 2" but does not provide section-level citations for the
specific claims. A focused reviewer could ask "Which section of Chapter 2?" The PR text in the
"Why bot Should Be Primitive" section (line 50) says "Chapter 2" which is appropriate at the PR
description level.

---

### 3. Roadmap Communication

The PR includes a 6-PR roadmap (lines 74-84). This is the **right level of detail for a first PR**,
with these caveats:

**Strengths of the current roadmap:**
- Shows scope and ambition (semantic completeness for all three logics)
- Shows reviewers what they are enabling by approving this PR
- Explicitly references TroelstraVanDalen1988 as the structural guide (line 85)
- 6 items is scannable without being overwhelming

**Weaknesses:**
- The roadmap is **inconsistent with the actual task 188 team research recommendation.** The
  task 188 team synthesis (team-research.md) recommended a 7+ PR sequence with a separate
  "PR 0" for Connectives.lean. The PR description merges Connectives.lean into the current PR
  ("PR 1" of the 6-PR sequence), but the current PR's title is about the five-primitive formula
  type and connective typeclasses *combined*. This may be defensible or may invite "this is two
  separate concerns" pushback.

- PR 1 of the roadmap ("This PR: Connective typeclasses + five-primitive formula type + natural
  deduction update") is already bundling three conceptual contributions. Prior review history
  (PR #633 rejection for size, PR #636/637 style) shows CSLib reviewers prefer smaller units.
  However, the total LOC (~300 as described) is within range.

- The roadmap ends at "PR 6: Completeness for IPL" but the team research suggests this
  actually requires 8 PRs at the size constraints reviewers expect. The PR description's 6-PR
  sequence is optimistic on scope per PR.

**Strategic recommendation**: Keep the 6-PR roadmap but add a caveat that "some PRs may be
split if reviewers prefer smaller units." This sets expectations without over-promising.

---

### 4. Relationship to PR #607

The PR states: "Our PR is a superset of PR #607 for the propositional case, while PR #607
focuses on conjunctive/disjunctive operators. If PR #607 merges first, our `Connectives.lean`
can absorb its definitions."

This framing has a strategic problem: calling your PR "a superset" of a maintainer's open PR
can read as dismissive or competitive. fmontesi (the author of PR #607 and a CODEOWNERS
reviewer) will be approving this PR. A diplomatic framing is:

- **Current (problematic)**: "Our PR is a superset of PR #607"
- **Better**: "Our `Connectives.lean` builds directly on the per-operator typeclass direction
  established by PR #607. We define `HasBot` and `HasImp` as additional classes alongside
  PR #607's `HasAnd` and `HasOr`, and add bundled classes (`PropositionalConnectives`) for
  common logic combinations. If PR #607 merges first, our definitions would re-use its
  classes. We welcome coordination on the bundled-class approach."

The current PR also says "compatible" and "can absorb" — these are reasonable, but the
"superset" claim should be removed. Calling your PR a superset of a reviewer's PR is
a diplomatic error.

**Merge conflict risk**: The PR acknowledges `HasAnd`/`HasOr` name overlap with PR #607 but
does not explain what happens concretely if PR #607 merges first. A sentence explicitly
addressing the merge procedure would help: "If PR #607 merges before this one, we will
update `Connectives.lean` to import `HasAnd` and `HasOr` from that PR rather than redefining them."

---

### 5. AI Tools Disclosure

The current AI disclosure reads:
> "This PR was prepared with the assistance of Claude Code (Anthropic). The AI tool was used for:
> - Drafting and extracting files from a development branch to create a clean PR branch
> - Running CI verification commands"

This is **appropriately minimal** for CSLib's context and meets the CONTRIBUTING.md requirement
(following Mathlib AI policy). Prior review history shows:
- CONTRIBUTING.md requires explaining which tool and how
- PR #633/635 reviews did not object to AI disclosure per se
- The prior PR #635 (task 171 research) included a similar disclosure

However, the current disclosure is notable for what it **does not say**: it does not claim the
AI was used for writing the proofs or designing the architecture. This is strategically smart —
reviewers are more comfortable when AI assistance is scoped to "extraction and CI" rather than
"proof design." The framing is appropriate.

One potential improvement: note that the mathematical content, proof architecture, and design
decisions were verified by the human author. The Mathlib AI policy explicitly asks for this
clarification. Adding "All Lean proofs were verified to compile and reviewed by the author" would
preempt any reviewer concern.

---

### 6. Breaking Changes Communication

The PR documents four breaking changes (lines 96-104):
1. `Proposition.impl` renamed to `Proposition.imp`
2. `andE₁`/`andE₂`/`orI₁`/`orI₂` renamed to ASCII variants
3. `[Bot Atom]` constraints removed
4. `[Inhabited Atom]` constraint removed
5. Two instances removed

**The `impl` → `imp` rename justification is WEAK.**

The PR's "Naming" section (lines 55-58) provides two arguments for this breaking change:
1. "standard in Lean formalization practice (e.g., Lean's own `Prop` operations)"
2. "no major proof theory reference uses this abbreviation for implication"

The second argument is correct but proves nothing: neither author (Gentzen, Prawitz, Church)
used "impl" either. It eliminates one option (`impl`) by pointing out it is non-standard, but
does not positively establish that `imp` is preferred.

The first argument ("Lean's own `Prop` operations") is unsubstantiated in the PR. Where in
Lean's `Prop` operations does `imp` appear? If this refers to propositional logic theorems
in Lean's core (like `And.intro`, `Or.inl`), those don't use `imp`. The citation
"e.g., Lean's own `Prop` operations" needs a specific example.

**What makes the rename justifiable:**
- The upstream `impl` was a non-standard abbreviation in the propositional logic context
- `imp` is shorter and follows constructor-naming patterns across related Lean projects
- The consistency with the `imp` prefix in `impI`/`impE` (rule names) is cleaner than
  `impl`/`implI`/`implE`

**Recommended reframing**: Drop the "standard in Lean formalization practice" claim (which is
hard to verify) and instead argue from internal consistency: "The constructor name `imp`
aligns with the derived rule names `impI`/`impE` (introduction/elimination), following the
convention that rule name prefixes match constructor names (cf. `andI`/`andE1`/`andE2`,
`orI1`/`orI2`/`orE`)."

The `andE₁`→`andE1` rename (subscripts to ASCII) is not separately justified in the PR. This
should be explicitly noted: "ASCII names are required by Lean naming guidelines for exported
definitions intended for case-analysis notation."

---

### 7. Overall PR Structure Assessment

**What the PR does well:**
- Clear three-part Summary (new file, refactored Defs, updated ND)
- Detailed technical rationale for `bot` as primitive (the three concrete defects)
- Explicit connection to Zulip discussion
- References known open PR (#607) explicitly
- 6-PR roadmap communicates ambition and scope
- AI disclosure is present and appropriately scoped

**What could be improved:**

1. **The `imp` naming section needs a stronger argument** or should be merged with the bot
   justification. The current Naming section reads as an afterthought.

2. **The PR #607 "superset" claim should be reframed** as collaborative rather than competitive.

3. **The AI disclosure should add human verification statement** for the proofs.

4. **The `bot` justification conflates two separate points**: Church §24 discusses primitive
   connective *choices* generically; Troelstra & van Dalen Chapter 2 establishes the specific
   five-primitive set for intuitionistic logic. These should be separated.

5. **No mention of PR #536** (thomaskwaring's open `Defs.lean` modification). If PR #536
   is still open when this PR is submitted, reviewers will immediately ask about merge conflicts.
   The PR description should acknowledge the conflict explicitly.

---

## Recommended Improvements

### Priority 1: Fix the `imp` naming justification

Current (line 56): "The name `imp` is standard in Lean formalization practice (e.g., Lean's own
`Prop` operations and modal logic formalizations)."

Suggested replacement:
> The name `imp` follows from internal naming consistency: introduction and elimination rule names
> `impI`/`impE` use the `imp` prefix, matching the pattern of `andI`/`andE1`/`andE2`,
> `orI1`/`orI2`/`orE`. The previous `impl` created an inconsistency (`implI`/`implE` were already
> renamed in the natural deduction system). No major proof theory reference uses the abbreviation
> `impl` for implication.

### Priority 2: Reframe the PR #607 relationship

Current (line 70): "Our PR is a superset of PR #607 for the propositional case"

Suggested replacement:
> Our `Connectives.lean` builds on the per-operator typeclass direction of PR #607. We add
> `HasBot` and `HasImp` alongside PR #607's `HasAnd` and `HasOr`, plus bundled classes
> (`PropositionalConnectives`) for the complete propositional language. If PR #607 merges first,
> we will update `Connectives.lean` to import its definitions rather than redefining them.

### Priority 3: Add human verification statement to AI disclosure

Append to AI disclosure:
> The mathematical content, proof architecture, and design decisions were verified by the author
> (Benjamin Brast-McKie). All Lean code compiles on the PR branch with no sorries.

### Priority 4: Acknowledge PR #536

Add a sentence in the PR #607 section or as a separate subsection:
> This PR also intersects with PR #536 (thomaskwaring), which modifies `Defs.lean` and
> `NaturalDeduction/Basic.lean`. If PR #536 merges first, this PR will be rebased accordingly.
> We welcome coordination with @thomaskwaring on sequencing.

### Priority 5: Separate Church §24 from TvD Chapter 2

Current (line 49): "discussed in [Church1956] §24; the five-primitive signature with ⊥ is the
standard one for intuitionistic and minimal logic in [TroelstraVanDalen1988] Chapter 2"

Suggested: Keep this as-is — it is accurate and appropriately scoped. However, if a reviewer
challenges it, be prepared to clarify: "Church §24 discusses the general topic of primitive
connective selection; the specific five-primitive {⊥, →, ∧, ∨} signature is from the
intuitionistic tradition codified in Troelstra & van Dalen."

---

## Strategic Considerations

### For Upstream Acceptance

**The technical content is strong.** The three-defect argument for primitive `bot` is technically
sound and directly answers the prior ctchou objection (PR #635). The literature justifications
for `bot` as primitive are accurate. The structural relationship to PR #607 is acknowledged.

**The main acceptance risk is the rename (breaking change).** Reviewers of established libraries
dislike breaking changes without compelling justification. The `impl` → `imp` rename is the
most likely point of pushback. The current justification ("standard in Lean formalization
practice") will not satisfy a skeptical reviewer. The internal consistency argument (rule names
already use `imp` prefix) is much stronger.

**The roadmap is an asset.** Showing a 6-PR plan toward completeness for three logics demonstrates
that this PR is not an isolated contribution but the beginning of a coherent framework. This
shifts the reviewer mindset from "should we accept this?" to "should we block this series?"

**The Zulip reference** (line 63) is a strong signal that the authors did pre-coordination.
Reviewers who are aware of the Zulip discussion (including fmontesi and arademaker, who are
on the channel) will be more receptive.

### For the Series as a Whole

The PR's 6-item roadmap matches Troelstra & van Dalen Chapter 2's structure (syntax, proof
systems, equivalence, semantics, classical completeness, intuitionistic completeness). This is
a credible intellectual structure that reviewers familiar with the proof theory literature will
recognize. It signals that the contribution is designed as a serious, complete formalization
project — not an ad hoc addition.

One risk: the team research (task 188) found that a 7+ PR sequence is more realistic at the
~300-500 LOC reviewer constraint. If the current PR is approved and PR 2 of the roadmap turns
out to be 800+ LOC, reviewers may ask to split it. This is manageable, but setting expectations
in the current PR ("later PRs may be split if reviewers prefer smaller units") would help.

---

## Confidence Level

| Finding | Confidence | Evidence Base |
|---------|------------|---------------|
| [Johansson1937] claim is fully accurate | HIGH | Primary source OCR (Johansson1937.md) |
| [TroelstraVanDalen1988] Ch. 2 claim is accurate | HIGH | Secondary sources + sources.md |
| [Church1956] §24 claim is accurate (qualified) | MEDIUM | Section title confirmed; full content not available |
| `imp` naming claim is weak/unsupported | HIGH | Task 190 literature verification; prior review evidence |
| BibKeys all exist in references.bib | HIGH | Direct grep of references.bib |
| "superset of PR #607" is diplomatically risky | HIGH | PR review history; fmontesi is CODEOWNERS |
| AI disclosure format is appropriate | HIGH | CONTRIBUTING.md requirement; task 188 Teammate C findings |
| Breaking change justification needs strengthening | HIGH | Task 190 literature verification; reviewer expectations |
| 6-PR roadmap is the right level of detail | MEDIUM | Team research synthesis; PR review history |
