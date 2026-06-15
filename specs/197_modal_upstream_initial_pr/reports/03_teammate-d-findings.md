# Teammate D Findings: Strategic Horizon Analysis for Modal Upstream PR

**Task**: 197 — Scope initial Modal/ upstream PR (~300 LOC)
**Role**: Teammate D (Horizons) — Long-term alignment and strategic direction
**Date**: 2026-06-14

---

## Key Findings

### 1. The Core Strategic Tension: Primitive Sets Define Trajectories

The modal PR is not a routine refactoring — it is a stake-in-the-ground about which mathematical
abstractions CSLib will build on. The upstream currently uses `{atom, not, and, diamond}` (4
constructors); our proposed PR changes this to `{atom, bot, imp, box}` (4 constructors). These
two choices have radically different downstream implications:

| Dimension | Upstream `{not, and, diamond}` | Our `{bot, imp, box}` |
|-----------|-------------------------------|----------------------|
| Intuitionistic compatibility | No: `not` encodes classical negation by position | Yes: `neg := φ → ⊥` works in minimal logic |
| Diamond derivability | Primitive (easy) | Derived via `¬□¬φ` (requires classical logic) |
| K axiom natural form | `□(φ → ψ) → (□φ → □ψ)` derived | `□(φ → ψ) → (□φ → □ψ)` direct |
| Proof obligation for grind | Lighter (match cases = `not`, `and`, `diamond`) | Heavier (must unfold `neg`, `diamond` via lemmata) |
| `Satisfies` match cases | 4 primitive cases | 4 primitive cases |
| Temporal logic extension | Parallel structure likely independent | `TemporalConnectives` extends `PropositionalConnectives` + Until/Since |
| Non-classical modal logic | New `HasDia` primitive needed later anyway | Same: `HasDia` needed for intuitionistic modal |

**Strategic verdict**: Our `{bot, imp, box}` primitive set is architecturally superior for the
long-term roadmap (tense/temporal/bimodal hierarchy, non-classical extensions, substitution
correctness). The cost is heavier explicit proofs that do not use `grind` directly, and the
inability to simply write `theorem not_satisfies` via `induction φ <;> grind`.

### 2. PR #607 Is Not a Blocker — It Is an Opportunity for Alignment

PR #607 (fmontesi) introduces per-operator typeclasses (`HasAnd`, `HasOr`, `HasImpl`, `HasNot`,
`HasBox`, `HasDiamond`, `HasIff`) and registers them for the existing upstream
`{atom, not, and, diamond}` types. Crucially:

- PR #607 has **`CHANGES_REQUESTED`** from chenson2018 (the main concern: grind direction on
  `simp`/`grind =` lemmas, and whether to consolidate into fewer files).
- PR #607 was **not updated** since 2026-06-01 (13 days ago), suggesting it may be stalled.
- The reviewer feedback on PR #607 **partially aligns with our approach**:
  - chenson2018 wants *fewer files* (one file for notation typeclasses) — our `Connectives.lean`
    is a single-file bundled approach, which directly addresses this concern.
  - chenson2018 identified that `grind =` simp direction was wrong in PR #607 (simp should
    unfold notation to constructors, not the reverse). Our proofs use explicit term-mode
    tactics and avoid this pitfall.
  - fmontesi himself is uncertain about file structure ("I don't know yet").

This suggests the upstream community is not yet committed to PR #607's specific structure.
The window for proposing an alternative (our bundled single-file approach) is still open.

### 3. The Upstream Modal Files Already Define the Integration Point

Reading all four upstream modal files reveals the integration landscape:

- **`Basic.lean`**: The central file. Our PR proposes to refactor the `Proposition` type
  and update `Satisfies`. This is the highest-risk change (it's a breaking change to the
  public API of `Cslib.Logic.Modal.Proposition`).
- **`Cube.lean`**: Defines the 15 standard modal logics (K, T, B, 4, 5, S4, S5, etc.) as
  subsets of `Proposition.valid`. This file imports only `Basic.lean` and **needs no changes**
  — it is structurally insensitive to whether `not` or `neg` is primitive.
- **`Denotation.lean`**: Defines `Proposition.denotation` by recursion over constructors.
  Our PR **must update this file** (the match cases change from `not`, `and`, `diamond` to
  `bot`, `imp`, `box`). The diff is moderate (~35 insertions).
- **`LogicalEquivalence.lean`**: Already in upstream! This file defines `Proposition.Equiv`,
  `Proposition.Context`, and instantiates `LogicalEquivalence`. **This is a surprise**: we
  planned to contribute `LogicalEquivalence.lean` as a later PR, but it already exists
  upstream. Our PR's scope changes: we need to *update* this file's context patterns to match
  our new constructors, not contribute it fresh.

**The LogicalEquivalence.lean discovery is significant**: our prior plan said "defer
LogicalEquivalence.lean to PR 3" but it already exists in upstream and imports `Basic.lean`.
If we change `Basic.lean`'s constructors, we must simultaneously update `LogicalEquivalence.lean`
to match (specifically, `Proposition.Context` has branches `not`, `andL`, `andR`, `diamond`
that must become `imp`, `andL`, `andR`, `box`). This adds scope to the PR but cannot be avoided.

### 4. How Our Approach Relates to fmontesi's Approach

The fundamental difference is not just file organization but **the semantic contract of each
primitive**:

- **PR #607**: Keeps diamond as primitive, derives box as `¬◇¬φ`. Registers `HasDiamond`
  directly on `Proposition`, treating diamond as first-class.
- **Our PR**: Makes box primitive, derives diamond as `¬□¬φ`. Registers `HasBox` on
  `Proposition`, treating diamond as notation for a derived term.

These are **dual designs** that are formally equivalent for classical modal logic but diverge
for:
1. Non-classical modal logic (where box and diamond must be independent primitives).
2. The K axiom and necessitation (naturally stated with box).
3. The long-term roadmap: our `Bimodal/` uses `HasBox` as the modal component of the bimodal
   hierarchy, which imports from `Modal/`. Consistency demands `Modal.Proposition` also uses
   `HasBox` primitively.

**A convergence path exists**: The PR #607 operator-typeclass approach and our single-file
bundled approach are compatible if we agree on which operators are primitive. The convergence
point would be: add `HasBox` and `HasBot` and `HasImp` as primitive classes in a single file
(satisfying chenson2018's "fewer files" request), register them on the refactored
`{atom, bot, imp, box}` type, and derive `HasDiamond`/`HasNot` as notation for derived terms.

### 5. Proof Style: Our Explicit Proofs Directly Address the Grind Transparency Issue

PR #607 stalled partly because of `grind =` direction problems and transparency issues. Our
`Basic.lean` uses explicit term-mode and lightweight tactic proofs (`rw`, `constructor`, `exact`,
`obtain`) that avoid `grind` for the frame axiom verification theorems. The K axiom proof is now:
```lean
theorem Satisfies.k : ⇓Modal[m,w ⊨ □(φ₁ → φ₂) → (□φ₁ → □φ₂)] := by
  change Satisfies m w (.imp (.box (.imp φ₁ φ₂)) (.imp (.box φ₁) (.box φ₂)))
  simp only [Satisfies]
  intro h1 h2 w' hr
  exact h1 w' hr (h2 w' hr)
```
This is maximally transparent: no `grind`, no notation layers, direct unfolding. This
addresses exactly what chenson2018 identified as the problem in PR #607 ("I think that if you
add lemmas that make sure to use the notation for judgements... that this becomes a lot easier").

### 6. Decision-Making Power Lies with fmontesi as Lead Maintainer

The GOVERNANCE.md reveals that Fabrizio Montesi is the **lead maintainer** and also the
author of PR #607. This has two implications:

1. **PR #607 will not be rejected** — fmontesi controls the project and his own PR has
   architectural significance to him. We should not position our PR as competing with #607.
2. **Zulip coordination with fmontesi** (not just any reviewer) is the critical path. He
   needs to see our approach as **complementary** (better primitive set, same operator-typeclass
   philosophy) not as a rejection of his work.

The framing for Zulip should be: "We share the operator-typeclass vision of PR #607. We
propose a different primitive set for `Modal.Proposition` that strengthens the architecture
for non-classical extensions and aligns with the textbook treatment. Here is how the two
approaches can converge."

---

## Recommended Approach

### Primary Recommendation: Converge on a Shared Primitive + Typeclass Design

Rather than submitting a PR that conflicts with PR #607, propose a **convergence PR** that:

1. **Adopts PR #607's per-operator typeclass idea** but consolidates into fewer files (directly
   addressing chenson2018's review comment). Use a single `Connectives.lean` or a small
   `Operators.lean` rather than 8 individual files.

2. **Changes the modal primitive set to `{atom, bot, imp, box}`** while implementing PR #607's
   operator-typeclass instances — just registering `HasBox` instead of (or in addition to)
   `HasDiamond`.

3. **Includes `LogicalEquivalence.lean` updates** (since that file already exists upstream
   and must change if `Basic.lean` changes).

4. **Posts the explicit K/T/B/4/5/D proofs** as a resolution to the grind transparency issue
   chenson2018 raised.

This approach makes our PR an *improvement to PR #607* rather than a competitor.

### Fallback Recommendation: Submit Minimal Proof-Only Contribution

If fmontesi insists on keeping `{atom, not, and, diamond}` as primitives and PR #607 moves
toward merge:

1. Submit only **new theorems** to the existing upstream `Basic.lean` (e.g., explicit
   `Satisfies.diamond_iff`, `Satisfies.and_iff` lemmas that address PR #607's grind issue).
2. Submit our **Metalogic/**, **ProofSystem/**, and **Completeness** machinery as new files
   that work over whichever formula type the upstream settles on.
3. Reserve the formula refactoring for a later PR after the typeclass architecture stabilizes.

### Minimum Viable Path to Acceptance

The minimum that maximizes acceptance probability in the short term:

1. **Send Zulip message now** (before any code PR) to fmontesi specifically, not just the
   general CSLib channel. Reference PR #607 and propose convergence.
2. **Wait for PR #607's fate** before submitting any code. If PR #607 merges in its current
   form, rebase our changes on top. If PR #607 stalls further or is revised, present our
   approach as the revision.
3. **First code contribution**: Submit only Metalogic (DeductionTheorem, MCS, Soundness,
   Completeness) that adds content *to the existing* `Modal/` structure, not refactoring it.
   This builds reviewer trust before requesting the breaking primitive change.

---

## Evidence and Examples

### Evidence 1: LogicalEquivalence.lean Is Already in Upstream

```
upstream/main:Cslib/Logics/Modal/LogicalEquivalence.lean  (exists, ~117 lines)
```
This file defines `Proposition.Equiv`, `Proposition.Context` with branches for the existing
`{not, andL, andR, diamond}` constructors, and registers `LogicalEquivalence` for Modal K.
Our change to `Basic.lean` constructors **requires updating this file** as part of the same PR.
The prior plan's assumption that LogicalEquivalence.lean is a "new file to contribute later"
is wrong.

### Evidence 2: PR #607's Grind Problem Validates Our Proof Style

thomaskwaring (reviewer) wrote in PR #607: "I couldn't make the `grind` see through the
notation / typeclass correctly in the proofs of `Satisfies.or_iff_or` & relatives without
explicitly rewriting back to `φ.neg` or whatever". Our `Basic.lean` uses exactly that pattern:
explicit unfold to constructors, then direct proof. This means our proof style is already the
correct answer to the open technical question in PR #607.

### Evidence 3: chenson2018's "One File" Preference Aligns with Our Design

chenson2018 commented on PR #607: "Would it be better to just have one file for these?
If they're just notation typeclasses it seems unlikely to be heavyweight and they're likely to
be used together." Our `Connectives.lean` is exactly one file covering all logic connectives.
This creates a clear narrative: "We heard the review concern and designed accordingly."

### Evidence 4: fmontesi Is Uncertain About the Architecture

fmontesi replied to ctchou's proposal for 3 files (Modal, Tensor, Propositional):
"I don't know yet. We will expand these files with extended classes for expected properties
about these operators, but you're right that some will require importing more than one. I think
we'll know more once we get there." This indicates the architecture is still open to influence.

### Evidence 5: The Bimodal Roadmap Demands Box-as-Primitive

The ROADMAP.md shows `Logics/Bimodal/` uses `HasBox` (inherited from `ModalConnectives`) as
the modal component of the bimodal system. The bimodal embeddings (`ModalEmbedding.lean`)
map `Modal.Proposition.box` to a bimodal box. If upstream's modal type keeps diamond as
primitive and box as derived, the embedding layer becomes significantly more complex
(embedding a derived term into a primitive).

### Evidence 6: PR #607 Stalled with CHANGES_REQUESTED for 13+ Days

PR #607 was last updated 2026-06-01 and has an unresolved `CHANGES_REQUESTED` review from
chenson2018. It has not responded to any reviewer concerns. This suggests an opportunity to
step in with a revised approach that addresses those concerns.

---

## Confidence Level

| Finding | Confidence |
|---------|------------|
| LogicalEquivalence.lean already exists in upstream and must be updated | **High** (verified by git show) |
| PR #607 stalled with unaddressed CHANGES_REQUESTED | **High** (GitHub API verified) |
| Our explicit proofs directly address the grind transparency issue | **High** (chenson2018's comment is verbatim) |
| fmontesi controls the merge decision (lead maintainer) | **High** (GOVERNANCE.md) |
| The upstream community is open to a convergence approach | **Medium** (fmontesi said "I don't know yet") |
| Submitting formula refactoring without Zulip coordination first will be rejected | **Medium-High** (breaking change + open #607 = collision) |
| Submitting Metalogic first (before formula refactoring) would be lower risk | **Medium** (speculation on reviewer priorities) |
| The PR #607 "one file" concern makes our Connectives.lean approach look good | **High** (comment is verbatim; our design matches the request) |

---

## Action Priorities (Strategic Order)

1. **Highest priority**: Draft and send a Zulip message to fmontesi **before** any code PR,
   framing our work as "aligning with PR #607's typeclass vision while proposing a more
   architecturally stable primitive set."

2. **Second priority**: Update the plan to include `LogicalEquivalence.lean` in this PR's scope
   (it must change if `Basic.lean` changes — this was not in the prior plan).

3. **Third priority**: Prepare an alternative PR scope (Metalogic-first, no primitive refactoring)
   as a fallback strategy in case Zulip coordination reveals fmontesi is committed to `{not, and,
   diamond}` primitives.

4. **Lower priority**: The formula refactoring itself — important but gated on community buy-in.
