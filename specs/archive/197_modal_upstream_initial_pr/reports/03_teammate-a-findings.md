# Teammate A Findings: Modal Upstream PR Review

**Task**: 197 — Scope initial Modal/ upstream PR (~300 LOC)
**Role**: Primary Angle — Open PR review and upstream modal logic landscape
**Date**: 2026-06-14
**Scope**: PRs #607, #587, #536, #542, #413, #648; upstream modal files; local fork comparison

---

## Key Findings

### 1. PR #648 (Our Propositional PR) Is OPEN With Zero Reviews

PR #648 was submitted on 2026-06-14 and is currently open with no comments or reviews. This is
the successor to the previously closed PRs #647, #637, and #636 (all self-closed for branch
or content corrections). PR #648 is correctly stacked on nothing — it introduces
`Connectives.lean` and the five-primitive propositional type as a standalone submission.

**Critical implication**: The Modal PR cannot be submitted until #648 receives feedback. The
dependency is hard: our `Basic.lean` imports `Cslib.Foundations.Logic.Connectives` which does
not exist upstream. Until #648 merges, the Modal PR must either (a) be stacked on #648's
branch, or (b) include `Connectives.lean` inline, or (c) omit the `ModalConnectives` instance.

### 2. Upstream Modal/Basic.lean Still Uses `{atom, not, and, diamond}` Primitives

Confirmed by fetching the current upstream main. The upstream file has:
- Primitives: `.atom`, `.not`, `.and`, `.diamond`
- Derived: `.or`, `.impl`, `.iff`, `.box`
- Satisfies: 4 match cases (atom/not/and/diamond), uses `grind` throughout
- Import: `Cslib.Foundations.Relation.Euclidean` (NOT `Data.Relation`)
- No typeclass instances for operator notation

Our local `Basic.lean` uses `{atom, bot, imp, box}` with 6 derived connectives and explicit
proofs. The structural difference is complete and breaking.

### 3. The Relation Module Split (PR #632) Is Already Merged Upstream

PR #632 (merged 2026-06-13) moved `Cslib/Foundations/Data/Relation.lean` into a split
directory `Cslib/Foundations/Relation/`. The upstream Modal/Basic.lean already uses the new
path `Cslib.Foundations.Relation.Euclidean`.

**Critical implication for PR branch**: Our local `Basic.lean` still imports
`Cslib.Foundations.Data.Relation` (the old path). The PR branch MUST change this to
`Cslib.Foundations.Relation.Euclidean`. The local fork does NOT have the Relation split —
so the local fork itself cannot be used as the PR branch without this fix.

### 4. PR #607 (fmontesi's Operator Typeclasses) Is Still Open with Active Review Discussion

PR #607 adds per-file operator typeclasses (`Operators/And.lean`, `Operators/Box.lean`, etc.)
and modifies `Modal/Basic.lean` to add `HasNot`, `HasAnd`, `HasDiamond`, `HasImpl`, `HasIff`,
`HasOr`, `HasBox` instances. It keeps `{atom, not, and, diamond}` as primitives.

Key review comments that shape our strategy:

- **@chenson2018** asked whether characterization lemmas like `not_def (φ) : ¬φ = φ.neg` are
  backwards — they should simplify into notation, not away from it. This is the simp direction
  question.
- **@chenson2018** suggested consolidating all operator files into one file rather than the
  per-file approach. Our `Connectives.lean` already takes this consolidated approach, which
  aligns with what @chenson2018 wants.
- **@thomaskwaring** noted difficulty getting `grind` to see through notation/typeclass layers.
  Our explicit proof style avoids this.
- **@ctchou** proposed three file groupings: `Modal` (box+diamond), `Tensor`, `Propositional`
  (the rest).
- **@fmontesi** acknowledged the organization is provisional.

**Net assessment**: PR #607 is not converging on a decision and has changes_requested from
@chenson2018. The file-per-operator approach is being pushed back on. Our single-file
`Connectives.lean` approach is better aligned with reviewer preferences.

**Structural incompatibility**: PR #607 CANNOT merge alongside our Modal PR without
coordination. They modify the same file and disagree on primitives. PR #607 keeps
`.not`/`.and`/`.diamond` as constructors; our PR removes them as constructors and makes them
derived. This is a fundamental incompatibility.

### 5. PR #587 (thomaskwaring's Notation+Models) Is DRAFT — Different Layer

PR #587 introduces `HasEntails`, `HasInterp`, `HasInterpEntails` typeclasses for
model-theoretic forcing. This is the semantics layer, not the syntax layer. Key observations:

- It imports `Cslib.Logics.Modal.Basic` and builds on top of it.
- It does NOT change `Modal/Basic.lean` directly.
- The `Connectives.lean` it introduces (from PR #587's diff) only has `HasImpl`, `HasAnd`,
  `HasOr`, `HasNot` — no `HasBot`, no `HasBox`. Very different scope from our `Connectives.lean`.
- Status: DRAFT, significant reviewer concerns about notation conventions and design.
- **Impact on our PR**: Orthogonal. PR #587 is a consumer of `Basic.lean`, not a modifier.

### 6. PR #536 (thomaskwaring's Propositional Refactoring) Is OPEN — Approved by fmontesi

PR #536 refactors `IsClassical` and `IsIntuitionistic` in `Propositional/Defs.lean` to refer
to inference systems rather than theories. It has fmontesi's approval and is waiting on
@chenson2018. It does NOT touch `Modal/Basic.lean`.

**Impact on our PR**: Our PR #648 modifies `Propositional/Defs.lean`. If PR #536 merges first,
our PR must be rebased. However PR #536 modifies different parts of `Defs.lean` — the
`IsClassical`/`IsIntuitionistic` definitions — while we modify the `Proposition` inductive and
add `HasBot`/`HasAnd`/`HasOr` instances. Moderate merge conflict risk.

### 7. PR #413 (Linear Temporal Logic) Is OPEN — Different Domain

PR #413 adds LTL semantics on omega-sequences. Changes_requested from @ctchou. Does NOT touch
modal logic files. Relevant to the roadmap (temporal logic is the next level after modal) but
no impact on the initial Modal PR scope.

### 8. Current Upstream Modal File Survey

Files confirmed present in upstream main:
- `Cslib/Logics/Modal/Basic.lean` — uses `{atom, not, and, diamond}` primitives
- `Cslib/Logics/Modal/Denotation.lean` — match cases for `.not`, `.and`, `.diamond`
- `Cslib/Logics/Modal/LogicalEquivalence.lean` — uses `Proposition.Context` with `.not`,
  `.andL`, `.andR`, `.diamond` constructors
- `Cslib/Logics/Modal/Cube.lean` — (confirmed identical to local in prior research)

No modal Proof System or Metalogic files exist upstream. These are entirely local additions.

### 9. Review Dynamics: What Upstream Reviewers Care About

From examining PR #607 and #648 comment threads, active reviewers are:
- **@chenson2018 (Chris Henson)**: Focus on simp/grind lemma direction, file organization
  (prefers fewer files), notation consistency. Has marked PR #607 as changes_requested.
- **@fmontesi (Fabrizio Montesi)**: Author of Modal logic and LTS foundations. Key stakeholder
  for any Modal PR. Approved PR #536. Engaged but patient.
- **@ctchou**: Focuses on notation intuitiveness and consistency. Made the parameterized box
  question for HML.
- **@arademaker**: Requested reviewer on PR #648. Background in logic.
- **@kim-em (Kim Morrison)**: Requested reviewer on PR #637 (our earlier closed Modal PR).

The review community is engaged but deliberate. No PR touching Modal/Basic.lean has merged
recently. The design decisions (primitives, typeclass organization, simp direction) are actively
debated.

---

## Recommended Approach

### Primary Recommendation: Wait for #648 Feedback, Then Submit Modal PR Stacked on It

1. **Do not submit the Modal PR yet.** PR #648 (Propositional) has no reviews. The Modal PR
   depends on `Connectives.lean` from #648. Stack the Modal PR on #648's branch.

2. **When #648 receives feedback**, incorporate any requested changes, then submit the Modal PR
   as a follow-up stacked on #648. Reference #648 explicitly in the Modal PR description.

3. **The Modal PR scope should be: `Basic.lean` + `Denotation.lean`** (~290 LOC total).
   This is unchanged from Report 01's Option A recommendation. Confirmed here by examining
   upstream files directly.

4. **The PR branch must fix the Relation import**. Change `Cslib.Foundations.Data.Relation`
   to `Cslib.Foundations.Relation.Euclidean` in `Basic.lean`. The Relation split (PR #632)
   is already merged upstream, so this is not optional.

5. **Engage on Zulip about PR #607 conflict BEFORE submitting**. The primitive set disagreement
   (bot/imp/box vs. not/and/diamond) requires alignment. Use the review feedback on #607 as
   leverage: @chenson2018 is already pushing for a single consolidated file (which is what
   `Connectives.lean` is) and grind/simp issues with PR #607's approach are documented.

### Alternative: Self-Contained Modal PR (if #648 stalls)

If #648 does not receive feedback within ~2 weeks:
- Submit a smaller `Connectives.lean` containing ONLY `HasBot`, `HasImp`, `HasBox`,
  `PropositionalConnectives`, `ModalConnectives` (omitting `HasAnd`, `HasOr`, `HasUntil`,
  `HasSince`, `BimodalConnectives`) as a standalone PR.
- Submit the Modal PR stacked on this minimal Connectives PR.
- This avoids holding the Modal work hostage to the larger propositional design discussion.

---

## Evidence/Examples

### Upstream primitive set (current main)
```lean
-- Cslib/Logics/Modal/Basic.lean (upstream current)
inductive Proposition (Atom : Type u) : Type u where
  | atom (p : Atom)
  | not (φ : Proposition Atom)     -- PRIMITIVE
  | and (φ₁ φ₂ : Proposition Atom) -- PRIMITIVE
  | diamond (φ : Proposition Atom)  -- PRIMITIVE
```

### Local primitive set (our PR)
```lean
-- Cslib/Logics/Modal/Basic.lean (local fork)
inductive Proposition (Atom : Type u) : Type u where
  | atom (p : Atom)
  | bot                              -- PRIMITIVE (new)
  | imp (φ₁ φ₂ : Proposition Atom)  -- PRIMITIVE (was derived)
  | box (φ : Proposition Atom)       -- PRIMITIVE (was derived)
  deriving DecidableEq, BEq
```

### Import correction needed for PR branch
```lean
-- WRONG (local fork uses old path)
public import Cslib.Foundations.Data.Relation

-- CORRECT (upstream has moved this)
public import Cslib.Foundations.Relation.Euclidean
```

### PR #607 reviewer positions (from GitHub API)
- @chenson2018: "Would it be better to just have one file for these?" (on the Operators/ dir)
- @chenson2018: "Are these simp/grind lemmas all backwards? They should simplify into notation"
- @ctchou: "3 files: Modal (box+diamond), Tensor, Propositional (rest)"
- @thomaskwaring: "couldn't make grind see through notation/typeclass correctly"

### Key structural incompatibilities between PR #607 and our PR
| Aspect | PR #607 | Our approach |
|--------|---------|--------------|
| Primitives | `{atom, not, and, diamond}` | `{atom, bot, imp, box}` |
| `HasNot` | Included (primitive) | Absent (derived) |
| `HasDiamond` | Included (primitive) | Absent (derived) |
| `HasBot` | Absent | Included (primitive) |
| `HasImp`/`HasImpl` | `HasImpl` (name) | `HasImp` (name) |
| File organization | Per-file Operators/ | Single Connectives.lean |
| Simp lemmas | `not_def : ¬φ = φ.neg` etc. | Not needed (primitive names) |

---

## Confidence Levels

| Finding | Confidence | Basis |
|---------|------------|-------|
| PR #648 is open with zero reviews | High | GitHub API confirmed |
| Upstream still uses `{not, and, diamond}` primitives | High | Fetched upstream file |
| PR #632 Relation split is merged; import must change | High | PR confirmed merged; upstream file uses new path |
| PR #607 conflict with our approach | High | Diff analysis + review comments |
| PR #607 not converging on design decision | High | changes_requested, open discussion |
| PR #587 is orthogonal (doesn't touch Basic.lean) | High | Diff analysis |
| Reviewer preferences favor single-file approach | Medium | Inferred from @chenson2018 comments |
| Modal PR stacking on #648 is the right strategy | Medium | Depends on #648 review timeline |
| Coordination on Zulip will unblock the primitive debate | Low | Social dynamics uncertain |
