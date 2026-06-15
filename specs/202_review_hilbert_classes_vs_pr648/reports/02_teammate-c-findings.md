# Teammate C (Critic) Findings: PR #648 Review

**PR Title**: `feat(Logics/Propositional): five-primitive formula type with connective typeclasses`
**PR URL**: https://github.com/leanprover/cslib/pull/648
**Reviewer**: Teammate C (Critic)
**Date**: 2026-06-15

---

## Key Findings

### Finding 1: Direct Naming Conflict with Competing PR #607

**Severity: High**

PR #607 by Fabrizio Montesi (`feat(Logic): logical operators`) is OPEN and introduces
per-file operator typeclasses in `Cslib/Foundations/Logic/Operators/`. The naming choices
between the two PRs are inconsistent on the most critical class:

| Concept | PR #648 (this PR) | PR #607 (Montesi) |
|---------|-------------------|-------------------|
| Implication typeclass | `class HasImp` | `class HasImpl` |
| Implication field | `.imp` | `.impl` |
| Both modified file | `Defs.lean` | `Defs.lean` |
| `HasAnd` | identical definition | identical definition |
| `HasOr` | identical definition | identical definition |
| Diamond | absent (neg-derived) | `class HasDiamond` |
| Negation | absent (neg-derived) | `class HasNot` |
| Biconditional | absent (iff-derived) | `class HasIff` |

The PR body acknowledges this: "If PR #607 merges first, we can align our definitions with its
typeclass names." But this is a forward dependency, not a resolution. Both PRs are currently
open. The coordination is therefore still unresolved at submission time.

The `HasImp` vs `HasImpl` naming difference is not cosmetic: `HasImpl` matches the
upstream Lean 4 constructor name `impl` (which this PR renames to `imp`), creating a two-way
tension with the upstream ecosystem.

Both PRs ALSO modify `Cslib/Logics/Propositional/Defs.lean`. This is a hard merge conflict:
the two PRs cannot be merged independently without a manual reconciliation step.

### Finding 2: Incomplete `PropositionalConnectives` Bundled Class

**Severity: Medium**

The PR introduces `PropositionalConnectives` as a bundled class, but it only extends
`HasBot` and `HasImp`:

```lean
class PropositionalConnectives (F : Type*) extends HasBot F, HasImp F
```

`HasAnd` and `HasOr` are explicitly excluded with the comment "deferred to task 173."
This means the bundled class does not represent full propositional connectives — it is
incomplete by design at submission time. Upstream reviewers will reasonably ask: why
introduce a bundled class that omits `and` and `or` from propositional connectives?

The PR body states that extending `PropositionalConnectives` to include `HasAnd`/`HasOr`
is "deferred to task 173 after the four concrete formula types will be updated." This
references an internal task management system that has no meaning to upstream reviewers.
The comment should either be rewritten to describe the actual dependency (the four
formula types in other logics) or the bundled class should include `HasAnd`/`HasOr`.

### Finding 3: PR Scope Mismatch — Title Says "Propositional" But Connectives.lean Is Modal/Temporal

**Severity: Medium**

The PR title is `feat(Logics/Propositional): ...` but `Connectives.lean` defines classes
that span all four logic levels:

- `HasBox` (modal)
- `HasUntil`, `HasSince` (temporal)
- `ModalConnectives`, `TemporalConnectives`, `BimodalConnectives`

These are not used by any files within the PR's stated scope of "propositional logic." They
exist to support future PRs in the roadmap. Reviewers may question whether introducing
`ModalConnectives`, `TemporalConnectives`, and `BimodalConnectives` is in scope for a PR
about the propositional formula type. This is `Foundations/Logic/Connectives.lean` defining
architecture for logic systems that are not yet part of this PR's diff.

### Finding 4: Internal Task References Embedded in Upstream-Facing Code

**Severity: Medium**

`Connectives.lean` contains explicit references to internal task numbers:

```lean
-- Line 39: "task 173 after `HasAnd` is instantiated on the formula types."
-- Line 108: "Extending `PropositionalConnectives` to include them is deferred to task 173,"
```

These task numbers are meaningless to upstream maintainers and reviewers. They refer to the
contributor's internal project management system (Claude Code task management in
`specs/TODO.md`). Upstream code and comments should not contain references to private
workflow tools. These should be replaced with substantive descriptions of the actual
dependency.

### Finding 5: Breaking Change Scope Not Fully Specified

**Severity: Medium**

The PR lists breaking changes:
- `Proposition.impl` renamed to `Proposition.imp`
- `andE₁`/`andE₂`/`orI₁`/`orI₂` renamed to ASCII variants `andE1`/`andE2`/`orI1`/`orI2`
- `implI`/`implE` renamed to `impI`/`impE`

The upstream `NaturalDeduction/Basic.lean` currently uses `implI`/`implE` (and subscript
variants). The PR states "Files affected upstream: Defs.lean, NaturalDeduction/Basic.lean
(only consumers)." However, any downstream code (test files, examples, other PRs in review
queue) using the old names will silently break. The PR should include a migration guide or
`@deprecated` stubs.

Also: the upstream `Basic.lean` contains a `TODO: this implementation is not capture
avoiding.` comment on `Theory.Derivation.subs`. This pre-existing issue carries into the
PR and may draw reviewer attention, though it is not introduced by this PR.

### Finding 6: `PropositionalConnectives` vs Mathlib's `HImp`/`Bot` Tension Not Fully Resolved

**Severity: Low-Medium**

The PR body explains why CSLib uses `HasImp` instead of Mathlib's `HImp` (field `himp`,
notation `⇨`). However, `Defs.lean` registers both:
- `PropositionalConnectives` instance (CSLib-specific) which provides `imp`
- `Bot (Proposition Atom)` instance (Lean 4 core) which provides `⊥`

The PR simultaneously uses Lean 4 core's `Bot`/`Top` classes for notation (`⊥`, `⊤`) AND
CSLib's `HasBot` class for typeclass polymorphism. This dual registration (`HasBot.bot` vs
`Bot.bot`) means two different fields serve the same role. The PR body notes the distinction
but does not explain why `HasBot` is needed rather than reusing the existing `Bot` typeclass
from Lean 4 core. Reviewers familiar with Mathlib conventions may ask why a `Has*` shadow
of `Bot` is needed rather than simply using `[Bot F]`.

### Finding 7: The `conj'`/`disj'` Lukasiewicz Helpers in `Axioms.lean` Are Outside PR Scope

**Severity: Low**

`Axioms.lean` (which exists on our local main but is NOT in upstream/main and is NOT part of
PR #648's diff) uses `conj'`/`disj'` Lukasiewicz encodings for formula types without `HasAnd`/
`HasOr`. These are labeled as "embedding-layer helpers" with a comment warning they are
classically-only. This is correct, but the naming with trailing apostrophes (`conj'`, `disj'`,
`top'`, `neg'`) is not standard Lean 4 or Mathlib style. Future PRs contributing this file will
need to address the naming convention.

---

## Gaps in Current Analysis

### Gap 1: Zulip Comment Content Unknown

The task description points to a specific reviewer comment at
`https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/near/603367168`.
This comment could not be retrieved (Zulip requires authentication). The review team does
not know what the commenter's specific objection was. This is a significant blind spot:
the whole motivation for the review task is grounded in an unread comment.

**Risk**: The Zulip comment may raise concerns that are entirely different from what the
review team has identified, making the analysis incomplete.

### Gap 2: PR #536 (thomaskwaring) Integration Not Tested

PR #536 "refactors `IsClassical` and `IsIntuitionistic` to refer to inference systems." The
PR description notes this modifies the same files. No analysis has been done on whether the
PR #648 changes to `IsClassical`/`IsIntuitionistic` (now constraint-free, no `[Bot Atom]`)
are compatible with PR #536's inference-system refactor.

### Gap 3: PR #587 (thomaskwaring) Interaction

PR #587 introduces "model and semantics typeclasses (satisfaction relations, valuations,
frame conditions)" and ALSO modifies `Connectives.lean`. No content analysis of PR #587
was available to assess whether both PRs can coexist on that file.

### Gap 4: Instance Resolution Performance Not Tested

The PR introduces a typeclass hierarchy with bundled classes extending multiple atomic
classes. No performance testing via `lean_profile_proof` was done to verify that
instance resolution chains for the bundled classes (`BimodalConnectives extends ModalConnectives
extends PropositionalConnectives`) do not introduce noticeable slowdowns in existing files.

### Gap 5: `lake shake` Import Minimization Not Verified

The PR's CI checklist should include `lake shake` output. Files like `Defs.lean` that now
import `Cslib.Foundations.Logic.Connectives` (new dependency) need to be verified as
minimal. It is possible that `lake shake` would flag the `Connectives` import as unnecessary
for some consumers.

---

## Unvalidated Assumptions

### Assumption 1: "PR #607 can align with our names if we merge first"

The PR states: "if ours merges first, #607 can import from `Connectives.lean`." This assumes
fmontesi will accept the `HasImp`/`HasBot` naming from this PR rather than his `HasImpl`/`HasNot`
naming. There has been no explicit agreement documented. Given that PR #607 was submitted earlier
and uses the existing `impl` constructor name (matching the upstream `impl` before this PR
renames it to `imp`), fmontesi's naming may be considered more natural by maintainers.

### Assumption 2: `Has*` Naming Is Preferred Over Mathlib's Conventions

The PR justifies `HasImp` over Mathlib's `HImp` but assumes CSLib maintainers prefer the
`Has*` uniformity over alignment with Mathlib conventions. This is an architectural decision
that would need explicit maintainer sign-off. The `Has*` pattern is not standard in Mathlib.

### Assumption 3: Modal/Temporal Classes Are Welcome in a Propositional PR

The PR introduces `HasBox`, `HasUntil`, `HasSince`, `ModalConnectives`, etc. within a PR
scoped to "propositional." This assumes reviewers are comfortable with infrastructure for
unrelated logic systems being introduced as a side-effect of a propositional formula change.

### Assumption 4: The Five-Primitive Approach Won't Conflict with Downstream Tableau Systems

The PR roadmap includes tableau systems (PRs 7, 8, 9). The five-primitive signature with
primitive `and` and `or` may require more complex tableau rules than a minimal signature
would. This is a design choice with downstream implications that have not been analyzed in
this PR.

---

## Questions That Should Be Asked

1. **What did the Zulip commenter at near/603367168 say specifically?** The review task
   cannot be properly grounded without reading the actual reviewer comment. All other analysis
   is speculative about what concerns it raised.

2. **Has the CSLib maintainer team (arademaker, fmontesi, chossen2018, thomaskwaring) agreed
   on `HasImp` vs `HasImpl` as the standard name?** Both PRs use different names. One must
   yield to the other. Is there a documented decision?

3. **What is the merge ordering plan for PRs #536, #587, #607, and #648?** All four are open
   and touch overlapping files. A merge ordering plan should be documented.

4. **Why does `PropositionalConnectives` not include `HasAnd` and `HasOr`?** The bundled
   class is introduced in this PR but intentionally incomplete. Should it be introduced later
   when it is complete, or is the current partial form acceptable upstream?

5. **Should `HasBot` shadow Lean 4 core's `Bot` class?** The PR uses both, but does not
   justify why `[HasBot F]` constraints are preferable to `[Bot F]` constraints where Lean 4
   core already provides what is needed.

6. **What is the CSLib policy on internal task references in code comments?** The current
   code references "task 173" which is meaningless to external contributors.

7. **Is the `subs` "not capture avoiding" TODO a blocker for this PR?** It predates this PR,
   but it is an acknowledged correctness gap in a derivation operation. The PR does not
   address it.

---

## Risk Assessment

| Risk | Likelihood | Severity |
|------|-----------|---------|
| PR #607 merge conflict on Defs.lean | High | High |
| `HasImpl` vs `HasImp` naming rejected | Medium | High |
| Modal/temporal scope creep rejected | Medium | Medium |
| Task reference comments flagged | High | Low |
| `PropositionalConnectives` design questioned | High | Medium |
| Performance regression from instance chains | Low | Low |
| `Bot` redundancy questioned | Medium | Low |

**Overall Risk**: The PR has a meaningful probability of requiring significant revision before
merge due to the unresolved coordination with PR #607 (same files, conflicting names). The
CONTRIBUTING.md explicitly states: "for any major development, it is strongly recommended to
discuss first on Zulip... New cross-cutting abstractions / typeclasses / notation schemes."
The `Has*` typeclass hierarchy is explicitly of this type. The Zulip discussion exists but the
specific reviewer concern (message 603367168) is not known to this reviewer.

---

## Confidence Level

**Overall: Medium**

- High confidence on: finding the naming conflict with PR #607 (directly verified in PR
  source), the internal task references, the incomplete bundled class, and the scope
  mismatch.
- Medium confidence on: the Mathlib `HImp`/`Bot` tension (technically valid but may be
  acceptable to maintainers), the merge conflict risk (depends on unread PR content).
- Low confidence on: the Zulip commenter's actual concerns (unread), performance implications
  (untested), compatibility with PRs #536 and #587 (not analyzed).

**Critical unknown**: The Zulip comment at message 603367168 is the explicit motivation for
this review task and could not be read. Any synthesis that claims to address the reviewer's
concern without reading that comment is ungrounded.
